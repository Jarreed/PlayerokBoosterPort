from __future__ import annotations

from cardinal import Cardinal
import requests
import FunPayAPI.updater.events as FPEvents
import os
import sys
import re
import time
import traceback
import shutil
import json
import uuid
from datetime import datetime, timezone
from threading import Thread, RLock, Event
from json import loads, dumps
from logging import getLogger
from FunPayAPI.types import MessageTypes, OrderStatuses
from typing import Optional, Dict, Any, Tuple, List
from dataclasses import dataclass, field
from requests.adapters import HTTPAdapter
from urllib.parse import quote, urlparse, urlunparse

NAME = "Booster"
VERSION = "3.4.14"
CREDITS = "HoldBoost"
DESCRIPTION = "Автоматическая выдача бустов Discord"
UUID = "001f1c43-6f1e-45f2-bbb3-038d7ecde66b"
BIND_TO_DELETE = None
SETTINGS_PAGE = False
API_URL = "https://api.holdboost.store/v1/external"
API_KEY = "hb_097a80e7302754e1a01eb8d1fb8e744d"
API_FALLBACK_URLS = (
    "https://holdboost.store/api/v1/external",
    "https://api.holdboost.store/v1/external",
)
PUBLIC_UPDATE_URLS = ("https://holdboost.store/api/v1/public",)
API_KEY_PLACEHOLDERS = {
    "",
    "YOUR_API_KEY",
    "YOUR_API_KEY_HERE",
    "<YOUR_API_KEY>",
    "PASTE_API_KEY_HERE",
}
FAST_API_TIMEOUT = 8
FAST_API_RETRIES = 2
SYNC_API_TIMEOUT = 15
SYNC_API_RETRIES = 2
ORDER_CONFIG_REFRESH_TIMEOUT = 3
ORDER_CONFIG_REFRESH_RETRIES = 1
ORDER_CONFIG_REFRESH_MIN_INTERVAL = 90
ORDER_API_TIMEOUT = 120
LOT_SAVE_RETRIES = 3
LOT_SAVE_VERIFY_DELAY = 1.0
LOT_CHECK_MIN_INTERVAL = 10
LOT_TITLE_CACHE_REFRESH_MIN_INTERVAL = 600
STORAGE_PATH = f"storage/plugins/{UUID}"
PLUGIN_FILE_PATH = os.path.abspath(__file__)
BACKUP_PATH = f"{STORAGE_PATH}/backup"
DIRTY_USERS_FILE = "dirty_users.json"
SERVER_COOLDOWNS_FILE = "server_cooldowns.json"
STANDARD_DELIVERY_ATTEMPTS = 2
PRIORITY_DELIVERY_ATTEMPTS = 4
MAX_DELIVERY_ATTEMPTS = STANDARD_DELIVERY_ATTEMPTS
MAX_BOOSTS_PER_PURCHASE = 30
SERVER_DELIVERY_COOLDOWN_SECONDS = 20 * 60
CAPTCHA_GUARD_MIN_ORDER_BOOSTS = 10
CAPTCHA_GUARD_CLEAR_TOKEN_DIVISOR = 5

_base_logger = getLogger("FPC.booster")
_lock = RLock()
_state_lock = RLock()
_processed_orders: set = set()
_processed_orders_lock = RLock()
_processed_refunds: set = set()
_processed_refunds_lock = RLock()
_last_order_config_refresh_ts = 0.0
_last_lot_title_cache_refresh_ts = 0.0
_user_locks: Dict[str, RLock] = {}
_user_locks_guard = RLock()
_init_complete = Event()
REFUND_MESSAGE_TYPES = {
    MessageTypes.REFUND,
    MessageTypes.PARTIAL_REFUND,
    MessageTypes.REFUND_BY_ADMIN,
}


def _normalize_api_url(url: str) -> str:
    value = (url or "").strip().rstrip("/")
    if not value:
        return ""

    parsed = urlparse(value)
    if parsed.netloc == "api.holdboost.store" and parsed.path.startswith("/api/v1/"):
        parsed = parsed._replace(path=parsed.path[len("/api") :])
        value = urlunparse(parsed).rstrip("/")
    return value


def _build_api_urls(primary_url: str = API_URL) -> List[str]:
    urls: List[str] = []
    for raw_url in (primary_url, *API_FALLBACK_URLS):
        url = _normalize_api_url(raw_url)
        if url and url not in urls:
            urls.append(url)
    return urls


def _normalize_api_key(api_key: Optional[str] = None) -> str:
    value = str(API_KEY if api_key is None else api_key).strip()
    match = re.search(r"\bhb_[A-Za-z0-9]{32}\b", value)
    if match:
        return match.group(0)
    if ":" in value and value.split(":", 1)[0].strip().lower() in {"x-api-key", "authorization"}:
        value = value.split(":", 1)[1].strip()
    if value.upper().startswith("API_KEY") and "=" in value:
        value = value.split("=", 1)[1].strip()
    if value.lower().startswith("bearer "):
        value = value[7:].strip()
    value = value.strip().strip('"').strip("'").strip()
    return "" if value in API_KEY_PLACEHOLDERS else value


def _valid_lot_config(amount: Any, months: Any) -> bool:
    try:
        normalized_amount = int(amount)
        normalized_months = int(months)
    except (TypeError, ValueError):
        return False
    return 0 < normalized_amount <= MAX_BOOSTS_PER_PURCHASE and normalized_months in (1, 3)


def _get_user_lock(username: str) -> RLock:
    with _user_locks_guard:
        if username not in _user_locks:
            _user_locks[username] = RLock()
        return _user_locks[username]


def _coerce_float(value: Any) -> Optional[float]:
    if value is None:
        return None
    if isinstance(value, (int, float)):
        return float(value)
    try:
        normalized = str(value).strip().replace(" ", "").replace(",", ".")
        match = re.search(r"-?\d+(?:\.\d+)?", normalized)
        if not match:
            return None
        return float(match.group(0))
    except (TypeError, ValueError):
        return None


def _compare_semver(current: str, latest: str) -> bool:
    def parse(value: str) -> List[int]:
        parts: List[int] = []
        for part in str(value or "").split("."):
            try:
                parts.append(int(part))
            except ValueError:
                parts.append(0)
        return parts

    current_parts = parse(current)
    latest_parts = parse(latest)
    length = max(len(current_parts), len(latest_parts))
    current_parts.extend([0] * (length - len(current_parts)))
    latest_parts.extend([0] * (length - len(latest_parts)))
    return latest_parts > current_parts


def _server_cooldown_key(server: Any) -> str:
    value = str(server or "").strip()
    if not value:
        return ""
    match = re.search(r"discord\.(?:gg|com/invite)/([a-zA-Z0-9-]+)", value, re.IGNORECASE)
    if match:
        return match.group(1).lower()
    parsed = urlparse(value if "://" in value else f"https://{value}")
    path = parsed.path.strip("/")
    if path:
        return path.split("/")[-1].lower()
    return value.lower()


def _format_cooldown_time(expires_at: float) -> Tuple[int, str]:
    remaining_seconds = max(int(expires_at - time.time()), 0)
    minutes = max((remaining_seconds + 59) // 60, 1)
    available_at = datetime.fromtimestamp(expires_at).strftime("%H:%M:%S")
    return minutes, available_at


DEFAULT_MESSAGES = {
    "refund": "🔄 Бусты обнулены после возврата",
    "no_boosts": "❌ У вас нет доступных бустов",
    "confirm": "✅ Сервер: {server}\nБустов: {amount} на {months} мес.\n\nОтправьте 'да' для подтверждения",
    "creating": "⏳ Создаю заказ...",
    "processing": "⏳ Выдаю бусты... {done}/{amount}",
    "success": "✅ Готово! Выдано {done}/{amount} бустов",
    "partial": "⚠️ Заказ завершён частично: выдано {done}/{amount} бустов.",
    "failed": "❌ Ошибка: {error}",
    "not_enough": "❌ Недостаточно бустов",
    "purchase": "✅ Начислено {boosts} бустов на {months} мес.\n\nОтправьте ссылку на Discord сервер (discord.gg/...) для выдачи бустов.",
    "need_link": "🔗 Отправьте ссылку на Discord сервер (discord.gg/...) для выдачи бустов.",
    "rules_enabled": "⚠️ На сервере включены правила или заявки на вступление. Отключите их в настройках сервера и отправьте ссылку ещё раз.",
    "need_one_boost": "⚠️ Выдача бустов возможна только чётным количеством! Пожалуйста, докупите ещё 1 буст для активации.",
    "server_cooldown": "⚠️ Выдача на этот сервер временно ограничена после частичной выдачи. Повторно запросить выдачу можно через {minutes} мин. ({available_at}).",
    "captcha_guard_partial": "⚠️ Частичная выдача {done}/{amount}. Мы вынуждены досрочно завершить выдачу из-за возможных проблем на стороне Discord. Не выданные бусты возвращены на баланс. Повторно запросить выдачу на этот сервер можно через {minutes} мин. ({available_at}).",
}


@dataclass
class PluginSettings:
    messages: Dict[str, str] = field(default_factory=lambda: dict(DEFAULT_MESSAGES))
    message_settings: Dict[str, Dict[str, Any]] = field(default_factory=dict)
    auto_update: bool = True
    sync_interval: int = 60
    markup_percent: float = 0.0
    min_balance_threshold: float = 0.0
    min_stock_threshold: int = 0
    open_stock_threshold: int = 0
    auto_lot_management: bool = True
    price_1m: float = 0.0
    price_3m: float = 0.0

    def update_from_server(self, data: Dict[str, Any]) -> None:
        if not data:
            return
        if "messageSettings" in data and isinstance(data["messageSettings"], dict):
            for key, value in data["messageSettings"].items():
                if not isinstance(value, dict):
                    continue
                text = str(value.get("text", DEFAULT_MESSAGES.get(key, "")))
                enabled = bool(value.get("enabled", True))
                self.message_settings[key] = {
                    "text": text,
                    "enabled": enabled,
                }
                self.messages[key] = text if enabled else ""
        if "messages" in data and isinstance(data["messages"], dict):
            for key, value in data["messages"].items():
                if key not in self.message_settings:
                    self.messages[key] = str(value)
        if "autoUpdate" in data:
            self.auto_update = bool(data["autoUpdate"])
        if "syncInterval" in data:
            try:
                self.sync_interval = max(int(data["syncInterval"]), 60)
            except (ValueError, TypeError):
                pass
        if "markupPercent" in data:
            try:
                self.markup_percent = max(float(data["markupPercent"]), 0.0)
            except (ValueError, TypeError):
                pass
        if "minBalanceThreshold" in data:
            try:
                self.min_balance_threshold = max(float(data["minBalanceThreshold"]), 0.0)
            except (ValueError, TypeError):
                pass
        if "minStockThreshold" in data:
            try:
                self.min_stock_threshold = max(int(float(data["minStockThreshold"])), 0)
            except (ValueError, TypeError):
                pass
        if "openStockThreshold" in data:
            try:
                self.open_stock_threshold = max(int(float(data["openStockThreshold"])), 0)
            except (ValueError, TypeError):
                pass
        if "autoLotManagement" in data:
            self.auto_lot_management = bool(data["autoLotManagement"])
        if "price1m" in data:
            try:
                self.price_1m = max(float(data["price1m"]), 0.0)
            except (ValueError, TypeError):
                pass
        if "price3m" in data:
            try:
                self.price_3m = max(float(data["price3m"]), 0.0)
            except (ValueError, TypeError):
                pass

    def get_message(self, key: str, **kwargs) -> str:
        setting = self.message_settings.get(key)
        if setting is not None and not setting.get("enabled", True):
            return ""
        text = self.messages.get(key, DEFAULT_MESSAGES.get(key, key))
        if kwargs:
            try:
                text = text.format(**kwargs)
            except Exception:
                pass
        return text


plugin_settings = PluginSettings()
_cardinal_ref: Optional[Cardinal] = None
_cardinal_lifecycle_patch_installed = False


def _ensure_cardinal(cardinal: Cardinal):
    global _cardinal_ref
    if _cardinal_ref is None:
        _cardinal_ref = cardinal
        lot_manager.set_cardinal(cardinal)
    _ensure_runtime_event_handlers(cardinal)


def _mark_cardinal_ready(cardinal: Cardinal, reason: str):
    _ensure_cardinal(cardinal)
    lot_manager.schedule_run(reason, force=True)


def _install_cardinal_lifecycle_patch():
    global _cardinal_lifecycle_patch_installed
    if _cardinal_lifecycle_patch_installed:
        return
    if getattr(Cardinal, "_holdboost_lifecycle_patch_installed", False):
        _cardinal_lifecycle_patch_installed = True
        return

    original_run = Cardinal.run
    original_start = Cardinal.start

    def run_with_holdboost(cardinal_self, *args, **kwargs):
        try:
            _mark_cardinal_ready(cardinal_self, "cardinal_run")
        except Exception as e:
            logger.error("LotManager: Cardinal run hook failed", error=e)
        return original_run(cardinal_self, *args, **kwargs)

    def start_with_holdboost(cardinal_self, *args, **kwargs):
        try:
            _mark_cardinal_ready(cardinal_self, "cardinal_start")
        except Exception as e:
            logger.error("LotManager: Cardinal start hook failed", error=e)
        return original_start(cardinal_self, *args, **kwargs)

    Cardinal.run = run_with_holdboost
    Cardinal.start = start_with_holdboost
    Cardinal._holdboost_lifecycle_patch_installed = True
    _cardinal_lifecycle_patch_installed = True
    logger.info("LotManager: Cardinal lifecycle patch installed")


class LotManager:
    """Автоматическое управление лотами FunPay: открытие/закрытие, цены, баланс."""

    def __init__(self):
        self._cardinal: Optional[Cardinal] = None
        self._lot_states: Dict[str, bool] = {}
        self._lot_titles: Dict[str, List[str]] = {}
        self._last_prices: Dict[str, float] = {}
        self._balance_closed: bool = False
        self._last_check_ts: float = 0
        self._run_scheduled: bool = False
        self._run_pending: bool = False
        self._pending_reason: str = "pending"
        self._pending_force: bool = False
        self._waiting_for_cardinal_logged: bool = False

    def set_cardinal(self, cardinal: Cardinal):
        self._cardinal = cardinal
        self._waiting_for_cardinal_logged = False
        logger.info("LotManager: cardinal reference set")
        if _init_complete.is_set():
            self.schedule_run("cardinal_ready", force=True)

    def schedule_run(self, reason: str = "scheduled", force: bool = False):
        with _lock:
            if self._run_scheduled:
                self._run_pending = True
                self._pending_reason = reason
                self._pending_force = self._pending_force or force
                return
            self._run_scheduled = True

        def do_run():
            current_reason = reason
            current_force = force
            try:
                while True:
                    _init_complete.wait(timeout=120)
                    self.run_checks(reason=current_reason, force=current_force)
                    with _lock:
                        if self._run_pending:
                            current_reason = self._pending_reason
                            current_force = self._pending_force
                            self._run_pending = False
                            self._pending_reason = "pending"
                            self._pending_force = False
                            continue
                        self._run_scheduled = False
                        break
            finally:
                with _lock:
                    self._run_scheduled = False
                    self._run_pending = False
                    self._pending_reason = "pending"
                    self._pending_force = False

        Thread(target=do_run, daemon=True).start()

    def run_checks(self, reason: str = "periodic", force: bool = False):
        if not plugin_settings.auto_lot_management:
            logger.debug("LotManager: auto lot management disabled", reason=reason)
            return
        if not self._cardinal:
            if not self._waiting_for_cardinal_logged:
                logger.info("LotManager: waiting for Cardinal initialization", reason=reason)
                self._waiting_for_cardinal_logged = True
            return
        try:
            account = getattr(self._cardinal, "account", None)
            if account is None or not getattr(account, "is_initiated", False):
                logger.info("LotManager: waiting for FunPay account initialization", reason=reason)
                return

            now = time.time()
            if not force and now - self._last_check_ts < LOT_CHECK_MIN_INTERVAL:
                return
            self._last_check_ts = now

            lots = Storage.get_all_lots()
            if not lots:
                logger.debug("LotManager: no configured lots", reason=reason)
                return

            logger.info(
                "LotManager: check started",
                reason=reason,
                lots_count=len(lots),
                markup_percent=plugin_settings.markup_percent,
                min_balance_threshold=plugin_settings.min_balance_threshold,
                min_stock_threshold=plugin_settings.min_stock_threshold,
                open_stock_threshold=plugin_settings.open_stock_threshold,
                price_1m=plugin_settings.price_1m,
                price_3m=plugin_settings.price_3m,
            )

            balance_ok = self._check_balance_threshold(account, lots)
            if not balance_ok:
                return

            self._check_stock_and_toggle_lots(account, lots)
            self._update_lot_prices(account, lots)
        except Exception as e:
            logger.error("LotManager: check failed", error=e)

    def remember_lot_titles(self, lot_id: int, fields: Any) -> None:
        candidates: List[str] = []
        for attr in ("title_ru", "title_en", "description_ru", "description_en"):
            value = _safe_getattr(fields, attr)
            if value:
                candidates.append(str(value))
        raw_fields = _safe_getattr(fields, "fields")
        if isinstance(raw_fields, dict):
            for key in (
                "fields[summary][ru]",
                "fields[summary][en]",
                "fields[desc][ru]",
                "fields[desc][en]",
            ):
                value = raw_fields.get(key)
                if value:
                    candidates.append(str(value))
        unique: List[str] = []
        seen = set()
        for value in candidates:
            normalized = _normalize_match_text(value)
            if not normalized or normalized in seen:
                continue
            seen.add(normalized)
            unique.append(value)
        if unique:
            with _lock:
                self._lot_titles[str(lot_id)] = unique

    def get_cached_lot_titles(self) -> Dict[str, List[str]]:
        with _lock:
            return {key: list(values) for key, values in self._lot_titles.items()}

    def _save_lot_verified(self, account, lot_id: int, mutate, verify, action: str) -> bool:
        last_error: Optional[Exception] = None
        for attempt in range(1, LOT_SAVE_RETRIES + 1):
            try:
                lot_fields = account.get_lot_fields(lot_id)
                before_active = bool(getattr(lot_fields, "active", False))
                before_price = _coerce_float(getattr(lot_fields, "price", None))
                mutate(lot_fields)
                account.save_lot(lot_fields)
                time.sleep(LOT_SAVE_VERIFY_DELAY)
                checked = account.get_lot_fields(lot_id)
                if verify(checked):
                    logger.info(
                        "LotManager: lot save verified",
                        lot_id=lot_id,
                        action=action,
                        attempt=attempt,
                        before_active=before_active,
                        after_active=bool(getattr(checked, "active", False)),
                        before_price=before_price,
                        after_price=_coerce_float(getattr(checked, "price", None)),
                    )
                    return True
                logger.warning(
                    "LotManager: lot save not applied, retrying",
                    lot_id=lot_id,
                    action=action,
                    attempt=attempt,
                    active=bool(getattr(checked, "active", False)),
                    price=_coerce_float(getattr(checked, "price", None)),
                )
            except Exception as e:
                last_error = e
                logger.warning(
                    "LotManager: lot save attempt failed",
                    lot_id=lot_id,
                    action=action,
                    attempt=attempt,
                    error=e,
                )
                time.sleep(min(attempt * 2, 5))
        logger.error(
            "LotManager: lot save failed after retries",
            lot_id=lot_id,
            action=action,
            error=last_error,
        )
        return False

    def _check_balance_threshold(self, account, lots: Dict[str, UserData]) -> bool:
        if plugin_settings.min_balance_threshold <= 0:
            if self._balance_closed:
                self._balance_closed = False
            return True

        try:
            profile = API.get_profile()
            if profile is None:
                logger.warning("LotManager: failed to fetch profile for balance check")
                return True

            balance = profile.get("apiBalance", profile.get("balance", 0.0))
            if balance < plugin_settings.min_balance_threshold:
                if not self._balance_closed:
                    logger.warning(
                        "LotManager: balance below threshold, closing ALL lots",
                        balance=balance,
                        threshold=plugin_settings.min_balance_threshold,
                    )
                else:
                    logger.debug(
                        "LotManager: balance still below threshold, enforcing closed lots",
                        balance=balance,
                        threshold=plugin_settings.min_balance_threshold,
                    )
                self._close_all_lots(account, lots, reason="low_balance")
                self._balance_closed = True
                return False
            else:
                if self._balance_closed:
                    logger.info(
                        "LotManager: balance restored above threshold",
                        balance=balance,
                        threshold=plugin_settings.min_balance_threshold,
                    )
                    self._balance_closed = False
                return True
        except Exception as e:
            logger.error("LotManager: balance check failed", error=e)
            return True

    def _check_stock_and_toggle_lots(self, account, lots: Dict[str, UserData]):
        try:
            stock_data = API.get_stock()
            if stock_data is None:
                logger.warning("LotManager: failed to fetch stock")
                return

            stock_1m = stock_data.get("month1", 0)
            stock_3m = stock_data.get("month3", 0)
            logger.debug("LotManager: stock check", stock_1m=stock_1m, stock_3m=stock_3m)
            opened = 0
            closed = 0
            kept_active = 0
            kept_inactive = 0
            failed = 0
            skipped = 0
            blocked_to_open = 0
            blocked_open_required_min = None
            blocked_open_required_max = 0

            for lot_key, lot_data in lots.items():
                try:
                    lot_id = int(lot_key)
                except (ValueError, TypeError):
                    skipped += 1
                    continue

                if not _valid_lot_config(lot_data.amount, lot_data.months):
                    try:
                        lot_fields = account.get_lot_fields(lot_id)
                        self.remember_lot_titles(lot_id, lot_fields)
                        if not bool(getattr(lot_fields, "active", False)):
                            self._lot_states[lot_key] = False
                            kept_inactive += 1
                            continue

                        def mutate_invalid(fields):
                            fields.active = False

                        def verify_invalid(fields):
                            return not bool(getattr(fields, "active", False))

                        if self._save_lot_verified(
                            account,
                            lot_id,
                            mutate_invalid,
                            verify_invalid,
                            "close_invalid_limit",
                        ):
                            self._lot_states[lot_key] = False
                            closed += 1
                            logger.info(
                                "LotManager: invalid lot CLOSED",
                                lot_id=lot_id,
                                lot_amount=lot_data.amount,
                                months=lot_data.months,
                                max_boosts=MAX_BOOSTS_PER_PURCHASE,
                            )
                        else:
                            failed += 1
                    except Exception as e:
                        failed += 1
                        logger.error(
                            "LotManager: failed to close invalid lot",
                            error=e,
                            lot_id=lot_id,
                        )
                    continue

                stock = stock_1m if lot_data.months == 1 else stock_3m
                close_required_stock = max(lot_data.amount, plugin_settings.min_stock_threshold)
                open_required_stock = max(lot_data.amount, plugin_settings.open_stock_threshold)

                try:
                    lot_fields = account.get_lot_fields(lot_id)
                    self.remember_lot_titles(lot_id, lot_fields)
                    actual_active = bool(getattr(lot_fields, "active", False))
                    required_stock = close_required_stock if actual_active else open_required_stock
                    should_be_active = stock >= required_stock
                    if actual_active == should_be_active:
                        self._lot_states[lot_key] = should_be_active
                        if actual_active:
                            kept_active += 1
                        else:
                            kept_inactive += 1
                            blocked_to_open += 1
                            blocked_open_required_min = (
                                required_stock
                                if blocked_open_required_min is None
                                else min(blocked_open_required_min, required_stock)
                            )
                            blocked_open_required_max = max(
                                blocked_open_required_max, required_stock
                            )
                        continue

                    def mutate(fields, value=should_be_active):
                        fields.active = value

                    def verify(fields, value=should_be_active):
                        return bool(getattr(fields, "active", False)) == value

                    action = "open" if should_be_active else "close"
                    if self._save_lot_verified(account, lot_id, mutate, verify, action):
                        self._lot_states[lot_key] = should_be_active
                        if should_be_active:
                            opened += 1
                        else:
                            closed += 1
                        action_label = "OPENED" if should_be_active else "CLOSED"
                        logger.info(
                            f"LotManager: lot {action_label}",
                            lot_id=lot_id,
                            stock=stock,
                            decision_required_stock=required_stock,
                            lot_amount=lot_data.amount,
                            close_threshold=plugin_settings.min_stock_threshold,
                            open_threshold=plugin_settings.open_stock_threshold,
                            threshold_source="server_config",
                        )
                    else:
                        failed += 1
                except Exception as e:
                    failed += 1
                    logger.error("LotManager: failed to toggle lot", error=e, lot_id=lot_id)

            logger.info(
                "LotManager: stock enforcement summary",
                stock_1m=stock_1m,
                stock_3m=stock_3m,
                close_threshold=plugin_settings.min_stock_threshold,
                open_threshold=plugin_settings.open_stock_threshold,
                threshold_source="server_config",
                blocked_to_open=blocked_to_open,
                blocked_open_required_min=blocked_open_required_min or 0,
                blocked_open_required_max=blocked_open_required_max,
                opened=opened,
                closed=closed,
                kept_active=kept_active,
                kept_inactive=kept_inactive,
                failed=failed,
                skipped=skipped,
            )

        except Exception as e:
            logger.error("LotManager: stock check failed", error=e)

    def _update_lot_prices(self, account, lots: Dict[str, UserData]):
        if plugin_settings.markup_percent <= 0:
            return

        for lot_key, lot_data in lots.items():
            try:
                lot_id = int(lot_key)
            except (ValueError, TypeError):
                continue

            base_price = (
                plugin_settings.price_1m if lot_data.months == 1 else plugin_settings.price_3m
            )
            if base_price <= 0:
                continue

            target_price = round(
                base_price * lot_data.amount * (1 + plugin_settings.markup_percent / 100), 2
            )
            if target_price <= 0:
                continue

            try:
                current_fields = account.get_lot_fields(lot_id)
                self.remember_lot_titles(lot_id, current_fields)
                current_price = _coerce_float(getattr(current_fields, "price", None))

                if current_price is not None and abs(current_price - target_price) < 0.01:
                    self._last_prices[lot_key] = target_price
                    continue

                def mutate(fields, value=target_price):
                    fields.price = value

                def verify(fields, value=target_price):
                    actual = _coerce_float(getattr(fields, "price", None))
                    return actual is not None and abs(actual - value) < 0.01

                if self._save_lot_verified(account, lot_id, mutate, verify, "update_price"):
                    self._last_prices[lot_key] = target_price
                    logger.info(
                        "LotManager: price updated",
                        lot_id=lot_id,
                        old_price=current_price,
                        new_price=target_price,
                        base=base_price,
                        lot_amount=lot_data.amount,
                        markup=plugin_settings.markup_percent,
                    )
            except Exception as e:
                logger.error("LotManager: failed to update price", error=e, lot_id=lot_id)

    def _close_all_lots(self, account, lots: Dict[str, UserData], reason: str = ""):
        for lot_key in lots:
            try:
                lot_id = int(lot_key)
            except (ValueError, TypeError):
                continue
            try:
                lot_fields = account.get_lot_fields(lot_id)
                self.remember_lot_titles(lot_id, lot_fields)
                if not lot_fields.active:
                    self._lot_states[lot_key] = False
                    continue

                def mutate(fields):
                    fields.active = False

                def verify(fields):
                    return not bool(getattr(fields, "active", False))

                if self._save_lot_verified(account, lot_id, mutate, verify, f"close_{reason}"):
                    self._lot_states[lot_key] = False
                    logger.info(f"LotManager: lot CLOSED ({reason})", lot_id=lot_id)
            except Exception as e:
                logger.error("LotManager: failed to close lot", error=e, lot_id=lot_id)


lot_manager = LotManager()


@dataclass
class UserData:
    amount: int = 0
    months: int = 1
    chat_id: int = 0
    priority_delivery: bool = False


@dataclass
class PendingOrder:
    server: str
    amount: int
    months: int
    retried_captcha: bool = False
    request_id: str = field(default_factory=lambda: uuid.uuid4().hex)
    attempts: int = 0
    delivered: int = 0
    deducted: bool = False
    priority: bool = False
    captcha_failures: int = 0


def _is_expected_network_error(error: Exception) -> bool:
    return isinstance(
        error,
        (
            requests.exceptions.ConnectionError,
            requests.exceptions.Timeout,
            requests.exceptions.ChunkedEncodingError,
            ConnectionResetError,
        ),
    )


class Logger:
    def __init__(self, base_logger=None):
        self._logger = base_logger or _base_logger

    def _ts(self) -> str:
        return datetime.now(timezone.utc).isoformat(timespec="milliseconds")

    def _ctx(self, **context: Any) -> str:
        if not context:
            return ""
        parts = []
        for key, value in context.items():
            if value is None:
                continue
            if isinstance(value, float):
                parts.append(f"{key}={value:.3f}")
            elif isinstance(value, str) and " " in value:
                parts.append(f'{key}="{value}"')
            else:
                parts.append(f"{key}={value}")
        return " | " + ", ".join(parts) if parts else ""

    def _fmt(self, event: str, level: str, **context: Any) -> str:
        return f"[{self._ts()}] [{level}] {event}{self._ctx(**context)}"

    def info(self, event: str, **ctx: Any) -> None:
        self._logger.info(self._fmt(event, "INFO", **ctx))

    def error(
        self,
        event: str,
        error: Optional[Exception] = None,
        include_traceback: Optional[bool] = None,
        **ctx: Any,
    ) -> None:
        if error is not None:
            ctx["error_type"] = type(error).__name__
            ctx["error_message"] = str(error)
        self._logger.error(self._fmt(event, "ERROR", **ctx))
        if include_traceback is None:
            include_traceback = error is not None and not _is_expected_network_error(error)
        if error is not None and include_traceback:
            for line in traceback.format_exception(type(error), error, error.__traceback__):
                for sub in line.rstrip().split("\n"):
                    self._logger.error(f"  {sub}")

    def debug(self, event: str, **ctx: Any) -> None:
        self._logger.debug(self._fmt(event, "DEBUG", **ctx))

    def warning(self, event: str, **ctx: Any) -> None:
        self._logger.warning(self._fmt(event, "WARNING", **ctx))


logger = Logger()


class MessageDeduplicator:
    def __init__(self, max_size: int = 1000, ttl: float = 3600):
        self._max_size = max_size
        self._ttl = ttl
        self._lock = RLock()
        self._processed: Dict[int, float] = {}

    def check_and_mark(self, message_id: int) -> bool:
        with self._lock:
            if message_id in self._processed:
                return False
            if len(self._processed) >= self._max_size:
                self._evict()
            self._processed[message_id] = time.time()
            return True

    def _evict(self) -> None:
        if not self._processed:
            return
        keep = self._max_size // 2
        sorted_entries = sorted(self._processed.items(), key=lambda x: x[1], reverse=True)
        self._processed.clear()
        for msg_id, ts in sorted_entries[:keep]:
            self._processed[msg_id] = ts


message_deduplicator = MessageDeduplicator()


class StorageRecovery:
    def __init__(self, storage_path: str = STORAGE_PATH):
        self.storage_path = storage_path
        self.backup_path = os.path.join(storage_path, "backups")

    def _ensure_backup_dir(self) -> None:
        os.makedirs(self.backup_path, exist_ok=True)

    def create_backup(self, filename: str) -> Optional[str]:
        source_path = os.path.join(self.storage_path, filename)
        if not os.path.exists(source_path):
            return None
        try:
            self._ensure_backup_dir()
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            backup_file = os.path.join(self.backup_path, f"{filename}.{timestamp}.backup")
            shutil.copy2(source_path, backup_file)
            self._cleanup_old_backups(filename)
            return backup_file
        except Exception as e:
            logger.error("Failed to create backup", error=e, filename=filename)
            return None

    def _cleanup_old_backups(self, filename: str) -> None:
        try:
            backups = []
            for f in os.listdir(self.backup_path):
                if f.startswith(filename) and f.endswith(".backup"):
                    full_path = os.path.join(self.backup_path, f)
                    backups.append((full_path, os.path.getmtime(full_path)))
            backups.sort(key=lambda x: x[1], reverse=True)
            for path, _ in backups[5:]:
                try:
                    os.remove(path)
                except Exception:
                    pass
        except Exception:
            pass

    def get_latest_backup(self, filename: str) -> Optional[str]:
        try:
            if not os.path.exists(self.backup_path):
                return None
            backups = []
            for f in os.listdir(self.backup_path):
                if f.startswith(filename) and f.endswith(".backup"):
                    full_path = os.path.join(self.backup_path, f)
                    backups.append((full_path, os.path.getmtime(full_path)))
            if not backups:
                return None
            backups.sort(key=lambda x: x[1], reverse=True)
            return backups[0][0]
        except Exception:
            return None

    def safe_load(self, filename: str, default: Dict = None) -> Dict[str, Any]:
        if default is None:
            default = {}
        filepath = os.path.join(self.storage_path, filename)
        if not os.path.exists(filepath):
            return default
        try:
            with open(filepath, "r", encoding="utf-8") as f:
                content = f.read()
                if not content.strip():
                    return default
                return loads(content)
        except (json.JSONDecodeError, ValueError):
            success, data = self._attempt_recovery(filepath, filename)
            return data if data is not None else default
        except Exception as e:
            logger.error("Failed to load storage", error=e, filename=filename)
            return default

    def _attempt_recovery(self, filepath: str, filename: str) -> Tuple[bool, Optional[Dict]]:
        logger.warning("Attempting storage recovery", filename=filename)
        backup_path = self.get_latest_backup(filename)
        if backup_path:
            try:
                with open(backup_path, "r", encoding="utf-8") as f:
                    data = loads(f.read())
                shutil.copy2(backup_path, filepath)
                logger.info("Storage recovered from backup", filename=filename)
                return True, data
            except Exception:
                pass
        try:
            with open(filepath, "r", encoding="utf-8") as f:
                content = f.read()
            for i in range(len(content), 0, -1):
                try:
                    partial = content[:i]
                    if partial.rstrip().endswith("}"):
                        data = loads(partial)
                        with open(filepath, "w", encoding="utf-8") as f:
                            f.write(dumps(data, indent=2, ensure_ascii=False))
                        return True, data
                except Exception:
                    continue
        except Exception:
            pass
        try:
            with open(filepath, "w", encoding="utf-8") as f:
                f.write("{}")
        except Exception:
            pass
        return False, {}

    def safe_save(self, filename: str, data: Dict[str, Any]) -> bool:
        filepath = os.path.join(self.storage_path, filename)
        try:
            if os.path.exists(filepath):
                self.create_backup(filename)
            temp_path = filepath + ".tmp"
            with open(temp_path, "w", encoding="utf-8") as f:
                f.write(dumps(data, indent=2, ensure_ascii=False))
            with open(temp_path, "r", encoding="utf-8") as f:
                loads(f.read())
            shutil.move(temp_path, filepath)
            return True
        except Exception as e:
            logger.error("Failed to save storage", error=e, filename=filename)
            temp_path = filepath + ".tmp"
            if os.path.exists(temp_path):
                try:
                    os.remove(temp_path)
                except Exception:
                    pass
            return False


storage_recovery = StorageRecovery()


class RetryHandler:
    RETRYABLE_EXCEPTIONS = (
        requests.exceptions.ConnectionError,
        requests.exceptions.Timeout,
        ConnectionResetError,
        requests.exceptions.ChunkedEncodingError,
    )
    RETRYABLE_STATUS_CODES = {500, 502, 503, 504, 429}

    def __init__(self, max_retries: int = 3, base_delay: float = 1.0, multiplier: float = 2.0):
        self.max_retries = max_retries
        self.base_delay = base_delay
        self.multiplier = multiplier
        self.retryable_exceptions = self.RETRYABLE_EXCEPTIONS
        self.retryable_status_codes = self.RETRYABLE_STATUS_CODES

    def execute_request(
        self,
        session: requests.Session,
        method: str,
        url: str,
        operation_name: str = "request",
        reset_session_callback=None,
        max_retries: Optional[int] = None,
        **kwargs,
    ) -> requests.Response:
        last_exception = None
        last_response = None
        attempts = max(1, max_retries if max_retries is not None else self.max_retries)
        for attempt in range(attempts):
            try:
                response = session.request(method, url, **kwargs)
                if response.status_code in self.retryable_status_codes:
                    last_response = response
                    if attempt < attempts - 1:
                        delay = self.base_delay * (self.multiplier**attempt)
                        logger.warning(
                            "Retry attempt",
                            attempt=attempt + 1,
                            max_attempts=attempts,
                            delay=delay,
                            reason=f"HTTP {response.status_code}",
                            operation=operation_name,
                        )
                        time.sleep(delay)
                        continue
                    return response
                return response
            except self.RETRYABLE_EXCEPTIONS as e:
                last_exception = e
                if reset_session_callback and isinstance(
                    e, (requests.exceptions.ConnectionError, ConnectionResetError)
                ):
                    try:
                        reset_session_callback()
                    except Exception:
                        pass
                if attempt < attempts - 1:
                    delay = self.base_delay * (self.multiplier**attempt)
                    logger.warning(
                        "Retry attempt",
                        attempt=attempt + 1,
                        max_attempts=attempts,
                        delay=delay,
                        reason=str(e)[:100],
                        operation=operation_name,
                    )
                    time.sleep(delay)
                else:
                    logger.warning(
                        f"All retries exhausted for {operation_name}",
                        error_type=type(e).__name__,
                        error_message=str(e)[:200],
                    )
        if last_exception:
            raise last_exception
        return last_response


retry_handler = RetryHandler()


class SyncClient:
    def __init__(self, api_url: str = API_URL, api_key: str = API_KEY):
        self.api_urls = _build_api_urls(api_url)
        self.api_url = self.api_urls[0] if self.api_urls else _normalize_api_url(API_URL)
        self.api_key = _normalize_api_key(api_key)
        self._session: Optional[requests.Session] = None
        self._last_sync: Optional[datetime] = None
        self._offline_until: float = 0
        self._offline_failures: int = 0

    def _get_session(self) -> requests.Session:
        if self._session is None:
            self._session = requests.Session()
            headers = {
                "User-Agent": f"HoldBoost-Plugin/{VERSION}",
                "Accept": "application/json",
                "Content-Type": "application/json",
            }
            if self.api_key:
                headers["X-API-Key"] = self.api_key
            self._session.headers.update(headers)
        return self._session

    def _reset_session(self) -> None:
        if self._session:
            try:
                self._session.close()
            except Exception:
                pass
            self._session = None

    @property
    def last_sync(self) -> Optional[datetime]:
        return self._last_sync

    def is_backing_off(self) -> bool:
        return time.time() < self._offline_until

    def _skip_if_backing_off(self, operation: str) -> bool:
        remaining = int(max(self._offline_until - time.time(), 0))
        if remaining <= 0:
            return False
        logger.warning(
            "API temporarily unavailable, skipping request",
            operation=operation,
            retry_after=remaining,
        )
        return True

    def _mark_online(self) -> None:
        self._offline_failures = 0
        self._offline_until = 0

    def _mark_offline(self, operation: str, error: Exception) -> None:
        self._offline_failures = min(self._offline_failures + 1, 5)
        retry_after = min(300, 30 * (2 ** (self._offline_failures - 1)))
        self._offline_until = time.time() + retry_after
        logger.warning(
            "API request failed, entering backoff",
            operation=operation,
            retry_after=retry_after,
            error_type=type(error).__name__,
            error_message=str(error)[:200],
        )

    def _ordered_api_urls(self) -> List[str]:
        return [self.api_url] + [url for url in self.api_urls if url != self.api_url]

    def _request_from_urls(
        self,
        urls: List[str],
        method: str,
        endpoint: str,
        operation_name: str,
        timeout: int,
        max_retries: Optional[int] = None,
    ) -> requests.Response:
        last_exception: Optional[Exception] = None
        last_response: Optional[requests.Response] = None
        endpoint = endpoint.lstrip("/")

        for index, api_url in enumerate(urls):
            try:
                response = retry_handler.execute_request(
                    session=self._get_session(),
                    method=method,
                    url=f"{api_url}/{endpoint}",
                    operation_name=f"{operation_name}@{api_url}",
                    reset_session_callback=self._reset_session,
                    timeout=timeout,
                    max_retries=max_retries,
                )
                if (
                    response.status_code in retry_handler.retryable_status_codes
                    and index < len(urls) - 1
                ):
                    last_response = response
                    logger.warning(
                        "Update endpoint returned retryable status, trying fallback",
                        operation=operation_name,
                        api_url=api_url,
                        status=response.status_code,
                    )
                    continue
                return response
            except retry_handler.retryable_exceptions as e:
                last_exception = e
                logger.warning(
                    "Update endpoint failed, trying fallback",
                    operation=operation_name,
                    api_url=api_url,
                    error_type=type(e).__name__,
                    error_message=str(e)[:160],
                )
                self._reset_session()

        if last_exception:
            raise last_exception
        if last_response is not None:
            return last_response
        raise RuntimeError("No update endpoints configured")

    def _request(
        self,
        method: str,
        endpoint: str,
        operation_name: str,
        timeout: int,
        max_retries: Optional[int] = None,
        **kwargs,
    ) -> requests.Response:
        last_exception: Optional[Exception] = None
        last_response: Optional[requests.Response] = None
        endpoint = endpoint.lstrip("/")

        ordered_urls = self._ordered_api_urls()
        for index, api_url in enumerate(ordered_urls):
            try:
                response = retry_handler.execute_request(
                    session=self._get_session(),
                    method=method,
                    url=f"{api_url}/{endpoint}",
                    operation_name=f"{operation_name}@{api_url}",
                    reset_session_callback=self._reset_session,
                    timeout=timeout,
                    max_retries=max_retries,
                    **kwargs,
                )
                if (
                    response.status_code in retry_handler.retryable_status_codes
                    and index < len(ordered_urls) - 1
                ):
                    last_response = response
                    logger.warning(
                        "API endpoint returned retryable status, trying fallback",
                        operation=operation_name,
                        api_url=api_url,
                        status=response.status_code,
                    )
                    continue
                if api_url != self.api_url:
                    logger.info("API endpoint switched", operation=operation_name, api_url=api_url)
                self.api_url = api_url
                return response
            except retry_handler.retryable_exceptions as e:
                last_exception = e
                logger.warning(
                    "API endpoint failed, trying fallback",
                    operation=operation_name,
                    api_url=api_url,
                    error_type=type(e).__name__,
                    error_message=str(e)[:160],
                )
                self._reset_session()

        if last_exception:
            raise last_exception
        if last_response is not None:
            return last_response
        raise RuntimeError("No API endpoints configured")

    def fetch_config(
        self,
        timeout: int = FAST_API_TIMEOUT,
        max_retries: Optional[int] = FAST_API_RETRIES,
        operation_name: str = "fetch_config",
        mark_offline: bool = True,
    ) -> Optional[Dict[str, Any]]:
        if self._skip_if_backing_off(operation_name):
            return None
        try:
            response = self._request(
                method="GET",
                endpoint="plugin/config",
                operation_name=operation_name,
                timeout=timeout,
                max_retries=max_retries,
            )
            if response.status_code == 200:
                data = response.json()
                if data.get("success"):
                    config = data.get("data", {})
                    self._last_sync = datetime.now(timezone.utc)
                    self._mark_online()
                    settings = config.get("settings", {}) or {}
                    logger.info(
                        "Config fetched from server",
                        lots_count=len(config.get("lots", {})),
                        users_count=len(config.get("users", {})),
                        auto_lot_management=settings.get("autoLotManagement"),
                        markup_percent=settings.get("markupPercent"),
                        min_balance_threshold=settings.get("minBalanceThreshold"),
                        min_stock_threshold=settings.get("minStockThreshold"),
                        open_stock_threshold=settings.get("openStockThreshold"),
                    )
                    return config
            return None
        except Exception as e:
            if mark_offline:
                self._mark_offline(operation_name, e)
            else:
                logger.warning(
                    "API request failed without global backoff",
                    operation=operation_name,
                    error_type=type(e).__name__,
                    error_message=str(e)[:200],
                )
            return None

    def push_sync(
        self,
        local_state: Dict[str, Any] = None,
        include_users: bool = False,
        include_lots: bool = False,
    ) -> Optional[Dict[str, Any]]:
        if self._skip_if_backing_off("push_sync"):
            return None
        if local_state is None:
            local_state = self._get_local_state(
                include_users=include_users, include_lots=include_lots
            )
        payload = {
            "lots": local_state.get("lots", {}),
            "users": local_state.get("users", {}),
            "pluginVersion": VERSION,
        }
        try:
            response = self._request(
                method="POST",
                endpoint="plugin/sync",
                operation_name="push_sync",
                json=payload,
                timeout=SYNC_API_TIMEOUT,
                max_retries=SYNC_API_RETRIES,
            )
            if response.status_code == 200:
                data = response.json()
                if data.get("success"):
                    result = data.get("data", {})
                    self._last_sync = datetime.now(timezone.utc)
                    self._mark_online()
                    logger.info(
                        "Sync completed",
                        lots_count=len(result.get("lots", {})),
                        users_count=len(result.get("users", {})),
                    )
                    return result
            return None
        except Exception as e:
            self._mark_offline("push_sync", e)
            return None

    def _get_local_state(
        self, include_users: bool = False, include_lots: bool = False
    ) -> Dict[str, Any]:
        lots = {}
        if include_lots:
            with _lock:
                if Storage._lots:
                    lots = {
                        k: {"amount": v.amount, "months": v.months}
                        for k, v in Storage._lots.items()
                        if _valid_lot_config(v.amount, v.months)
                    }
        users = {}
        if include_users:
            with _lock:
                if Storage._users:
                    dirty_users = set(Storage._dirty_users or set())
                    source = {
                        k: v
                        for k, v in Storage._users.items()
                        if not dirty_users or k in dirty_users
                    }
                    users = {
                        k: {"amount": v.amount, "months": v.months, "chat_id": v.chat_id}
                        for k, v in source.items()
                    }
        return {"lots": lots, "users": users}

    def apply_config(
        self,
        config: Dict[str, Any],
        skip_users: bool = False,
        preserve_dirty_users: bool = False,
    ) -> bool:
        if not config:
            return False
        try:
            server_lots = config.get("lots")
            if isinstance(server_lots, dict):
                with _lock:
                    if Storage._lots is None:
                        Storage._lots = {}
                    local_invalid_lots = {
                        k: v
                        for k, v in Storage._lots.items()
                        if not _valid_lot_config(v.amount, v.months)
                    }
                    normalized_lots = {}
                    for k, v in server_lots.items():
                        if not isinstance(v, dict):
                            logger.warning("Skipping invalid lot config", lot_id=k)
                            continue
                        amount = v.get("amount", 0)
                        months = v.get("months", 1)
                        if not _valid_lot_config(amount, months):
                            logger.warning(
                                "Skipping lot outside purchase limits",
                                lot_id=k,
                                amount=amount,
                                months=months,
                                max_boosts=MAX_BOOSTS_PER_PURCHASE,
                            )
                            continue
                        normalized_lots[k] = UserData(amount=int(amount), months=int(months))
                    normalized_lots.update(local_invalid_lots)
                    Storage._lots = normalized_lots
                    Storage._save_lots(sync=False)

            if not skip_users:
                server_users = config.get("users")
                if isinstance(server_users, dict):
                    with _lock:
                        existing_users = Storage._users or {}
                        dirty_users = (
                            set(Storage._dirty_users or set()) if preserve_dirty_users else set()
                        )
                        merged_users = {
                            k: UserData(
                                amount=v.get("amount", 0),
                                months=v.get("months", 1),
                                chat_id=v.get("chat_id", existing_users.get(k, UserData()).chat_id),
                                priority_delivery=bool(
                                    v.get(
                                        "priorityDelivery",
                                        v.get(
                                            "priority_delivery",
                                            existing_users.get(k, UserData()).priority_delivery,
                                        ),
                                    )
                                ),
                            )
                            for k, v in server_users.items()
                        }
                        for username in dirty_users:
                            if username in existing_users:
                                merged_users[username] = existing_users[username]
                        Storage._users = merged_users
                        if not preserve_dirty_users:
                            Storage._dirty_users.clear()
                            Storage._save_dirty_users()
                        Storage._save_users(sync=False)

            server_settings = config.get("settings", {})
            if server_settings:
                plugin_settings.update_from_server(server_settings)

            logger.info(
                "Server config applied",
                lots_count=len(Storage._lots or {}),
                users_count=len(Storage._users or {}),
                dirty_users_count=len(Storage._dirty_users or set()),
                preserve_dirty_users=preserve_dirty_users,
            )
            lot_manager.schedule_run("server_config_applied", force=True)
            return True
        except Exception as e:
            logger.error("Failed to apply server config", error=e)
            return False

    def sync_on_startup(self) -> bool:
        logger.info("Starting initial sync with server")
        config = self.fetch_config()
        if config:
            local_users = {}
            dirty_users = set()
            with _lock:
                local_users = dict(Storage._users or {})
                dirty_users = set(Storage._dirty_users or set())
            if dirty_users:
                logger.warning(
                    "Pushing pending local user sync before applying server users",
                    dirty_users_count=len(dirty_users),
                )
                result = self.push_sync(include_users=True)
                if result:
                    return self.apply_config(result, skip_users=False)
                self.apply_config(config, skip_users=True)
                logger.warning(
                    "Pending local user sync preserved after startup sync failure",
                    dirty_users_count=len(dirty_users),
                )
                return False
            if not config.get("users") and not config.get("lastSync") and local_users:
                logger.info("Migrating local plugin users to server", users_count=len(local_users))
                result = self.push_sync(include_users=True, include_lots=True)
                if result:
                    return self.apply_config(result, skip_users=False)
            return self.apply_config(config, skip_users=False)
        logger.warning("Initial sync failed - using local storage only")
        return False

    def sync_on_change(self) -> bool:
        result = self.push_sync(
            include_users=bool(Storage._dirty_users),
            include_lots=False,
        )
        if result:
            return self.apply_config(result, skip_users=False)
        return False


sync_client = SyncClient()


class Storage:
    _users: Dict[str, UserData] = None
    _pending: Dict[str, PendingOrder] = None
    _lots: Dict[str, UserData] = None
    _server_cooldowns: Dict[str, float] = None
    _initialized: bool = False
    _sync_scheduled: bool = False
    _sync_include_users: bool = False
    _sync_include_lots: bool = False
    _dirty_users: set = None
    _last_sync_ts: float = 0

    @classmethod
    def init(cls):
        if cls._initialized:
            return
        with _lock:
            if cls._initialized:
                return
            cls._users = {}
            cls._pending = {}
            cls._lots = {}
            cls._server_cooldowns = {}
            cls._dirty_users = set()
            cls._last_sync_ts = time.time()
            os.makedirs(STORAGE_PATH, exist_ok=True)
            os.makedirs(BACKUP_PATH, exist_ok=True)
            cls._users = cls._load_json("users.json")
            cls._lots = cls._load_json("lots.json")
            cls._server_cooldowns = cls._load_server_cooldowns()
            cls._dirty_users = cls._load_dirty_users()
            cls._initialized = True

    @classmethod
    def _load_json(cls, filename: str) -> Dict[str, UserData]:
        try:
            raw = storage_recovery.safe_load(filename, default={})
            return {
                k: UserData(
                    amount=v.get("amount", v) if isinstance(v, dict) else v,
                    months=v.get("months", 1) if isinstance(v, dict) else 1,
                    chat_id=v.get("chat_id", 0) if isinstance(v, dict) else 0,
                    priority_delivery=bool(
                        v.get(
                            "priorityDelivery",
                            v.get("priority_delivery", v.get("priority", False)),
                        )
                    )
                    if isinstance(v, dict)
                    else False,
                )
                for k, v in raw.items()
            }
        except Exception as e:
            logger.error(f"Failed to load {filename}", error=e)
            return {}

    @classmethod
    def _load_dirty_users(cls) -> set:
        try:
            raw = storage_recovery.safe_load(DIRTY_USERS_FILE, default={})
            if isinstance(raw, dict):
                return {str(username) for username, value in raw.items() if value}
            if isinstance(raw, list):
                return {str(username) for username in raw}
        except Exception as e:
            logger.error("Failed to load dirty users", error=e)
        return set()

    @classmethod
    def _save_dirty_users(cls) -> None:
        try:
            data = {username: True for username in sorted(cls._dirty_users or set())}
            if not storage_recovery.safe_save(DIRTY_USERS_FILE, data):
                path = f"{STORAGE_PATH}/{DIRTY_USERS_FILE}"
                with open(path, "w", encoding="utf-8") as f:
                    f.write(dumps(data, indent=2, ensure_ascii=False))
        except Exception as e:
            logger.error("Failed to save dirty users", error=e)

    @classmethod
    def _load_server_cooldowns(cls) -> Dict[str, float]:
        try:
            raw = storage_recovery.safe_load(SERVER_COOLDOWNS_FILE, default={})
            if not isinstance(raw, dict):
                return {}
            now_ts = time.time()
            cooldowns: Dict[str, float] = {}
            for key, value in raw.items():
                normalized_key = _server_cooldown_key(key)
                try:
                    expires_at = float(value)
                except (TypeError, ValueError):
                    continue
                if normalized_key and expires_at > now_ts:
                    cooldowns[normalized_key] = expires_at
            return cooldowns
        except Exception as e:
            logger.error("Failed to load server cooldowns", error=e)
            return {}

    @classmethod
    def _save_server_cooldowns(cls) -> None:
        try:
            now_ts = time.time()
            data = {
                key: expires_at
                for key, expires_at in (cls._server_cooldowns or {}).items()
                if expires_at > now_ts
            }
            cls._server_cooldowns = dict(data)
            if not storage_recovery.safe_save(SERVER_COOLDOWNS_FILE, data):
                path = f"{STORAGE_PATH}/{SERVER_COOLDOWNS_FILE}"
                with open(path, "w", encoding="utf-8") as f:
                    f.write(dumps(data, indent=2, ensure_ascii=False))
        except Exception as e:
            logger.error("Failed to save server cooldowns", error=e)

    @classmethod
    def _save_users(cls, sync: bool = True):
        try:
            data = {
                k: {
                    "amount": v.amount,
                    "months": v.months,
                    "chat_id": v.chat_id,
                    "priority_delivery": v.priority_delivery,
                }
                for k, v in cls._users.items()
            }
            if not storage_recovery.safe_save("users.json", data):
                path = f"{STORAGE_PATH}/users.json"
                with open(path, "w", encoding="utf-8") as f:
                    f.write(dumps(data, indent=2, ensure_ascii=False))
            if sync:
                cls._schedule_server_sync(include_users=True)
        except Exception as e:
            logger.error("Failed to save users", error=e)

    @classmethod
    def _save_lots(cls, sync: bool = True):
        try:
            data = {k: {"amount": v.amount, "months": v.months} for k, v in cls._lots.items()}
            if not storage_recovery.safe_save("lots.json", data):
                path = f"{STORAGE_PATH}/lots.json"
                with open(path, "w", encoding="utf-8") as f:
                    f.write(dumps(data, indent=2, ensure_ascii=False))
            if sync:
                cls._schedule_server_sync(include_lots=True)
        except Exception as e:
            logger.error("Failed to save lots", error=e)

    @classmethod
    def _schedule_server_sync(cls, include_users: bool = False, include_lots: bool = False):
        with _lock:
            cls._sync_include_users = cls._sync_include_users or include_users
            cls._sync_include_lots = cls._sync_include_lots or include_lots
            if cls._sync_scheduled:
                return
            cls._sync_scheduled = True

        def do_sync():
            with _lock:
                cls._sync_scheduled = False
                push_users = cls._sync_include_users
                push_lots = cls._sync_include_lots
                cls._sync_include_users = False
                cls._sync_include_lots = False
            try:
                result = sync_client.push_sync(include_users=push_users, include_lots=push_lots)
                if result:
                    with _lock:
                        preserve_dirty = bool(cls._dirty_users) and not push_users
                    sync_client.apply_config(
                        result,
                        skip_users=False,
                        preserve_dirty_users=preserve_dirty,
                    )
                    with _lock:
                        if push_users:
                            cls._dirty_users.clear()
                            cls._save_dirty_users()
                        cls._last_sync_ts = time.time()
            except Exception as e:
                logger.error("Server sync failed", error=e)

        Thread(target=do_sync, daemon=True).start()

    @classmethod
    def _set_local_user(
        cls,
        username: str,
        amount: int,
        months: int,
        chat_id: int = 0,
        priority_delivery: Optional[bool] = None,
        sync: bool = False,
        dirty: bool = False,
    ):
        with _lock:
            if cls._users is None:
                cls._users = {}
            if cls._dirty_users is None:
                cls._dirty_users = set()
            current = cls._users.get(username, UserData())
            cls._users[username] = UserData(
                amount=max(amount, 0),
                months=months or current.months or 1,
                chat_id=chat_id or current.chat_id,
                priority_delivery=current.priority_delivery
                if priority_delivery is None
                else bool(priority_delivery),
            )
            if dirty:
                cls._dirty_users.add(username)
            else:
                cls._dirty_users.discard(username)
            cls._save_dirty_users()
            cls._save_users(sync=sync)

    @classmethod
    def _sync_users_once(cls) -> None:
        def do_sync():
            try:
                result = sync_client.push_sync(include_users=True)
                if result:
                    sync_client.apply_config(result, skip_users=False)
                    with _lock:
                        cls._dirty_users.clear()
                        cls._save_dirty_users()
            except Exception as e:
                logger.error("Deferred user sync failed", error=e)

        Thread(target=do_sync, daemon=True).start()

    @classmethod
    def get_user(cls, username: str) -> UserData:
        if cls._users is None:
            cls.init()
        with _lock:
            user = cls._users.get(username, UserData())
            return UserData(
                amount=user.amount,
                months=user.months,
                chat_id=user.chat_id,
                priority_delivery=user.priority_delivery,
            )

    @classmethod
    def get_server_cooldown(cls, server: Any) -> Optional[float]:
        if cls._server_cooldowns is None:
            cls.init()
        key = _server_cooldown_key(server)
        if not key:
            return None
        with _state_lock:
            expires_at = (cls._server_cooldowns or {}).get(key)
            if not expires_at:
                return None
            if expires_at <= time.time():
                cls._server_cooldowns.pop(key, None)
                cls._save_server_cooldowns()
                return None
            return expires_at

    @classmethod
    def set_server_cooldown(
        cls, server: Any, seconds: int = SERVER_DELIVERY_COOLDOWN_SECONDS
    ) -> Optional[float]:
        if cls._server_cooldowns is None:
            cls.init()
        key = _server_cooldown_key(server)
        if not key:
            return None
        expires_at = time.time() + max(int(seconds), 1)
        with _state_lock:
            if cls._server_cooldowns is None:
                cls._server_cooldowns = {}
            cls._server_cooldowns[key] = expires_at
            cls._save_server_cooldowns()
        return expires_at

    @classmethod
    def set_user(cls, username: str, data: UserData):
        if cls._users is None:
            cls.init()
        with _lock:
            cls._users[username] = data
            cls._dirty_users.add(username)
            cls._save_dirty_users()
            cls._save_users()

    @classmethod
    def add_boosts(cls, username: str, amount: int, months: int, chat_id: int = 0):
        if cls._users is None:
            cls.init()
        current = cls.get_user(username)
        response = API.update_user_balance(username, amount, months)
        if response:
            cls._set_local_user(
                username,
                response.get("amount", current.amount + amount),
                response.get("months", months),
                chat_id=chat_id or current.chat_id,
                priority_delivery=response.get("priorityDelivery", current.priority_delivery),
                sync=False,
            )
            return
        latest = sync_client.fetch_config()
        if latest:
            sync_client.apply_config(latest, skip_users=False)
            synced_user = cls.get_user(username)
            if synced_user.amount >= current.amount + amount:
                logger.info(
                    "Server balance already reflected credit after retryable failure",
                    username=username,
                    amount=synced_user.amount,
                )
                return
        logger.warning(
            "Falling back to local balance credit", username=username, amount=amount, months=months
        )
        cls._set_local_user(
            username,
            current.amount + amount,
            months,
            chat_id=chat_id or current.chat_id,
            sync=False,
            dirty=True,
        )
        cls._sync_users_once()

    @classmethod
    def use_boosts(cls, username: str, amount: int) -> bool:
        if cls._users is None:
            cls.init()
        user = cls.get_user(username)
        if user.amount < amount:
            return False

        response = API.update_user_balance(username, -amount, user.months)
        if not response:
            latest = sync_client.fetch_config()
            if latest:
                sync_client.apply_config(latest, skip_users=False)
                user = cls.get_user(username)
                if user.amount < amount:
                    return False
                response = API.update_user_balance(username, -amount, user.months)
        if not response:
            logger.warning("Balance deduction rejected by server", username=username, amount=amount)
            return False

        cls._set_local_user(
            username,
            response.get("amount", user.amount - amount),
            response.get("months", user.months),
            chat_id=user.chat_id,
            priority_delivery=response.get("priorityDelivery", user.priority_delivery),
            sync=False,
        )
        return True

    @classmethod
    def reset_user(cls, username: str) -> bool:
        if cls._users is None:
            cls.init()
        current = cls.get_user(username)
        if current.amount <= 0 and username not in (cls._users or {}):
            return False

        server_amount = current.amount
        needs_deferred_sync = False
        config = sync_client.fetch_config()
        if config:
            server_user = (config.get("users") or {}).get(username)
            if isinstance(server_user, dict):
                server_amount = max(int(server_user.get("amount", server_amount)), 0)
        if server_amount > 0:
            if not API.update_user_balance(username, -server_amount, current.months):
                needs_deferred_sync = True
        cls._set_local_user(
            username,
            0,
            current.months or 1,
            chat_id=current.chat_id,
            priority_delivery=current.priority_delivery,
            sync=False,
            dirty=needs_deferred_sync,
        )
        if needs_deferred_sync:
            logger.warning(
                "Refund balance sync deferred after API rejection",
                username=username,
                amount=server_amount,
            )
            cls._sync_users_once()
        return True

    @classmethod
    def refund_purchase(cls, username: str, amount: int) -> bool:
        refund_amount = max(_safe_int(amount), 0)
        if refund_amount <= 0:
            return cls.reset_user(username)
        current = cls.get_user(username)
        if current.amount > refund_amount:
            return cls.use_boosts(username, refund_amount)
        return cls.reset_user(username)

    @classmethod
    def get_lot(cls, description: str) -> Optional[UserData]:
        if cls._lots is None:
            cls.init()
        with _lock:
            for key, lot in cls._lots.items():
                if key in description:
                    return lot
            return None

    @classmethod
    def set_lot(cls, key: str, data: UserData):
        if cls._lots is None:
            cls.init()
        with _lock:
            cls._lots[key] = data
            cls._save_lots()

    @classmethod
    def remove_lot(cls, key: str) -> bool:
        if cls._lots is None:
            cls.init()
        with _lock:
            if key in cls._lots:
                del cls._lots[key]
                cls._save_lots()
                return True
            return False

    @classmethod
    def get_all_lots(cls) -> Dict[str, UserData]:
        if cls._lots is None:
            cls.init()
        with _lock:
            return dict(cls._lots)

    @classmethod
    def get_all_users(cls) -> Dict[str, UserData]:
        if cls._users is None:
            cls.init()
        with _lock:
            return dict(cls._users)

    @classmethod
    def set_pending(cls, username: str, order: PendingOrder):
        if cls._pending is None:
            cls.init()
        with _state_lock:
            cls._pending[username] = order

    @classmethod
    def get_pending(cls, username: str) -> Optional[PendingOrder]:
        if cls._pending is None:
            cls.init()
        with _state_lock:
            return cls._pending.get(username)

    @classmethod
    def clear_pending(cls, username: str):
        if cls._pending is None:
            cls.init()
        with _state_lock:
            cls._pending.pop(username, None)

    @classmethod
    def pop_pending(cls, username: str) -> Optional[PendingOrder]:
        if cls._pending is None:
            cls.init()
        with _state_lock:
            return cls._pending.pop(username, None)


class API:
    _session: requests.Session = None
    last_error: Optional[str] = None
    _api_urls: List[str] = _build_api_urls(API_URL)
    _active_api_url: str = _api_urls[0] if _api_urls else _normalize_api_url(API_URL)

    @classmethod
    def _get_session(cls) -> requests.Session:
        if cls._session is None:
            cls._session = requests.Session()
            adapter = HTTPAdapter(pool_connections=1, pool_maxsize=1)
            cls._session.mount("https://", adapter)
            cls._session.mount("http://", adapter)
        return cls._session

    @classmethod
    def _reset_session(cls):
        if cls._session:
            try:
                cls._session.close()
            except Exception:
                pass
        cls._session = None
        cls._get_session()

    @classmethod
    def _ordered_api_urls(cls) -> List[str]:
        return [cls._active_api_url] + [url for url in cls._api_urls if url != cls._active_api_url]

    @classmethod
    def _handle_response(cls, endpoint: str, response: requests.Response) -> Optional[Dict]:
        if response.status_code in (200, 201):
            result = response.json()
            if result.get("success"):
                return result.get("data")
            error_data = result.get("error")
            if isinstance(error_data, dict):
                cls.last_error = str(
                    error_data.get("message") or error_data.get("code") or "Unknown API error"
                )
            else:
                cls.last_error = str(error_data or "Unknown API error")
            logger.warning("API error", endpoint=endpoint, error=cls.last_error)
            return None
        try:
            error_payload = response.json()
            error_data = error_payload.get("error")
            if isinstance(error_data, dict):
                cls.last_error = str(
                    error_data.get("message") or error_data.get("code") or response.status_code
                )
            else:
                cls.last_error = str(error_data or response.status_code)
        except Exception:
            cls.last_error = f"HTTP {response.status_code}"
        logger.warning(
            "HTTP error", endpoint=endpoint, status=response.status_code, error=cls.last_error
        )
        return None

    @classmethod
    def _request(
        cls,
        method: str,
        endpoint: str,
        data: Optional[Dict] = None,
        timeout: int = ORDER_API_TIMEOUT,
        max_retries: Optional[int] = None,
        extra_headers: Optional[Dict[str, str]] = None,
    ) -> Optional[Dict]:
        cls.last_error = None
        endpoint = endpoint.lstrip("/")
        api_key = _normalize_api_key()
        if not api_key:
            cls.last_error = "API key is missing or still set to YOUR_API_KEY"
            logger.warning("API key missing or placeholder", endpoint=endpoint)
            return None
        last_exception: Optional[Exception] = None

        ordered_urls = cls._ordered_api_urls()
        for index, api_url in enumerate(ordered_urls):
            try:
                headers = {
                    "X-API-Key": api_key,
                    "Accept": "application/json",
                    "Connection": "close",
                }
                if extra_headers:
                    headers.update(
                        {str(k): str(v) for k, v in extra_headers.items() if v is not None}
                    )

                response = retry_handler.execute_request(
                    session=cls._get_session(),
                    method=method,
                    url=f"{api_url}/{endpoint}",
                    operation_name=f"{method} {endpoint}@{api_url}",
                    reset_session_callback=cls._reset_session,
                    json=data,
                    headers=headers,
                    timeout=timeout,
                    max_retries=max_retries,
                    verify=True,
                )
                if (
                    response.status_code in retry_handler.retryable_status_codes
                    and index < len(ordered_urls) - 1
                ):
                    logger.warning(
                        "API endpoint returned retryable status, trying fallback",
                        endpoint=endpoint,
                        api_url=api_url,
                        status=response.status_code,
                    )
                    continue
                if api_url != cls._active_api_url:
                    logger.info("API endpoint switched", endpoint=endpoint, api_url=api_url)
                cls._active_api_url = api_url
                return cls._handle_response(endpoint, response)
            except retry_handler.retryable_exceptions as e:
                last_exception = e
                logger.warning(
                    "API endpoint failed, trying fallback",
                    endpoint=endpoint,
                    api_url=api_url,
                    error_type=type(e).__name__,
                    error_message=str(e)[:160],
                )
                cls._reset_session()

        if last_exception:
            cls.last_error = str(last_exception)
            logger.warning(
                "API request failed",
                endpoint=endpoint,
                error_type=type(last_exception).__name__,
                error_message=str(last_exception)[:200],
            )
        return None

    @classmethod
    def get_profile(cls) -> Optional[Dict]:
        return cls._request(
            "GET", "profile", timeout=FAST_API_TIMEOUT, max_retries=FAST_API_RETRIES
        )

    @classmethod
    def get_stock(cls) -> Optional[Dict]:
        return cls._request("GET", "stock", timeout=SYNC_API_TIMEOUT, max_retries=SYNC_API_RETRIES)

    @classmethod
    def create_order(
        cls,
        guild_invite: str,
        amount: int,
        boost_months: int,
        idempotency_key: Optional[str] = None,
    ) -> Optional[Dict]:
        headers = {"X-Idempotency-Key": idempotency_key} if idempotency_key else None
        return cls._request(
            "POST",
            "orders",
            {"guild_invite": guild_invite, "amount": amount, "boost_months": boost_months},
            extra_headers=headers,
        )

    @classmethod
    def get_order(cls, order_id: str) -> Optional[Dict]:
        return cls._request("GET", f"orders/{order_id}")

    @classmethod
    def update_user_balance(cls, username: str, amount_delta: int, months: int) -> Optional[Dict]:
        return cls._request(
            "PATCH",
            f"plugin/users/{quote(username, safe='')}",
            {
                "amountDelta": amount_delta,
                "months": months,
            },
            timeout=SYNC_API_TIMEOUT,
            max_retries=SYNC_API_RETRIES,
        )

    @classmethod
    def validate_invite(cls, invite: str) -> Optional[Dict]:
        return cls._request(
            "POST",
            "plugin/validate-invite",
            {"invite": invite},
            timeout=SYNC_API_TIMEOUT,
            max_retries=SYNC_API_RETRIES,
        )


class AutoUpdater:
    def __init__(self, api_url: str = API_URL, api_key: str = API_KEY):
        self.api_urls = _build_api_urls(api_url)
        self.api_url = self.api_urls[0] if self.api_urls else _normalize_api_url(API_URL)
        self.api_key = _normalize_api_key(api_key)
        self.plugin_path = os.path.abspath(__file__)
        self.backup_dir = f"{STORAGE_PATH}/backups"
        self._backup_path: Optional[str] = None
        self._session: Optional[requests.Session] = None

    def _get_session(self) -> requests.Session:
        if self._session is None:
            self._session = requests.Session()
            headers = {
                "User-Agent": f"HoldBoost-Plugin/{VERSION}",
                "Accept": "application/json",
                "X-Plugin-Version": VERSION,
            }
            if self.api_key:
                headers["X-API-Key"] = self.api_key
            self._session.headers.update(headers)
        return self._session

    def _reset_session(self) -> None:
        if self._session:
            try:
                self._session.close()
            except Exception:
                pass
            self._session = None

    def _ordered_api_urls(self) -> List[str]:
        return [self.api_url] + [url for url in self.api_urls if url != self.api_url]

    def _request_from_urls(
        self,
        urls: List[str],
        method: str,
        endpoint: str,
        operation_name: str,
        timeout: int,
        max_retries: Optional[int] = None,
    ) -> requests.Response:
        last_exception: Optional[Exception] = None
        last_response: Optional[requests.Response] = None
        endpoint = endpoint.lstrip("/")

        for index, api_url in enumerate(urls):
            try:
                response = retry_handler.execute_request(
                    session=self._get_session(),
                    method=method,
                    url=f"{api_url}/{endpoint}",
                    operation_name=f"{operation_name}@{api_url}",
                    reset_session_callback=self._reset_session,
                    timeout=timeout,
                    max_retries=max_retries,
                )
                if (
                    response.status_code in retry_handler.retryable_status_codes
                    and index < len(urls) - 1
                ):
                    last_response = response
                    logger.warning(
                        "Update endpoint returned retryable status, trying fallback",
                        operation=operation_name,
                        api_url=api_url,
                        status=response.status_code,
                    )
                    continue
                return response
            except retry_handler.retryable_exceptions as e:
                last_exception = e
                logger.warning(
                    "Update endpoint failed, trying fallback",
                    operation=operation_name,
                    api_url=api_url,
                    error_type=type(e).__name__,
                    error_message=str(e)[:160],
                )
                self._reset_session()

        if last_exception:
            raise last_exception
        if last_response is not None:
            return last_response
        raise RuntimeError("No update endpoints configured")

    def _request(
        self,
        method: str,
        endpoint: str,
        operation_name: str,
        timeout: int,
        max_retries: Optional[int] = None,
    ) -> requests.Response:
        response = self._request_from_urls(
            self._ordered_api_urls(),
            method,
            endpoint,
            operation_name,
            timeout,
            max_retries,
        )
        return response

    def _request_public(
        self,
        method: str,
        endpoint: str,
        operation_name: str,
        timeout: int,
        max_retries: Optional[int] = None,
    ) -> requests.Response:
        urls = [_normalize_api_url(url) for url in PUBLIC_UPDATE_URLS if _normalize_api_url(url)]
        return self._request_from_urls(urls, method, endpoint, operation_name, timeout, max_retries)

    def check_version(self) -> Tuple[str, str, bool]:
        current = VERSION
        if sync_client.is_backing_off():
            logger.warning("Version check attempting fallback while API is in backoff")
        try:
            response = self._request(
                method="GET",
                endpoint="plugin/version",
                operation_name="version_check",
                timeout=FAST_API_TIMEOUT,
                max_retries=FAST_API_RETRIES,
            )
            if response.status_code == 200:
                data = response.json()
                if data.get("success"):
                    info = data.get("data", {})
                    latest = info.get("latest", current)
                    update_available = info.get("updateAvailable", False)
                    return current, latest, update_available
        except Exception as e:
            logger.warning(
                "Version check failed", error_type=type(e).__name__, error_message=str(e)[:200]
            )
        try:
            response = self._request_public(
                method="GET",
                endpoint="plugin/version",
                operation_name="public_version_check",
                timeout=FAST_API_TIMEOUT,
                max_retries=FAST_API_RETRIES,
            )
            if response.status_code == 200:
                data = response.json()
                if data.get("success"):
                    info = data.get("data", {})
                    latest = info.get("latest", current)
                    return current, latest, _compare_semver(current, latest)
        except Exception as e:
            logger.warning(
                "Public version check failed",
                error_type=type(e).__name__,
                error_message=str(e)[:200],
            )
        return current, current, False

    def download_update(self) -> Optional[bytes]:
        try:
            response = self._request(
                method="GET",
                endpoint="plugin/download",
                operation_name="download_update",
                timeout=60,
                max_retries=SYNC_API_RETRIES,
            )
            if response.status_code == 200:
                content = response.content
                if content and len(content) > 100:
                    return content
        except Exception as e:
            logger.warning(
                "Download update failed", error_type=type(e).__name__, error_message=str(e)[:200]
            )
        try:
            response = self._request_public(
                method="GET",
                endpoint="plugin/download",
                operation_name="public_download_update",
                timeout=60,
                max_retries=SYNC_API_RETRIES,
            )
            if response.status_code == 200:
                content = response.content
                if content and len(content) > 100:
                    logger.info("Update downloaded from public fallback")
                    return content
        except Exception as e:
            logger.warning(
                "Public download update failed",
                error_type=type(e).__name__,
                error_message=str(e)[:200],
            )
        return None

    def _inject_runtime_settings(self, content: bytes) -> bytes:
        try:
            text = content.decode("utf-8")
        except UnicodeDecodeError:
            return content

        api_key = _normalize_api_key()
        if not api_key:
            logger.warning(
                "Update downloaded but API key is missing; keeping downloaded API_KEY unchanged"
            )
            return content

        def replace_setting(name: str, value: str, source: str) -> str:
            pattern = rf"(?m)^{name}\s*=\s*.*$"
            replacement = f"{name} = {json.dumps(value, ensure_ascii=False)}"
            return re.sub(pattern, replacement, source, count=1)

        updated = replace_setting("API_KEY", api_key, text)
        updated = replace_setting("API_URL", API_URL, updated)
        return updated.encode("utf-8")

    def apply_update(self, content: bytes) -> bool:
        try:
            content = self._inject_runtime_settings(content)
            os.makedirs(self.backup_dir, exist_ok=True)
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            self._backup_path = os.path.join(self.backup_dir, f"booster.py.{timestamp}.backup")
            shutil.copy2(self.plugin_path, self._backup_path)
            with open(self.plugin_path, "wb") as f:
                f.write(content)
            with open(self.plugin_path, "rb") as f:
                if f.read() != content:
                    raise IOError("Written content mismatch")
            logger.info("Update applied successfully, restarting process")
            try:
                os.execv(sys.executable, [sys.executable] + sys.argv)
            except OSError as e:
                logger.error("Restart failed, update will apply on next manual restart", error=e)
            return True
        except Exception as e:
            logger.error("Update failed", error=e)
            self.rollback()
            return False

    def rollback(self) -> bool:
        if not self._backup_path or not os.path.exists(self._backup_path):
            return False
        try:
            shutil.copy2(self._backup_path, self.plugin_path)
            logger.info("Rollback completed")
            return True
        except Exception as e:
            logger.error("Rollback failed", error=e)
            return False

    def update_if_available(self) -> bool:
        if not plugin_settings.auto_update:
            logger.info("Auto-update disabled via server settings")
            return False
        current, latest, update_available = self.check_version()
        if not update_available:
            return False
        logger.info("Update available", current=current, latest=latest)
        content = self.download_update()
        if not content:
            return False
        return self.apply_update(content)


auto_updater = AutoUpdater()


def extract_invite(text: str) -> Optional[str]:
    match = re.search(r"discord\.(?:gg|com/invite)/([a-zA-Z0-9-]+)", text)
    return f"https://discord.gg/{match.group(1)}" if match else None


def is_server_settings_error(error: Optional[str]) -> bool:
    normalized = str(error or "").lower()
    return any(
        marker in normalized
        for marker in (
            "server_rules_or_join_requests_enabled",
            "server_rules_enabled",
            "join_requests_enabled",
            "server_gate_enabled",
            "membership screening",
            "rules / join requests",
            "safety setup",
        )
    )


def _normalize_chat_id(chat_id: Any) -> Any:
    if isinstance(chat_id, int):
        return chat_id if chat_id > 0 else 0
    if isinstance(chat_id, str):
        value = chat_id.strip()
        if not value or value == "0":
            return 0
        if value.isdigit():
            parsed = int(value)
            return parsed if parsed > 0 else 0
        return value
    return 0


def send_msg(cardinal: Cardinal, chat_id: Any, username: str, key: str, **kwargs):
    text = plugin_settings.get_message(key, **kwargs)
    if not text.strip():
        return
    chat_id = _normalize_chat_id(chat_id)
    if not chat_id:
        logger.warning(
            "Cannot send message: chat_id is missing", username=username, message_key=key
        )
        return
    try:
        result = cardinal.send_message(
            chat_id=chat_id, message_text=text, chat_name=username, attempts=3
        )
        if not result:
            logger.warning(
                "Message was not delivered", username=username, chat_id=chat_id, message_key=key
            )
        return result
    except Exception as e:
        logger.error(
            "Failed to send message", username=username, chat_id=chat_id, message_key=key, error=e
        )
        return None


def _normalize_match_text(text: Any) -> str:
    if text is None:
        return ""
    value = str(text).lower()
    value = re.sub(r"\s+", " ", value)
    return value.strip()


def _extract_lot_id_from_html(html: str) -> Optional[str]:
    match = re.search(r"(?:offer|offerEdit)\?(?:id|offer)=(\d+)", html)
    if match:
        return match.group(1)
    match = re.search(r'(?:data-offer-id|data-offer|offer_id)=["\']?(\d+)', html)
    if match:
        return match.group(1)
    return None


def _safe_getattr(obj: Any, name: str, default: Any = None) -> Any:
    try:
        return getattr(obj, name, default)
    except Exception:
        return default


def _extract_lot_id_from_object(obj: Any) -> Optional[str]:
    if obj is None:
        return None
    for attr in ("lot_id", "lotId", "offer_id", "offerId", "lot_key", "lotKey"):
        value = _safe_getattr(obj, attr)
        if value is None:
            continue
        text = str(value).strip()
        if text.isdigit():
            return text
    lot_shortcut = _safe_getattr(obj, "lot_shortcut")
    shortcut_id = _safe_getattr(lot_shortcut, "id")
    if shortcut_id is not None:
        text = str(shortcut_id).strip()
        if text.isdigit():
            return text
    return None


def _collect_event_text(event: Any) -> List[str]:
    values: List[str] = []
    detailed_order = _safe_getattr(_safe_getattr(event, "order"), "_order")
    for obj in (
        event,
        _safe_getattr(event, "order"),
        detailed_order,
        _safe_getattr(event, "message"),
    ):
        if obj is None:
            continue
        for attr in (
            "html",
            "description",
            "text",
            "title",
            "short_description",
            "full_description",
        ):
            value = _safe_getattr(obj, attr)
            if not value:
                continue
            try:
                values.append(str(value))
            except Exception:
                continue
    return values


def _lot_text_candidates(lot_obj: Any) -> List[str]:
    if lot_obj is None:
        return []
    values: List[str] = []
    server = _safe_getattr(lot_obj, "server")
    side = _safe_getattr(lot_obj, "side")
    description = _safe_getattr(lot_obj, "description") or _safe_getattr(lot_obj, "title")
    joined = ", ".join(str(part) for part in (server, side, description) if part)
    if joined:
        values.append(joined)
    if description:
        values.append(str(description))
    return values


def _candidate_matches_order(candidate: str, order_text: str) -> bool:
    candidate_norm = _normalize_match_text(candidate)
    order_norm = _normalize_match_text(order_text)
    return bool(candidate_norm and order_norm and candidate_norm in order_norm)


def _match_lot_by_texts(
    texts: List[str],
    lots: Dict[str, UserData],
    profile: Any = None,
) -> Tuple[Optional[str], Optional[UserData], str]:
    if not texts or not lots:
        return None, None, ""

    lot_ids = {str(key) for key in lots.keys()}
    cached_titles = lot_manager.get_cached_lot_titles()
    for key, candidates in cached_titles.items():
        if key not in lot_ids:
            continue
        for text in texts:
            if any(_candidate_matches_order(candidate, text) for candidate in candidates):
                return key, lots[key], "cached_lot_title"

    if profile is not None:
        try:
            profile_lots = list(profile.get_lots())
        except Exception:
            profile_lots = []
        profile_lots.sort(
            key=lambda item: max((len(value) for value in _lot_text_candidates(item)), default=0),
            reverse=True,
        )
        for profile_lot in profile_lots:
            key = str(_safe_getattr(profile_lot, "id", ""))
            if key not in lot_ids:
                continue
            candidates = _lot_text_candidates(profile_lot)
            for text in texts:
                if any(_candidate_matches_order(candidate, text) for candidate in candidates):
                    return key, lots[key], "profile_lot_title"

    for text in texts:
        lot = Storage.get_lot(text)
        if lot is not None:
            for key, known_lot in lots.items():
                if known_lot is lot:
                    return key, known_lot, "storage_text"
    return None, None, ""


def _refresh_lot_title_cache(
    cardinal: Cardinal,
    lots: Dict[str, UserData],
    force: bool = False,
) -> None:
    global _last_lot_title_cache_refresh_ts

    account = getattr(cardinal, "account", None)
    if account is None or not getattr(account, "is_initiated", False):
        return
    now_ts = time.time()
    with _state_lock:
        elapsed = now_ts - _last_lot_title_cache_refresh_ts
        if not force and elapsed < LOT_TITLE_CACHE_REFRESH_MIN_INTERVAL:
            logger.debug(
                "Lot title cache refresh skipped by throttle",
                retry_after=int(LOT_TITLE_CACHE_REFRESH_MIN_INTERVAL - elapsed),
                lots_count=len(lots),
            )
            return
        _last_lot_title_cache_refresh_ts = now_ts
    for key in lots:
        try:
            lot_id = int(key)
        except (TypeError, ValueError):
            continue
        try:
            fields = account.get_lot_fields(lot_id)
            lot_manager.remember_lot_titles(lot_id, fields)
        except Exception as e:
            logger.debug(
                "Lot title cache refresh failed",
                lot_id=lot_id,
                error_type=type(e).__name__,
                error_message=str(e)[:160],
            )


def _resolve_configured_lot(
    cardinal: Cardinal,
    event: Any,
    lots: Dict[str, UserData],
) -> Tuple[Optional[str], Optional[UserData], str]:
    if not lots:
        return None, None, "no_lots"

    foreign_lot_ids: List[str] = []
    for obj in (event, _safe_getattr(event, "order"), _safe_getattr(event, "message")):
        lot_id = _extract_lot_id_from_object(obj)
        if not lot_id:
            continue
        if lot_id in lots:
            return lot_id, lots[lot_id], "event_lot_id"
        foreign_lot_ids.append(lot_id)
    if foreign_lot_ids:
        return None, None, "foreign_event_lot_id"

    foreign_html_lot_ids: List[str] = []
    for text in _collect_event_text(event):
        lot_id = _extract_lot_id_from_html(text)
        if not lot_id:
            continue
        if lot_id in lots:
            return lot_id, lots[lot_id], "html_lot_id"
        foreign_html_lot_ids.append(lot_id)
    if foreign_html_lot_ids:
        return None, None, "foreign_html_lot_id"

    texts = _collect_event_text(event)
    key, lot, source = _match_lot_by_texts(texts, lots, getattr(cardinal, "profile", None))
    if lot:
        return key, lot, source

    try:
        order_obj = _safe_getattr(event, "order")
        if order_obj is not None:
            detailed = cardinal.get_order_from_object(order_obj)
            if detailed is not None:
                texts = _collect_event_text(event) + _collect_event_text(detailed)
                key, lot, source = _match_lot_by_texts(
                    texts, lots, getattr(cardinal, "profile", None)
                )
                if lot:
                    return key, lot, f"detailed_order_{source}"
    except Exception as e:
        logger.warning(
            "Failed to load detailed order for lot matching",
            error_type=type(e).__name__,
            error_message=str(e)[:160],
            order_id=_safe_getattr(_safe_getattr(event, "order"), "id"),
        )

    _refresh_lot_title_cache(cardinal, lots)
    key, lot, source = _match_lot_by_texts(
        _collect_event_text(event), lots, getattr(cardinal, "profile", None)
    )
    if lot:
        return key, lot, f"refreshed_{source}"

    return None, None, "not_found"


def _refresh_server_config_for_order(force: bool = False) -> bool:
    global _last_order_config_refresh_ts

    now_ts = time.time()
    with _state_lock:
        elapsed = now_ts - _last_order_config_refresh_ts
        if not force and elapsed < ORDER_CONFIG_REFRESH_MIN_INTERVAL:
            logger.debug(
                "Order config refresh skipped by throttle",
                retry_after=int(ORDER_CONFIG_REFRESH_MIN_INTERVAL - elapsed),
            )
            return False
        _last_order_config_refresh_ts = now_ts
    try:
        config = sync_client.fetch_config(
            timeout=ORDER_CONFIG_REFRESH_TIMEOUT,
            max_retries=ORDER_CONFIG_REFRESH_RETRIES,
            operation_name="fetch_config_order",
            mark_offline=False,
        )
        if not config:
            return False
        return sync_client.apply_config(config, skip_users=False)
    except Exception as e:
        logger.warning(
            "Order config refresh failed", error_type=type(e).__name__, error_message=str(e)[:160]
        )
        return False


def _is_definite_foreign_lot_source(match_source: str) -> bool:
    return match_source in {"foreign_event_lot_id", "foreign_html_lot_id"}


def _event_matches_configured_lot(event: Any, lots: Dict[str, UserData]) -> bool:
    if not lots:
        return False

    lot_ids = {str(key) for key in lots.keys()}
    for obj in (event, _safe_getattr(event, "order"), _safe_getattr(event, "message")):
        lot_id = _extract_lot_id_from_object(obj)
        if lot_id:
            return lot_id in lot_ids

    for text in _collect_event_text(event):
        lot_id = _extract_lot_id_from_html(text)
        if lot_id:
            return lot_id in lot_ids
        if Storage.get_lot(text) is not None:
            return True
    _, lot, _ = _match_lot_by_texts(_collect_event_text(event), lots)
    if lot is not None:
        return True

    return False


def _resolve_chat_id(cardinal: Cardinal, username: str, fallback_chat_id: Any = 0) -> Any:
    """Resolve FunPay chat_id for a given username.

    Tries multiple strategies:
    1. Use the provided fallback_chat_id if it's valid (> 0).
    2. Look up the chat by username through cardinal.account.get_chat_by_name.
    3. As a last resort, try get_chat_by_name with make_request=True to refresh.
    """
    normalized_fallback = _normalize_chat_id(fallback_chat_id)
    if normalized_fallback:
        return normalized_fallback
    try:
        account = getattr(cardinal, "account", None)
        if account and getattr(account, "is_initiated", False):
            chat = account.get_chat_by_name(username)
            if chat:
                return chat.id
            chat = account.get_chat_by_name(username, make_request=True)
            if chat:
                return chat.id
    except Exception as e:
        logger.warning(
            "Failed to resolve chat_id",
            username=username,
            error_type=type(e).__name__,
            error_message=str(e)[:200],
        )
    return 0


def _refund_identity(event: Any) -> Optional[str]:
    order_id = str(_safe_getattr(_safe_getattr(event, "order"), "id", "") or "").strip().lstrip("#")
    if order_id:
        return f"order:{order_id.upper()}"

    for text in _collect_event_text(event):
        match = re.search(r"#([A-Za-z0-9]{5,})", text)
        if match:
            return f"order:{match.group(1).upper()}"

    message_id = _safe_getattr(_safe_getattr(event, "message"), "id")
    if message_id is not None:
        return f"message:{message_id}"
    return None


def _claim_refund_event(event: Any) -> bool:
    identity = _refund_identity(event)
    if not identity:
        return True
    with _processed_refunds_lock:
        if identity in _processed_refunds:
            logger.info("Duplicate refund skipped", refund_identity=identity)
            return False
        _processed_refunds.add(identity)
        return True


def _handle_refund_event(cardinal: Cardinal, event: Any, source: str) -> None:
    lots = Storage.get_all_lots()
    lot_key, lot, match_source = _resolve_configured_lot(cardinal, event, lots)
    if (
        not lot
        and not _is_definite_foreign_lot_source(match_source)
        and _refresh_server_config_for_order()
    ):
        lots = Storage.get_all_lots()
        lot_key, lot, match_source = _resolve_configured_lot(cardinal, event, lots)
        if lot:
            match_source = f"after_config_refresh_{match_source}"
    if not lot:
        logger.info(
            "Refund ignored: event is not tied to configured lots",
            source=source,
            refund_identity=_refund_identity(event),
            match_source=match_source,
        )
        return

    order = _safe_getattr(event, "order")
    message = _safe_getattr(event, "message")
    username = str(
        _safe_getattr(order, "buyer_username", "") or _safe_getattr(message, "chat_name", "") or ""
    ).strip()
    if not username:
        logger.warning(
            "Refund ignored: buyer username is missing",
            source=source,
            lot_id=lot_key,
            refund_identity=_refund_identity(event),
        )
        return
    refund_identity = _refund_identity(event)
    if not _claim_refund_event(event):
        return

    user = Storage.get_user(username)
    raw_chat_id = (
        _safe_getattr(order, "chat_id", 0) or _safe_getattr(message, "chat_id", 0) or user.chat_id
    )
    chat_id = _resolve_chat_id(cardinal, username, raw_chat_id)
    order_amount = max(_safe_int(_safe_getattr(order, "amount", None), 1), 1)
    refund_boosts = max(_safe_int(getattr(lot, "amount", 0)), 0) * order_amount
    try:
        balance_reset = Storage.refund_purchase(username, refund_boosts)
    except Exception:
        if refund_identity:
            with _processed_refunds_lock:
                _processed_refunds.discard(refund_identity)
        raise
    logger.info(
        "Refund processed",
        username=username,
        source=source,
        lot_id=lot_key,
        match_source=match_source,
        balance_reset=balance_reset,
        refund_boosts=refund_boosts,
        order_amount=order_amount,
        refund_identity=refund_identity,
    )
    if chat_id:
        send_msg(cardinal, chat_id, username, "refund")
    else:
        logger.warning(
            "Cannot notify buyer about refund: chat_id not found",
            username=username,
            source=source,
            lot_id=lot_key,
        )


def handle_new_order(cardinal: Cardinal, event: FPEvents.NewOrderEvent) -> Optional[int]:
    order_id = None
    credited = False
    try:
        _ensure_cardinal(cardinal)
        order_id = getattr(event.order, "id", None)
        logger.info(
            "HoldBoost order handler started",
            order_id=order_id,
            buyer=getattr(event.order, "buyer_username", ""),
            description=getattr(event.order, "description", ""),
            event_lot_id=getattr(event, "lot_id", None),
            event_has_lot_shortcut=bool(getattr(event, "lot_shortcut", None)),
        )
        if order_id is not None:
            with _processed_orders_lock:
                if order_id in _processed_orders:
                    logger.info("Duplicate order skipped", order_id=order_id)
                    return None
                _processed_orders.add(order_id)

        lot = None
        lots = Storage.get_all_lots()
        lot_key, lot, match_source = _resolve_configured_lot(cardinal, event, lots)
        if not lot and not _is_definite_foreign_lot_source(match_source):
            logger.info(
                "Order lot not found locally, refreshing plugin config",
                order_id=order_id,
                local_lots_count=len(lots),
                known_lots=",".join(sorted(lots.keys())),
                initial_match_source=match_source,
            )
            if _refresh_server_config_for_order():
                lots = Storage.get_all_lots()
                lot_key, lot, match_source = _resolve_configured_lot(cardinal, event, lots)
                if lot:
                    match_source = f"after_config_refresh_{match_source}"
        elif not lot:
            logger.debug(
                "Order config refresh skipped for definite foreign lot",
                order_id=order_id,
                match_source=match_source,
                event_lot_id=getattr(event, "lot_id", None),
            )

        if not lot:
            if order_id is not None:
                with _processed_orders_lock:
                    _processed_orders.discard(order_id)
            logger.info(
                "Lot not found, ignoring order",
                description=getattr(event.order, "description", ""),
                known_lots=",".join(sorted(lots.keys())),
                match_source=match_source,
                event_lot_id=getattr(event, "lot_id", None),
                order_id=order_id,
            )
            return None

        order_amount = max(_safe_int(getattr(event.order, "amount", None), 1), 1)
        total = lot.amount * order_amount
        username = getattr(event.order, "buyer_username", "") or ""
        raw_chat_id = getattr(event.order, "chat_id", 0) or 0
        chat_id = _resolve_chat_id(cardinal, username, raw_chat_id)
        if total > MAX_BOOSTS_PER_PURCHASE:
            logger.warning(
                "Order exceeds HoldBoost purchase limit, skipping credit",
                username=username,
                order_id=order_id,
                lot_id=lot_key,
                lot_amount=lot.amount,
                order_amount=order_amount,
                total=total,
                max_boosts=MAX_BOOSTS_PER_PURCHASE,
            )
            if chat_id:
                try:
                    cardinal.send_message(
                        chat_id=chat_id,
                        message_text=(
                            f"⚠️ Максимум {MAX_BOOSTS_PER_PURCHASE} бустов за одну покупку. "
                            "Этот заказ не был начислен автоматически, обратитесь в поддержку."
                        ),
                        chat_name=username,
                        attempts=3,
                    )
                except Exception as e:
                    logger.error(
                        "Failed to send purchase limit message",
                        error=e,
                        username=username,
                        chat_id=chat_id,
                        order_id=order_id,
                    )
            return None
        Storage.add_boosts(username, total, lot.months, chat_id)
        user_after_credit = Storage.get_user(username)
        available_boosts = max(int(getattr(user_after_credit, "amount", 0) or 0), 0)
        credited = True
        logger.info(
            "Boosts added",
            username=username,
            lot_id=lot_key,
            match_source=match_source,
            boosts=total,
            months=lot.months,
            chat_id=chat_id,
            available_boosts=available_boosts,
        )

        if chat_id:
            try:
                if available_boosts % 2 != 0:
                    text = plugin_settings.get_message(
                        "need_one_boost",
                        boosts=available_boosts,
                        months=lot.months,
                        username=username,
                    )
                    message_mode = "need_one_boost"
                else:
                    text = plugin_settings.get_message(
                        "purchase",
                        boosts=total,
                        months=lot.months,
                        username=username,
                    )
                    message_mode = "purchase"
                logger.info(
                    "Purchase message selected",
                    username=username,
                    order_id=order_id,
                    message_mode=message_mode,
                    credited_boosts=total,
                    available_boosts=available_boosts,
                )
                if text.strip():
                    result = cardinal.send_message(
                        chat_id=chat_id, message_text=text, chat_name=username, attempts=3
                    )
                    if not result:
                        logger.warning(
                            "Purchase message was not delivered",
                            username=username,
                            chat_id=chat_id,
                            order_id=order_id,
                        )
            except Exception as e:
                logger.error(
                    "Failed to send purchase message",
                    error=e,
                    username=username,
                    chat_id=chat_id,
                    order_id=order_id,
                )
        else:
            logger.warning(
                "Cannot send purchase message: chat_id not found",
                username=username,
                order_id=order_id,
            )

        return None
    except Exception as e:
        if order_id is not None and not credited:
            with _processed_orders_lock:
                _processed_orders.discard(order_id)
        logger.error("Error in handle_new_order", error=e, order_id=order_id)
        return None


def handle_new_message(cardinal: Cardinal, event: FPEvents.NewMessageEvent):
    _ensure_cardinal(cardinal)
    try:
        msg_id = event.message.id
        if not message_deduplicator.check_and_mark(msg_id):
            return
        if event.message.type in REFUND_MESSAGE_TYPES:
            _handle_refund_event(cardinal, event, "message")
            return
        if event.message.author_id == cardinal.account.id:
            return

        username = event.message.chat_name
        user = Storage.get_user(username)

        if user.amount <= 0:
            return

        text = (event.message.text or "").strip().lower()
        pending = Storage.get_pending(username)

        if pending and text in ["yes", "да"]:
            pending = Storage.pop_pending(username)
            if pending:
                Thread(target=safe_process_order, args=(cardinal, event, pending)).start()
            return

        invite = extract_invite(event.message.text or "")
        if invite:
            Thread(target=safe_handle_invite, args=(cardinal, event, invite)).start()
    except Exception as e:
        logger.error("Error in handle_new_message", error=e)


def handle_order_status_changed(cardinal: Cardinal, event: FPEvents.OrderStatusChangedEvent):
    _ensure_cardinal(cardinal)
    try:
        if _safe_getattr(event.order, "status") == OrderStatuses.REFUNDED:
            _handle_refund_event(cardinal, event, "order_status")
    except Exception as e:
        logger.error(
            "Error in handle_order_status_changed",
            error=e,
            order_id=_safe_getattr(_safe_getattr(event, "order"), "id"),
        )


def handle_invite(cardinal: Cardinal, event: FPEvents.NewMessageEvent, invite: str):
    username = event.message.chat_name
    user = Storage.get_user(username)
    if user.amount <= 0:
        send_msg(cardinal, event.message.chat_id, username, "no_boosts")
        return
    if user.amount % 2 != 0:
        send_msg(cardinal, event.message.chat_id, username, "need_one_boost")
        return
    cooldown_until = Storage.get_server_cooldown(invite)
    if cooldown_until:
        minutes, available_at = _format_cooldown_time(cooldown_until)
        send_msg(
            cardinal,
            event.message.chat_id,
            username,
            "server_cooldown",
            minutes=minutes,
            available_at=available_at,
            server=invite,
        )
        return
    validation = API.validate_invite(invite)
    if validation:
        if validation.get("settingsBlocked"):
            send_msg(cardinal, event.message.chat_id, username, "rules_enabled")
            return
        if not validation.get("valid", False):
            send_msg(
                cardinal,
                event.message.chat_id,
                username,
                "failed",
                error=validation.get("reason", "invalid_invite"),
            )
            return
    Storage.set_pending(
        username,
        PendingOrder(invite, user.amount, user.months, priority=user.priority_delivery),
    )
    send_msg(
        cardinal,
        event.message.chat_id,
        username,
        "confirm",
        server=invite,
        amount=user.amount,
        months=user.months,
    )


def safe_handle_invite(cardinal: Cardinal, event: FPEvents.NewMessageEvent, invite: str):
    username = event.message.chat_name
    user_lock = _get_user_lock(username)
    with user_lock:
        try:
            handle_invite(cardinal, event, invite)
        except Exception as e:
            logger.error("Error in handle_invite", error=e)


def _safe_int(value: Any, default: int = 0) -> int:
    try:
        return int(float(value))
    except (TypeError, ValueError):
        return default


def _pending_remaining(pending: PendingOrder) -> int:
    return max(_safe_int(pending.amount) - max(_safe_int(pending.delivered), 0), 0)


def _max_delivery_attempts(pending: PendingOrder) -> int:
    if getattr(pending, "priority", False) or max(_safe_int(getattr(pending, "delivered", 0)), 0) > 0:
        return PRIORITY_DELIVERY_ATTEMPTS
    return MAX_DELIVERY_ATTEMPTS


def _attempt_key(pending: PendingOrder, attempt_no: int, amount: int) -> str:
    return f"funpay-{pending.request_id}-{attempt_no}-{amount}"


def _is_captcha_error(error: Optional[str]) -> bool:
    normalized = str(error or "").lower()
    return "captcha" in normalized or "капч" in normalized


def _is_retryable_delivery_error(error: Optional[str]) -> bool:
    if is_server_settings_error(error):
        return False
    normalized = str(error or "").strip().lower()
    if not normalized:
        return True
    non_retryable_markers = (
        "insufficient stock",
        "insufficient balance",
        "not enough",
        "invalid invite",
        "invite_invalid",
        "invite_rejected",
        "expired",
        "forbidden",
        "permission",
        "daily order limit",
        "balance limit",
    )
    if any(marker in normalized for marker in non_retryable_markers):
        return False
    retryable_markers = (
        "unknown",
        "api error",
        "captcha",
        "капч",
        "locked",
        "token locked",
        "account locked",
        "rate limited",
        "rate_limited",
        "timeout",
        "timed out",
        "gateway",
        "no boosts delivered",
        "zero boosts",
        "provider finished without delivered boosts",
    )
    return any(marker in normalized for marker in retryable_markers)


def _extract_order_error(order: Optional[Dict], status: str = "") -> Optional[str]:
    if not order:
        return None
    for key in ("error", "error_message", "errorMessage", "reason", "error_code", "errorCode"):
        value = order.get(key)
        if value:
            return str(value)
    return "Unknown" if status == "FAILED" else (status or None)


def _extract_order_boosts_done(order: Optional[Dict], fallback: int = 0) -> int:
    if not order:
        return fallback
    for key in ("boosts_done", "boostsDone"):
        if key in order and order.get(key) is not None:
            return _safe_int(order.get(key), fallback)
    progress = order.get("progress")
    if isinstance(progress, dict):
        for key in ("done", "boosts_done", "boostsDone"):
            if key in progress and progress.get(key) is not None:
                return _safe_int(progress.get(key), fallback)
    return fallback


def _record_attempt_delivery(pending: PendingOrder, attempt_done: Any, attempt_amount: int) -> int:
    done = max(min(_safe_int(attempt_done), max(_safe_int(attempt_amount), 0)), 0)
    pending.delivered = min(_safe_int(pending.amount), max(_safe_int(pending.delivered), 0) + done)
    return done


def _refund_remaining(username: str, chat_id: Any, pending: PendingOrder) -> int:
    remaining = _pending_remaining(pending)
    if remaining > 0:
        Storage.add_boosts(username, remaining, pending.months, chat_id)
    return remaining


def _can_retry_delivery(pending: PendingOrder, error: Optional[str], remaining: int) -> bool:
    return (
        remaining > 0
        and pending.attempts < _max_delivery_attempts(pending)
        and _is_retryable_delivery_error(error)
    )


def _should_stop_for_captcha_guard(pending: PendingOrder, error: Optional[str]) -> bool:
    if not _is_captcha_error(error):
        return False
    pending.captcha_failures += 1
    amount = max(_safe_int(pending.amount), 0)
    if amount <= CAPTCHA_GUARD_MIN_ORDER_BOOSTS:
        return False
    token_count = max((amount + 1) // 2, 1)
    delivered_tokens = max((_safe_int(pending.delivered) + 1) // 2, 0)
    min_clear_tokens = max(
        1,
        (token_count + CAPTCHA_GUARD_CLEAR_TOKEN_DIVISOR - 1) // CAPTCHA_GUARD_CLEAR_TOKEN_DIVISOR,
    )
    too_few_clear_tokens = delivered_tokens <= min_clear_tokens
    captcha_dominates = pending.captcha_failures >= 2
    return too_few_clear_tokens and captcha_dominates


def _finalize_captcha_guard_partial(
    cardinal: Cardinal,
    chat_id: Any,
    username: str,
    pending: PendingOrder,
    error: Optional[str],
    order_id: Optional[str] = None,
) -> None:
    refunded = _refund_remaining(username, chat_id, pending)
    expires_at = Storage.set_server_cooldown(pending.server) or (
        time.time() + SERVER_DELIVERY_COOLDOWN_SECONDS
    )
    minutes, available_at = _format_cooldown_time(expires_at)
    delivered = max(_safe_int(pending.delivered), 0)
    send_msg(
        cardinal,
        chat_id,
        username,
        "captcha_guard_partial",
        done=delivered,
        amount=pending.amount,
        refunded=refunded,
        minutes=minutes,
        available_at=available_at,
        server=pending.server,
    )
    logger.warning(
        "Order stopped by captcha guard",
        username=username,
        done=delivered,
        amount=pending.amount,
        refunded=refunded,
        attempts=pending.attempts,
        captcha_failures=pending.captcha_failures,
        order_id=order_id,
        error_msg=error or "captcha",
        cooldown_until=available_at,
    )


def _finalize_delivery_failure(
    cardinal: Cardinal,
    chat_id: Any,
    username: str,
    pending: PendingOrder,
    error: Optional[str],
    order_id: Optional[str] = None,
) -> None:
    refunded = _refund_remaining(username, chat_id, pending)
    delivered = max(_safe_int(pending.delivered), 0)
    if delivered > 0:
        send_msg(cardinal, chat_id, username, "partial", done=delivered, amount=pending.amount)
        logger.warning(
            "Order partial after delivery attempts",
            username=username,
            done=delivered,
            amount=pending.amount,
            refunded=refunded,
            attempts=pending.attempts,
            order_id=order_id,
        )
        return
    if is_server_settings_error(error):
        send_msg(cardinal, chat_id, username, "rules_enabled")
    else:
        send_msg(cardinal, chat_id, username, "failed", error=error or "API error")
    logger.error(
        "Order failed after delivery attempts",
        username=username,
        error_msg=error or "API error",
        refunded=refunded,
        attempts=pending.attempts,
        order_id=order_id,
    )


def _create_order_once(pending: PendingOrder, attempt_no: int, amount: int) -> Optional[Dict]:
    idempotency_key = _attempt_key(pending, attempt_no, amount)
    for request_attempt in range(3):
        result = API.create_order(
            pending.server, amount, pending.months, idempotency_key=idempotency_key
        )
        if result or not _is_retryable_delivery_error(API.last_error):
            return result
        logger.warning(
            "Retrying create_order with same idempotency key",
            request_attempt=request_attempt + 1,
            delivery_attempt=attempt_no,
            amount=amount,
            error=API.last_error,
        )
        time.sleep(5)
    return None


def process_order(cardinal: Cardinal, event: FPEvents.NewMessageEvent, pending: PendingOrder):
    username = event.message.chat_name
    chat_id = event.message.chat_id
    pending.amount = max(_safe_int(pending.amount), 0)
    pending.delivered = max(min(_safe_int(pending.delivered), pending.amount), 0)

    if pending.amount <= 0:
        send_msg(cardinal, chat_id, username, "failed", error="Invalid order amount")
        return

    if not pending.deducted:
        if not Storage.use_boosts(username, pending.amount):
            send_msg(cardinal, chat_id, username, "not_enough")
            return
        pending.deducted = True

    while _pending_remaining(pending) > 0:
        max_attempts = _max_delivery_attempts(pending)
        if pending.attempts >= max_attempts:
            _finalize_delivery_failure(cardinal, chat_id, username, pending, "Unknown")
            return

        remaining = _pending_remaining(pending)
        pending.attempts += 1
        attempt_no = pending.attempts

        if attempt_no == 1:
            send_msg(cardinal, chat_id, username, "creating")
        else:
            send_msg(
                cardinal,
                chat_id,
                username,
                "processing",
                done=pending.delivered,
                amount=pending.amount,
            )

        result = _create_order_once(pending, attempt_no, remaining)
        if not result:
            error = API.last_error or "API error"
            # If the HTTP request might have reached the backend, do not start
            # a fresh delivery attempt with a new idempotency key. That could
            # duplicate boosts. _create_order_once already retried the same key.
            _finalize_delivery_failure(cardinal, chat_id, username, pending, error)
            return

        order_id = result.get("id")
        status = str(result.get("status", "") or "").upper()
        order = result

        if order_id and status not in ("COMPLETED", "PARTIAL", "FAILED", "CANCELLED"):
            polled = _poll_order_status(
                cardinal, event, chat_id, username, order_id, pending, remaining
            )
            if polled:
                order = polled
                status = str(order.get("status", "") or "").upper()

        if not order_id and status not in ("COMPLETED", "PARTIAL", "FAILED"):
            error = "API did not return order id"
            if _can_retry_delivery(pending, error, _pending_remaining(pending)):
                time.sleep(5)
                continue
            _finalize_delivery_failure(cardinal, chat_id, username, pending, error)
            logger.error(
                "Order creation returned no order id", username=username, response_status=status
            )
            return

        explicit_done = _extract_order_boosts_done(order, 0)
        if status == "COMPLETED" and explicit_done <= 0:
            logger.warning(
                "Completed order response has no explicit delivered boosts",
                username=username,
                amount=remaining,
                order_id=order_id,
                response_status=status,
            )
        attempt_done = _record_attempt_delivery(pending, explicit_done, remaining)
        total_done = max(_safe_int(pending.delivered), 0)
        remaining_after_attempt = _pending_remaining(pending)
        max_attempts = _max_delivery_attempts(pending)

        if remaining_after_attempt <= 0:
            send_msg(cardinal, chat_id, username, "success", done=total_done, amount=pending.amount)
            logger.info(
                "Order completed",
                username=username,
                done=total_done,
                amount=pending.amount,
                order_id=order_id,
                attempts=pending.attempts,
            )
            return

        error = _extract_order_error(order, status) or "Unknown"
        if _should_stop_for_captcha_guard(pending, error):
            _finalize_captcha_guard_partial(
                cardinal, chat_id, username, pending, error, order_id=order_id
            )
            return
        if status in ("COMPLETED", "PARTIAL") or _can_retry_delivery(
            pending, error, remaining_after_attempt
        ):
            if _is_captcha_error(error):
                pending.retried_captcha = True
            if pending.attempts < max_attempts:
                logger.warning(
                    "Order did not deliver all boosts, retrying remaining amount",
                    username=username,
                    done=attempt_done,
                    total_done=total_done,
                    remaining=remaining_after_attempt,
                    amount=pending.amount,
                    order_id=order_id,
                    status=status,
                    error_msg=error,
                    max_attempts=max_attempts,
                )
                time.sleep(5)
                continue

        _finalize_delivery_failure(cardinal, chat_id, username, pending, error, order_id=order_id)
        return


def _poll_order_status(
    cardinal: Cardinal,
    event: FPEvents.NewMessageEvent,
    chat_id: Any,
    username: str,
    order_id: str,
    pending: PendingOrder,
    attempt_amount: int,
) -> Optional[Dict]:
    max_polls = 1500
    poll_interval = 5
    last_done = 0
    last_order: Optional[Dict] = None

    for i in range(max_polls):
        time.sleep(poll_interval)
        order = API.get_order(order_id)
        if not order:
            continue
        last_order = order

        status = str(order.get("status", "") or "").upper()
        done = max(min(_extract_order_boosts_done(order, 0), max(_safe_int(attempt_amount), 0)), 0)

        if done > last_done:
            send_msg(
                cardinal,
                chat_id,
                username,
                "processing",
                done=min(_safe_int(pending.delivered) + done, pending.amount),
                amount=pending.amount,
            )
            last_done = done

        if status in ("COMPLETED", "PARTIAL", "FAILED", "CANCELLED"):
            return order

    order = API.get_order(order_id)
    if order:
        return order
    logger.warning("Poll timeout no response", username=username, order_id=order_id)
    return last_order


def safe_process_order(cardinal: Cardinal, event: FPEvents.NewMessageEvent, pending: PendingOrder):
    username = (
        getattr(event.message, "chat_name", "unknown") if hasattr(event, "message") else "unknown"
    )
    user_lock = _get_user_lock(username)
    with user_lock:
        try:
            process_order(cardinal, event, pending)
        except Exception as e:
            logger.error("Error in process_order", error=e, username=username)


def _runtime_new_order_handler(cardinal: Cardinal, event: FPEvents.NewOrderEvent):
    return handle_new_order(cardinal, event)


def _runtime_new_message_handler(cardinal: Cardinal, event: FPEvents.NewMessageEvent):
    return handle_new_message(cardinal, event)


def _runtime_order_status_changed_handler(
    cardinal: Cardinal, event: FPEvents.OrderStatusChangedEvent
):
    return handle_order_status_changed(cardinal, event)


def _has_runtime_handler(handlers: Any, marker: str) -> bool:
    try:
        return any(
            getattr(handler, "_holdboost_runtime_marker", None) == marker for handler in handlers
        )
    except Exception:
        return False


def _ensure_runtime_event_handlers(cardinal: Cardinal):
    """Attach direct handlers that are not skipped by Cardinal's plugin enabled flag."""
    try:
        attached = []
        new_order_handlers = getattr(cardinal, "new_order_handlers", None)
        if isinstance(new_order_handlers, list) and not _has_runtime_handler(
            new_order_handlers, "new_order"
        ):
            _runtime_new_order_handler.plugin_uuid = None
            _runtime_new_order_handler._holdboost_runtime_marker = "new_order"
            new_order_handlers.insert(0, _runtime_new_order_handler)
            attached.append("new_order")

        new_message_handlers = getattr(cardinal, "new_message_handlers", None)
        if isinstance(new_message_handlers, list) and not _has_runtime_handler(
            new_message_handlers, "new_message"
        ):
            _runtime_new_message_handler.plugin_uuid = None
            _runtime_new_message_handler._holdboost_runtime_marker = "new_message"
            new_message_handlers.insert(0, _runtime_new_message_handler)
            attached.append("new_message")

        order_status_changed_handlers = getattr(cardinal, "order_status_changed_handlers", None)
        if isinstance(order_status_changed_handlers, list) and not _has_runtime_handler(
            order_status_changed_handlers, "order_status_changed"
        ):
            _runtime_order_status_changed_handler.plugin_uuid = None
            _runtime_order_status_changed_handler._holdboost_runtime_marker = "order_status_changed"
            order_status_changed_handlers.insert(0, _runtime_order_status_changed_handler)
            attached.append("order_status_changed")

        if attached:
            logger.info(
                "HoldBoost runtime event handlers attached",
                attached=",".join(attached),
                new_order_handlers_count=len(new_order_handlers or []),
                new_message_handlers_count=len(new_message_handlers or []),
                order_status_changed_handlers_count=len(order_status_changed_handlers or []),
            )
    except Exception as e:
        logger.error("Failed to attach HoldBoost runtime event handlers", error=e)


def _periodic_sync():
    # Wait for init() to complete (sync_on_startup + settings loaded)
    # so that plugin_settings.price_1m/price_3m/markup_percent are populated.
    _init_complete.wait(timeout=120)

    # Run initial lot checks AFTER settings are loaded
    try:
        lot_manager.run_checks(reason="periodic_start", force=True)
    except Exception as e:
        logger.error("LotManager initial check failed", error=e)

    while True:
        try:
            interval = max(plugin_settings.sync_interval, 60)
            time.sleep(interval)
            with _lock:
                has_dirty_users = bool(Storage._dirty_users)
            result = sync_client.push_sync(include_users=has_dirty_users)
            if result:
                with _lock:
                    if has_dirty_users:
                        Storage._dirty_users.clear()
                        Storage._save_dirty_users()
                    Storage._last_sync_ts = time.time()
                sync_client.apply_config(result, skip_users=False)
            try:
                lot_manager.run_checks(reason="periodic_sync")
            except Exception as e:
                logger.error("LotManager periodic check failed", error=e)
        except Exception as e:
            logger.error("Periodic sync failed", error=e)


def on_cardinal_ready(cardinal: Cardinal):
    """FunPayCardinal вызывает этот хук сразу после инициализации Cardinal.

    Устанавливает cardinal в LotManager. Фактические проверки лотов запускаются
    из _periodic_sync() после _init_complete Event, чтобы plugin_settings
    (цены, наценка, пороги) были уже загружены с сервера.
    """
    try:
        _mark_cardinal_ready(cardinal, "cardinal_hook")
    except Exception as e:
        logger.error("cardinal ready handler failed", error=e)


def on_post_init(cardinal: Cardinal):
    on_cardinal_ready(cardinal)


def on_post_start(cardinal: Cardinal):
    on_cardinal_ready(cardinal)


def init():
    Storage.init()

    try:
        sync_success = sync_client.sync_on_startup()
        if sync_success:
            logger.info("Server config synced")
        else:
            logger.warning("Server sync failed - using local storage")
    except Exception as e:
        logger.error("Server sync failed on startup", error=e)

    # Signal that settings are loaded — _periodic_sync and on_post_init can now
    # run lot_manager.run_checks() with correct prices/markup/thresholds.
    _init_complete.set()

    if plugin_settings.auto_update:
        try:
            auto_updater.update_if_available()
        except Exception as e:
            logger.error("Auto-update check failed", error=e)

    profile = None if sync_client.is_backing_off() else API.get_profile()
    api_status = "connected" if profile else "failed"
    logger.info(
        "Plugin started",
        version=VERSION,
        api_status=api_status,
        users_count=len(Storage._users),
        lots_count=len(Storage._lots),
        auto_update=plugin_settings.auto_update,
        sync_interval=plugin_settings.sync_interval,
        auto_lot_management=plugin_settings.auto_lot_management,
        markup_percent=plugin_settings.markup_percent,
        min_balance_threshold=plugin_settings.min_balance_threshold,
        min_stock_threshold=plugin_settings.min_stock_threshold,
        open_stock_threshold=plugin_settings.open_stock_threshold,
        price_1m=plugin_settings.price_1m,
        price_3m=plugin_settings.price_3m,
    )

    if profile:
        logger.info("API profile loaded", balance=profile.get("balance", 0))
    else:
        if sync_client.is_backing_off():
            logger.warning("API connection failed - network/API unavailable or API_KEY invalid")
        else:
            logger.warning("API connection failed - check API_KEY")

    Thread(target=_periodic_sync, daemon=True).start()


_install_cardinal_lifecycle_patch()
Thread(target=init).start()

BIND_TO_POST_INIT = [on_post_init]
BIND_TO_PRE_INIT = [on_post_init]
BIND_TO_POST_START = [on_post_start]
BIND_TO_PRE_START = [on_post_start]
BIND_TO_NEW_ORDER = [handle_new_order]
BIND_TO_NEW_MESSAGE = [handle_new_message]
BIND_TO_ORDER_STATUS_CHANGED = [handle_order_status_changed]
