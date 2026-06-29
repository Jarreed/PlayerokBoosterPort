from __future__ import annotations

from cardinal import Cardinal
import requests
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

_base_logger = getLogger("POC.booster")
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
    "rules_enabled": "⚠️ На сервере включены правила или заявки на вступление. Отключите их в настройках сервера и повторите попытку.",
    "need_one_boost": "⚠️ Выдача бустов возможна только чётным количеством! Пожалуйста, докупите ещё 1 буст для активирования заказа.",
    "server_cooldown": "⚠️ Выдача на этот сервер временно ограничена. Повторно запросить можно через {minutes} мин. ({available_at})",
    "captcha_guard_partial": "⚠️ Частичная выдача {done}/{amount}. Выдача завершена досрочно.",
}


@dataclass
class PluginSettings:
    messages: Dict[str, str] = field(default_factory=lambda: dict(DEFAULT_MESSAGES))
    message_settings: Dict[str, Dict[str, Any]] = field(default_factory=dict)

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


def _ensure_cardinal(cardinal: Cardinal):
    global _cardinal_ref
    if _cardinal_ref is None:
        _cardinal_ref = cardinal


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
            include_traceback = error is not None
        if error is not None and include_traceback:
            for line in traceback.format_exception(type(error), error, error.__traceback__):
                for sub in line.rstrip().split("\n"):
                    self._logger.error(f"  {sub}")

    def debug(self, event: str, **ctx: Any) -> None:
        self._logger.debug(self._fmt(event, "DEBUG", **ctx))

    def warning(self, event: str, **ctx: Any) -> None:
        self._logger.warning(self._fmt(event, "WARNING", **ctx))


logger = Logger()


class StorageRecovery:
    def __init__(self, storage_path: str = STORAGE_PATH):
        self.storage_path = storage_path
        self.backup_path = os.path.join(storage_path, "backups")

    def _ensure_backup_dir(self) -> None:
        os.makedirs(self.backup_path, exist_ok=True)

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
        except Exception as e:
            logger.error("Failed to load storage", error=e, filename=filename)
            return default

    def safe_save(self, filename: str, data: Dict[str, Any]) -> bool:
        filepath = os.path.join(self.storage_path, filename)
        try:
            os.makedirs(os.path.dirname(filepath), exist_ok=True)
            with open(filepath, "w", encoding="utf-8") as f:
                f.write(dumps(data, indent=2, ensure_ascii=False))
            return True
        except Exception as e:
            logger.error("Failed to save storage", error=e, filename=filename)
            return False


storage_recovery = StorageRecovery()


def extract_invite(text: str) -> Optional[str]:
    match = re.search(r"discord\.(?:gg|com/invite)/([a-zA-Z0-9-]+)", text)
    return f"https://discord.gg/{match.group(1)}" if match else None


def is_server_settings_error(error: Optional[str]) -> bool:
    normalized = str(error or "").lower()
    return any(
        marker in normalized
        for marker in (
            "server_rules_enabled",
            "join_requests_enabled",
            "server_gate_enabled",
            "membership screening",
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
            chat_id=chat_id, text=text, watermark=False
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


def _safe_getattr(obj: Any, name: str, default: Any = None) -> Any:
    try:
        return getattr(obj, name, default)
    except Exception:
        return default


def _safe_int(value: Any, default: int = 0) -> int:
    try:
        return int(float(value))
    except (TypeError, ValueError):
        return default


def on_init(cardinal: Cardinal):
    """Инициализирует плагин при загрузке Cardinal"""
    _ensure_cardinal(cardinal)
    logger.info("Booster plugin initialized with PlayerokCardinal")
    os.makedirs(STORAGE_PATH, exist_ok=True)
    _init_complete.set()


def on_post_init(cardinal: Cardinal):
    """Хук после инициализации Cardinal"""
    _ensure_cardinal(cardinal)


# Привязка к системе обработчиков Cardinal
BIND_TO_PRE_INIT = [on_init]
BIND_TO_POST_INIT = [on_post_init]
