import asyncio
import json
import logging
import re
import os
import time as pytime
import uuid
from collections import defaultdict
from datetime import date, datetime, time, timedelta, timezone
from pathlib import Path

import aiofiles

from telegram import InlineKeyboardButton, InlineKeyboardMarkup, Update
from telegram.ext import (
    ApplicationBuilder,
    CommandHandler,
    CallbackQueryHandler,
    MessageHandler,
    ContextTypes,
    filters,
)
from telegram.error import BadRequest, NetworkError, RetryAfter, TimedOut
from telegram.constants import ParseMode

logging.basicConfig(
    format="%(asctime)s - %(name)s - %(levelname)s - %(message)s",
    level=logging.INFO
)
logger = logging.getLogger(__name__)

TOKEN = os.getenv("BOT_TOKEN")
DATA_DIR = Path(__file__).parent
MINSK_TZ = timezone(timedelta(hours=3))

BIRTHDAYS = []
DUTIES_TEXT = ""
SCHEDULES = {}
PARSED_SCHEDULES = {}

chat_states = defaultdict(lambda: {
    "votes": {},
    "poll_message_id": None,
    "results_message_id": None,
    "last_save": 0.0,
    "dirty": False,
    "awaiting_new_event": False,
    "editing_event_id": None,
    "last_prompt_message_id": None,
    "last_events_message_id": None,
    "chat_title": None,
    # ДЗ
    "awaiting_hw_subject": None,
    "editing_hw_id": None,
    "hw_last_prompt_id": None,
})

file_write_lock = asyncio.Lock()
_chat_file_locks: dict[int, asyncio.Lock] = defaultdict(asyncio.Lock)
last_birthday_sent_date = None
last_pinned_birthday_msg_id = {}
ADMIN_CACHE_TTL = 300.0
admin_cache: dict[int, dict] = {}
hw_cache: dict[int, dict] = {}
# main_keyboard_cache removed — rebuilt per-call (instantaneous, no stale admin button)

# Хранит ключи уже отправленных напоминаний
sent_reminders: dict[int, set] = defaultdict(set)
# Хранит message_id последнего напоминания для каждого мероприятия
reminder_message_ids: dict[int, dict[str, int]] = defaultdict(dict)
HW_STATUS_TTL = 30


# ====================== СТРУКТУРА ПРЕДМЕТОВ ДЗ ======================

DAY_KEYS = ["pn", "vt", "sr", "cht", "pt"]
WEEKDAY_TO_DAY_KEY = {0: "pn", 1: "vt", 2: "sr", 3: "cht", 4: "pt"}
DAY_LABELS = {"pn": "Пн", "vt": "Вт", "sr": "Ср", "cht": "Чт", "pt": "Пт"}
DAY_HEADER_NAMES = {"понедельник", "вторник", "среда", "четверг", "пятница"}

HOMEWORK_SUBJECT_ALIASES = {
    "bel_lang": ("белорусский",),
    "bel_lit": ("бел лит", "белорусская литература"),
    "rus_lang": ("русский",),
    "rus_lit": ("рус лит", "русская литература"),
    "eng_lang": ("иностранный", "английский"),
    "ger_lang": ("иностранный", "немецкий"),
    "history": ("история",),
    "society": ("общество", "обществоведение"),
    "geography": ("география",),
    "biology": ("биология",),
    "physics": ("физика",),
    "chem": ("химия",),
    "drafting": ("черчение",),
    "dopriz": ("доприз",),
    "med": ("мед", "медицин"),
}

HOMEWORK_PROFILE_LABELS = {
    "math": {
        "profile": "📐 Профиль",
        "base": "📘 База",
    },
    "chem": {
        "profile": "🧪 Профиль",
        "base": "📘 База",
    },
    "rus_lang": {
        "profile": "📐 Профиль",
        "base": "📘 База",
    },
}

MATH_BRANCH_LABELS = {
    "algebra": "➗ Алгебра",
    "geometry": "📐 Геометрия",
}

# Все предметы в нужном порядке: key -> display_name
SUBJECTS_LIST = [
    ("bel_lang",   "🇧🇾 Белорусский язык"),
    ("bel_lit",    "📚 Белорусская литература"),
    ("rus_lang",   "🇷🇺 Русский язык"),
    ("rus_lit",    "📚 Русская литература"),
    ("eng_lang",   "🌍 Английский язык"),
    ("ger_lang",   "🌍 Немецкий язык"),
    ("math",       "➗ Математика"),
    ("history",    "🏛 История Беларуси"),
    ("society",    "⚖️ Обществоведение"),
    ("geography",  "🌍 География"),
    ("biology",    "🧬 Биология"),
    ("physics",    "⚡ Физика"),
    ("chem",       "🧪 Химия"),
    ("drafting",   "📏 Черчение"),
    ("dopriz",     "🪖 Допризывная подготовка"),
    ("med",        "🩺 Медицинская подготовка"),
]
SUBJECTS_DICT = dict(SUBJECTS_LIST)

def _hw_display_key(subject_key: str, sub_key: str | None) -> str:
    """Человекочитаемое название раздела ДЗ."""
    base = SUBJECTS_DICT.get(subject_key, subject_key)
    if not sub_key:
        return base

    if subject_key == "math":
        level, _, branch = sub_key.partition("_")
        branch_label = MATH_BRANCH_LABELS.get(branch, branch)
        level_label = "профиль" if level == "profile" else "база"
        return f"{branch_label} ({level_label})"

    if subject_key == "chem":
        level_label = "профиль" if sub_key == "profile" else "база"
        return f"{base} ({level_label})"

    if subject_key == "rus_lang":
        labels = {
            "profile": "профиль",
            "base": "база",
        }
        return f"{base} ({labels.get(sub_key, sub_key)})"

    if subject_key in HOMEWORK_PROFILE_LABELS:
        label = HOMEWORK_PROFILE_LABELS[subject_key].get(sub_key, sub_key)
        return f"{base} ({label})"

    return base


def _normalize_schedule_line(text: str) -> str:
    text = re.sub(r"\*\([^)]*\)\*", " ", text)
    text = text.replace("*", " ")
    text = re.sub(r"[^0-9A-Za-zА-Яа-яЁё/ ]+", " ", text)
    text = re.sub(r"^\s*\d+\s*", " ", text)
    return re.sub(r"\s+", " ", text).strip().lower()


def _rebuild_schedule_cache():
    global PARSED_SCHEDULES

    parsed: dict[str, dict[str, list[dict[str, str]]]] = {}
    for profile, day_map in SCHEDULES.items():
        parsed[profile] = {}
        for day_key in DAY_KEYS:
            lessons = []
            for raw_line in str(day_map.get(day_key, "")).splitlines():
                normalized = _normalize_schedule_line(raw_line)
                if not normalized or normalized in DAY_HEADER_NAMES:
                    continue
                lessons.append({"raw": raw_line.strip(), "normalized": normalized})
            parsed[profile][day_key] = lessons

    PARSED_SCHEDULES = parsed


def _normalize_hw_entry(entry: dict) -> tuple[dict, bool]:
    item = dict(entry)
    changed = False

    subject_key = item.get("subject_key")
    sub_key = item.get("sub_key")

    if subject_key == "russian":
        item["subject_key"] = "rus_lang"
        subject_key = "rus_lang"
        changed = True

    if sub_key == "":
        item["sub_key"] = None
        sub_key = None
        changed = True

    if subject_key == "math":
        if sub_key in ("algebra", "geometry"):
            item["sub_key"] = f"profile_{sub_key}"
            changed = True
        elif isinstance(sub_key, str) and sub_key.endswith(("_algebra", "_geometry")):
            branch = "algebra" if sub_key.endswith("_algebra") else "geometry"
            level = "profile" if sub_key.startswith("math_") else "base"
            normalized = f"{level}_{branch}"
            if item.get("sub_key") != normalized:
                item["sub_key"] = normalized
                changed = True

    elif subject_key == "chem":
        mapping = {
            None: "base",
            "chem_math": "base",
            "chem_base": "base",
            "chem_chem": "profile",
        }
        if sub_key in mapping and item.get("sub_key") != mapping[sub_key]:
            item["sub_key"] = mapping[sub_key]
            changed = True

    elif subject_key == "rus_lang":
        mapping = {
            None: "base",
            "math": "profile",
            "chem": "profile",
            "rus_math": "profile",
            "rus_chem": "profile",
            "rus_base": "base",
            "profile": "profile",
            "base": "base",
        }
        if sub_key in mapping and item.get("sub_key") != mapping[sub_key]:
            item["sub_key"] = mapping[sub_key]
            changed = True

    return item, changed


def _parse_due_date(due_date: str | None) -> date | None:
    if not due_date:
        return None
    try:
        return datetime.strptime(due_date, "%Y-%m-%d").date()
    except ValueError:
        return None


def _get_schedule_profiles_for_hw(subject_key: str, sub_key: str | None) -> list[str]:
    if subject_key == "math":
        return ["math"] if sub_key and sub_key.startswith("profile_") else ["base"]

    if subject_key == "chem":
        return ["chem"] if sub_key == "profile" else ["base"]

    if subject_key == "rus_lang":
        if sub_key == "profile":
            return ["math", "chem"]
        if sub_key == "base":
            return ["base"]
        return ["base"]

    return [profile for profile in SCHEDULES.keys() if profile in PARSED_SCHEDULES]


def _get_subject_aliases(subject_key: str, sub_key: str | None) -> tuple[str, ...]:
    if subject_key == "math":
        if sub_key and sub_key.endswith("_algebra"):
            return ("алгебра",)
        if sub_key and sub_key.endswith("_geometry"):
            return ("геометрия",)
        return ("алгебра", "геометрия")

    return HOMEWORK_SUBJECT_ALIASES.get(subject_key, ())


def _schedule_contains_subject(profile: str, day_key: str, subject_key: str, sub_key: str | None) -> bool:
    aliases = _get_subject_aliases(subject_key, sub_key)
    if not aliases:
        return False

    lessons = PARSED_SCHEDULES.get(profile, {}).get(day_key, [])
    for lesson in lessons:
        normalized = lesson["normalized"]
        if any(alias in normalized for alias in aliases):
            return True
    return False


def _find_next_lesson_date(subject_key: str, sub_key: str | None, start_after: date) -> str:
    schedule_profiles = _get_schedule_profiles_for_hw(subject_key, sub_key)
    if not schedule_profiles:
        return (start_after + timedelta(days=7)).isoformat()

    for delta in range(1, 22):
        check_date = start_after + timedelta(days=delta)
        if check_date.weekday() > 4:
            continue

        day_key = WEEKDAY_TO_DAY_KEY.get(check_date.weekday())
        if not day_key:
            continue

        for profile in schedule_profiles:
            if _schedule_contains_subject(profile, day_key, subject_key, sub_key):
                return check_date.isoformat()

    return (start_after + timedelta(days=7)).isoformat()


def _calc_due_date(subject_key: str, sub_key: str | None, hw_list: list | None = None) -> str:
    """
    Вычисляет дату следующего урока по расписанию.
    Если по этому же разделу уже есть ДЗ, новая запись ставится на следующий урок после последней даты.
    """
    today = datetime.now(MINSK_TZ).date()
    latest_due = None

    for hw in hw_list or []:
        if hw.get("subject_key") != subject_key or hw.get("sub_key") != sub_key:
            continue
        parsed_due = _parse_due_date(hw.get("due_date"))
        if parsed_due and (latest_due is None or parsed_due > latest_due):
            latest_due = parsed_due

    start_after = max(today, latest_due) if latest_due else today
    return _find_next_lesson_date(subject_key, sub_key, start_after)


# ====================== ФАЙЛЫ ДЗ ======================

def get_hw_file(chat_id: int) -> Path:
    return DATA_DIR / f"homework_{chat_id}.json"


def _clone_hw_list(hw_list: list) -> list:
    return [dict(item) for item in hw_list]


async def load_hw(chat_id: int) -> list:
    """Загружает ДЗ и мягко приводит старые записи к новой схеме ключей."""
    path = get_hw_file(chat_id)
    if not path.exists():
        hw_cache[chat_id] = {"mtime_ns": None, "size": 0, "data": []}
        return []
    try:
        stat = path.stat()
        cached = hw_cache.get(chat_id)
        if cached and cached["mtime_ns"] == stat.st_mtime_ns and cached["size"] == stat.st_size:
            return _clone_hw_list(cached["data"])

        async with aiofiles.open(path, "r", encoding="utf-8") as f:
            raw = json.loads(await f.read())
        normalized = []
        changed = False
        for item in raw:
            normalized_item, item_changed = _normalize_hw_entry(item)
            normalized.append(normalized_item)
            changed = changed or item_changed
        if changed:
            await save_hw(chat_id, normalized)
            return _clone_hw_list(normalized)

        hw_cache[chat_id] = {
            "mtime_ns": stat.st_mtime_ns,
            "size": stat.st_size,
            "data": _clone_hw_list(normalized),
        }
        return _clone_hw_list(normalized)
    except Exception as e:
        logger.error(f"Ошибка загрузки ДЗ {chat_id}: {e}")
        return []


async def save_hw(chat_id: int, hw_list: list):
    async with _chat_file_locks[chat_id]:
        try:
            path = get_hw_file(chat_id)
            await _write_json_atomic(path, hw_list)
            try:
                stat = path.stat()
                hw_cache[chat_id] = {
                    "mtime_ns": stat.st_mtime_ns,
                    "size": stat.st_size,
                    "data": _clone_hw_list(hw_list),
                }
            except Exception:
                hw_cache[chat_id] = {"mtime_ns": None, "size": len(hw_list), "data": _clone_hw_list(hw_list)}
        except Exception as e:
            logger.error(f"Ошибка сохранения ДЗ {chat_id}: {e}")


# ====================== РЕГИСТРАЦИЯ ЧАТОВ ======================

def _register_chat(chat_id: int, chat_title: str):
    chat_states[chat_id]["chat_title"] = chat_title


def _get_chat_title(chat_id: int) -> str:
    saved = chat_states[chat_id].get("chat_title")
    if saved:
        return saved
    for f in DATA_DIR.glob(f"events_*_{chat_id}.json"):
        parts = f.stem.split("_")
        title = "_".join(parts[1:-1])
        chat_states[chat_id]["chat_title"] = title
        return title
    return f"chat_{chat_id}"


def _discover_known_chats():
    for f in DATA_DIR.glob("stolovaya_*_*.json"):
        try:
            chat_id = int(f.stem.split("_")[-1])
            _ = chat_states[chat_id]
        except (ValueError, IndexError):
            pass
    for f in DATA_DIR.glob("events_*_*.json"):
        try:
            chat_id = int(f.stem.split("_")[-1])
            _ = chat_states[chat_id]
        except (ValueError, IndexError):
            pass


# ====================== ФАЙЛЫ ======================

def _safe_name(chat_id: int, chat_title: str) -> str:
    return re.sub(r'[^a-zA-Z0-9_-]', '_', chat_title or f"chat_{chat_id}")[:40]

def get_file(chat_id: int, chat_title: str) -> Path:
    return DATA_DIR / f"stolovaya_{_safe_name(chat_id, chat_title)}_{chat_id}.json"

def get_events_file(chat_id: int, chat_title: str) -> Path:
    return DATA_DIR / f"events_{_safe_name(chat_id, chat_title)}_{chat_id}.json"


async def _write_json_atomic(path: Path, data, *, use_lock: bool = False):
    tmp = path.with_suffix(".tmp")
    encoded = json.dumps(data, ensure_ascii=False, separators=(",", ":"))

    async def _write():
        async with aiofiles.open(tmp, "w", encoding="utf-8") as f:
            await f.write(encoded)
        tmp.replace(path)

    if use_lock:
        async with file_write_lock:
            await _write()
    else:
        await _write()


async def save_state_periodically(chat_id: int, chat_title: str):
    now_ts = pytime.monotonic()
    state = chat_states[chat_id]
    if not state["dirty"] or now_ts - state["last_save"] < 12:
        return
    try:
        await _write_json_atomic(get_file(chat_id, chat_title), {
            "date": date.today().isoformat(),
            "votes": state["votes"],
            "poll_message_id": state["poll_message_id"],
            "results_message_id": state["results_message_id"],
        }, use_lock=True)
        state["last_save"] = now_ts
        state["dirty"] = False
    except Exception as e:
        logger.error(f"Ошибка сохранения {chat_id}: {e}")


async def load_state_from_file(chat_id: int, chat_title: str):
    path = get_file(chat_id, chat_title)
    if not path.exists():
        return None
    try:
        async with aiofiles.open(path, "r", encoding="utf-8") as f:
            return json.loads(await f.read())
    except Exception:
        return None


async def save_events(chat_id: int, chat_title: str, events: list):
    async with _chat_file_locks[chat_id]:
        try:
            await _write_json_atomic(get_events_file(chat_id, chat_title), events)
        except Exception as e:
            logger.error(f"Ошибка сохранения мероприятий {chat_id}: {e}")


async def load_events(chat_id: int, chat_title: str) -> list:
    path = get_events_file(chat_id, chat_title)
    if not path.exists():
        return []
    try:
        async with aiofiles.open(path, "r", encoding="utf-8") as f:
            raw_events = json.loads(await f.read())
        now = datetime.now(MINSK_TZ)
        today_iso = now.date().isoformat()

        def _event_passed(ev: dict) -> bool:
            ev_date = ev.get("date", "9999-99-99")
            ev_time = ev.get("time")
            if ev_time:
                try:
                    ev_dt = datetime.strptime(f"{ev_date} {ev_time}", "%Y-%m-%d %H:%M").replace(tzinfo=MINSK_TZ)
                    return now >= ev_dt
                except ValueError:
                    pass
            return ev_date < today_iso

        events = [e for e in raw_events if not _event_passed(e)]
        if len(events) != len(raw_events):
            # Удаляем напоминания прошедших мероприятий
            passed_ids = {e.get("id") for e in raw_events if _event_passed(e) and e.get("id")}
            # (будут удалены в следующем цикле check_event_reminders)
            await save_events(chat_id, chat_title, events)
        return events
    except Exception as e:
        logger.error(f"Ошибка загрузки мероприятий {chat_id}: {e}")
        return []


async def save_last_birthday_date(date_str: str):
    try:
        await _write_json_atomic(DATA_DIR / "last_birthday_sent.json", {"date": date_str})
    except Exception as e:
        logger.error(f"Не удалось сохранить дату ДР: {e}")


async def load_last_birthday_date():
    global last_birthday_sent_date
    path = DATA_DIR / "last_birthday_sent.json"
    if not path.exists():
        return
    try:
        async with aiofiles.open(path, "r", encoding="utf-8") as f:
            data = json.loads(await f.read())
        last_birthday_sent_date = data.get("date")
    except Exception as e:
        logger.error(f"Ошибка чтения last_birthday_sent: {e}")


def load_static_data():
    global BIRTHDAYS, DUTIES_TEXT, SCHEDULES
    files = {
        "data_birthdays.json": ("BIRTHDAYS", lambda d: d),
        "data_duties.json":    ("DUTIES_TEXT", lambda d: d["text"]),
        "data_schedules.json": ("SCHEDULES", lambda d: d),
    }
    targets = {"BIRTHDAYS": None, "DUTIES_TEXT": None, "SCHEDULES": None}
    for filename, (key, transform) in files.items():
        try:
            with (DATA_DIR / filename).open("r", encoding="utf-8") as f:
                targets[key] = transform(json.load(f))
        except Exception as e:
            logger.error(f"{filename}: {e}")
    if targets["BIRTHDAYS"] is not None:
        BIRTHDAYS = targets["BIRTHDAYS"]
    if targets["DUTIES_TEXT"] is not None:
        DUTIES_TEXT = targets["DUTIES_TEXT"]
    if targets["SCHEDULES"] is not None:
        SCHEDULES = targets["SCHEDULES"]
        _rebuild_schedule_cache()


# ====================== ДНИ РОЖДЕНИЯ ======================

async def check_birthdays(context: ContextTypes.DEFAULT_TYPE):
    global last_birthday_sent_date
    today = datetime.now(MINSK_TZ).date()
    today_iso = today.isoformat()

    if last_birthday_sent_date == today_iso:
        return

    birthday_people = [b["name"] for b in BIRTHDAYS if b["date"] == today.strftime("%d.%m")]
    if not birthday_people:
        return

    message = (
        "🎉 <b>С днём рождения!</b>\n\n"
        + "\n".join(f"🎂 {name}" for name in birthday_people)
        + "\n\nОт всего класса — счастья, здоровья, успехов и море позитива!"
    )

    for chat_id in list(chat_states.keys()):
        try:
            if chat_id in last_pinned_birthday_msg_id:
                await context.bot.unpin_chat_message(chat_id=chat_id)
            sent_msg = await context.bot.send_message(
                chat_id=chat_id, text=message,
                parse_mode=ParseMode.HTML, disable_notification=True
            )
            await context.bot.pin_chat_message(
                chat_id=chat_id, message_id=sent_msg.message_id, disable_notification=True
            )
            last_pinned_birthday_msg_id[chat_id] = sent_msg.message_id
        except Exception as e:
            logger.error(f"[ДР] Ошибка в чате {chat_id}: {e}")

    last_birthday_sent_date = today_iso
    await save_last_birthday_date(today_iso)


# ====================== НАПОМИНАНИЯ О МЕРОПРИЯТИЯХ ======================

async def _delete_reminder(bot, chat_id: int, ev_id: str):
    msg_id = reminder_message_ids[chat_id].pop(ev_id, None)
    if msg_id:
        try:
            await bot.delete_message(chat_id=chat_id, message_id=msg_id)
        except Exception:
            pass


async def check_event_reminders(context: ContextTypes.DEFAULT_TYPE):
    now = datetime.now(MINSK_TZ)
    today_iso = now.date().isoformat()
    tomorrow_iso = (now.date() + timedelta(days=1)).isoformat()

    for chat_id in list(chat_states.keys()):
        chat_title = _get_chat_title(chat_id)
        try:
            events = await load_events(chat_id, chat_title)
        except Exception:
            continue

        active_ev_ids = {ev.get("id") for ev in events if ev.get("id")}

        # Удаляем напоминания для мероприятий, которых уже нет в списке (прошли)
        stale_ids = set(reminder_message_ids[chat_id].keys()) - active_ev_ids
        for stale_id in stale_ids:
            await _delete_reminder(context.bot, chat_id, stale_id)
        stale_keys = {k for k in sent_reminders[chat_id]
                      if k.split("_")[0] not in active_ev_ids}
        sent_reminders[chat_id] -= stale_keys

        for ev in events:
            ev_id = ev.get("id")
            ev_date = ev.get("date")
            ev_time = ev.get("time")
            title = ev.get("title", "Мероприятие")
            if not ev_id or not ev_date:
                continue

            ev_dt = None
            if ev_time:
                try:
                    ev_dt = datetime.strptime(
                        f"{ev_date} {ev_time}", "%Y-%m-%d %H:%M"
                    ).replace(tzinfo=MINSK_TZ)
                except ValueError:
                    pass

            d_str = datetime.strptime(ev_date, "%Y-%m-%d").strftime("%d.%m.%Y")
            t_str = f" в {ev_time}" if ev_time else ""

            # Мероприятие прошло — удаляем последнее напоминание
            if ev_dt and now >= ev_dt:
                await _delete_reminder(context.bot, chat_id, ev_id)
                continue
            if not ev_dt and ev_date < today_iso:
                await _delete_reminder(context.bot, chat_id, ev_id)
                continue

            # Напоминание за 1 день
            if ev_date == tomorrow_iso:
                day_key = f"{ev_id}_day"
                if day_key not in sent_reminders[chat_id]:
                    text = (
                        f"🔔 <b>Напоминание!</b>\n\n"
                        f"Завтра — <b>{title}</b>\n"
                        f"📅 {d_str}{t_str}"
                    )
                    try:
                        await _delete_reminder(context.bot, chat_id, ev_id)
                        sent_msg = await context.bot.send_message(
                            chat_id=chat_id, text=text,
                            parse_mode=ParseMode.HTML, disable_notification=False
                        )
                        reminder_message_ids[chat_id][ev_id] = sent_msg.message_id
                        sent_reminders[chat_id].add(day_key)
                        logger.info(f"[Напоминание-день] chat={chat_id} ev={title}")
                    except Exception as e:
                        logger.error(f"[Напоминание-день] chat={chat_id}: {e}")

            # Напоминания в день мероприятия каждые 4 часа
            elif ev_date == today_iso:
                current_slot = now.hour // 4
                slot_key = f"{ev_id}_slot{current_slot}"

                if slot_key not in sent_reminders[chat_id]:
                    if ev_dt:
                        delta = ev_dt - now
                        if delta.total_seconds() < 600:
                            continue
                        time_left = ""
                        total_minutes = int(delta.total_seconds() // 60)
                        if total_minutes >= 60:
                            hours = total_minutes // 60
                            mins = total_minutes % 60
                            time_left = f"\n⏱ До начала: {hours} ч" + (f" {mins} мин" if mins else "")
                        else:
                            time_left = f"\n⏱ До начала: {total_minutes} мин"
                    else:
                        time_left = ""

                    text = (
                        f"📣 <b>Сегодня мероприятие!</b>\n\n"
                        f"<b>{title}</b>\n"
                        f"📅 {d_str}{t_str}"
                        f"{time_left}"
                    )
                    try:
                        await _delete_reminder(context.bot, chat_id, ev_id)
                        sent_msg = await context.bot.send_message(
                            chat_id=chat_id, text=text,
                            parse_mode=ParseMode.HTML, disable_notification=False
                        )
                        reminder_message_ids[chat_id][ev_id] = sent_msg.message_id
                        sent_reminders[chat_id].add(slot_key)
                        logger.info(f"[Напоминание-день-слот{current_slot}] chat={chat_id} ev={title}")
                    except Exception as e:
                        logger.error(f"[Напоминание-сегодня] chat={chat_id}: {e}")


# ====================== ПАРСИНГ ======================

_TODAY_VARIANTS = re.compile(
    r'сегодня|сёдня|сёдн|сегодн[яь]|сгодня|segodnya|today|щас|щаз|сейчас',
    re.IGNORECASE
)
_TOMORROW_VARIANTS = re.compile(
    r'завтр[ауеяь]?|завтор[ауа]?|зафтра|zaftra|tomorrow|на\s*след(?:ующий)?\s*день',
    re.IGNORECASE
)
_DAYAFTER_VARIANTS = re.compile(
    r'после\s*завтр[ауаеяь]?|послезавтр[ауаеяь]?|через\s*2\s*дн[яей]?'
    r'|послезавтра|черездвадня',
    re.IGNORECASE
)

_WEEKDAY_MAP = {
    'понедельник': 0, 'пн': 0, 'пон': 0, 'monday': 0, 'mon': 0,
    'вторник': 1, 'вт': 1, 'вторн': 1, 'tuesday': 1, 'tue': 1,
    'среда': 2, 'среду': 2, 'среды': 2, 'ср': 2, 'среди': 2, 'wednesday': 2, 'wed': 2,
    'четверг': 3, 'чт': 3, 'четв': 3, 'thursday': 3, 'thu': 3,
    'пятница': 4, 'пятницу': 4, 'пятн': 4, 'пт': 4, 'friday': 4, 'fri': 4,
    'суббота': 5, 'субботу': 5, 'субб': 5, 'сб': 5, 'субота': 5, 'saturday': 5, 'sat': 5,
    'воскресенье': 6, 'воскресенья': 6, 'воскр': 6, 'вс': 6, 'воскресение': 6,
    'sunday': 6, 'sun': 6,
}

_WEEKDAY_PATTERN = re.compile(
    r'(?:в\s+)?(?:(эту?|этой|следующ(?:ий|ую|его|ей)|след\.?|next)\s+)?'
    r'(' + '|'.join(sorted(_WEEKDAY_MAP.keys(), key=len, reverse=True)) + r')\b',
    re.IGNORECASE
)

_THROUGH_PATTERN = re.compile(
    r'через\s+(?:(\d+)\s+)?(д[еён][нь]?|дней|дн\.?|д\.'
    r'|недел[юьи]?|неделек|нед\.?|нед\b'
    r'|месяц(?:ев|а)?|мес\.?|мес\b'
    r'|год(?:а|ов)?|лет)',
    re.IGNORECASE
)

_NEXT_WEEK_WEEKDAY = re.compile(
    r'на\s+(?:следующей|след\.?|будущей)\s+недел[еи]\s+(?:в\s+)?'
    r'(' + '|'.join(sorted(_WEEKDAY_MAP.keys(), key=len, reverse=True)) + r')\b',
    re.IGNORECASE
)

_MONTH_NAMES = {
    'январ': 1, 'янв': 1, 'january': 1, 'jan': 1,
    'феврал': 2, 'фев': 2, 'февр': 2, 'february': 2, 'feb': 2,
    'март': 3, 'мар': 3, 'march': 3, 'mar': 3,
    'апрел': 4, 'апр': 4, 'april': 4, 'apr': 4,
    'май': 5, 'мая': 5, 'may': 5,
    'июн': 6, 'june': 6, 'jun': 6,
    'июл': 7, 'july': 7, 'jul': 7,
    'август': 8, 'авг': 8, 'august': 8, 'aug': 8,
    'сентябр': 9, 'сен': 9, 'сент': 9, 'september': 9, 'sep': 9, 'sept': 9,
    'октябр': 10, 'окт': 10, 'october': 10, 'oct': 10,
    'ноябр': 11, 'ноя': 11, 'november': 11, 'nov': 11,
    'декабр': 12, 'дек': 12, 'december': 12, 'dec': 12,
}

_DATE_WORD_PATTERN = re.compile(
    r'\b(\d{1,2})(?:-?го|-?е|-?ого)?\s+([а-яёa-z]+)',
    re.IGNORECASE
)
_DATE_NUM_PATTERN = re.compile(
    r'\b(\d{1,2})[./](\d{1,2})(?:[./]\d{2,4})?\b'
)

_MONTH_PART_PATTERN = re.compile(
    r'(начал[ео]|в\s+начале|конец|в\s+конце|конц[еа]|середин[еа]|в\s+середине)'
    r'\s+([а-яёa-z]+)',
    re.IGNORECASE
)


def _fuzzy_match_month(word: str) -> int | None:
    w = word.lower().strip('.,')
    for prefix, num in _MONTH_NAMES.items():
        if w == prefix or w.startswith(prefix) or prefix.startswith(w[:4]):
            return num
    return None


def _next_weekday(base: date, weekday: int, force_next_week: bool = False) -> date:
    days_ahead = weekday - base.weekday()
    if force_next_week:
        if days_ahead <= 0:
            days_ahead += 7
        days_ahead += 7
    else:
        if days_ahead <= 0:
            days_ahead += 7
    return base + timedelta(days=days_ahead)


def parse_date(text: str, base_date: date) -> str | None:
    t = text.lower()

    if _DAYAFTER_VARIANTS.search(t):
        return (base_date + timedelta(days=2)).isoformat()
    if _TOMORROW_VARIANTS.search(t):
        return (base_date + timedelta(days=1)).isoformat()
    if _TODAY_VARIANTS.search(t):
        return base_date.isoformat()

    m = _NEXT_WEEK_WEEKDAY.search(t)
    if m:
        wd = _WEEKDAY_MAP.get(m.group(1).lower())
        if wd is not None:
            return _next_weekday(base_date, wd, force_next_week=True).isoformat()

    m = _THROUGH_PATTERN.search(t)
    if m:
        n = int(m.group(1)) if m.group(1) else 1
        unit = m.group(2).lower()
        if unit.startswith('д') or unit.startswith('d'):
            return (base_date + timedelta(days=n)).isoformat()
        if unit.startswith('нед') or unit.startswith('ned'):
            return (base_date + timedelta(weeks=n)).isoformat()
        if unit.startswith('мес') or unit.startswith('mes'):
            month = base_date.month - 1 + n
            year  = base_date.year + month // 12
            month = month % 12 + 1
            leap  = int((year % 4 == 0 and year % 100 != 0) or year % 400 == 0)
            day   = min(base_date.day, [31, 28 + leap, 31, 30, 31, 30, 31, 31, 30, 31, 30, 31][month - 1])
            return date(year, month, day).isoformat()
        if unit.startswith('год') or unit.startswith('лет'):
            return base_date.replace(year=base_date.year + n).isoformat()

    m = _WEEKDAY_PATTERN.search(t)
    if m:
        modifier = (m.group(1) or '').lower()
        wd_word  = m.group(2).lower()
        wd = _WEEKDAY_MAP.get(wd_word)
        if wd is not None:
            force_next = bool(modifier) and ('след' in modifier or 'next' in modifier)
            return _next_weekday(base_date, wd, force_next_week=force_next).isoformat()

    m = _MONTH_PART_PATTERN.search(t)
    if m:
        part    = m.group(1).lower()
        month_n = _fuzzy_match_month(m.group(2))
        if month_n:
            if 'начал' in part:
                day_n = 1
            elif 'конц' in part or 'конец' in part:
                day_n = 28
            else:
                day_n = 15
            try:
                d = date(base_date.year, month_n, day_n)
                if d < base_date:
                    d = d.replace(year=d.year + 1)
                return d.isoformat()
            except ValueError:
                pass

    m = _DATE_WORD_PATTERN.search(text)
    if m:
        day_n   = int(m.group(1))
        month_n = _fuzzy_match_month(m.group(2))
        if month_n and 1 <= day_n <= 31:
            try:
                d = date(base_date.year, month_n, day_n)
                if d < base_date:
                    d = d.replace(year=d.year + 1)
                return d.isoformat()
            except ValueError:
                pass

    m = _DATE_NUM_PATTERN.search(text)
    if m:
        day_n, month_n = int(m.group(1)), int(m.group(2))
        try:
            d = date(base_date.year, month_n, day_n)
            if d < base_date:
                d = d.replace(year=d.year + 1)
            return d.isoformat()
        except ValueError:
            pass

    return None


_TIME_PREPOSITIONS = re.compile(
    r'(?:в|at|в\s+(?:районе|около|примерно))\s*(\d{1,2})(?:[:.,-](\d{2}))?\s*(?:ч(?:асов?|\.)?|h(?:rs?)?)?',
    re.IGNORECASE
)
_TIME_BARE = re.compile(r'\b(\d{1,2})[:.,-](\d{2})\b')
_TIME_WORDS = re.compile(
    r'\b(утром?|с\s*утра|днём?|дня|вечером?|ночью?|полдень|полночь|полуноч\w*)\b',
    re.IGNORECASE
)
_TIME_WORD_MAP = {
    'утром': 9, 'утра': 9, 'с утра': 9,
    'днём': 13, 'дня': 13,
    'вечером': 18, 'вечера': 18,
    'ночью': 0, 'ночи': 0,
    'полдень': 12,
    'полночь': 0,
}


def parse_time(text: str) -> str | None:
    m = _TIME_PREPOSITIONS.search(text)
    if m:
        h  = int(m.group(1))
        mn = int(m.group(2)) if m.group(2) else 0
        if 0 <= h < 24 and 0 <= mn < 60:
            return f"{h:02d}:{mn:02d}"

    m = _TIME_BARE.search(text)
    if m:
        h, mn = int(m.group(1)), int(m.group(2))
        if 0 <= h < 24 and 0 <= mn < 60:
            return f"{h:02d}:{mn:02d}"

    m = _TIME_WORDS.search(text)
    if m:
        key = m.group(1).lower().strip()
        h   = _TIME_WORD_MAP.get(key)
        if h is not None:
            return f"{h:02d}:00"

    return None


_CLEAN_THROUGH  = re.compile(_THROUGH_PATTERN.pattern, re.IGNORECASE)
_CLEAN_TIME_V   = re.compile(r'\bв\s*\d{1,2}[:.,-]?\d{0,2}\b', re.IGNORECASE)
_CLEAN_TIME_HM  = re.compile(r'\b\d{1,2}[.:]\d{2}\b')
_CLEAN_DATE_NUM = re.compile(r'\b\d{1,2}[./]\d{1,2}(?:[./]\d{2,4})?\b')
_CLEAN_DATE_WD  = re.compile(_DATE_WORD_PATTERN.pattern, re.IGNORECASE)
_CLEAN_REL      = re.compile(
    r'\b(завтр\w*|послезавтр\w*|сегодня|сёдня|через'
    r'|утром?|вечером?|днём?|ночью?|полдень|полночь'
    r'|понедельник\w*|вторник\w*|среду?|среды?|четверг\w*|пятниц\w*|суббот\w*|воскресень\w*'
    r'|пн|вт|ср|чт|пт|сб|вс)\b',
    re.IGNORECASE
)
_CLEAN_SPACES   = re.compile(r'\s+')


def clean_event_title(text: str) -> str:
    text = _CLEAN_THROUGH.sub('', text)
    text = _CLEAN_TIME_V.sub('', text)
    text = _CLEAN_TIME_HM.sub('', text)
    text = _CLEAN_DATE_NUM.sub('', text)
    text = _CLEAN_DATE_WD.sub('', text)
    text = _CLEAN_REL.sub('', text)
    return _CLEAN_SPACES.sub(' ', text).strip() or "Без названия"


def parse_new_event(text: str, message_date: datetime) -> dict | None:
    date_str = parse_date(text, message_date.date())
    if not date_str:
        return None
    return {
        "id": str(uuid.uuid4()),
        "title": clean_event_title(text)[:160],
        "date": date_str,
        "time": parse_time(text),
        "description": text,
        "added_at": datetime.now(MINSK_TZ).isoformat(),
    }


# ====================== МЕНЮ ======================

EVENTS_ACTION_MENU = InlineKeyboardMarkup([
    [InlineKeyboardButton("📝 Создать мероприятие", callback_data="event_new")],
    [InlineKeyboardButton("✏️ Изменить мероприятие", callback_data="event_edit")],
    [InlineKeyboardButton("↩️ Назад", callback_data="back_main")],
])

ADMIN_MENU = InlineKeyboardMarkup([
    [InlineKeyboardButton("🧹 Очистить мероприятия", callback_data="admin_clear_events")],
    [InlineKeyboardButton("🗓 Удалить мероприятие", callback_data="admin_delete_event")],
    [InlineKeyboardButton("📚 Очистить все ДЗ", callback_data="admin_clear_hw")],
    [InlineKeyboardButton("✂️ Удалить одно ДЗ", callback_data="admin_delete_one_hw")],
    [InlineKeyboardButton("↩️ Назад", callback_data="back_main")],
])

PROFILE_MENU = InlineKeyboardMarkup([
    [InlineKeyboardButton("📐 Математика (профиль)", callback_data="profile_math")],
    [InlineKeyboardButton("🧪 Химия (профиль)",      callback_data="profile_chem")],
    [InlineKeyboardButton("📘 База",                 callback_data="profile_base")],
    [InlineKeyboardButton("↩️ Назад",                callback_data="back_main")],
])

STOL_MAIN_MENU = InlineKeyboardMarkup([
    [InlineKeyboardButton("📊 Создать опрос",   callback_data="stol_create_poll")],
    [InlineKeyboardButton("📈 Показать итоги", callback_data="stol_show_results")],
    [InlineKeyboardButton("↩️ Назад",          callback_data="back_main")],
])

STOL_POLL_MARKUP = InlineKeyboardMarkup([
    [InlineKeyboardButton("🍽 Буду есть",       callback_data="stol_eat")],
    [InlineKeyboardButton("🙅 Не буду есть",   callback_data="stol_no_eat")],
    [InlineKeyboardButton("🏫 Не буду в школе", callback_data="stol_absent")],
])

DUTIES_MENU    = InlineKeyboardMarkup([[InlineKeyboardButton("↩️ Назад", callback_data="back_main")]])
BIRTHDAYS_MENU = InlineKeyboardMarkup([[InlineKeyboardButton("↩️ Назад", callback_data="back_main")]])
EVENTS_MENU    = InlineKeyboardMarkup([[InlineKeyboardButton("↩️ Назад", callback_data="back_main")]])


def days_menu(profile: str) -> InlineKeyboardMarkup:
    days = [(DAY_LABELS[key], key) for key in DAY_KEYS]
    return InlineKeyboardMarkup([
        [InlineKeyboardButton(label, callback_data=f"day*{profile}*{key}") for label, key in days[:3]],
        [InlineKeyboardButton(label, callback_data=f"day*{profile}*{key}") for label, key in days[3:]],
        [InlineKeyboardButton("↩️ Назад", callback_data="menu_schedule")],
    ])


def _hw_suffix(subject_key: str, sub_key: str | None) -> str:
    return f"{subject_key}_{sub_key}" if sub_key else subject_key


def _hw_back_callback(subject_key: str) -> str:
    if subject_key in {"math", "chem", "rus_lang"}:
        return f"hw_subject_{subject_key}"
    return "menu_hw_all"


def hw_subjects_menu(back_callback: str = "back_main") -> InlineKeyboardMarkup:
    """Меню выбора предмета для ДЗ."""
    buttons = []
    row = []
    for key, name in SUBJECTS_LIST:
        row.append(InlineKeyboardButton(name, callback_data=f"hw_subject_{key}"))
        if len(row) == 2:
            buttons.append(row)
            row = []
    if row:
        buttons.append(row)
    buttons.append([InlineKeyboardButton("↩️ Назад", callback_data=back_callback)])
    return InlineKeyboardMarkup(buttons)


def hw_math_menu() -> InlineKeyboardMarkup:
    """Для математики: сначала профиль/база, потом алгебра/геометрия."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("📐 Профиль", callback_data="hw_mathprof_profile")],
        [InlineKeyboardButton("📘 База", callback_data="hw_mathprof_base")],
        [InlineKeyboardButton("↩️ Назад", callback_data="menu_hw_all")],
    ])


def hw_math_sub_menu(level: str) -> InlineKeyboardMarkup:
    """Выбор алгебра/геометрия."""
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("➗ Алгебра", callback_data=f"hw_mathsub_{level}_algebra")],
        [InlineKeyboardButton("📐 Геометрия", callback_data=f"hw_mathsub_{level}_geometry")],
        [InlineKeyboardButton("↩️ Назад", callback_data="hw_subject_math")],
    ])


def hw_profile_menu(subject_key: str) -> InlineKeyboardMarkup:
    """Выбор профиля для предметов, где ДЗ зависит от группы."""
    profiles = HOMEWORK_PROFILE_LABELS.get(subject_key, {})
    buttons = [
        [InlineKeyboardButton(name, callback_data=f"hw_prof_{subject_key}_{pkey}")]
        for pkey, name in profiles.items()
    ]
    buttons.append([InlineKeyboardButton("↩️ Назад", callback_data="menu_hw_all")])
    return InlineKeyboardMarkup(buttons)


def hw_view_menu(subject_key: str, sub_key: str | None) -> InlineKeyboardMarkup:
    """Меню просмотра ДЗ по предмету."""
    suffix = _hw_suffix(subject_key, sub_key)
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("✏️ Записать ДЗ", callback_data=f"hw_write_{suffix}")],
        [InlineKeyboardButton("🔄 Изменить ДЗ", callback_data=f"hw_edit_{suffix}")],
        [InlineKeyboardButton("↩️ Назад", callback_data=_hw_back_callback(subject_key))],
    ])


# ====================== УТИЛИТЫ ======================

async def is_chat_admin(chat_id: int, user_id: int, bot) -> bool:
    now_ts = pytime.monotonic()
    cached = admin_cache.get(chat_id)
    if cached and (now_ts - cached["ts"] < ADMIN_CACHE_TTL):
        return user_id in cached["ids"]

    try:
        admins = await bot.get_chat_administrators(chat_id)
        admin_ids = {a.user.id for a in admins}
        admin_cache[chat_id] = {"ts": now_ts, "ids": admin_ids}
        return user_id in admin_ids
    except Exception:
        return False


MAIN_KEYBOARD = InlineKeyboardMarkup([
    [InlineKeyboardButton("📅 Расписание",   callback_data="menu_schedule")],
    [InlineKeyboardButton("🗓 Мероприятия",  callback_data="menu_events")],
    [InlineKeyboardButton("📚 ДЗ",           callback_data="menu_hw")],
    [InlineKeyboardButton("🍽 Столовая",     callback_data="menu_stolovaya")],
    [InlineKeyboardButton("🧹 Дежурства",    callback_data="duties")],
    [InlineKeyboardButton("🎂 Дни рождения", callback_data="menu_birthdays")],
    [InlineKeyboardButton("👨‍💼 Админ панель", callback_data="admin_panel")],
])

async def get_main_keyboard(chat_id: int, user_id: int, bot) -> InlineKeyboardMarkup:
    return MAIN_KEYBOARD


async def _do_edit(coro_fn, label: str, retries: int = 3):
    for attempt in range(retries):
        try:
            await coro_fn()
            return True
        except RetryAfter as e:
            wait = e.retry_after + 0.5
            if wait > 3:
                logger.warning(f"{label}: rate limit {wait:.1f}с, пропускаю долгий повтор")
                return False
            logger.warning(f"{label}: rate limit, повтор через {wait:.1f}с (попытка {attempt + 1}/{retries})")
            await asyncio.sleep(wait)
        except BadRequest as e:
            err = str(e).lower()
            if "not modified" in err or "message to edit not found" in err:
                return True
            logger.warning(f"{label} BadRequest: {e}")
            return False
        except (TimedOut, NetworkError) as e:
            wait = min(1.0 + attempt, 3.0)
            logger.warning(f"{label} network error: {e}. Повтор через {wait:.1f}с")
            await asyncio.sleep(wait)
        except Exception as e:
            logger.warning(f"{label} error: {e}")
            return False
    return False


async def safe_edit(query, text, reply_markup=None, parse_mode=ParseMode.MARKDOWN):
    return await _do_edit(
        lambda: query.edit_message_text(text=text, reply_markup=reply_markup, parse_mode=parse_mode),
        "safe_edit",
    )


async def fast_edit(bot, chat_id, msg_id, text) -> bool:
    if not msg_id:
        return False
    return await _do_edit(
        lambda: bot.edit_message_text(
            chat_id=chat_id, message_id=msg_id, text=text, parse_mode=ParseMode.MARKDOWN
        ),
        "fast_edit",
    )


def _clear_hw_interaction_state(state: dict):
    state["awaiting_hw_subject"] = None
    state["editing_hw_id"] = None
    state["hw_last_prompt_id"] = None


def _hw_prompt_markup(cancel_callback: str) -> InlineKeyboardMarkup:
    return InlineKeyboardMarkup([
        [InlineKeyboardButton("↩️ Назад", callback_data=cancel_callback)],
    ])


async def _send_hw_prompt(bot, chat_id: int, text: str, cancel_callback: str):
    return await safe_send_message(
        bot,
        label="hw_prompt",
        chat_id=chat_id,
        text=text,
        reply_markup=_hw_prompt_markup(cancel_callback),
        parse_mode=ParseMode.MARKDOWN,
    )


async def safe_send_message(bot, label: str = "safe_send_message", **kwargs):
    for attempt in range(3):
        try:
            return await bot.send_message(**kwargs)
        except RetryAfter as e:
            wait = e.retry_after + 0.5
            if wait > 3:
                logger.warning(f"{label}: rate limit {wait:.1f}с, пропускаю долгий повтор")
                return None
            logger.warning(f"{label}: rate limit, повтор через {wait:.1f}с")
            await asyncio.sleep(wait)
        except BadRequest as e:
            logger.warning(f"{label} BadRequest: {e}")
            return None
        except (TimedOut, NetworkError) as e:
            wait = min(1.0 + attempt, 3.0)
            logger.warning(f"{label} network error: {e}. Повтор через {wait:.1f}с")
            await asyncio.sleep(wait)
        except Exception as e:
            logger.warning(f"{label} error: {e}")
            return None
    return None


async def safe_answer_callback(query, text: str | None = None, show_alert: bool = False) -> bool:
    try:
        await query.answer(text=text, show_alert=show_alert)
        return True
    except BadRequest as e:
        err = str(e).lower()
        if "query is too old" in err or "query_id_invalid" in err:
            return False
        logger.warning(f"safe_answer_callback BadRequest: {e}")
        return False
    except (TimedOut, NetworkError) as e:
        logger.warning(f"safe_answer_callback network error: {e}")
        return False
    except Exception as e:
        logger.warning(f"safe_answer_callback error: {e}")
        return False


async def _delete_message_later(bot, chat_id: int, message_id: int, delay_seconds: int = HW_STATUS_TTL):
    await asyncio.sleep(delay_seconds)
    try:
        await bot.delete_message(chat_id=chat_id, message_id=message_id)
    except Exception:
        pass


async def send_auto_delete_message(
    bot,
    chat_id: int,
    text: str,
    delay_seconds: int = HW_STATUS_TTL,
    parse_mode=ParseMode.MARKDOWN,
    reply_markup=None,
):
    message = await safe_send_message(
        bot,
        label="send_auto_delete_message",
        chat_id=chat_id,
        text=text,
        parse_mode=parse_mode,
        reply_markup=reply_markup,
    )
    if not message:
        return None
    asyncio.create_task(_delete_message_later(bot, chat_id, message.message_id, delay_seconds))
    return message


def _escape_md(text: str) -> str:
    return text.replace("_", "\\_").replace("*", "\\*")


def get_results_text(votes: dict) -> str:
    def fmt(v):
        name = _escape_md(v["name"] or "Без имени")
        un = v.get("username")
        return f"{name} (@{_escape_md(un)})" if un else name

    eat    = [fmt(v) for v in votes.values() if v["status"] == "eat"]
    no_eat = [fmt(v) for v in votes.values() if v["status"] == "no_eat"]
    absent = [fmt(v) for v in votes.values() if v["status"] == "absent"]

    return (
        f" **Результаты опроса** — {len(votes)} голосов\n\n"
        f"🍽 Будут есть ({len(eat)}):\n" + ("\n".join(eat) or "—") + "\n\n"
        f"🙅 Не будут есть ({len(no_eat)}):\n" + ("\n".join(no_eat) or "—") + "\n\n"
        f"🏠 Не придут ({len(absent)}):\n" + ("\n".join(absent) or "—")
    )


def _format_event_label(ev: dict, max_title: int = 40) -> str:
    d_str = datetime.strptime(ev["date"], "%Y-%m-%d").strftime("%d.%m.%Y")
    t_str = f" {ev.get('time', '')}" if ev.get("time") else ""
    title = ev["title"]
    title_short = title[:max_title] + ("…" if len(title) > max_title else "")
    return f"{d_str}{t_str} — {title_short}"


def _load_state_votes(state: dict, loaded: dict):
    state.update(loaded)
    state["last_save"] = pytime.monotonic() - 25
    state["dirty"] = False


# ====================== ДЗ УТИЛИТЫ ======================

def _parse_hw_callback(suffix: str):
    """
    Парсит суффикс вида 'subject_key' или 'subject_key_sub_key'.
    Возвращает (subject_key, sub_key_or_None).
    sub_key — всё после первого '_' если subject_key заканчивается известным ключом профиля.
    """
    # Перебираем все возможные subject_key (от длинных к коротким)
    for skey, _ in sorted(SUBJECTS_LIST, key=lambda x: len(x[0]), reverse=True):
        if suffix == skey:
            return skey, None
        if suffix.startswith(skey + "_"):
            sub = suffix[len(skey) + 1:]
            return skey, sub
    return suffix, None


def _get_hw_for_subject(hw_list: list, subject_key: str, sub_key: str | None) -> list:
    return [h for h in hw_list
            if h.get("subject_key") == subject_key and h.get("sub_key") == sub_key]


def _get_hw_sections_for_subject(hw_list: list, subject_key: str) -> list[str | None]:
    sections = []
    seen = set()
    for h in hw_list:
        if h.get("subject_key") != subject_key:
            continue
        sub_key = h.get("sub_key")
        if sub_key not in seen:
            seen.add(sub_key)
            sections.append(sub_key)
    return sections


def hw_section_jump_menu(subject_key: str, sub_keys: list[str | None]) -> InlineKeyboardMarkup:
    buttons = [
        [InlineKeyboardButton(_hw_display_key(subject_key, sub_key), callback_data=f"hw_open_{_hw_suffix(subject_key, sub_key)}")]
        for sub_key in sub_keys
    ]
    buttons.append([InlineKeyboardButton("↩️ Назад", callback_data="menu_hw_all")])
    return InlineKeyboardMarkup(buttons)


async def get_hw_text(chat_id: int, subject_key: str, sub_key: str | None) -> str:
    hw_list = await load_hw(chat_id)
    entries = _get_hw_for_subject(hw_list, subject_key, sub_key)
    title = _hw_display_key(subject_key, sub_key)
    if not entries:
        return f"📚 **{title}**\n\nДЗ не записано."
    lines = []
    for h in sorted(entries, key=lambda x: (x.get("due_date", "9999-99-99"), x.get("added_at", ""))):
        due = h.get("due_date", "")
        due_str = ""
        if due:
            try:
                due_str = f" 📅 на {datetime.strptime(due, '%Y-%m-%d').strftime('%d.%m')}"
            except ValueError:
                due_str = f" 📅 {due}"
        lines.append(f"• {_escape_md(h['text'])}{due_str}")
    return f"📚 **{title}**\n\n" + "\n".join(lines)


# ====================== КОМАНДЫ ======================

async def start(update: Update, context: ContextTypes.DEFAULT_TYPE):
    chat_id = update.message.chat.id
    _register_chat(chat_id, update.message.chat.title or f"chat_{chat_id}")
    markup = await get_main_keyboard(chat_id, update.message.from_user.id, context.bot)
    await safe_send_message(context.bot, label="start", chat_id=chat_id, text="Выбери раздел:", reply_markup=markup)


async def event_command(update: Update, context: ContextTypes.DEFAULT_TYPE):
    try:
        await update.message.delete()
    except Exception:
        pass
    await safe_send_message(
        context.bot,
        label="event_command",
        chat_id=update.message.chat.id,
        text="🗓 Управление мероприятиями",
        reply_markup=EVENTS_ACTION_MENU,
    )


# ====================== ОБРАБОТКА ТЕКСТА ======================

async def handle_text_message(update: Update, context: ContextTypes.DEFAULT_TYPE):
    message = update.message
    if not message or not message.text:
        return

    chat_id = message.chat.id
    chat_title = message.chat.title or f"chat_{chat_id}"
    _register_chat(chat_id, chat_title)
    text = message.text.strip()
    state = chat_states[chat_id]

    # ── Запись/изменение ДЗ ──
    if state.get("awaiting_hw_subject") or state.get("editing_hw_id"):
        await _handle_hw_text(message, context, chat_id, chat_title, text, state)
        return

    if not state.get("awaiting_new_event") and not state.get("editing_event_id"):
        return

    events = await load_events(chat_id, chat_title)
    success = False
    reply_text = ""

    if state.get("awaiting_new_event"):
        state["awaiting_new_event"] = False
        new_event = parse_new_event(text, message.date)
        if new_event:
            events.append(new_event)
            await save_events(chat_id, chat_title, events)
            d_str = datetime.strptime(new_event["date"], "%Y-%m-%d").strftime("%d.%m.%Y")
            t_str = f" в {new_event['time']}" if new_event.get("time") else ""
            reply_text = f"✅ Мероприятие записано!\n\n📅 **{d_str}{t_str}** — {new_event['title']}"
            success = True
        else:
            state["awaiting_new_event"] = True
            reply_text = "❌ Не удалось распознать дату. Напиши иначе, например: «завтра в 15:00 поход» или «через неделю концерт»."

    elif state.get("editing_event_id"):
        event_id = state.pop("editing_event_id")
        target_idx = next((i for i, e in enumerate(events) if e.get("id") == event_id), None)

        if target_idx is not None:
            target = events[target_idx]
            changed = False
            new_date = parse_date(text, message.date.date())
            new_time = parse_time(text)

            if new_date:
                target["date"] = new_date
                changed = True
            if new_time:
                target["time"] = new_time
                changed = True
            if not new_date and not new_time:
                clean_text = clean_event_title(text)
                if clean_text and clean_text != target.get("title"):
                    target["title"] = clean_text
                    changed = True

            if changed:
                await save_events(chat_id, chat_title, events)
                reply_text = f"✅ Мероприятие обновлено:\n**{target.get('title')}**"
                success = True
            else:
                reply_text = "❌ Изменения не распознаны."
        else:
            reply_text = "❌ Мероприятие не найдено."

    try:
        await message.delete()
    except Exception:
        pass

    if reply_text:
        await context.bot.send_message(chat_id=chat_id, text=reply_text, parse_mode=ParseMode.MARKDOWN)

    prompt_id = state.pop("last_prompt_message_id", None)
    if prompt_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=prompt_id)
        except Exception:
            pass

    if success and state.get("last_events_message_id"):
        try:
            await fast_edit(context.bot, chat_id, state["last_events_message_id"],
                            await get_events_text(chat_id, chat_title))
        except Exception:
            pass


async def _handle_hw_text(message, context, chat_id, chat_title, text, state):
    """Обрабатывает ввод текста ДЗ."""
    hw_list = await load_hw(chat_id)
    reply_text = ""

    if state.get("awaiting_hw_subject"):
        target = state.get("awaiting_hw_subject") or {}
        subject_key = target.get("subject_key")
        sub_key = target.get("sub_key")
        due_date = target.get("due_date") or _calc_due_date(subject_key, sub_key, hw_list=hw_list)
        new_hw = {
            "id": str(uuid.uuid4()),
            "subject_key": subject_key,
            "sub_key": sub_key,
            "text": text[:500],
            "due_date": due_date,
            "added_at": datetime.now(MINSK_TZ).isoformat(),
        }
        hw_list.append(new_hw)
        await save_hw(chat_id, hw_list)
        display = _hw_display_key(subject_key, sub_key)
        try:
            due_str = datetime.strptime(due_date, "%Y-%m-%d").strftime("%d.%m.%Y")
        except ValueError:
            due_str = due_date
        reply_text = f"✅ ДЗ записано!\n\n📚 **{display}**\n📅 На {due_str}:\n{_escape_md(text[:200])}"
        state["awaiting_hw_subject"] = None

    elif state.get("editing_hw_id"):
        hw_id = state.get("editing_hw_id")
        idx = next((i for i, h in enumerate(hw_list) if h.get("id") == hw_id), None)
        if idx is not None:
            hw_list[idx]["text"] = text[:500]
            await save_hw(chat_id, hw_list)
            display = _hw_display_key(hw_list[idx]["subject_key"], hw_list[idx].get("sub_key"))
            reply_text = f"✅ ДЗ обновлено!\n\n📚 **{display}**"
        else:
            reply_text = "❌ ДЗ не найдено."
        state["editing_hw_id"] = None

    try:
        await message.delete()
    except Exception:
        pass

    prompt_id = state.pop("hw_last_prompt_id", None)
    if prompt_id:
        try:
            await context.bot.delete_message(chat_id=chat_id, message_id=prompt_id)
        except Exception:
            pass

    if reply_text:
        await send_auto_delete_message(context.bot, chat_id, reply_text, parse_mode=ParseMode.MARKDOWN)


async def get_events_text(chat_id: int, chat_title: str) -> str:
    events = await load_events(chat_id, chat_title)
    if not events:
        return "🗓 Активных мероприятий нет"
    lines = "".join(
        "📅 **{}{}** — {}\n".format(
            datetime.strptime(ev["date"], "%Y-%m-%d").strftime("%d.%m.%Y"),
            f" в {ev['time']}" if ev.get("time") else "",
            ev["title"],
        )
        for ev in sorted(events, key=lambda e: (e["date"], e.get("time") or "00:00"))
    )
    return f"🗓 **Ближайшие мероприятия**\n\n{lines}"


# ====================== CALLBACK ======================

async def callback(update: Update, context: ContextTypes.DEFAULT_TYPE):
    q = update.callback_query
    if not q or not q.message:
        return

    data = q.data
    if data not in ("stol_eat", "stol_no_eat", "stol_absent"):
        await safe_answer_callback(q)

    chat_id = q.message.chat.id
    chat_title = q.message.chat.title or f"chat_{chat_id}"
    _register_chat(chat_id, chat_title)
    user = q.from_user
    uid = str(user.id)
    state = chat_states[chat_id]

    # --- Админ панель ---
    if data == "admin_panel":
        await safe_edit(q, "👨‍💼 Админ панель", ADMIN_MENU)
        return

    if data == "admin_clear_events":
        events = await load_events(chat_id, chat_title)
        # Удаляем все напоминания
        for ev in events:
            ev_id = ev.get("id")
            if ev_id:
                await _delete_reminder(context.bot, chat_id, ev_id)
        await save_events(chat_id, chat_title, [])
        await safe_edit(q, "✅ Все мероприятия очищены.", ADMIN_MENU)
        return

    if data == "admin_delete_event":
        events = await load_events(chat_id, chat_title)
        if not events:
            await safe_edit(q, "Нет мероприятий для удаления.", ADMIN_MENU)
            return
        sorted_events = sorted(events, key=lambda e: (e["date"], e.get("time") or "00:00"))
        buttons = [
            [InlineKeyboardButton(_format_event_label(ev), callback_data=f"delete_confirm_{ev['id']}")]
            for ev in sorted_events
        ]
        buttons.append([InlineKeyboardButton("↩️ Отмена", callback_data="admin_panel")])
        await safe_edit(q, "🗑 Выберите мероприятие для удаления:", InlineKeyboardMarkup(buttons))
        return

    if data.startswith("delete_confirm_"):
        event_id = data[15:]
        events = await load_events(chat_id, chat_title)
        await save_events(chat_id, chat_title, [e for e in events if e.get("id") != event_id])
        await _delete_reminder(context.bot, chat_id, event_id)
        await safe_edit(q, "✅ Мероприятие удалено.", ADMIN_MENU)
        return

    # --- Админ: ДЗ ---
    if data == "admin_clear_hw":
        await save_hw(chat_id, [])
        await safe_edit(q, "✅ Все ДЗ удалены.", ADMIN_MENU)
        return

    if data == "admin_delete_one_hw":
        hw_list = await load_hw(chat_id)
        if not hw_list:
            await safe_edit(q, "Нет ДЗ для удаления.", ADMIN_MENU)
            return
        buttons = []
        for h in hw_list:
            display = _hw_display_key(h.get("subject_key", ""), h.get("sub_key"))
            due = h.get("due_date", "")
            try:
                due_str = datetime.strptime(due, "%Y-%m-%d").strftime("%d.%m")
            except Exception:
                due_str = due
            label = f"{display} — {h['text'][:30]} ({due_str})"
            buttons.append([InlineKeyboardButton(label, callback_data=f"admin_hw_del_{h['id']}")])
        buttons.append([InlineKeyboardButton("↩️ Отмена", callback_data="admin_panel")])
        await safe_edit(q, "❌ Выберите ДЗ для удаления:", InlineKeyboardMarkup(buttons))
        return

    if data.startswith("admin_hw_del_"):
        hw_id = data[13:]
        hw_list = await load_hw(chat_id)
        await save_hw(chat_id, [h for h in hw_list if h.get("id") != hw_id])
        await safe_edit(q, "✅ ДЗ удалено.", ADMIN_MENU)
        return

    # --- Мероприятия ---
    if data == "event_new":
        state["awaiting_new_event"] = True
        state["editing_event_id"] = None
        state["last_prompt_message_id"] = q.message.message_id
        await safe_edit(q, "📝 Опишите новое мероприятие (можно писать дату и время)")
        return

    if data == "event_edit":
        events = await load_events(chat_id, chat_title)
        if not events:
            await safe_edit(q, "🗓 Активных мероприятий нет.\n\nИспользуйте «Создать мероприятие».", EVENTS_ACTION_MENU)
            return
        sorted_events = sorted(events, key=lambda e: (e["date"], e.get("time") or "00:00"))
        buttons = [
            [InlineKeyboardButton(_format_event_label(ev), callback_data=f"select_edit_{ev['id']}")]
            for ev in sorted_events
        ]
        buttons.append([InlineKeyboardButton("↩️ Отмена", callback_data="event_edit_cancel")])
        await safe_edit(q, f"✏️ Выберите мероприятие для изменения ({len(events)} шт.):", InlineKeyboardMarkup(buttons))
        return

    if data.startswith("select_edit_"):
        state["editing_event_id"] = data[12:]
        state["awaiting_new_event"] = False
        state["last_prompt_message_id"] = q.message.message_id
        await safe_edit(q, "Напишите новый текст, дату или время")
        return

    if data == "event_edit_cancel":
        await safe_edit(q, "🗓 Управление мероприятиями", EVENTS_ACTION_MENU)
        return

    if data == "menu_events":
        _clear_hw_interaction_state(state)
        text = await get_events_text(chat_id, chat_title)
        await safe_edit(q, text, EVENTS_MENU)
        state["last_events_message_id"] = q.message.message_id
        return

    # --- ДЗ ---
    if data in ("menu_hw", "menu_hw_all"):
        _clear_hw_interaction_state(state)
        await safe_edit(q, "📚 Выбери предмет:", hw_subjects_menu())
        return

    if data in ("menu_hw_tomorrow", "menu_hw_tomorrow_write", "hw_tomwrite_empty") or any(
        data.startswith(p) for p in ("hw_tomorrow_", "hw_tomwrite_profile_", "hw_tomwrite_pick*")
    ):
        _clear_hw_interaction_state(state)
        await safe_edit(q, "📚 Выбери предмет:", hw_subjects_menu())
        return

    if data == "hw_subject_math":
        _clear_hw_interaction_state(state)
        await safe_edit(q, "➗ Математика — выбери уровень:", hw_math_menu())
        return

    if data.startswith("hw_mathprof_"):
        level = data[12:]
        _clear_hw_interaction_state(state)
        await safe_edit(q, "Выбери раздел:", hw_math_sub_menu(level))
        return

    if data.startswith("hw_mathsub_"):
        parts = data[11:].split("_", 1)
        if len(parts) == 2:
            level, branch = parts
            await _show_hw_view(q, chat_id, "math", f"{level}_{branch}")
        return

    if data.startswith("hw_subject_"):
        _clear_hw_interaction_state(state)
        subject_key = data[11:]
        if subject_key == "math":
            await safe_edit(q, "➗ Математика — выбери уровень:", hw_math_menu())
        elif subject_key in {"chem", "rus_lang"}:
            name = SUBJECTS_DICT.get(subject_key, subject_key)
            await safe_edit(q, f"{name} — выбери профиль:", hw_profile_menu(subject_key))
        elif subject_key in SUBJECTS_DICT:
            await _show_hw_view(q, chat_id, subject_key, None)
        return

    if data.startswith("hw_prof_"):
        _clear_hw_interaction_state(state)
        suffix = data[8:]
        subject_key, sub_key = _parse_hw_callback(suffix)
        await _show_hw_view(q, chat_id, subject_key, sub_key)
        return

    if data.startswith("hw_open_"):
        _clear_hw_interaction_state(state)
        suffix = data[8:]
        subject_key, sub_key = _parse_hw_callback(suffix)
        await _show_hw_view(q, chat_id, subject_key, sub_key)
        return

    if data.startswith("hw_write_"):
        suffix = data[9:]
        subject_key, sub_key = _parse_hw_callback(suffix)
        display = _hw_display_key(subject_key, sub_key)

        state["awaiting_hw_subject"] = {
            "subject_key": subject_key,
            "sub_key": sub_key,
            "due_date": None,
        }
        state["editing_hw_id"] = None
        prompt = await _send_hw_prompt(
            context.bot,
            chat_id,
            f"✏️ Напиши ДЗ по предмету:\n**{display}**",
            "menu_hw_all",
        )
        state["hw_last_prompt_id"] = prompt.message_id
        await safe_edit(q, "📚 Выбери предмет:", hw_subjects_menu())
        return

    if data.startswith("hw_edit_"):
        suffix = data[8:]
        subject_key, sub_key = _parse_hw_callback(suffix)
        hw_list = await load_hw(chat_id)
        entries = _get_hw_for_subject(hw_list, subject_key, sub_key)
        display = _hw_display_key(subject_key, sub_key)

        if not entries:
            related_sections = _get_hw_sections_for_subject(hw_list, subject_key)
            if related_sections:
                await safe_send_message(
                    context.bot,
                    label="hw_edit_related_sections",
                    chat_id=chat_id,
                    text=(
                        f"📚 **{display}**\n\n"
                        f"Для этого раздела ДЗ нет.\n"
                        f"Но у этого предмета есть записи в других разделах:"
                    ),
                    reply_markup=hw_section_jump_menu(subject_key, related_sections),
                    parse_mode=ParseMode.MARKDOWN,
                )
            else:
                await send_auto_delete_message(
                    context.bot,
                    chat_id,
                    f"📚 **{display}**\n\nНет ДЗ для изменения.",
                    parse_mode=ParseMode.MARKDOWN,
                )
            await safe_edit(q, "📚 Выбери предмет:", hw_subjects_menu())
            return

        if len(entries) == 1:
            state["awaiting_hw_subject"] = None
            state["editing_hw_id"] = entries[0]["id"]
            prompt = await _send_hw_prompt(
                context.bot,
                chat_id,
                f"✏️ Напиши новый текст ДЗ:\n**{display}**",
                "menu_hw_all",
            )
            state["hw_last_prompt_id"] = prompt.message_id
            await safe_edit(q, "📚 Выбери предмет:", hw_subjects_menu())
            return

        buttons = []
        for h in sorted(entries, key=lambda x: (x.get("due_date", "9999-99-99"), x.get("added_at", ""))):
            due = h.get("due_date", "")
            try:
                due_str = datetime.strptime(due, "%Y-%m-%d").strftime("%d.%m")
            except Exception:
                due_str = due
            label = f"{h['text'][:40]} ({due_str})"
            buttons.append([InlineKeyboardButton(label, callback_data=f"hw_editone_{h['id']}")])
        buttons.append([InlineKeyboardButton("↩️ Назад", callback_data="menu_hw_all")])

        await context.bot.send_message(
            chat_id=chat_id,
            text=f"🔄 Выбери ДЗ для изменения:\n**{display}**",
            reply_markup=InlineKeyboardMarkup(buttons),
            parse_mode=ParseMode.MARKDOWN,
        )
        await safe_edit(q, "📚 Выбери предмет:", hw_subjects_menu())
        return

    if data.startswith("hw_editone_"):
        hw_id = data[11:]
        state["awaiting_hw_subject"] = None
        state["editing_hw_id"] = hw_id
        prompt = await _send_hw_prompt(
            context.bot,
            chat_id,
            "✏️ Напиши новый текст ДЗ:",
            "menu_hw_all",
        )
        state["hw_last_prompt_id"] = prompt.message_id
        return

    # --- Основные разделы ---
    if data == "menu_birthdays":
        _clear_hw_interaction_state(state)
        months = {1:"Январь",2:"Февраль",3:"Март",4:"Апрель",5:"Май",6:"Июнь",
                  7:"Июль",8:"Август",9:"Сентябрь",10:"Октябрь",11:"Ноябрь",12:"Декабрь"}
        emojis = {1:"❄️",2:"💕",3:"🌸",4:"🐰",5:"🌷",6:"☀️",7:"🏖️",8:"🌻",9:"🍁",10:"🎃",11:"🍂",12:"🎄"}
        by_month: dict[int, list] = {i: [] for i in range(1, 13)}
        for p in BIRTHDAYS:
            d, m = map(int, p["date"].split("."))
            by_month[m].append((d, p["name"]))

        text = "🎂 **Дни рождения класса**\n\n"
        for m in range(1, 13):
            if by_month[m]:
                text += f"{emojis.get(m, '⭐')} **{months[m]}**\n"
                text += "".join(f"  • {d:02d} → {name}\n" for d, name in sorted(by_month[m]))
                text += "\n"
        await safe_edit(q, text, BIRTHDAYS_MENU)
        return

    if data == "menu_schedule":
        _clear_hw_interaction_state(state)
        await safe_edit(q, "Выбери профиль:", PROFILE_MENU)
        return

    if data.startswith("profile_"):
        prof = data.split("_")[1]
        await safe_edit(q, SCHEDULES[prof]["title"], days_menu(prof))
        return

    if data.startswith("day*"):
        _, prof, day = data.split("*")
        await safe_edit(q, SCHEDULES[prof][day].replace("*", "**"), days_menu(prof))
        return

    if data in ("back_main", "back_main_from_profile"):
        _clear_hw_interaction_state(state)
        markup = await get_main_keyboard(chat_id, q.from_user.id, context.bot)
        await safe_edit(q, "Выбери раздел:", markup)
        return

    if data == "duties":
        _clear_hw_interaction_state(state)
        await safe_edit(q, DUTIES_TEXT, DUTIES_MENU)
        return

    if data == "menu_stolovaya":
        _clear_hw_interaction_state(state)
        await safe_edit(q, "Выбери действие:", STOL_MAIN_MENU)
        return

    # ====================== БЛОК СТОЛОВОЙ ======================

    async def _ensure_votes_loaded():
        if not state.get("votes"):
            loaded = await load_state_from_file(chat_id, chat_title)
            if loaded:
                _load_state_votes(state, loaded)

    if data == "stol_create_poll":
        try:
            await q.message.delete()
        except Exception:
            pass

        state["votes"].clear()
        state["dirty"] = True

        poll_msg = await context.bot.send_message(
            chat_id=chat_id,
            text="🍽 **Опрос на завтра**",
            reply_markup=STOL_POLL_MARKUP,
            parse_mode=ParseMode.MARKDOWN,
        )
        state["poll_message_id"] = poll_msg.message_id

        try:
            await context.bot.pin_chat_message(
                chat_id=chat_id, message_id=poll_msg.message_id, disable_notification=True
            )
        except Exception:
            pass

        res_msg = await context.bot.send_message(
            chat_id=chat_id,
            text=get_results_text(state["votes"]),
            parse_mode=ParseMode.MARKDOWN,
        )
        state["results_message_id"] = res_msg.message_id
        await save_state_periodically(chat_id, chat_title)
        return

    if data in ("stol_eat", "stol_no_eat", "stol_absent"):
        await _ensure_votes_loaded()

        status_map = {"stol_eat": "eat", "stol_no_eat": "no_eat", "stol_absent": "absent"}
        state["votes"][uid] = {
            "name": user.first_name or "Без имени",
            "username": user.username or None,
            "status": status_map[data],
        }
        state["dirty"] = True

        if state.get("results_message_id"):
            success = await fast_edit(context.bot, chat_id, state["results_message_id"],
                                      get_results_text(state["votes"]))
            await safe_answer_callback(
                q,
                "Голос изменён ✓" if success else "Результаты обновлены",
                show_alert=not success,
            )
        else:
            await safe_answer_callback(q, "Голос принят")

        await save_state_periodically(chat_id, chat_title)
        return

    if data == "stol_show_results":
        await _ensure_votes_loaded()
        text = get_results_text(state["votes"]) if state.get("votes") else "Пока никто не проголосовал."
        await context.bot.send_message(chat_id=chat_id, text=text, parse_mode=ParseMode.MARKDOWN)
        return


async def _show_hw_view(q, chat_id: int, subject_key: str, sub_key: str | None):
    """Показывает ДЗ по предмету с кнопками."""
    text = await get_hw_text(chat_id, subject_key, sub_key)
    await safe_edit(q, text, hw_view_menu(subject_key, sub_key))


# ====================== ЗАПУСК ======================

async def error_handler(update: object, context: ContextTypes.DEFAULT_TYPE):
    err = context.error
    if isinstance(err, (TimedOut, NetworkError)):
        logger.warning(f"Сетевой сбой Telegram API: {err}")
        return
    logger.error("Необработанная ошибка в update", exc_info=err)

def build_application():
    app = (
        ApplicationBuilder()
        .token(TOKEN)
        .concurrent_updates(100)
        .connection_pool_size(64)
        .connect_timeout(30)
        .read_timeout(30)
        .write_timeout(30)
        .pool_timeout(30)
        .get_updates_connect_timeout(30)
        .get_updates_read_timeout(45)
        .get_updates_write_timeout(30)
        .get_updates_pool_timeout(30)
        .build()
    )

    app.add_handler(CommandHandler("start", start))
    app.add_handler(CommandHandler(["event", "ivent"], event_command))
    app.add_handler(CallbackQueryHandler(callback))
    app.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, handle_text_message))
    app.add_error_handler(error_handler)

    # ДР: проверка сразу при старте и каждый день в 8:00
    app.job_queue.run_once(callback=check_birthdays, when=10)
    app.job_queue.run_daily(callback=check_birthdays, time=time(8, 0, tzinfo=MINSK_TZ))

    # Напоминания о мероприятиях — каждые 30 минут
    app.job_queue.run_repeating(callback=check_event_reminders, interval=1800, first=15)

    return app


async def _startup_with_retry():
    attempt = 1
    while True:
        app = build_application()
        try:
            await app.initialize()
            await app.start()
            await app.updater.start_polling(
                drop_pending_updates=True,
                poll_interval=0.1,
                timeout=30,
                allowed_updates=Update.ALL_TYPES,
            )
            if attempt > 1:
                logger.info("Подключение к Telegram восстановлено, бот запущен")
            return app
        except (TimedOut, NetworkError) as e:
            delay = min(5 * attempt, 30)
            logger.warning(
                "Не удалось подключиться к Telegram (попытка %s): %s. Повтор через %s сек.",
                attempt,
                e,
                delay,
            )
            try:
                if app.updater.running:
                    await app.updater.stop()
            except Exception:
                pass
            try:
                await app.stop()
            except Exception:
                pass
            try:
                await app.shutdown()
            except Exception:
                pass
            attempt += 1
            await asyncio.sleep(delay)


async def main():
    load_static_data()
    await load_last_birthday_date()
    _discover_known_chats()

    if not TOKEN:
        raise RuntimeError("Не задан BOT_TOKEN")

    await _startup_with_retry()
    await asyncio.Event().wait()


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except (KeyboardInterrupt, SystemExit):
        logger.info("Бот остановлен")
    except Exception as e:
        logger.critical(f"Критическая ошибка запуска: {e}", exc_info=True)
