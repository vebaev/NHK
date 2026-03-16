
import os
import re
import argparse
import html as html_lib
import hashlib
import json
import time
import uuid
from concurrent.futures import ThreadPoolExecutor, as_completed
from datetime import datetime
from functools import lru_cache
import threading
from urllib.parse import urljoin, urlparse

import requests
from bs4 import BeautifulSoup, NavigableString
try:
    from googletrans import Translator
except Exception:
    Translator = None
try:
    from google import genai
except Exception:
    genai = None

try:
    import fugashi
except Exception:
    fugashi = None

try:
    import genanki
except Exception:
    genanki = None

try:
    from sudachipy import dictionary as sudachi_dictionary
    from sudachipy import tokenizer as sudachi_tokenizer
except Exception:
    sudachi_dictionary = None
    sudachi_tokenizer = None

try:
    from jinf import Jinf
except Exception:
    Jinf = None

EASY_SITEMAP_URL = "https://news.web.nhk/news/easy/sitemap/sitemap.xml"
NHKEASIER_FEED_URL = "https://nhkeasier.com/feed/"
DEFAULT_OUTPUT = "docs/index.html"
DEFAULT_ANKI_FILENAME = "anki_cards_bg.tsv"
DEFAULT_ANKI_APKG_FILENAME = "nhk_easy_elements_bg.apkg"
DEFAULT_ANKI_SEEN_WORDS_FILENAME = "anki_seen_words.json"

translator = Translator() if Translator is not None else None
DEEPL_API_KEY = os.environ.get("DEEPL_API_KEY", "").strip()
GROQ_API_KEY = os.environ.get("GROQ_API_KEY", "").strip()
GROQ_MODEL = os.environ.get("GROQ_MODEL", "qwen/qwen3-32b").strip() or "qwen/qwen3-32b"
GEMINI_API_KEY = ""
GEMINI_MODEL = ""
_TRANSLATION_CACHE = {}
_TRANSLATION_STATS = {"deepl": 0, "google": 0}
_GEMINI_CACHE = {}
_MECAB_TAGGER = None
_SUDACHI_TOKENIZER = None
_JINF = None
_WORD_GLOSSARY = None
_THREAD_LOCAL = threading.local()
_TRANSLATION_CACHE_DIRTY = False
_GEMINI_CACHE_DIRTY = False

PARTICLE_PREFIXES = ("が", "を", "に", "で", "は", "と", "へ", "や", "も", "の")
GODAN_I_TO_U = {"い":"う","き":"く","ぎ":"ぐ","し":"す","ち":"つ","に":"ぬ","び":"ぶ","み":"む","り":"る"}
GODAN_A_TO_U = {"わ":"う","か":"く","が":"ぐ","さ":"す","た":"つ","な":"ぬ","ば":"ぶ","ま":"む","ら":"る"}
GODAN_U_TO_I = {"う":"い","く":"き","ぐ":"ぎ","す":"し","つ":"ち","ぬ":"に","ぶ":"び","む":"み","る":"り"}
GODAN_E_TO_U = {"え":"う","け":"く","げ":"ぐ","せ":"す","て":"つ","で":"づ","ね":"ぬ","べ":"ぶ","め":"む","れ":"る"}

GRAMMAR_RULES = [
    {"id": "kedo", "label": "けど / けれど", "explanation_bg": "Съюз за противопоставяне: но / обаче.", "explanation_en": ""},
    {"id": "shikashi", "label": "しかし", "explanation_bg": "Обаче / въпреки това.", "explanation_en": ""},
    {"id": "temo", "label": "〜ても / 〜でも", "explanation_bg": "Дори ако / дори и да.", "explanation_en": ""},
    {"id": "nagara", "label": "〜ながら", "explanation_bg": "Едновременно действие: докато...", "explanation_en": ""},
    {"id": "tsutsu", "label": "〜つつ", "explanation_bg": "Докато..., в хода на...", "explanation_en": ""},
    {"id": "aida_ni", "label": "間 / あいだ(に)", "explanation_bg": "Докато / през времето, когато...", "explanation_en": ""},
    {"id": "uchi_ni", "label": "うちに", "explanation_bg": "Докато все още..., преди да се промени...", "explanation_en": ""},
    {"id": "kara_reason", "label": "〜から", "explanation_bg": "Причина: защото / понеже.", "explanation_en": ""},
    {"id": "node", "label": "〜ので", "explanation_bg": "Причина: тъй като / понеже.", "explanation_en": ""},
    {"id": "sorede", "label": "それで", "explanation_bg": "И затова / поради това.", "explanation_en": ""},
    {"id": "soshite", "label": "そして", "explanation_bg": "И / и след това.", "explanation_en": ""},
    {"id": "yori", "label": "〜より", "explanation_bg": "Сравнение: по-... от...", "explanation_en": ""},
    {"id": "hou", "label": "〜方", "explanation_bg": "Страна / начин; използва се и в сравнения.", "explanation_en": ""},
    {"id": "hou_ga_ii", "label": "〜方がいい / 〜方がよい", "explanation_bg": "По-добре е да...", "explanation_en": ""},
    {"id": "noni", "label": "〜のに", "explanation_bg": "Въпреки че / макар че.", "explanation_en": ""},
    {"id": "you_ni", "label": "〜ように", "explanation_bg": "Така че да..., по начин, че...", "explanation_en": ""},
    {"id": "tame_ni", "label": "〜ため(に)", "explanation_bg": "За да..., заради..., в името на...", "explanation_en": ""},
    {"id": "sei_de", "label": "〜せいで", "explanation_bg": "По вина на..., заради (негативно).", "explanation_en": ""},
    {"id": "okage_de", "label": "〜おかげで", "explanation_bg": "Благодарение на...", "explanation_en": ""},
    {"id": "rashii", "label": "〜らしい", "explanation_bg": "Изглежда / явно / характерно за.", "explanation_en": ""},
    {"id": "ppoi", "label": "〜っぽい", "explanation_bg": "Прилича на..., има оттенък на...", "explanation_en": ""},
    {"id": "dame", "label": "だめ", "explanation_bg": "Не става / не бива / забранено е.", "explanation_en": ""},
    {"id": "naranai", "label": "〜ならない", "explanation_bg": "Не бива / не става; в комбинации може да означава задължение.", "explanation_en": ""},
    {"id": "ikenai", "label": "〜いけない", "explanation_bg": "Не бива / не става; в комбинации може да означава задължение.", "explanation_en": ""},
    {"id": "nakereba_naranai", "label": "〜なければならない", "explanation_bg": "Трябва да...", "explanation_en": ""},
    {"id": "nakereba_ikenai", "label": "〜なければいけない", "explanation_bg": "Трябва да...", "explanation_en": ""},
    {"id": "nakutewa_naranai", "label": "〜なくてはならない", "explanation_bg": "Трябва да...", "explanation_en": ""},
    {"id": "ba_yokatta", "label": "〜ばよかった", "explanation_bg": "Трябваше / искаше ми се да бях...; израз на съжаление за пропусната добра възможност.", "explanation_en": ""},
    {"id": "koto_ga_aru", "label": "〜ことがある", "explanation_bg": "Случва се да... / понякога...", "explanation_en": ""},
    {"id": "koto_ni_naru", "label": "〜ことになる", "explanation_bg": "Решено е / става така, че...", "explanation_en": ""},
    {"id": "koto_ni_suru", "label": "〜ことにする", "explanation_bg": "Решавам да...", "explanation_en": ""},
    {"id": "you_ni_naru", "label": "〜ようになる", "explanation_bg": "Започвам да... / става възможно да...", "explanation_en": ""},
    {"id": "you_ni_suru", "label": "〜ようにする", "explanation_bg": "Старая се да... / правя така, че...", "explanation_en": ""},
    {"id": "souda", "label": "〜そうだ", "explanation_bg": "Изглежда / казват, че...", "explanation_en": ""},
    {"id": "tame_plain", "label": "〜ため", "explanation_bg": "Поради / заради / в името на...", "explanation_en": ""},
    {"id": "koto_nominalizer", "label": "〜こと", "explanation_bg": "Номинализация: превръща действие/състояние в „нещо, че...“.", "explanation_en": ""},
    {"id": "tokoro", "label": "〜ところ", "explanation_bg": "Точно преди / по време на / току-що след...", "explanation_en": ""},
    {"id": "tabakari", "label": "〜たばかり", "explanation_bg": "Току-що...", "explanation_en": ""},
    {"id": "te_kara", "label": "〜てから", "explanation_bg": "След като...", "explanation_en": ""},
    {"id": "mae_ni", "label": "〜前に", "explanation_bg": "Преди да...", "explanation_en": ""},
    {"id": "ato_de", "label": "〜あとで / 〜後で", "explanation_bg": "След като... / по-късно...", "explanation_en": ""},
    {"id": "nagara_mo", "label": "〜ながらも", "explanation_bg": "Макар че / въпреки че...", "explanation_en": ""},
    {"id": "ni_taishite", "label": "〜に対して", "explanation_bg": "Срещу / по отношение на...", "explanation_en": ""},
    {"id": "ni_tsuite", "label": "〜について", "explanation_bg": "Относно / за...", "explanation_en": ""},
    {"id": "ni_yoru_to", "label": "〜によると", "explanation_bg": "Според...", "explanation_en": ""},
    {"id": "ni_yotte", "label": "〜によって", "explanation_bg": "Чрез / в зависимост от / от...", "explanation_en": ""},
    {"id": "to_shite", "label": "〜として", "explanation_bg": "Като / в ролята на...", "explanation_en": ""},
    {"id": "to_tomo_ni", "label": "〜とともに", "explanation_bg": "Заедно с / едновременно с...", "explanation_en": ""},
    {"id": "ni_yori", "label": "〜により", "explanation_bg": "Поради / чрез... (формално)", "explanation_en": ""},
    {"id": "ni_oite", "label": "〜において", "explanation_bg": "В / на... (формално)", "explanation_en": ""},
    {"id": "ni_mukete", "label": "〜に向けて", "explanation_bg": "Към / с цел към...", "explanation_en": ""},
    {"id": "ni_naru", "label": "〜になる", "explanation_bg": "Става / превръща се в...", "explanation_en": ""},
    {"id": "to_naru", "label": "〜となる", "explanation_bg": "Става / се оказва... (по-формално)", "explanation_en": ""},
    {"id": "to_shite_iru", "label": "〜としている", "explanation_bg": "Възнамерява / опитва се да...", "explanation_en": ""},
    {"id": "koto_ga_dekiru", "label": "〜ことができる", "explanation_bg": "Може да...", "explanation_en": ""},
    {"id": "yasui", "label": "〜やすい", "explanation_bg": "Лесно е да...", "explanation_en": ""},
    {"id": "youda_mitaida", "label": "〜ようだ / 〜みたいだ", "explanation_bg": "Изглежда, че... / сякаш...", "explanation_en": ""},
    {"id": "wake_dewa_nai", "label": "〜わけではない", "explanation_bg": "Не значи непременно, че... / не е точно че...", "explanation_en": ""},
    {"id": "towa_kagiranai", "label": "〜とは限らない", "explanation_bg": "Не е задължително / не винаги...", "explanation_en": ""},
    {"id": "osore_ga_aru", "label": "〜おそれがある", "explanation_bg": "Има опасност да...", "explanation_en": ""},
    {"id": "mikomi", "label": "〜見込み", "explanation_bg": "Очаква се / има изгледи за...", "explanation_en": ""},
    {"id": "yotei", "label": "〜予定", "explanation_bg": "Планира се / по план...", "explanation_en": ""},
    {"id": "chu", "label": "〜中", "explanation_bg": "По време на / в процес на...", "explanation_en": ""},
    {"id": "ato_after", "label": "〜後 / 〜あと", "explanation_bg": "След / след като...", "explanation_en": ""},
    {"id": "ijo", "label": "〜以上", "explanation_bg": "Повече от / след като...", "explanation_en": ""},
    {"id": "ni_awasete", "label": "〜に合わせて", "explanation_bg": "В съответствие с / според...", "explanation_en": ""},
    {"id": "tari_tari", "label": "〜たり〜たりする", "explanation_bg": "Правя разни неща като...", "explanation_en": ""},
    {"id": "dake", "label": "〜だけ", "explanation_bg": "Само / единствено.", "explanation_en": ""},
    {"id": "nomi", "label": "〜のみ", "explanation_bg": "Само / единствено (по-формално).", "explanation_en": ""},
    {"id": "bakari", "label": "〜ばかり", "explanation_bg": "Само..., все...", "explanation_en": ""},
    {"id": "shika_nai", "label": "〜しか〜ない", "explanation_bg": "Нищо друго освен..., само...", "explanation_en": ""},
    {"id": "mou", "label": "もう", "explanation_bg": "Вече.", "explanation_en": ""},
    {"id": "mada", "label": "まだ", "explanation_bg": "Още / все още.", "explanation_en": ""},
    {"id": "mata", "label": "また", "explanation_bg": "Пак / отново / също така.", "explanation_en": ""},
    {"id": "te_ii", "label": "〜ていい", "explanation_bg": "Разрешено е да...", "explanation_en": ""},
    {"id": "temo_ii", "label": "〜てもいい", "explanation_bg": "Може да... / разрешено е да...", "explanation_en": ""},
    {"id": "te_miru", "label": "〜てみる", "explanation_bg": "Да пробвам да...", "explanation_en": ""},
    {"id": "kke", "label": "〜っけ", "explanation_bg": "Беше ли..., как беше...", "explanation_en": ""},
    {"id": "kana", "label": "〜かな", "explanation_bg": "Чудя се дали..., дали...", "explanation_en": ""},
    {"id": "kai_dai", "label": "〜かい / 〜だい", "explanation_bg": "Разговорна въпросителна форма.", "explanation_en": ""},
    {"id": "janai", "label": "〜じゃない", "explanation_bg": "Не е ли..., нали...", "explanation_en": ""},
    {"id": "causative_saseru", "label": "使役 (〜させる / 〜せる)", "explanation_bg": "Каузатив: карам/оставям някого да...", "explanation_en": ""},
    {"id": "nakute", "label": "〜なくて", "explanation_bg": "Без да..., не и..., понеже не...", "explanation_en": ""},
    {"id": "naide", "label": "〜ないで", "explanation_bg": "Без да..., не правейки...", "explanation_en": ""},
    {"id": "zu", "label": "〜ず / 〜ずに", "explanation_bg": "Без да...", "explanation_en": ""},
    {"id": "te_shimau", "label": "〜てしまう", "explanation_bg": "Завършеност или нежелан резултат.", "explanation_en": ""},
    {"id": "te_oku", "label": "〜ておく", "explanation_bg": "Правя нещо предварително.", "explanation_en": ""},
    {"id": "datte", "label": "だって", "explanation_bg": "Защото..., дори..., дори и...", "explanation_en": ""},
    {"id": "wake", "label": "〜わけ", "explanation_bg": "Причина / смисъл / следва, че...", "explanation_en": ""},
    {"id": "hazu", "label": "〜はず", "explanation_bg": "Би трябвало / очаква се.", "explanation_en": ""},
    {"id": "beki", "label": "〜べき", "explanation_bg": "Трябва / редно е.", "explanation_en": ""},
    {"id": "beki_datta", "label": "〜べきだった", "explanation_bg": "Трябвало е да...", "explanation_en": ""},
    {"id": "beshi", "label": "〜べし", "explanation_bg": "Трябва / следва (книжовно).", "explanation_en": ""},
    {"id": "mono_da", "label": "〜ものだ", "explanation_bg": "По принцип така е / естествено е / подобава.", "explanation_en": ""},
    {"id": "kamoshirenai", "label": "〜かもしれない / 〜かもしれません", "explanation_bg": "Може би... / възможно е...", "explanation_en": ""},
    {"id": "kamo", "label": "〜かも", "explanation_bg": "Може би... (разговорно).", "explanation_en": ""},
    {"id": "nikui", "label": "〜にくい", "explanation_bg": "Трудно е да се... / не е лесно да...", "explanation_en": ""},
    {"id": "koro", "label": "〜ころ", "explanation_bg": "Около даден момент / по времето, когато...", "explanation_en": ""},
    {"id": "goro", "label": "〜ごろ", "explanation_bg": "Около (час/период).", "explanation_en": ""},
    {"id": "kurai_gurai", "label": "〜くらい / 〜ぐらい", "explanation_bg": "Около / приблизително / до такава степен.", "explanation_en": ""},
    {"id": "made", "label": "〜まで", "explanation_bg": "До / чак до.", "explanation_en": ""},
    {"id": "kara_made", "label": "〜から〜まで", "explanation_bg": "От... до...", "explanation_en": ""},
    {"id": "made_ni", "label": "〜までに", "explanation_bg": "До (краен срок).", "explanation_en": ""},
    {"id": "hodo", "label": "〜ほど", "explanation_bg": "До такава степен / колкото...", "explanation_en": ""},
    {"id": "sugiru", "label": "〜すぎる", "explanation_bg": "Прекалено / твърде много.", "explanation_en": ""},
]
GRAMMAR_RULES_BY_ID = {r["id"]: r for r in GRAMMAR_RULES}


def get_http_session():
    session = getattr(_THREAD_LOCAL, "http_session", None)
    if session is None:
        session = requests.Session()
        session.headers.update({"User-Agent": "nhk-easy-pipeline/1.0"})
        _THREAD_LOCAL.http_session = session
    return session


def get_sudachi_tokenizer():
    global _SUDACHI_TOKENIZER
    if _SUDACHI_TOKENIZER is not None:
        return _SUDACHI_TOKENIZER
    if sudachi_dictionary is None or sudachi_tokenizer is None:
        return None
    try:
        _SUDACHI_TOKENIZER = sudachi_dictionary.Dictionary().create()
    except Exception:
        _SUDACHI_TOKENIZER = None
    return _SUDACHI_TOKENIZER


def get_jinf():
    global _JINF
    if _JINF is not None:
        return _JINF
    if Jinf is None:
        return None
    try:
        _JINF = Jinf()
    except Exception:
        _JINF = None
    return _JINF


def get_translation_cache_path(output_path: str = "") -> str:
    candidates = []
    if output_path:
        output_dir = os.path.dirname(output_path)
        if output_dir:
            candidates.append(os.path.join(output_dir, "translations_cache.json"))
    candidates.extend([
        os.path.join("docs", "translations_cache.json"),
        os.path.join(os.path.dirname(__file__), "docs", "translations_cache.json"),
        "translations_cache.json",
    ])
    for path in candidates:
        if path:
            return path
    return "translations_cache.json"


def get_gemini_cache_path(output_path: str = "") -> str:
    candidates = []
    if output_path:
        output_dir = os.path.dirname(output_path)
        if output_dir:
            candidates.append(os.path.join(output_dir, "gemini_verbs_cache.json"))
    candidates.extend([
        os.path.join("docs", "gemini_verbs_cache.json"),
        os.path.join(os.path.dirname(__file__), "docs", "gemini_verbs_cache.json"),
        "gemini_verbs_cache.json",
    ])
    for path in candidates:
        if path:
            return path
    return "gemini_verbs_cache.json"


def load_translation_cache(path: str):
    global _TRANSLATION_CACHE, _TRANSLATION_CACHE_DIRTY
    if _TRANSLATION_CACHE:
        return
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict):
            loaded = {}
            for raw_key, value in data.items():
                try:
                    parsed_key = json.loads(raw_key)
                except Exception:
                    continue
                if isinstance(parsed_key, list):
                    loaded[tuple(parsed_key)] = str(value or "")
            _TRANSLATION_CACHE = loaded
    except Exception:
        _TRANSLATION_CACHE = {}
    _TRANSLATION_CACHE_DIRTY = False


def load_gemini_cache(path: str):
    global _GEMINI_CACHE, _GEMINI_CACHE_DIRTY
    if _GEMINI_CACHE:
        return
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        if isinstance(data, dict):
            _GEMINI_CACHE = {str(k): v for k, v in data.items()}
    except Exception:
        _GEMINI_CACHE = {}
    _GEMINI_CACHE_DIRTY = False


def save_translation_cache(path: str):
    global _TRANSLATION_CACHE_DIRTY
    if not _TRANSLATION_CACHE_DIRTY:
        return
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    data = {json.dumps(list(key), ensure_ascii=False): value for key, value in _TRANSLATION_CACHE.items()}
    with open(path, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False, indent=2, sort_keys=True)
    _TRANSLATION_CACHE_DIRTY = False


def save_gemini_cache(path: str):
    global _GEMINI_CACHE_DIRTY
    if not _GEMINI_CACHE_DIRTY:
        return
    os.makedirs(os.path.dirname(path) or ".", exist_ok=True)
    with open(path, "w", encoding="utf-8") as f:
        json.dump(_GEMINI_CACHE, f, ensure_ascii=False, indent=2, sort_keys=True)
    _GEMINI_CACHE_DIRTY = False


def cache_translation_result(cache_key, value: str) -> str:
    global _TRANSLATION_CACHE_DIRTY
    normalized = (value or "").strip()
    if _TRANSLATION_CACHE.get(cache_key) != normalized:
        _TRANSLATION_CACHE_DIRTY = True
    _TRANSLATION_CACHE[cache_key] = normalized
    return normalized


def cache_gemini_result(cache_key: str, value):
    global _GEMINI_CACHE_DIRTY
    if _GEMINI_CACHE.get(cache_key) != value:
        _GEMINI_CACHE_DIRTY = True
    _GEMINI_CACHE[cache_key] = value
    return value

def ensure_grammar_bilingual():
    missing_bg = [rule.get("explanation_bg", "") for rule in GRAMMAR_RULES if not rule.get("explanation_en")]
    translated = translate_texts(missing_bg, dest="en")
    for rule in GRAMMAR_RULES:
        if not rule.get("explanation_en"):
            bg = rule.get("explanation_bg", "")
            rule["explanation_en"] = translated.get(bg) or translate_text(bg, dest="en") or bg
    global GRAMMAR_RULES_BY_ID
    GRAMMAR_RULES_BY_ID = {r["id"]: r for r in GRAMMAR_RULES}


def load_word_glossary():
    global _WORD_GLOSSARY
    if _WORD_GLOSSARY is not None:
        return _WORD_GLOSSARY
    candidates = ["glossary_overrides.json", os.path.join(os.path.dirname(__file__), "glossary_overrides.json")]
    for path in candidates:
        if os.path.exists(path):
            try:
                with open(path, "r", encoding="utf-8") as f:
                    data = json.load(f)
                if isinstance(data, dict):
                    _WORD_GLOSSARY = {str(k).strip(): str(v).strip() for k, v in data.items() if str(k).strip()}
                    return _WORD_GLOSSARY
            except Exception:
                pass
    _WORD_GLOSSARY = {}
    return _WORD_GLOSSARY


def sudachi_tokenize(text: str):
    tokenizer = get_sudachi_tokenizer()
    if tokenizer is None or not text:
        return []
    try:
        return list(tokenizer.tokenize(text, sudachi_tokenizer.Tokenizer.SplitMode.C))
    except Exception:
        return []


def sudachi_feature(m):
    pos = tuple(m.part_of_speech()) if hasattr(m, "part_of_speech") else ()
    return {
        "pos1": pos[0] if len(pos) > 0 else "",
        "pos2": pos[1] if len(pos) > 1 else "",
        "ctype": pos[4] if len(pos) > 4 else "",
        "cform": pos[5] if len(pos) > 5 else "",
    }


def sudachi_reading(m) -> str:
    try:
        return normalize_katakana_to_hiragana((m.reading_form() or "").strip())
    except Exception:
        return ""


def sudachi_dictionary_form(m) -> str:
    try:
        return (m.dictionary_form() or "").strip()
    except Exception:
        return ""


def sudachi_surface(m) -> str:
    try:
        return (m.surface() or "").strip()
    except Exception:
        return ""


def sudachi_content_tokens(tokens):
    return [m for m in tokens if sudachi_feature(m)["pos1"] not in {"助詞", "助動詞", "補助記号"}]


def choose_sudachi_core_token(tokens):
    content = sudachi_content_tokens(tokens)
    if not content:
        return tokens[0] if tokens else None
    conditional = next((m for m in content if "仮定形" in sudachi_feature(m)["cform"]), None)
    if conditional is not None:
        return conditional
    for m in reversed(content):
        if sudachi_feature(m)["pos1"] in {"動詞", "形容詞"}:
            return m
    return content[0]


def build_sudachi_compound_lemma(surface: str, tokens):
    derived = to_dictionary_form(surface)
    if derived and derived != surface:
        return derived
    content = sudachi_content_tokens(tokens)
    if not content:
        return derived or surface
    if len(content) == 1:
        return sudachi_dictionary_form(content[0]) or derived or surface
    prefix = "".join(sudachi_surface(m) for m in content[:-1]).strip()
    tail = sudachi_dictionary_form(content[-1]).strip()
    if prefix and tail:
        return prefix + tail
    return tail or derived or surface

@lru_cache(maxsize=8192)
def lookup_dictionary_meaning(word: str, reading: str = "") -> str:
    return translate_word_lang(word, reading=reading, dest="en")


@lru_cache(maxsize=8192)
def lookup_dictionary_entry(word: str, reading: str = ""):
    word = (word or "").strip()
    reading = normalize_katakana_to_hiragana((reading or "").strip())
    lemma = to_dictionary_form(word) if word else ""
    base = lemma or word
    if not base and not reading:
        return None
    return {
        "surface": base or reading,
        "reading": reading,
        "gloss": "",
        "pos": "",
        "priority": 0,
    }


def merge_compound_nouns(tokens):
    compounds = []
    current = []
    for token in tokens:
        feat = token_feature(token)
        pos1 = getattr(feat, "pos1", "") if feat is not None else ""
        pos2 = getattr(feat, "pos2", "") if feat is not None else ""
        surface = token_surface(token).strip()
        reading = normalize_katakana_to_hiragana(feature_reading(token).strip())
        if pos1 == "名詞" and pos2 not in {"代名詞", "非自立"} and surface:
            current.append((surface, reading))
        else:
            if len(current) >= 2:
                compounds.append(current[:])
            current = []
    if len(current) >= 2:
        compounds.append(current[:])
    return compounds


def merge_katakana_phrases(tokens):
    phrases = []
    current = []
    for token in tokens:
        surface = token_surface(token).strip()
        feat = token_feature(token)
        pos1 = getattr(feat, "pos1", "") if feat is not None else ""
        reading = normalize_katakana_to_hiragana(feature_reading(token).strip())
        is_katakana = bool(surface) and bool(re.fullmatch(r"[ァ-ヶー]+", surface))
        is_connector = surface in {"・", "＝", "-", "−", "ー"} and current
        if is_katakana or (is_connector and pos1 in {"記号", "補助記号", ""}):
            current.append((surface, reading))
            continue
        if len(current) >= 2 or (current and any(part[0] == "・" for part in current)):
            phrases.append(current[:])
        current = []
    if len(current) >= 2 or (current and any(part[0] == "・" for part in current)):
        phrases.append(current[:])
    return phrases

def contains_japanese(text: str) -> bool:
    return bool(re.search(r"[ぁ-んァ-ン一-龯]", text or ""))

def normalize_for_compare(text: str) -> str:
    return re.sub(r"\s+", "", (text or "").strip())


def _deepl_target_lang(dest: str) -> str:
    return {"en": "EN", "bg": "BG"}.get((dest or "").lower(), (dest or "").upper())


def translate_text(text: str, dest: str = "bg") -> str:
    text = (text or "").strip()
    if not text:
        return ""
    cache_key = ("text", text, dest, bool(DEEPL_API_KEY))
    if cache_key in _TRANSLATION_CACHE:
        return _TRANSLATION_CACHE[cache_key]
    result = ""
    if DEEPL_API_KEY:
        try:
            deepl_url = "https://api-free.deepl.com/v2/translate"
            if not DEEPL_API_KEY.endswith(":fx"):
                deepl_url = "https://api.deepl.com/v2/translate"
            resp = get_http_session().post(
                deepl_url,
                headers={"Authorization": f"DeepL-Auth-Key {DEEPL_API_KEY}"},
                data={"text": text, "target_lang": _deepl_target_lang(dest)},
                timeout=20,
            )
            data = resp.json()
            translations = data.get("translations") or []
            if translations and translations[0].get("text"):
                result = (translations[0]["text"] or "").strip()
                _TRANSLATION_STATS["deepl"] += 1
        except Exception:
            result = ""
    if not result:
        try:
            if translator is None:
                raise RuntimeError("googletrans unavailable")
            result = (translator.translate(text, dest=dest).text or "").strip()
            if result:
                _TRANSLATION_STATS["google"] += 1
        except Exception:
            result = ""
    if not result:
        return cache_translation_result(cache_key, "")
    src_norm = normalize_for_compare(text)
    out_norm = normalize_for_compare(result)
    if out_norm == src_norm:
        return cache_translation_result(cache_key, "")
    if contains_japanese(result) and dest in {"bg", "en"}:
        return cache_translation_result(cache_key, "")
    return cache_translation_result(cache_key, result)


def translate_texts(texts, dest: str = "bg"):
    unique_texts = unique_keep_order(texts)
    if not unique_texts:
        return {}

    results = {}
    missing = []
    for text in unique_texts:
        cache_key = ("text", text, dest, bool(DEEPL_API_KEY))
        if cache_key in _TRANSLATION_CACHE:
            results[text] = _TRANSLATION_CACHE[cache_key]
        else:
            missing.append(text)

    if missing and DEEPL_API_KEY:
        try:
            deepl_url = "https://api-free.deepl.com/v2/translate"
            if not DEEPL_API_KEY.endswith(":fx"):
                deepl_url = "https://api.deepl.com/v2/translate"
            payload = [("text", text) for text in missing]
            payload.append(("target_lang", _deepl_target_lang(dest)))
            resp = get_http_session().post(
                deepl_url,
                headers={"Authorization": f"DeepL-Auth-Key {DEEPL_API_KEY}"},
                data=payload,
                timeout=30,
            )
            data = resp.json()
            translations = data.get("translations") or []
            if len(translations) == len(missing):
                for text, item in zip(missing, translations):
                    translated = (item.get("text") or "").strip()
                    if translated:
                        results[text] = cache_translation_result(("text", text, dest, bool(DEEPL_API_KEY)), translated)
                        _TRANSLATION_STATS["deepl"] += 1
                missing = [text for text in missing if text not in results]
        except Exception:
            pass

    for text in missing:
        results[text] = translate_text(text, dest=dest)
    return results

def translate_word_lang(word: str, reading: str = "", dest: str = "bg") -> str:
    word = (word or "").strip()
    if not word:
        return ""
    cache_key = ("word_lang", word, reading, dest)
    if cache_key in _TRANSLATION_CACHE:
        return _TRANSLATION_CACHE[cache_key]
    translated = translate_text(to_dictionary_form(word) or word, dest=dest)
    return cache_translation_result(cache_key, translated.strip())


def contextual_surface_meaning(surface: str, lemma: str = "", reading_surface: str = "", reading_lemma: str = "", form_label_bg: str = "", form_label_en: str = ""):
    surface = (surface or "").strip()
    lemma = (lemma or "").strip()
    reading_surface = normalize_katakana_to_hiragana((reading_surface or "").strip())
    reading_lemma = normalize_katakana_to_hiragana((reading_lemma or "").strip())
    form_label_bg = (form_label_bg or "").strip()
    form_label_en = (form_label_en or "").strip()

    base_bg = translate_word_lang(lemma or surface, reading_lemma or reading_surface, dest="bg") or ""
    base_en = translate_word_lang(lemma or surface, reading_lemma or reading_surface, dest="en") or ""

    direct_bg = translate_text(surface, dest="bg") or ""
    direct_en = translate_text(surface, dest="en") or ""

    def usable_direct(src, out):
        src = (src or "").strip()
        out = (out or "").strip()
        return bool(out and out != src)

    if form_label_bg == "учтива отрицателна форма на 〜ている":
        bg = "не е " + base_bg if base_bg and not base_bg.startswith("не ") else (base_bg or "")
        en = "has not been " + base_en if base_en else ""
        if not bg:
            bg = direct_bg if usable_direct(surface, direct_bg) else "не е намерено"
        if not en:
            en = direct_en if usable_direct(surface, direct_en) else "has not been found"
        return {"bg": bg, "en": en}

    if form_label_bg == "учтива форма на 〜ている" and base_bg:
        return {"bg": "е " + base_bg, "en": ("is " + base_en) if base_en else direct_en}
    if form_label_bg == "минала форма на 〜ている" and base_bg:
        return {"bg": "беше " + base_bg, "en": ("was " + base_en) if base_en else direct_en}

    return {
        "bg": direct_bg if usable_direct(surface, direct_bg) else base_bg,
        "en": direct_en if usable_direct(surface, direct_en) else base_en,
    }


def get_article_blocks(content):
    blocks = []
    for el in content.find_all(["p", "h2", "h3", "li"], recursive=True):
        txt = el.get_text(" ", strip=True)
        if not txt or len(txt) < 3:
            continue
        blocks.append({"text": txt, "html": "".join(str(x) for x in el.contents).strip()})
    return blocks

def get_mecab_tagger():
    global _MECAB_TAGGER
    if _MECAB_TAGGER is not None:
        return _MECAB_TAGGER
    if fugashi is None:
        return None
    try:
        _MECAB_TAGGER = fugashi.Tagger()
    except Exception:
        _MECAB_TAGGER = None
    return _MECAB_TAGGER

def token_feature(token):
    return getattr(token, "feature", None)
def token_surface(token) -> str:
    return getattr(token, "surface", "") or ""
def token_lemma(token) -> str:
    feat = token_feature(token)
    if feat is None:
        return ""
    for name in ("lemma", "dictionary_form", "lemma_form", "orthBase"):
        value = getattr(feat, name, "") or ""
        if value:
            return value.strip()
    return ""
def feature_reading(token) -> str:
    feat = token_feature(token)
    if feat is None:
        return ""
    for name in ("kana", "pron", "reading", "pronBase"):
        value = getattr(feat, name, "") or ""
        if value and value != "*":
            return value.strip()
    return ""
@lru_cache(maxsize=16384)
def normalize_katakana_to_hiragana(text: str) -> str:
    result = []
    for ch in text or "":
        code = ord(ch)
        result.append(chr(code - 0x60) if 0x30A1 <= code <= 0x30F6 else ch)
    return "".join(result)


@lru_cache(maxsize=8192)
def get_reading_for_word(word: str, fallback: str = "") -> str:
    word = (word or "").strip()
    fallback = normalize_katakana_to_hiragana((fallback or "").strip())
    if not word:
        return fallback
    entry = lookup_dictionary_entry(word)
    if entry and (entry.get("reading") or "").strip():
        return normalize_katakana_to_hiragana((entry.get("reading") or "").strip())
    sudachi_tokens = sudachi_tokenize(word)
    if sudachi_tokens:
        reading = "".join(sudachi_reading(t) for t in sudachi_tokens).strip()
        if reading:
            return reading
    tagger = get_mecab_tagger()
    if tagger is not None:
        try:
            tokens = list(tagger(word))
            if tokens:
                reading = normalize_katakana_to_hiragana("".join(feature_reading(t).strip() for t in tokens))
                if reading:
                    return reading
        except Exception:
            pass
    return fallback

def unique_keep_order(values):
    seen = set()
    out = []
    for v in values or []:
        s = (v or "").strip()
        if s and s not in seen:
            seen.add(s)
            out.append(s)
    return out

def safe_feature_value(feat, *names):
    if feat is None:
        return ""
    for name in names:
        value = getattr(feat, name, "") or ""
        if value and value != "*":
            return str(value).strip()
    return ""

def classify_japanese_form(surface: str, lemma: str = "", pos1: str = "", pos2: str = "", ctype: str = "", cform: str = ""):
    s = (surface or "").strip()
    l = (lemma or "").strip()
    low = (ctype + " " + cform).lower()

    if "ばよかった" in s:
        return {"bg": "условна форма (-ば) + よかった", "en": "conditional (-ba) + yokatta"}
    if "仮定形" in cform or s.endswith("れば") or s.endswith("ば"):
        if "よかった" in s:
            return {"bg": "условна форма (-ば) + よかった", "en": "conditional (-ba) + yokatta"}
        return {"bg": "условна форма (-ば)", "en": "conditional (-ba) form"}
    if s and l and s == l:
        return {"bg": "речникова форма", "en": "dictionary form"}
    if s.endswith(("ていません", "でいません")):
        return {"bg": "учтива отрицателна форма на 〜ている", "en": "polite negative 〜te iru form"}
    if s.endswith(("ていました", "でいました")):
        return {"bg": "учтива минала форма на 〜ている", "en": "polite past 〜te iru form"}
    if s.endswith(("ています", "でいます")):
        return {"bg": "учтива форма на 〜ている", "en": "polite 〜te iru form"}
    if s.endswith(("ていない", "でいない")):
        return {"bg": "отрицателна форма на 〜ている", "en": "negative 〜te iru form"}
    if s.endswith(("ていた", "でいた")):
        return {"bg": "минала форма на 〜ている", "en": "past 〜te iru form"}
    if s.endswith(("ている", "でいる")):
        return {"bg": "форма на 〜ている", "en": "〜te iru form"}
    if s.endswith("なかった"):
        return {"bg": "отрицателна минала форма", "en": "past negative form"}
    if s.endswith("なくて"):
        return {"bg": "форма なくて", "en": "nakute form"}
    if s.endswith("ないで"):
        return {"bg": "форма ないで", "en": "naide form"}
    if any(x in low for x in ["past", "連用タ接続"]) or (s.endswith(("た","だ")) and s != l):
        if pos1 == "形容詞" or s.endswith("かった"):
            return {"bg": "минала форма на i-прилагателно", "en": "past i-adjective form"}
        if "polite" in low or s.endswith("ました"):
            return {"bg": "учтива минала форма", "en": "polite past form"}
        return {"bg": "минало време", "en": "past tense"}
    if s.endswith("ません"):
        return {"bg": "учтива отрицателна форма", "en": "polite negative form"}
    if s.endswith(("ない","ぬ","ん")) and s != l:
        return {"bg": "отрицателна форма", "en": "negative form"}
    if s.endswith(("て","で")) and s != l:
        return {"bg": "て-форма", "en": "te-form"}
    if s.endswith(("ます","です")) and s != l:
        return {"bg": "учтива форма", "en": "polite form"}
    if s.endswith("ましょう"):
        return {"bg": "учтива волева форма", "en": "polite volitional form"}
    if s.endswith(("よう","おう")) and s != l:
        return {"bg": "волева форма", "en": "volitional form"}
    if s.endswith(("れる","られる")) and s != l:
        return {"bg": "пасивна / потенциална форма", "en": "passive / potential form"}
    if "使役" in ctype or s.endswith(("せる","させる")):
        return {"bg": "каузативна форма", "en": "causative form"}
    if s.endswith("たい"):
        return {"bg": "форма за желание", "en": "desire form"}
    if s.endswith("くて"):
        return {"bg": "свързваща форма на i-прилагателно", "en": "i-adjective conjunctive form"}
    if s.endswith("くない"):
        return {"bg": "отрицателна форма на i-прилагателно", "en": "negative i-adjective form"}
    if s.endswith("かった"):
        return {"bg": "минала форма на i-прилагателно", "en": "past i-adjective form"}
    if pos1 == "動詞":
        return {"bg": "глаголна форма", "en": "verb form"}
    if pos1 == "形容詞":
        return {"bg": "форма на прилагателно", "en": "adjective form"}
    return {"bg": "форма в текста", "en": "form in context"}


def build_japanese_form_formula(surface: str, lemma: str = "", pos1: str = "", pos2: str = "", ctype: str = "", cform: str = ""):
    s = (surface or "").strip()
    l = (lemma or "").strip() or s
    if not s:
        return {"bg": "", "en": ""}

    def out(bg: str, en: str):
        return {"bg": bg, "en": en}

    def chain(*parts: str):
        cleaned = [p for p in parts if (p or "").strip()]
        text = " -> ".join(cleaned)
        return out(text, text)

    def jinf_inf_type(word: str, inf_type: str) -> str:
        inf_type = (inf_type or "").strip()
        word = (word or "").strip()
        if inf_type.startswith("五段-"):
            return f"子音動詞{inf_type.split('五段-', 1)[1]}"
        if inf_type.startswith("上一段") or inf_type.startswith("下一段"):
            return "母音動詞"
        if inf_type.startswith("カ行変格"):
            return "カ変動詞来" if word in {"来る", "くる"} else "カ変動詞"
        if inf_type.startswith("サ行変格"):
            return "サ変動詞"
        if inf_type == "形容詞" and word.endswith("い"):
            return "イ形容詞イ段"
        return ""

    def jinf_convert(word: str, inf_type: str, target_form: str) -> str:
        engine = get_jinf()
        mapped_type = jinf_inf_type(word, inf_type)
        if engine is None or not mapped_type:
            return ""
        try:
            if not engine.is_valid_type(mapped_type) or not engine.is_valid_form(mapped_type, target_form):
                return ""
            return (engine.convert(word, mapped_type, "基本形", target_form) or "").strip()
        except Exception:
            return ""

    def masu_stem(word: str) -> str:
        word = (word or "").strip()
        if not word:
            return ""
        via_jinf = jinf_convert(word, ctype, "基本連用形")
        if via_jinf:
            return via_jinf
        if word.endswith("する"):
            return word[:-2] + "し"
        if word.endswith("くる"):
            return word[:-2] + "き"
        if word.endswith("来る"):
            return word[:-2] + "来"
        if word.endswith("る") and len(word) >= 2:
            prev = word[-2]
            if prev in "えけげせぜてでねへべぺめれいきぎしじちぢにひびぴみり":
                return word[:-1]
        if word[-1] in GODAN_U_TO_I:
            return word[:-1] + GODAN_U_TO_I[word[-1]]
        return word

    def ba_form(word: str) -> str:
        word = (word or "").strip()
        if not word:
            return ""
        via_jinf = jinf_convert(word, ctype, "基本条件形")
        if via_jinf:
            return via_jinf
        if word.endswith("する"):
            return word[:-2] + "すれば"
        if word.endswith("くる"):
            return word[:-2] + "くれば"
        if word.endswith("来る"):
            return word[:-2] + "来れば"
        if word.endswith("る") and len(word) >= 2:
            prev = word[-2]
            if prev in "えけげせぜてでねへべぺめれいきぎしじちぢにひびぴみり":
                return word[:-1] + "れば"
        if word.endswith("う"):
            return word[:-1] + "えば"
        if word.endswith("く"):
            return word[:-1] + "けば"
        if word.endswith("ぐ"):
            return word[:-1] + "げば"
        if word.endswith("す"):
            return word[:-1] + "せば"
        if word.endswith("つ"):
            return word[:-1] + "てば"
        if word.endswith("ぬ"):
            return word[:-1] + "ねば"
        if word.endswith("ぶ"):
            return word[:-1] + "べば"
        if word.endswith("む"):
            return word[:-1] + "めば"
        if word.endswith("る"):
            return word[:-1] + "れば"
        if word.endswith("い"):
            return word[:-1] + "ければ"
        return word + "ば"

    if s == l:
        return out(l, l)

    if "よかった" in s and ("ば" in s or "仮定形" in cform):
        ba = ba_form(l)
        return chain(l, ba, s)
    if "仮定形" in cform or s.endswith("れば") or s.endswith("ば"):
        ba = ba_form(l)
        return chain(l, ba)

    te_iru_map = [
        ("ていませんでした", "te-form + いませんでした"),
        ("でいませんでした", "de-form + いませんでした"),
        ("ていました", "te-form + いました"),
        ("でいました", "de-form + いました"),
        ("ていません", "te-form + いません"),
        ("でいません", "de-form + いません"),
        ("ていない", "te-form + いない"),
        ("でいない", "de-form + いない"),
        ("ています", "te-form + います"),
        ("でいます", "de-form + います"),
        ("ていた", "te-form + いた"),
        ("でいた", "de-form + いた"),
        ("ている", "te-form + いる"),
        ("でいる", "de-form + いる"),
    ]
    for suffix, formula in te_iru_map:
        if s.endswith(suffix) and len(s) > len(suffix):
            return chain(l, "te-form", s)

    stem = masu_stem(l)
    if s.endswith("ましょう") and len(s) > 4:
        return chain(l, stem, s)
    if s.endswith("ました") and len(s) > 3:
        return chain(l, stem, s)
    if s.endswith("ません") and len(s) > 3:
        return chain(l, stem, s)
    if s.endswith("ます") and len(s) > 2:
        return chain(l, stem, s)
    if s.endswith("なかった") and len(s) > 4:
        return out(f"{l} + なかった", f"{l} + なかった")
    if s.endswith("ない") and len(s) > 2:
        return out(f"{l} + ない", f"{l} + ない")
    if s.endswith("たかった") and len(s) > 4:
        return chain(l, stem, s)
    if s.endswith("たくない") and len(s) > 4:
        return chain(l, stem, s)
    if s.endswith("たい") and len(s) > 2:
        return chain(l, stem, s)
    if s.endswith(("れる", "られる")) and len(s) > 2:
        return out(f"{l} + れる/られる", f"{l} + れる/られる")
    if "使役" in (ctype or "") or s.endswith(("せる", "させる")):
        return out(f"{l} + せる/させる", f"{l} + せる/させる")
    if s.endswith("くない") and len(s) > 3 and pos1 == "形容詞":
        return out(f"{l[:-1] if l.endswith('い') else l} + くない", f"{l[:-1] if l.endswith('い') else l} + くない")
    if s.endswith("かった") and len(s) > 3 and pos1 == "形容詞":
        return out(f"{l[:-1] if l.endswith('い') else l} + かった", f"{l[:-1] if l.endswith('い') else l} + かった")
    if s.endswith("くて") and len(s) > 2 and pos1 == "形容詞":
        return out(f"{l[:-1] if l.endswith('い') else l} + くて", f"{l[:-1] if l.endswith('い') else l} + くて")
    if s.endswith(("て", "で")) and len(s) > 1:
        return out(f"{l} -> te-form", f"{l} -> te-form")
    if s.endswith(("た", "だ")) and len(s) > 1:
        return out(f"{l} -> past form", f"{l} -> past form")
    if s.endswith(("よう", "おう")) and len(s) > 2:
        return out(f"{l} -> volitional", f"{l} -> volitional")
    return out(f"{l} -> {s}", f"{l} -> {s}")

@lru_cache(maxsize=8192)
def analyze_japanese_word(surface: str, reading_hint: str = "", lemma_hint: str = ""):
    surface = (surface or "").strip()
    reading_hint = normalize_katakana_to_hiragana((reading_hint or "").strip())
    lemma_hint = (lemma_hint or "").strip()
    info = {
        "surface": surface,
        "lemma": surface,
        "reading_surface": reading_hint,
        "reading_lemma": "",
        "pos1": "",
        "pos2": "",
        "ctype": "",
        "cform": "",
        "form_bg": "форма в текста",
        "form_en": "form in context",
        "formula_bg": "",
        "formula_en": "",
    }
    sudachi_tokens = sudachi_tokenize(surface)
    if sudachi_tokens:
        core = choose_sudachi_core_token(sudachi_tokens)
        core_feat = sudachi_feature(core) if core is not None else {}
        info["lemma"] = build_sudachi_compound_lemma(surface, sudachi_tokens) or lemma_hint or surface
        info["reading_surface"] = "".join(sudachi_reading(t) for t in sudachi_tokens).strip() or reading_hint
        info["pos1"] = core_feat.get("pos1", "")
        info["pos2"] = core_feat.get("pos2", "")
        info["ctype"] = core_feat.get("ctype", "")
        info["cform"] = core_feat.get("cform", "")
    tagger = get_mecab_tagger()
    if not sudachi_tokens and tagger is not None and surface:
        try:
            tokens = list(tagger(surface))
            if tokens:
                if len(tokens) == 1:
                    tok = tokens[0]
                    feat = token_feature(tok)
                    raw_lemma = token_lemma(tok).strip() or lemma_hint or surface
                    lemma = to_dictionary_form(raw_lemma) or to_dictionary_form(surface) or raw_lemma or surface
                    reading_surface = normalize_katakana_to_hiragana(feature_reading(tok).strip() or reading_hint)
                    info["lemma"] = lemma
                    info["reading_surface"] = reading_surface
                    info["reading_lemma"] = normalize_katakana_to_hiragana(reading_surface if lemma == surface else (lookup_dictionary_entry(lemma, reading=reading_surface) or {}).get("reading",""))
                    info["pos1"] = safe_feature_value(feat, "pos1")
                    info["pos2"] = safe_feature_value(feat, "pos2")
                    info["ctype"] = safe_feature_value(feat, "cType", "ctype", "conjType", "inflectionType")
                    info["cform"] = safe_feature_value(feat, "cForm", "cform", "conjForm", "inflectionForm")
                else:
                    token_lemmas = [to_dictionary_form(token_lemma(t).strip() or token_surface(t).strip()) for t in tokens]
                    derived = to_dictionary_form(surface)
                    non_aux_lemmas = [x for x in token_lemmas if x not in {"て", "で", "いる", "居る", "ます", "です", "ん", "ない"}]
                    if derived and derived != surface:
                        info["lemma"] = derived
                    elif non_aux_lemmas:
                        info["lemma"] = non_aux_lemmas[0]
                    elif lemma_hint:
                        info["lemma"] = lemma_hint
                    else:
                        info["lemma"] = "".join(token_lemmas).strip() or surface
                    info["reading_surface"] = normalize_katakana_to_hiragana("".join(feature_reading(t).strip() for t in tokens) or reading_hint)
        except Exception:
            pass
    info["lemma"] = to_dictionary_form(info["lemma"]) or to_dictionary_form(surface) or lemma_hint or surface
    if not info["reading_surface"]:
        info["reading_surface"] = reading_hint
    if not info["reading_lemma"]:
        if info["lemma"] == info["surface"]:
            info["reading_lemma"] = info["reading_surface"]
        else:
            info["reading_lemma"] = get_reading_for_word(info["lemma"], fallback="")
    form_labels = classify_japanese_form(info["surface"], info["lemma"], info["pos1"], info["pos2"], info["ctype"], info["cform"])
    info["form_bg"] = form_labels["bg"]
    info["form_en"] = form_labels["en"]
    formulas = build_japanese_form_formula(info["surface"], info["lemma"], info["pos1"], info["pos2"], info["ctype"], info["cform"])
    info["formula_bg"] = formulas["bg"]
    info["formula_en"] = formulas["en"]
    return info

@lru_cache(maxsize=16384)
def build_lookup_candidates(surface: str, reading: str = "", lemma: str = ""):
    surface = (surface or "").strip()
    reading = normalize_katakana_to_hiragana((reading or "").strip())
    lemma = (lemma or "").strip()
    candidates = [surface, lemma, lemmatize_japanese(surface), to_dictionary_form(surface), reading]
    return tuple(unique_keep_order(candidates))


def analysis_category_labels(pos1: str, item_type: str = ""):
    item_type = (item_type or "").strip().lower()
    if item_type == "particle":
        item_type = "grammar"
    if item_type == "grammar":
        return ("граматична конструкция", "grammar pattern")
    if item_type == "compound":
        return ("съчетание", "compound")
    if item_type == "noun" or pos1 == "名詞":
        return ("съществително", "noun")
    if item_type == "verb" or pos1 == "動詞":
        return ("глагол", "verb")
    if item_type == "adjective" or pos1 == "形容詞":
        return ("прилагателно", "adjective")
    if pos1 == "副詞":
        return ("наречие", "adverb")
    return ("елемент", "text item")


def enrich_popup_item(item):
    item = dict(item or {})
    surface = (item.get("surface") or item.get("word") or "").strip()
    if not surface:
        return item
    reading = normalize_katakana_to_hiragana((item.get("reading") or "").strip())
    lemma = (item.get("lemma") or item.get("word") or surface).strip()
    analysis = analyze_japanese_word(surface, reading_hint=reading, lemma_hint=lemma)
    item_type = (item.get("item_type") or "").strip().lower()
    if not item_type:
        pos1 = (analysis.get("pos1") or "").strip()
        if pos1 == "動詞":
            item_type = "verb"
        elif pos1 == "形容詞":
            item_type = "adjective"
        elif pos1 == "名詞":
            item_type = "noun"
        else:
            item_type = "compound" if len(surface) > 1 else ""
    category_bg, category_en = analysis_category_labels((analysis.get("pos1") or "").strip(), item_type=item_type)
    item["surface"] = surface
    item["lemma"] = lemma or (analysis.get("lemma") or surface)
    item["reading"] = reading or (analysis.get("reading_surface") or "")
    item["item_type"] = item_type
    item["translation_bg"] = (item.get("translation_bg") or item.get("meaning_bg") or "").strip()
    item["translation_en"] = (item.get("translation_en") or item.get("meaning_en") or "").strip()
    item["meaning_bg"] = (item.get("meaning_bg") or item["translation_bg"] or "").strip()
    item["meaning_en"] = (item.get("meaning_en") or item["translation_en"] or "").strip()
    item["category_bg"] = (item.get("category_bg") or category_bg).strip()
    item["category_en"] = (item.get("category_en") or category_en).strip()
    if item_type != "grammar":
        item["formation_bg"] = (item.get("formation_bg") or analysis.get("form_bg") or "").strip()
        item["formation_en"] = (item.get("formation_en") or analysis.get("form_en") or "").strip()
        item["formula_bg"] = (item.get("formula_bg") or analysis.get("formula_bg") or "").strip()
        item["formula_en"] = (item.get("formula_en") or analysis.get("formula_en") or "").strip()
    else:
        item["formation_bg"] = (item.get("formation_bg") or "").strip()
        item["formation_en"] = (item.get("formation_en") or "").strip()
        item["formula_bg"] = (item.get("formula_bg") or "").strip()
        item["formula_en"] = (item.get("formula_en") or "").strip()
    item["usage_bg"] = (item.get("usage_bg") or "").strip()
    item["usage_en"] = (item.get("usage_en") or "").strip()
    return item

def register_vocab_item(vocab_lookup, item, extra_keys=None):
    extra_keys = extra_keys or []
    item = enrich_popup_item(item)
    word = (item.get("word") or item.get("surface") or "").strip()
    reading = normalize_katakana_to_hiragana((item.get("reading") or "").strip())
    lemma = (item.get("lemma") or word).strip()
    keys = unique_keep_order([word, reading, lemma] + list(extra_keys))
    for key in keys:
        if not key:
            continue
        existing = vocab_lookup.get(key)
        if existing is None:
            vocab_lookup[key] = item
            continue
        existing_score = sum(1 for field in ("translation_bg", "translation_en", "category_bg", "formation_bg", "formula_bg", "usage_bg") if (existing.get(field) or "").strip())
        new_score = sum(1 for field in ("translation_bg", "translation_en", "category_bg", "formation_bg", "formula_bg", "usage_bg") if (item.get(field) or "").strip())
        if new_score >= existing_score:
            vocab_lookup[key] = item
def is_target_pos(token) -> bool:
    feat = token_feature(token)
    pos1 = getattr(feat, "pos1", "") if feat is not None else ""
    return pos1 in {"動詞", "形容詞"} or "動詞" in str(feat) or "形容詞" in str(feat)
@lru_cache(maxsize=8192)
def lemmatize_japanese(word: str) -> str:
    w = (word or "").strip()
    if not w:
        return w
    sudachi_tokens = sudachi_tokenize(w)
    if sudachi_tokens:
        return build_sudachi_compound_lemma(w, sudachi_tokens)
    tagger = get_mecab_tagger()
    if tagger is None:
        return to_dictionary_form(w)
    try:
        tokens = list(tagger(w))
        if len(tokens) == 1 and is_target_pos(tokens[0]):
            lemma = token_lemma(tokens[0])
            if lemma and lemma not in {"*", w}:
                return lemma
    except Exception:
        pass
    return to_dictionary_form(w)
def extract_following_okurigana(ruby_tag):
    sibling = ruby_tag.next_sibling
    while sibling is not None:
        txt = ""
        if isinstance(sibling, str):
            txt = sibling
        elif hasattr(sibling, "get_text"):
            break
        txt = (txt or "").lstrip(" 　\n\t")
        if not txt:
            sibling = sibling.next_sibling
            continue
        m = re.match(r"^([ぁ-んー]{1,8})", txt)
        if m:
            return m.group(1)
        return ""
    return ""
@lru_cache(maxsize=8192)
def to_dictionary_form(word: str) -> str:
    w = (word or "").strip()
    if not w:
        return w

    def ba_base_to_dictionary(form: str) -> str:
        form = (form or "").strip()
        if not form:
            return form
        if form.endswith("すれば"):
            return form[:-3] + "する"
        if form.endswith("くれば"):
            return form[:-3] + "くる"
        if form.endswith("来れば"):
            return form[:-3] + "来る"
        if form.endswith("れば"):
            stem = form[:-2]
            if not stem:
                return form
            mapped = GODAN_E_TO_U.get(stem[-1])
            return stem[:-1] + mapped if mapped else stem + "る"
        if form.endswith("ば"):
            stem = form[:-1]
            if not stem:
                return form
            mapped = GODAN_E_TO_U.get(stem[-1])
            return stem[:-1] + mapped if mapped else stem + "る"
        return form

    for suffix in ["ばよかったです", "ばよかった", "ればよかったです", "ればよかった"]:
        if w.endswith(suffix) and len(w) > len(suffix):
            prefix = w[:-len("よかったです")] if suffix.endswith("よかったです") else w[:-len("よかった")]
            return ba_base_to_dictionary(prefix)

    def te_base_to_dictionary(stem: str) -> str:
        stem = (stem or "").strip()
        if not stem:
            return stem
        if stem.endswith("っ"):
            return stem[:-1] + "る"
        if stem.endswith("ん"):
            return stem[:-1] + "む"
        if stem.endswith("し"):
            return stem[:-1] + "す"
        if stem.endswith("い"):
            return stem[:-1] + "く"
        if stem.endswith("ち"):
            return stem[:-1] + "つ"
        if stem.endswith("り"):
            return stem[:-1] + "る"
        if stem.endswith("び"):
            return stem[:-1] + "ぶ"
        if stem.endswith("み"):
            return stem[:-1] + "む"
        if stem.endswith("ぎ"):
            return stem[:-1] + "ぐ"
        return stem + "る"

    te_iru_suffixes = [
        "ていませんでした", "でいませんでした",
        "ていました", "でいました",
        "ていません", "でいません",
        "ていない", "でいない",
        "ています", "でいます",
        "ていた", "でいた",
        "ている", "でいる",
    ]
    for suffix in te_iru_suffixes:
        if w.endswith(suffix) and len(w) > len(suffix):
            return te_base_to_dictionary(w[:-len(suffix)])

    for suffix in ["していました", "しています", "しました", "します"]:
        if w.endswith(suffix):
            return w[:-len(suffix)] + "する"
    if w.endswith("して") and not w.endswith("まして"):
        return w[:-2] + "する"
    if w.endswith("した") and not w.endswith("ました"):
        return w[:-2] + "する"
    for suffix in ["きました", "きます", "きて", "きた", "こない", "こなかった"]:
        if w.endswith(suffix):
            return w[:-len(suffix)] + "くる"
    for suffix in ["ました", "ます"]:
        if w.endswith(suffix):
            stem = w[:-len(suffix)]
            if not stem:
                return w
            mapped = GODAN_I_TO_U.get(stem[-1])
            return stem[:-1] + mapped if mapped else stem + "る"
    if w.endswith("ない") and len(w) > 2:
        stem = w[:-2]
        mapped = GODAN_A_TO_U.get(stem[-1]) if stem else None
        return stem[:-1] + mapped if mapped else stem + "る"
    for src, dst in [("いて", "く"), ("いで", "ぐ"), ("して", "す"), ("した", "す"), ("いた", "く"), ("いだ", "ぐ")]:
        if w.endswith(src) and len(w) > len(src):
            return w[:-len(src)] + dst
    for src, dst in [("かった", "い"), ("くて", "い"), ("くない", "い")]:
        if w.endswith(src) and len(w) > len(src):
            return w[:-len(src)] + dst
    return w
def is_person_name_span(tokens_slice) -> bool:
    if not tokens_slice:
        return False
    pos1s = []
    pos2s = []
    surfaces = []
    for t in tokens_slice:
        feat = token_feature(t)
        pos1s.append(getattr(feat, "pos1", "") if feat is not None else "")
        pos2s.append(getattr(feat, "pos2", "") if feat is not None else "")
        surfaces.append(token_surface(t).strip())
    if any(p1 != "名詞" for p1 in pos1s):
        return False
    joined = "".join(surfaces)
    if joined.endswith(("さん", "君", "くん", "ちゃん", "氏")):
        return True
    markers = ("人名", "姓", "名")
    return any(any(m in (p2 or "") for m in markers) for p2 in pos2s)

def is_matchable_token_span(tokens_slice) -> bool:
    if not tokens_slice:
        return False
    if len(tokens_slice) == 1:
        return True
    pos1s = []
    surfaces = []
    for t in tokens_slice:
        feat = token_feature(t)
        pos1s.append(getattr(feat, "pos1", "") if feat is not None else "")
        surfaces.append(token_surface(t).strip())

    if any(p in {"記号", "補助記号"} for p in pos1s):
        return False

    # Reject phrases carrying particles such as で / を / が / の / など
    if any(p == "助詞" for p in pos1s):
        return False

    if all(p == "名詞" for p in pos1s):
        return True

    first = pos1s[0]
    if first in {"動詞", "形容詞"}:
        allowed_tail = {"助動詞", "動詞", "形容詞", "接尾辞", "接尾", "非自立"}
        return all((p in allowed_tail or p == "") for p in pos1s[1:])

    return False

def should_keep_token_for_vocab(token) -> bool:
    surface = token_surface(token).strip()
    if not surface:
        return False
    if len(surface) == 1 and re.fullmatch(r"[ぁ-んァ-ンー]", surface):
        return False
    feat = token_feature(token)
    pos1 = getattr(feat, "pos1", "") if feat is not None else ""
    pos2 = getattr(feat, "pos2", "") if feat is not None else ""
    if pos1 in {"名詞", "動詞", "形容詞", "副詞"}:
        if pos1 == "名詞" and pos2 in {"代名詞", "数詞", "非自立"}:
            return False
        return True
    return False

def is_suspicious_vocab_word(word: str) -> bool:
    w = (word or "").strip()
    if not w:
        return True
    if len(w) < 2:
        return True
    if re.match(r"^[ぁ-んー]+[ァ-ン一-龯]", w):
        return True
    if re.search(r"[<>{}=]", w):
        return True
    return False


def ruby_base_text(ruby_tag) -> str:
    text = ""
    for child in ruby_tag.contents:
        name = getattr(child, "name", None)
        if name in {"rt", "rp"}:
            continue
        text += child.get_text("", strip=True) if hasattr(child, "get_text") else str(child)
    return text.strip()


def make_dict_span(soup, item, inner_html: str, analysis=None):
    span = soup.new_tag("span")
    span["class"] = "dict-word"
    item = enrich_popup_item(item)
    surface = (item.get("surface") or item.get("word") or "").strip()
    lemma = (item.get("lemma") or item.get("word") or surface).strip()
    reading = normalize_katakana_to_hiragana((item.get("reading") or "").strip())
    span["data-surface"] = surface
    span["data-lemma"] = lemma
    span["data-reading"] = reading
    span["data-item-type"] = (item.get("item_type") or "").strip()
    span["data-category-bg"] = (item.get("category_bg") or "").strip()
    span["data-category-en"] = (item.get("category_en") or "").strip()
    span["data-translation-bg"] = (item.get("translation_bg") or "").strip()
    span["data-translation-en"] = (item.get("translation_en") or "").strip()
    span["data-meaning-bg"] = (item.get("meaning_bg") or "").strip()
    span["data-meaning-en"] = (item.get("meaning_en") or "").strip()
    span["data-formation-bg"] = (item.get("formation_bg") or "").strip()
    span["data-formation-en"] = (item.get("formation_en") or "").strip()
    span["data-formula-bg"] = (item.get("formula_bg") or "").strip()
    span["data-formula-en"] = (item.get("formula_en") or "").strip()
    span["data-usage-bg"] = (item.get("usage_bg") or "").strip()
    span["data-usage-en"] = (item.get("usage_en") or "").strip()

    if "<" not in inner_html and ">" not in inner_html:
        span.string = inner_html
    else:
        frag = BeautifulSoup(inner_html, "html.parser")
        for node in list(frag.contents):
            span.append(node)
    return span

def extract_vocab_from_blocks(blocks):
    vocab_map = {}
    for block in blocks:
        soup = BeautifulSoup(block["html"], "html.parser")
        for ruby in soup.find_all("ruby"):
            rb_text = ""
            rt_text = ""
            for child in ruby.contents:
                name = getattr(child, "name", None)
                if name == "rt":
                    rt_text += child.get_text("", strip=True)
                elif name == "rp":
                    continue
                else:
                    rb_text += child.get_text("", strip=True) if hasattr(child, "get_text") else str(child).strip()
            rb_text = rb_text.strip()
            rt_text = rt_text.strip()
            if not rb_text or not re.search(r"[一-龯]", rb_text):
                continue
            okurigana = extract_following_okurigana(ruby)
            word = rb_text
            reading = rt_text
            if okurigana and okurigana.startswith(PARTICLE_PREFIXES):
                okurigana = ""
            if okurigana:
                surface_word = rb_text + okurigana
                surface_reading = (rt_text + okurigana).strip()
                word = lemmatize_japanese(surface_word)
                reading = to_dictionary_form(surface_reading)
            if not is_suspicious_vocab_word(word) and word not in vocab_map:
                vocab_map[word] = reading
    tagger = get_mecab_tagger()
    if tagger is not None:
        for block in blocks:
            text = (block.get("text") or "").strip()
            if not text:
                continue
            try:
                tokens = list(tagger(text))
            except Exception:
                continue
            for token in tokens:
                if not should_keep_token_for_vocab(token):
                    continue
                surface = token_surface(token).strip()
                lemma = token_lemma(token).strip() or surface
                reading = normalize_katakana_to_hiragana(feature_reading(token).strip())
                word = lemma if re.search(r"[一-龯ぁ-んァ-ン]", lemma) else surface
                if not word or is_suspicious_vocab_word(word):
                    continue
                if word not in vocab_map:
                    vocab_map[word] = reading
            for compound in merge_compound_nouns(tokens):
                word = "".join(x[0] for x in compound).strip()
                reading = "".join(x[1] for x in compound).strip()
                if not is_suspicious_vocab_word(word) and word not in vocab_map:
                    vocab_map[word] = reading
    words = list(vocab_map.keys())
    meaning_bg_map = translate_texts(words, dest="bg")
    meaning_en_map = translate_texts(words, dest="en")

    vocab = []
    for word, reading in vocab_map.items():
        meaning_bg = (meaning_bg_map.get(word) or "").strip()
        meaning_en = (meaning_en_map.get(word) or "").strip()
        vocab.append({"word": word, "reading": reading, "meaning_bg": meaning_bg, "meaning_en": meaning_en, "meaning": meaning_bg})
    vocab.sort(key=lambda x: (-len(x["word"]), x["word"]))
    return vocab[:80]


def build_vocab_lookup(vocab_items):
    vocab_lookup = {}
    for item in vocab_items or []:
        word = (item.get("word") or "").strip()
        reading = normalize_katakana_to_hiragana((item.get("reading") or "").strip())
        if word and not is_suspicious_vocab_word(word):
            register_vocab_item(vocab_lookup, item, extra_keys=build_lookup_candidates(word, reading=reading, lemma=word))
    return vocab_lookup


def build_analysis_lookup(items):
    def richness(item):
        if not isinstance(item, dict):
            return -1
        score = 0
        item_type = (item.get("item_type") or "").strip().lower()
        if item_type == "grammar":
            score += 30
        if "・" in (item.get("surface") or ""):
            score += 20
        if (item.get("formation_en") or "").strip() == "katakana phrase":
            score += 20
        for key in (
            "category_bg",
            "translation_bg",
            "translation_en",
            "formation_bg",
            "formula_bg",
            "usage_bg",
        ):
            if (item.get(key) or "").strip():
                score += 1
        score += min(6, len((item.get("surface") or "").strip()))
        return score
    lookup = {}
    for item in items or []:
        item = enrich_popup_item(item)
        surface = (item.get("surface") or "").strip()
        if not surface:
            continue
        keys = build_lookup_candidates(surface, reading=item.get("reading", ""), lemma=item.get("lemma", ""))
        for key in keys:
            if not key:
                continue
            existing = lookup.get(key)
            if existing is None or richness(item) >= richness(existing):
                lookup[key] = item
    return lookup


def build_baseline_analysis_items_from_blocks(blocks):
    items = []
    seen = set()
    for block in blocks or []:
        soup = BeautifulSoup(block.get("html", ""), "html.parser")
        for ruby in soup.find_all("ruby"):
            base = ruby_base_text(ruby)
            reading = normalize_katakana_to_hiragana("".join(rt.get_text("", strip=True) for rt in ruby.find_all("rt")).strip())
            okurigana = extract_following_okurigana(ruby)
            surface = (base + okurigana).strip() if okurigana else (base or "").strip()
            if not surface or not contains_japanese(surface):
                continue
            key = normalize_for_compare(surface)
            if key in seen:
                continue
            seen.add(key)
            meaning_bg = translate_text(surface, dest="bg") or ""
            meaning_en = translate_text(surface, dest="en") or ""
            items.append(
                {
                    "surface": surface,
                    "lemma": surface,
                    "reading": reading,
                    "item_type": "compound",
                    "category_bg": "елемент",
                    "category_en": "text item",
                    "translation_bg": meaning_bg,
                    "translation_en": meaning_en,
                    "meaning_bg": meaning_bg,
                    "meaning_en": meaning_en,
                    "formation_bg": "",
                    "formation_en": "",
                    "formula_bg": "",
                    "formula_en": "",
                    "usage_bg": "",
                    "usage_en": "",
                }
            )
    return items


LOCAL_GRAMMAR_PATTERNS = [
    ("kamoshirenai", re.compile(r"(?:^|(?<=[をがはにでともへの、。！？]))([ぁ-んァ-ン一-龯]{1,16}かもしれ(?:ない|ません))")),
    ("koto_ni_suru", re.compile(r"(?:^|(?<=[をがはにでともへの、。！？]))([ぁ-んァ-ン一-龯]{1,16}ことに(?:する|した|して|します|しました|したい|しよう))")),
    ("koto_ni_naru", re.compile(r"(?:^|(?<=[をがはにでともへの、。！？]))([ぁ-んァ-ン一-龯]{1,16}ことに(?:なる|なった|なって|なります|なりました))")),
    ("you_ni_suru", re.compile(r"(?:^|(?<=[をがはにでともへの、。！？]))([ぁ-んァ-ン一-龯]{1,20}ように(?:する|した|して|します|しました|したい))")),
    ("you_ni_naru", re.compile(r"(?:^|(?<=[をがはにでともへの、。！？]))([ぁ-んァ-ン一-龯]{1,20}ように(?:なる|なった|なって|なります|なりました))")),
    ("souda", re.compile(r"(?:^|(?<=[をがはにでともへの、。！？]))([ぁ-んァ-ン一-龯]{1,16}そう(?:だ|です))")),
    ("nikui", re.compile(r"(?:^|(?<=[をがはにでともへの、。！？]))([ぁ-んァ-ン一-龯]{1,16}にくい(?:です|くて|かった)?)")),
    ("yasui", re.compile(r"(?:^|(?<=[をがはにでともへの、。！？]))([ぁ-んァ-ン一-龯]{1,16}やすい(?:です|くて|かった)?)")),
]


def build_local_analysis_items_from_blocks(blocks):
    items = []
    seen = set()
    tagger = get_mecab_tagger()

    def add_item(item):
        surface = (item.get("surface") or "").strip()
        if not surface:
            return
        key = (
            normalize_gemini_match_key(surface),
            normalize_gemini_match_key(item.get("lemma") or surface),
            normalize_gemini_match_key(item.get("item_type") or ""),
        )
        if key in seen:
            return
        seen.add(key)
        items.append(item)

    for block in blocks or []:
        text = (block.get("text") or "").strip()
        if not text:
            continue

        for match in re.finditer(r"[ァ-ヶー]+(?:・[ァ-ヶー]+)+", text):
            surface = match.group(0).strip()
            if not surface:
                continue
            meaning_bg = translate_text(surface, dest="bg") or ""
            meaning_en = translate_text(surface, dest="en") or ""
            add_item(
                {
                    "surface": surface,
                    "lemma": surface,
                    "reading": normalize_katakana_to_hiragana(surface),
                    "item_type": "compound",
                    "category_bg": "съчетание",
                    "category_en": "compound",
                    "translation_bg": meaning_bg,
                    "translation_en": meaning_en,
                    "meaning_bg": meaning_bg,
                    "meaning_en": meaning_en,
                    "formation_bg": "катакана фраза",
                    "formation_en": "katakana phrase",
                    "formula_bg": surface,
                    "formula_en": surface,
                    "usage_bg": "",
                    "usage_en": "",
                }
            )

        for pattern_id, pattern in LOCAL_GRAMMAR_PATTERNS:
            rule = GRAMMAR_RULES_BY_ID.get(pattern_id)
            if rule is None:
                continue
            for match in pattern.finditer(text):
                surface = match.group(0).strip()
                if not contains_japanese(surface):
                    continue
                add_item(
                    {
                        "surface": surface,
                        "lemma": rule["label"],
                        "reading": get_reading_for_word(surface, fallback=""),
                        "item_type": "grammar",
                        "category_bg": "граматична конструкция",
                        "category_en": "grammar pattern",
                        "translation_bg": rule["explanation_bg"],
                        "translation_en": rule.get("explanation_en") or translate_text(rule["explanation_bg"], dest="en") or "",
                        "meaning_bg": rule["explanation_bg"],
                        "meaning_en": rule.get("explanation_en") or "",
                        "formation_bg": "граматична конструкция",
                        "formation_en": "grammar pattern",
                        "formula_bg": rule["label"],
                        "formula_en": rule["label"],
                        "usage_bg": rule["explanation_bg"],
                        "usage_en": rule.get("explanation_en") or "",
                    }
                )

        if tagger is None:
            continue
        try:
            tokens = list(tagger(text))
        except Exception:
            continue

        for phrase in merge_katakana_phrases(tokens):
            surface = "".join(x[0] for x in phrase).strip()
            reading = "".join(x[1] for x in phrase).strip()
            if not surface or not contains_japanese(surface):
                continue
            meaning_bg = translate_text(surface, dest="bg") or ""
            meaning_en = translate_text(surface, dest="en") or ""
            add_item(
                {
                    "surface": surface,
                    "lemma": surface,
                    "reading": reading,
                    "item_type": "compound",
                    "category_bg": "съчетание",
                    "category_en": "compound",
                    "translation_bg": meaning_bg,
                    "translation_en": meaning_en,
                    "meaning_bg": meaning_bg,
                    "meaning_en": meaning_en,
                    "formation_bg": "катакана фраза",
                    "formation_en": "katakana phrase",
                    "formula_bg": surface,
                    "formula_en": surface,
                    "usage_bg": "",
                    "usage_en": "",
                }
            )

    return items


def fill_block_translations(blocks):
    texts = [(block.get("text") or "").strip() for block in blocks or []]
    bg_map = translate_texts(texts, dest="bg")
    en_map = translate_texts(texts, dest="en")
    for block in blocks or []:
        text = (block.get("text") or "").strip()
        block["translation_bg"] = bg_map.get(text, "")
        block["translation_en"] = en_map.get(text, "")
    return blocks


def prepare_article_render_data(article):
    if not article:
        return article
    title = (article.get("title") or "").strip()
    article["title_translation_bg"] = translate_text(title, dest="bg") if title else ""
    article["title_translation_en"] = translate_text(title, dest="en") if title else ""
    fill_block_translations(article.get("blocks") or [])
    analysis_items = list(article.get("analysis_items") or [])
    if not analysis_items:
        analysis_items.extend(build_baseline_analysis_items_from_blocks(article.get("blocks") or []))
        analysis_items.extend(build_local_analysis_items_from_blocks(article.get("blocks") or []))
        article["analysis_items"] = analysis_items
    vocab_lookup = build_analysis_lookup(analysis_items) if analysis_items else build_vocab_lookup(article.get("vocab") or [])
    for block in article.get("blocks") or []:
        block["wrapped_html"] = wrap_vocab_words_in_html(block.get("html", ""), vocab_lookup=vocab_lookup)
    return article


def split_sentences_for_gemini(text: str):
    return [s.strip() for s in re.split(r"(?<=[。！？?!])\s*", text or "") if s.strip()]


def article_text_for_gemini(article):
    texts = []
    for block in article.get("blocks") or []:
        text = (block.get("text") or "").strip()
        if text:
            texts.append(text)
    return "\n".join(texts).strip()


def extract_json_object(text: str):
    raw = (text or "").strip()
    if not raw:
        return None
    try:
        return json.loads(raw)
    except Exception:
        pass
    start = raw.find("{")
    end = raw.rfind("}")
    if start != -1 and end != -1 and end > start:
        try:
            return json.loads(raw[start:end + 1])
        except Exception:
            return None
    return None


def groq_chat_completion(prompt: str) -> str:
    if not GROQ_API_KEY:
        raise RuntimeError("Missing GROQ_API_KEY")
    last_error = None
    for attempt in range(6):
        response = None
        try:
            response = get_http_session().post(
                "https://api.groq.com/openai/v1/chat/completions",
                headers={
                    "Authorization": f"Bearer {GROQ_API_KEY}",
                    "Content-Type": "application/json",
                },
                json={
                    "model": GROQ_MODEL,
                    "messages": [
                        {"role": "system", "content": "Return only the requested content. Prefer strict JSON when asked."},
                        {"role": "user", "content": prompt},
                    ],
                    "temperature": 0.1,
                    "max_completion_tokens": 6000,
                },
                timeout=180,
            )
            response.raise_for_status()
            payload = response.json()
            choices = payload.get("choices") or []
            if not choices:
                return ""
            message = choices[0].get("message") or {}
            return (message.get("content") or "").strip()
        except Exception as e:
            last_error = e
            status = getattr(response, "status_code", None)
            if status == 429 and attempt < 5:
                time.sleep(12 * (attempt + 1))
                continue
            break
    raise last_error


def sanitize_gemini_analysis_item(item):
    if not isinstance(item, dict):
        return None
    surface = (item.get("surface") or "").strip()
    if not surface or not contains_japanese(surface):
        return None
    item_type = (item.get("item_type") or "").strip().lower()
    if item_type == "particle":
        item_type = "grammar"
    if item_type not in {"verb", "noun", "adjective", "compound", "grammar"}:
        return None
    lemma = (item.get("lemma") or item.get("dictionary_form") or "").strip() or surface
    reading = normalize_katakana_to_hiragana((item.get("reading") or "").strip())
    translation_bg = (item.get("translation_bg") or item.get("meaning_bg") or "").strip()
    translation_en = (item.get("translation_en") or item.get("meaning_en") or "").strip()
    category_bg_map = {
        "verb": "глагол",
        "noun": "съществително",
        "adjective": "прилагателно",
        "compound": "съчетание",
        "grammar": "граматична конструкция",
    }
    category_en_map = {
        "verb": "verb",
        "noun": "noun",
        "adjective": "adjective",
        "compound": "compound",
        "grammar": "grammar pattern",
    }
    return {
        "surface": surface,
        "lemma": lemma,
        "reading": reading,
        "item_type": item_type,
        "category_bg": (item.get("category_bg") or "").strip() or category_bg_map[item_type],
        "category_en": (item.get("category_en") or "").strip() or category_en_map[item_type],
        "translation_bg": translation_bg,
        "translation_en": translation_en,
        "meaning_bg": (item.get("meaning_bg") or translation_bg).strip(),
        "meaning_en": (item.get("meaning_en") or translation_en).strip(),
        "formation_bg": (item.get("formation_bg") or "").strip(),
        "formation_en": (item.get("formation_en") or "").strip(),
        "formula_bg": (item.get("formula_bg") or "").strip(),
        "formula_en": (item.get("formula_en") or "").strip(),
        "usage_bg": (item.get("usage_bg") or "").strip(),
        "usage_en": (item.get("usage_en") or "").strip(),
    }


def sanitize_gemini_grammar_item(item):
    if not isinstance(item, dict):
        return None
    label = (item.get("label") or "").strip()
    explanation_bg = (item.get("explanation_bg") or "").strip()
    explanation_en = (item.get("explanation_en") or "").strip()
    if not label or not explanation_bg:
        return None
    return {
        "label": label,
        "explanation_bg": explanation_bg,
        "explanation_en": explanation_en or translate_text(explanation_bg, dest="en") or explanation_bg,
    }


def normalize_gemini_match_key(value: str) -> str:
    return re.sub(r"\s+", "", (value or "").strip()).lower()


def chunk_sentences_for_gemini(sentences, max_chars: int = 220, max_sentences: int = 2):
    chunks = []
    current = []
    current_len = 0
    for sentence in sentences or []:
        s = (sentence or "").strip()
        if not s:
            continue
        projected = current_len + len(s) + (1 if current else 0)
        if current and (len(current) >= max_sentences or projected > max_chars):
            chunks.append(current)
            current = []
            current_len = 0
        current.append(s)
        current_len += len(s) + (1 if current_len else 0)
    if current:
        chunks.append(current)
    return chunks


def find_best_gemini_item(gemini_items, surface: str = "", reading: str = "", lemma: str = ""):
    if not gemini_items:
        return None
    s = normalize_gemini_match_key(surface)
    r = normalize_gemini_match_key(reading)
    l = normalize_gemini_match_key(lemma)
    for item in gemini_items:
        if normalize_gemini_match_key(item.get("surface")) == s and (not r or normalize_gemini_match_key(item.get("reading")) == r):
            return item
    for item in gemini_items:
        if normalize_gemini_match_key(item.get("surface")) == s:
            return item
    for item in gemini_items:
        if l and normalize_gemini_match_key(item.get("lemma")) == l:
            return item
    loose = []
    for item in gemini_items:
        item_surface = normalize_gemini_match_key(item.get("surface"))
        if item_surface and s and (item_surface in s or s in item_surface):
            loose.append(item)
    if loose:
        loose.sort(key=lambda item: abs(len(item.get("surface", "")) - len(surface or "")))
        return loose[0]
    return None


def analyze_article_block_with_groq(article_id: str, block_id: int, title: str, text: str):
    if not text:
        return []
    cache_payload = {
        "model": GROQ_MODEL,
        "task": "article_elements_groq_block_v1",
        "article_id": article_id,
        "block_id": block_id,
        "title": title,
        "text": text,
    }
    cache_key = hashlib.sha1(json.dumps(cache_payload, ensure_ascii=False, sort_keys=True).encode("utf-8")).hexdigest()
    cached = _GEMINI_CACHE.get(cache_key)
    if isinstance(cached, list):
        return [item for item in (sanitize_gemini_analysis_item(v) for v in cached) if item]

    prompt = (
        "Analyze this short Japanese NHK Easy paragraph and return strict JSON only.\n"
        "Be exhaustive rather than selective.\n"
        "Extract as many learner-relevant language elements as possible that actually appear in the text.\n"
        "Include nouns, katakana words, adjectives, conjugated verb forms, useful compounds, particles as grammar, auxiliary patterns, and grammar constructions.\n"
        "Use exact surface spans from the paragraph.\n"
        "Deduplicate only exact same encountered surface form within this paragraph.\n"
        "Cover the whole paragraph and do not stop after only a few examples.\n"
        "Return this JSON shape exactly:\n"
        "{\"items\":[{\"surface\":\"...\",\"lemma\":\"...\",\"reading\":\"...\","
        "\"item_type\":\"noun|adjective|verb|compound|grammar|particle\",\"translation_bg\":\"...\",\"translation_en\":\"...\","
        "\"meaning_bg\":\"...\",\"meaning_en\":\"...\",\"formation_bg\":\"...\",\"formation_en\":\"...\","
        "\"formula_bg\":\"...\",\"formula_en\":\"...\",\"usage_bg\":\"...\",\"usage_en\":\"...\"}]}\n"
        "Rules:\n"
        "- surface: exact form as written in the paragraph\n"
        "- lemma: dictionary/base form or canonical grammar pattern\n"
        "- reading: hiragana reading of the exact surface whenever possible; if uncertain, still provide the other fields\n"
        "- Include short grammar elements if they are genuinely useful to explain\n"
        "- Include katakana loanwords and named concepts if present\n"
        "- For adjectives and verbs not in dictionary form, explain formation and formula\n"
        "- For grammar items, explain meaning, usage, and compact formula\n"
        "- Do not invent anything not literally present in the paragraph\n"
        "- Aim for 15 to 50 items when possible\n"
        "- It is better to return many correct items than only a few polished ones\n"
        f"Article title: {title}\n"
        f"Paragraph text:\n{text}"
    )
    parsed = extract_json_object(groq_chat_completion(prompt))
    if not isinstance(parsed, dict):
        return []
    items = [item for item in (sanitize_gemini_analysis_item(v) for v in (parsed.get("items") or [])) if item]
    cache_gemini_result(cache_key, items)
    return items


def analyze_articles_with_groq(articles):
    for article in articles or []:
        article["analysis_items"] = []
    if not articles or not GROQ_API_KEY:
        return articles
    for index, article in enumerate((articles or [])[:4], start=1):
        title = (article.get("title") or "").strip()
        article_id = f"article_{index}"
        merged = {}
        baseline_items = build_baseline_analysis_items_from_blocks(article.get("blocks") or [])
        for item in baseline_items:
            key = (
                normalize_gemini_match_key(item.get("surface")),
                normalize_gemini_match_key(item.get("lemma")),
                normalize_gemini_match_key(item.get("item_type")),
            )
            merged[key] = item
        for block_id, block in enumerate((article.get("blocks") or []), start=1):
            text = (block.get("text") or "").strip()
            if not text:
                continue
            try:
                items = analyze_article_block_with_groq(article_id, block_id, title, text)
            except Exception as e:
                print(f"Groq article analysis failed for {article_id} block {block_id}: {e}")
                items = []
            for item in items:
                key = (
                    normalize_gemini_match_key(item.get("surface")),
                    normalize_gemini_match_key(item.get("lemma")),
                    normalize_gemini_match_key(item.get("item_type")),
                )
                existing = merged.get(key)
                if existing is None:
                    merged[key] = item
                    continue
                for field in (
                    "reading",
                    "translation_bg",
                    "translation_en",
                    "meaning_bg",
                    "meaning_en",
                    "formation_bg",
                    "formation_en",
                    "formula_bg",
                    "formula_en",
                    "usage_bg",
                    "usage_en",
                    "category_bg",
                    "category_en",
                ):
                    if not existing.get(field) and item.get(field):
                        existing[field] = item[field]
        try:
            article["analysis_items"] = list(merged.values())
        except Exception:
            article["analysis_items"] = baseline_items
        if index < min(4, len(articles or [])):
            # Groq rate limits aggressively on back-to-back long completions.
            time.sleep(5)
    return articles


def analyze_grammar_points_with_gemini(articles, existing_grammar_points=None):
    existing_grammar_points = existing_grammar_points or []
    if not articles or not GEMINI_API_KEY or genai is None:
        return []

    article_payload = []
    for index, article in enumerate(articles, start=1):
        text = article_text_for_gemini(article)
        if not text:
            continue
        article_payload.append(
            {
                "article_id": f"article_{index}",
                "title": (article.get("title") or "").strip(),
                "text": text,
            }
        )
    if not article_payload:
        return []

    existing_labels = [((g.get("label") or "").replace(" (AI)", "").strip()) for g in existing_grammar_points if (g.get("label") or "").strip()]
    cache_payload = {"model": GEMINI_MODEL, "task": "grammar_ai", "articles": article_payload, "existing": existing_labels}
    cache_key = hashlib.sha1(json.dumps(cache_payload, ensure_ascii=False, sort_keys=True).encode("utf-8")).hexdigest()
    cached = _GEMINI_CACHE.get(cache_key)
    if isinstance(cached, list):
        return [item for item in (sanitize_gemini_grammar_item(v) for v in cached) if item]

    prompt = (
        "Analyze the 4 Japanese NHK Easy articles below and identify additional grammar constructions or particles worth showing in a learner-facing "
        "\"Grammar in the texts\" summary.\n"
        "Return JSON only.\n"
        "Do not repeat items that are already covered by this existing list:\n"
        f"{json.dumps(existing_labels, ensure_ascii=False)}\n"
        "Return only a compact list of additional useful constructions actually present in the texts.\n"
        "Each item must have:\n"
        "- label: Japanese grammar form or particle pattern\n"
        "- explanation_bg: short Bulgarian explanation including how it is used and its meaning/translation\n"
        "- explanation_en: short English explanation including usage and meaning/translation\n"
        "Keep labels short. Prefer patterns like 〜として, 〜により, 〜わけではない, etc.\n"
        "Return this JSON shape exactly:\n"
        "{\"items\":[{\"label\":\"...\",\"explanation_bg\":\"...\",\"explanation_en\":\"...\"}]}\n"
        f"Articles:\n{json.dumps(article_payload, ensure_ascii=False, indent=2)}"
    )

    try:
        client = genai.Client(api_key=GEMINI_API_KEY)
        response = client.models.generate_content(
            model=GEMINI_MODEL,
            contents=prompt,
        )
        parsed = extract_json_object(getattr(response, "text", ""))
    except Exception as e:
        print(f"Gemini grammar analysis failed: {e}")
        return []

    if not isinstance(parsed, dict):
        print("Gemini grammar analysis returned invalid JSON.")
        return []

    items = [item for item in (sanitize_gemini_grammar_item(v) for v in (parsed.get("items") or [])) if item]
    if items:
        cache_gemini_result(cache_key, items)
    return items


def contains_digit(word: str) -> bool:
    return any(ch.isdigit() for ch in (word or ""))

def is_all_katakana(word: str) -> bool:
    w = (word or "").strip()
    return bool(w) and all(("ァ" <= ch <= "ヶ") or ch == "ー" for ch in w)

def canonicalize_vocab_item(word: str, reading: str = "", meaning_bg: str = "", meaning_en: str = ""):
    word = (word or "").strip()
    reading = normalize_katakana_to_hiragana((reading or "").strip())
    meaning_bg = (meaning_bg or "").strip()
    meaning_en = (meaning_en or "").strip()
    if not word:
        return None

    lemma = lemmatize_japanese(word) or to_dictionary_form(word) or word
    entry = lookup_dictionary_entry(lemma, reading=reading) or lookup_dictionary_entry(word, reading=reading)

    canonical_word = (entry.get("surface") if entry else "") or lemma or word
    canonical_word = canonical_word.strip()
    canonical_reading = normalize_katakana_to_hiragana(((entry.get("reading") if entry else "") or reading).strip())

    if not canonical_reading:
        lemma_entry = lookup_dictionary_entry(canonical_word, reading=reading)
        canonical_reading = normalize_katakana_to_hiragana(((lemma_entry or {}).get("reading","") or reading).strip())

    canonical_meaning_en = ((entry.get("gloss") if entry else "") or meaning_en).strip()
    canonical_meaning_bg = (translate_text(canonical_meaning_en, dest="bg") if canonical_meaning_en else "") or meaning_bg or canonical_meaning_en

    if not canonical_meaning_bg and meaning_bg:
        canonical_meaning_bg = meaning_bg
    if not canonical_meaning_en and meaning_en:
        canonical_meaning_en = meaning_en

    if not canonical_word:
        return None
    if contains_digit(canonical_word) or contains_digit(canonical_reading):
        return None
    if is_all_katakana(canonical_word):
        return None
    if is_suspicious_vocab_word(canonical_word) or is_single_kanji_word(canonical_word):
        return None
    if not re.search(r"[一-龯ぁ-ん]", canonical_word):
        return None
    if not canonical_meaning_bg and not canonical_meaning_en:
        return None

    return {
        "word": canonical_word,
        "reading": canonical_reading,
        "meaning_bg": canonical_meaning_bg or canonical_meaning_en,
        "meaning_en": canonical_meaning_en or canonical_meaning_bg,
    }

def normalize_vocab_group_key(word: str, reading: str = "") -> str:
    base = lemmatize_japanese((word or "").strip())
    entry = lookup_dictionary_entry(base, reading=reading) or lookup_dictionary_entry(word, reading=reading)
    if entry and (entry.get("surface") or "").strip():
        return (entry.get("surface") or "").strip()
    return base or (word or "").strip()

def is_single_kanji_word(word: str) -> bool:
    return bool(re.fullmatch(r"[一-龯]", (word or "").strip()))
def is_known_vocab_item(word: str, known_items):
    return word in known_items or f"v:{word}" in known_items
def is_valid_anki_vocab_item(item):
    word = (item.get("word") or "").strip()
    reading = (item.get("reading") or "").strip()
    meaning_bg = (item.get("meaning_bg") or item.get("meaning") or "").strip()
    meaning_en = (item.get("meaning_en") or "").strip()

    if not word or is_suspicious_vocab_word(word) or is_single_kanji_word(word):
        return None
    if contains_digit(word) or contains_digit(reading):
        return None
    if is_all_katakana(word):
        return None

    return canonicalize_vocab_item(word, reading=reading, meaning_bg=meaning_bg, meaning_en=meaning_en)

def build_vocab_anki_cards(articles, lang="bg"):
    cards = []
    grouped = {}

    for article in articles:
        for item in article.get("vocab", []):
            validated = is_valid_anki_vocab_item(item)
            if not validated:
                continue

            canonical = canonicalize_vocab_item(
                validated["word"],
                reading=validated.get("reading", ""),
                meaning_bg=validated.get("meaning_bg", ""),
                meaning_en=validated.get("meaning_en", ""),
            )
            if not canonical:
                continue

            word = canonical["word"]
            reading = canonical["reading"]
            meaning = canonical["meaning_bg"] if lang == "bg" else canonical["meaning_en"]
            group_key = normalize_vocab_group_key(word, reading=reading) or word

            if is_all_katakana(group_key) or is_all_katakana(word):
                continue
            if not re.search(r"[一-龯ぁ-ん]", group_key):
                continue

            existing = grouped.get(group_key)
            if existing is None:
                grouped[group_key] = {"word": group_key, "reading": reading, "meanings": [meaning] if meaning else []}
            else:
                if reading and not existing["reading"]:
                    existing["reading"] = reading
                if meaning and meaning not in existing["meanings"]:
                    existing["meanings"].append(meaning)

    for item in grouped.values():
        word = (item["word"] or "").strip()
        reading = normalize_katakana_to_hiragana((item["reading"] or "").strip())
        meaning = "; ".join(item["meanings"][:3]).strip()
        if not word or not meaning:
            continue
        if is_all_katakana(word):
            continue
        if not re.search(r"[一-龯ぁ-ん]", word):
            continue
        front = f"<ruby>{word}<rt>{reading}</rt></ruby>" if reading and reading != word else word
        cards.append((front, meaning))

    cards.sort(key=lambda x: x[0])
    return cards


def build_grammar_anki_cards(grammar_points, lang="bg"):
    cards = []
    seen_labels = set()

    for g in grammar_points or []:
        label = (g.get("label") or "").strip()
        explanation = (g.get("explanation_bg") if lang == "bg" else g.get("explanation_en") or "").strip()
        if not label or not explanation or label in seen_labels:
            continue
        seen_labels.add(label)
        cards.append((label, explanation))

    return cards


def build_grammar_points_from_analysis(articles):
    points = []
    seen = set()
    for article in articles or []:
        for item in article.get("analysis_items") or []:
            if item.get("item_type") != "grammar":
                continue
            label = (item.get("lemma") or item.get("surface") or "").strip()
            if not label:
                continue
            key = normalize_for_compare(label)
            if key in seen:
                continue
            seen.add(key)
            points.append(
                {
                    "label": label,
                    "explanation_bg": (item.get("usage_bg") or item.get("meaning_bg") or item.get("translation_bg") or "").strip(),
                    "explanation_en": (item.get("usage_en") or item.get("meaning_en") or item.get("translation_en") or "").strip(),
                }
            )
    return points


def format_analysis_anki_back(item, lang="bg"):
    category = (item.get("category_bg") if lang == "bg" else item.get("category_en") or "").strip()
    translation = (item.get("translation_bg") if lang == "bg" else item.get("translation_en") or "").strip()
    meaning = (item.get("meaning_bg") if lang == "bg" else item.get("meaning_en") or "").strip()
    formation = (item.get("formation_bg") if lang == "bg" else item.get("formation_en") or "").strip()
    formula = (item.get("formula_bg") if lang == "bg" else item.get("formula_en") or "").strip()
    usage = (item.get("usage_bg") if lang == "bg" else item.get("usage_en") or "").strip()
    lines = []
    if category:
        lines.append(f"<b>{'Тип' if lang == 'bg' else 'Type'}:</b> {html_lib.escape(category)}")
    if translation:
        lines.append(f"<b>{'Превод' if lang == 'bg' else 'Translation'}:</b> {html_lib.escape(translation)}")
    if meaning and meaning != translation:
        lines.append(f"<b>{'Значение' if lang == 'bg' else 'Meaning'}:</b> {html_lib.escape(meaning)}")
    if formation:
        lines.append(f"<b>{'Образуване' if lang == 'bg' else 'Formation'}:</b> {html_lib.escape(formation)}")
    if formula:
        lines.append(f"<b>{'Формула' if lang == 'bg' else 'Formula'}:</b> {html_lib.escape(formula)}")
    if usage:
        lines.append(f"<b>{'Употреба' if lang == 'bg' else 'Usage'}:</b> {html_lib.escape(usage)}")
    return "<br>".join(lines)


def build_analysis_anki_cards(articles, lang="bg"):
    cards = []
    seen = set()
    for article in articles or []:
        for item in article.get("analysis_items") or []:
            surface = (item.get("surface") or "").strip()
            lemma = (item.get("lemma") or surface).strip()
            reading = normalize_katakana_to_hiragana((item.get("reading") or "").strip())
            if not surface:
                continue
            back = format_analysis_anki_back(item, lang=lang)
            if not back:
                continue
            key = (
                normalize_for_compare(surface),
                normalize_for_compare(lemma),
                normalize_for_compare(item.get("item_type") or ""),
                lang,
            )
            if key in seen:
                continue
            seen.add(key)
            front = f"<ruby>{surface}<rt>{reading}</rt></ruby>" if reading and reading != surface else surface
            cards.append((front, back))
    cards.sort(key=lambda pair: pair[0])
    return cards
def load_seen_words(path):
    if not os.path.exists(path):
        return set()
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        return {str(x).strip() for x in data if str(x).strip()} if isinstance(data, list) else set()
    except Exception:
        return set()
def save_seen_words(path, words):
    with open(path, "w", encoding="utf-8") as f:
        json.dump(sorted({w.strip() for w in words if w and w.strip()}), f, ensure_ascii=False, indent=2)
def add_known_progress_to_articles(articles, known_words):
    known = set(known_words or [])
    for article in articles:
        vocab_words = []
        seen_in_article = set()
        for item in article.get("vocab", []):
            word = (item.get("word") or "").strip()
            if not word or is_single_kanji_word(word) or word in seen_in_article:
                continue
            seen_in_article.add(word)
            vocab_words.append(word)
        total = len(vocab_words)
        known_count = sum(1 for w in vocab_words if is_known_vocab_item(w, known))
        article["known_total"] = total
        article["known_count"] = known_count
        article["known_percent"] = int(round((known_count / total) * 100)) if total else 0
def save_anki_tsv(cards, path):
    with open(path, "w", encoding="utf-8") as f:
        for front, back in cards:
            f.write(f"{front}\t{back}\n")
def stable_int_id(seed: str, digits: int = 10) -> int:
    digest = hashlib.sha1(seed.encode("utf-8")).hexdigest()
    h = int(digest[:12], 16)
    mod = 10 ** digits
    return (h % mod) + (10 ** (digits - 1))
def build_anki_apkg(cards, apkg_path, deck_name="NHK Easy Vocabulary"):
    if genanki is None:
        print("genanki is not installed; skipping .apkg generation")
        return False

    model = genanki.Model(
        stable_int_id("nhk_easy_vocab_model_" + deck_name),
        "NHK Easy Card Model " + deck_name,
        fields=[{"name": "Front"}, {"name": "Back"}],
        templates=[{
            "name": "Card 1",
            "qfmt": "<div class='jp-word'>{{Front}}</div>",
            "afmt": "<div class='jp-word'>{{Front}}</div><hr id='answer'><div class='bg-meaning'>{{Back}}</div>",
        }],
        css=".card {font-family: Arial, sans-serif; font-size: 25px; text-align: center; color: black; background-color: white;}.jp-word {font-size: 31px;}.bg-meaning {font-size: 25px;}.jp-word ruby rt {font-size: 14px;}",
    )

    deck = genanki.Deck(stable_int_id("nhk_easy_vocab_deck_" + deck_name), deck_name)
    for front, back in cards:
        deck.add_note(genanki.Note(model=model, fields=[front, back], guid=genanki.guid_for(front, back)))

    genanki.Package(deck).write_to_file(apkg_path)
    return True
def split_japanese_sentences(text: str):
    t = (text or "").strip()
    if not t:
        return []
    return [p.strip() for p in re.split(r"(?<=[。！？])\s*", t) if p.strip()]
def _s(tokens, idx):
    return token_surface(tokens[idx]) if 0 <= idx < len(tokens) else ""
def _l(tokens, idx):
    return token_lemma(tokens[idx]) if 0 <= idx < len(tokens) else ""
def _seq(tokens, start, end):
    return [token_surface(t) for t in tokens[start:end]]
def detect_grammar_in_sentence(sentence: str):
    tagger = get_mecab_tagger()
    found = set()
    if tagger is None:
        return found
    try:
        tokens = list(tagger(sentence))
    except Exception:
        return found
    surfaces = [token_surface(t) for t in tokens]
    lemmas = [token_lemma(t) for t in tokens]
    for i in range(len(tokens)):
        s = surfaces[i]
        l = lemmas[i]
        if s in {"けど", "けれど", "けれども"}: found.add("kedo")
        if s == "しかし": found.add("shikashi")
        if s in {"ても", "でも"} or (s in {"て", "で"} and _s(tokens, i + 1) == "も"): found.add("temo")
        if s == "ながら": found.add("nagara")
        if s == "つつ": found.add("tsutsu")
        if s in {"間", "あいだ"}: found.add("aida_ni")
        if s == "うち" and _s(tokens, i + 1) == "に": found.add("uchi_ni")
        if s == "から": found.add("kara_reason")
        if s == "ので": found.add("node")
        if s == "それで": found.add("sorede")
        if s == "そして": found.add("soshite")
        if s == "より": found.add("yori")
        if s in {"方", "ほう"}:
            found.add("hou")
            if _s(tokens, i + 1) == "が" and _s(tokens, i + 2) in {"いい", "よい", "良い"}: found.add("hou_ga_ii")
        if s == "のに": found.add("noni")
        if s == "よう" and _s(tokens, i + 1) == "に": found.add("you_ni")
        if s == "ため" and (_s(tokens, i + 1) in {"", "に"}): found.add("tame_ni")
        if s == "せい" and _s(tokens, i + 1) == "で": found.add("sei_de")
        if s == "おかげ" and _s(tokens, i + 1) == "で": found.add("okage_de")
        if s == "らしい": found.add("rashii")
        if s == "っぽい": found.add("ppoi")
        if s == "だめ": found.add("dame")
        if s == "なら" and _s(tokens, i + 1) == "ない": found.add("naranai")
        if s == "いけ" and _s(tokens, i + 1) == "ない": found.add("ikenai")
        if s == "なけれ" and _s(tokens, i + 1) == "ば":
            if _s(tokens, i + 2) == "なら" and _s(tokens, i + 3) == "ない": found.add("nakereba_naranai")
            if _s(tokens, i + 2) == "いけ" and _s(tokens, i + 3) == "ない": found.add("nakereba_ikenai")
        if (s.endswith("ば") or s in {"ば", "れば"} or "ば" in s) and "よかっ" in "".join(surfaces[i + 1:i + 4]):
            found.add("ba_yokatta")
        if s == "なく" and _seq(tokens, i + 1, i + 5) == ["て", "は", "なら", "ない"]: found.add("nakutewa_naranai")
        if s == "こと":
            found.add("koto_nominalizer")
            if _s(tokens, i + 1) == "が" and _l(tokens, i + 2) in {"有る", "ある"}: found.add("koto_ga_aru")
            if _s(tokens, i + 1) == "に" and _l(tokens, i + 2) in {"成る", "なる"}: found.add("koto_ni_naru")
            if _s(tokens, i + 1) == "に" and _l(tokens, i + 2) in {"為る", "する"}: found.add("koto_ni_suru")
            if _s(tokens, i + 1) == "が" and (_l(tokens, i + 2) in {"出来る", "できる"} or _s(tokens, i + 2) in {"できる", "出来る"}): found.add("koto_ga_dekiru")
        if s == "よう" and _s(tokens, i + 1) == "に":
            found.add("you_ni")
            if _l(tokens, i + 2) in {"成る", "なる"}: found.add("you_ni_naru")
            if _l(tokens, i + 2) in {"為る", "する"}: found.add("you_ni_suru")
        if s == "そう" and (_s(tokens, i + 1) in {"だ", "です"} or i == len(tokens) - 1): found.add("souda")
        if s == "ため":
            found.add("tame_plain")
            if _s(tokens, i + 1) in {"", "に"}: found.add("tame_ni")
        if s in {"ところ", "所"}: found.add("tokoro")
        if s == "ばかり" and _s(tokens, i - 1) in {"た", "だ"}: found.add("tabakari")
        if s == "たり" and surfaces.count("たり") >= 2: found.add("tari_tari")
        if s == "だけ": found.add("dake")
        if s == "のみ": found.add("nomi")
        if s == "ばかり": found.add("bakari")
        if s == "しか" and "ない" in surfaces[i + 1:]: found.add("shika_nai")
        if s == "もう": found.add("mou")
        if s == "まだ": found.add("mada")
        if s == "また": found.add("mata")
        if (s in {"て", "で"} and _s(tokens, i + 1) in {"いい", "よい", "良い"}) or s in {"ていい", "でいい"}: found.add("te_ii")
        if s in {"ても", "でも"} and _s(tokens, i + 1) in {"いい", "よい", "良い"}: found.add("temo_ii")
        if s in {"て", "で"} and _s(tokens, i + 1) == "も" and _s(tokens, i + 2) in {"いい", "よい", "良い"}: found.add("temo_ii")
        if s in {"て", "で"} and _l(tokens, i + 1) in {"見る", "みる"}: found.add("te_miru")
        if s in {"て", "で"} and _s(tokens, i + 1) == "から": found.add("te_kara")
        if s == "っけ": found.add("kke")
        if s == "かな": found.add("kana")
        if s in {"かい", "だい"}: found.add("kai_dai")
        if s == "じゃ" and _s(tokens, i + 1) == "ない": found.add("janai")
        if "させ" in s or l in {"させる", "せる"}: found.add("causative_saseru")
        if s == "なく" and _s(tokens, i + 1) == "て": found.add("nakute")
        if s == "ない" and _s(tokens, i + 1) == "で": found.add("naide")
        if s in {"ず", "ずに"} or (s == "ず" and _s(tokens, i + 1) == "に"): found.add("zu")
        if s in {"て", "で"} and _l(tokens, i + 1) in {"仕舞う", "しまう"}: found.add("te_shimau")
        if s in {"て", "で"} and _l(tokens, i + 1) in {"置く", "おく"}: found.add("te_oku")
        if s == "だって": found.add("datte")
        if s == "わけ": found.add("wake")
        if s == "はず": found.add("hazu")
        if s == "べき":
            found.add("beki")
            if _s(tokens, i + 1) == "だっ" and _s(tokens, i + 2) == "た": found.add("beki_datta")
        if s == "べし": found.add("beshi")
        if s == "もの" and _s(tokens, i + 1) == "だ": found.add("mono_da")
        if s == "かも" and _s(tokens, i + 1) == "しれ" and (_s(tokens, i + 2) == "ない" or (_s(tokens, i + 2) == "ませ" and _s(tokens, i + 3) == "ん")): found.add("kamoshirenai")
        elif s == "かも": found.add("kamo")
        if s == "にくい" or l in {"にくい", "難い"}: found.add("nikui")
        if s == "やすい" or l in {"やすい", "易い"}: found.add("yasui")
        if s in {"前", "まえ"} and _s(tokens, i + 1) == "に": found.add("mae_ni")
        if s in {"後", "あと"}:
            found.add("ato_after")
            if _s(tokens, i + 1) == "で": found.add("ato_de")
        if s == "ながら" and _s(tokens, i + 1) == "も": found.add("nagara_mo")
        if s == "に":
            if (_s(tokens, i + 1) == "対し" and _s(tokens, i + 2) == "て") or _s(tokens, i + 1) == "対して": found.add("ni_taishite")
            if (_s(tokens, i + 1) == "つい" and _s(tokens, i + 2) == "て") or _s(tokens, i + 1) == "ついて": found.add("ni_tsuite")
            if (_l(tokens, i + 1) in {"依る", "よる"} or _s(tokens, i + 1) == "よる") and _s(tokens, i + 2) == "と": found.add("ni_yoru_to")
            if _s(tokens, i + 1) == "より": found.add("ni_yori")
            if (_s(tokens, i + 1) == "よっ" and _s(tokens, i + 2) == "て") or _s(tokens, i + 1) == "よって": found.add("ni_yotte")
            if (_s(tokens, i + 1) == "おい" and _s(tokens, i + 2) == "て") or _s(tokens, i + 1) == "おいて": found.add("ni_oite")
            if (_s(tokens, i + 1) == "向け" and _s(tokens, i + 2) == "て") or _s(tokens, i + 1) == "向けて": found.add("ni_mukete")
            if (_s(tokens, i + 1) == "合わせ" and _s(tokens, i + 2) == "て") or _s(tokens, i + 1) == "合わせて": found.add("ni_awasete")
            if _l(tokens, i + 1) in {"成る", "なる"}: found.add("ni_naru")
        if s == "と":
            if (_l(tokens, i + 1) in {"為る", "する"} or _s(tokens, i + 1) in {"し", "して"}) and _s(tokens, i + 2) in {"", "て"}: found.add("to_shite")
            if _s(tokens, i + 1) == "とも" and _s(tokens, i + 2) == "に": found.add("to_tomo_ni")
            if _l(tokens, i + 1) in {"成る", "なる"}: found.add("to_naru")
            if _s(tokens, i + 1) == "は" and (_l(tokens, i + 2) in {"限る", "かぎる"} or _s(tokens, i + 2) in {"限ら", "かぎら"}) and _s(tokens, i + 3) == "ない": found.add("towa_kagiranai")
            if (_l(tokens, i + 1) in {"為る", "する"} or _s(tokens, i + 1) == "し") and _s(tokens, i + 2) == "て" and _l(tokens, i + 3) in {"居る", "いる"}: found.add("to_shite_iru")
        if (s == "よう" and _s(tokens, i + 1) in {"だ", "です"}) or s in {"みたい", "みたいだ"}: found.add("youda_mitaida")
        if s == "わけ" and _seq(tokens, i + 1, i + 4) == ["で", "は", "ない"]: found.add("wake_dewa_nai")
        if s in {"おそれ", "恐れ"} and _s(tokens, i + 1) == "が" and _l(tokens, i + 2) in {"有る", "ある"}: found.add("osore_ga_aru")
        if s == "見込み": found.add("mikomi")
        if s == "予定": found.add("yotei")
        if s == "中": found.add("chu")
        if s == "ころ": found.add("koro")
        if s == "ごろ": found.add("goro")
        if s in {"くらい", "ぐらい"}: found.add("kurai_gurai")
        if s == "まで":
            found.add("made")
            if _s(tokens, i + 1) == "に": found.add("made_ni")
            if "から" in surfaces[:i]: found.add("kara_made")
        if s == "ほど": found.add("hodo")
        if s == "以上": found.add("ijo")
        if l == "過ぎる" or s == "すぎる": found.add("sugiru")
    return found
def extract_grammar_details(articles):
    details = []
    for article in articles:
        entry = {"title": article.get("title", ""), "items": []}
        for block in article.get("blocks", []):
            for sentence in split_japanese_sentences(block.get("text", "")):
                rule_ids = sorted(detect_grammar_in_sentence(sentence))
                if not rule_ids:
                    continue
                entry["items"].append({"sentence": sentence, "grammar": [GRAMMAR_RULES_BY_ID[r]["label"] for r in rule_ids if r in GRAMMAR_RULES_BY_ID]})
        details.append(entry)
    return details
def extract_grammar_points(articles):
    found = {}
    for article in articles:
        for block in article.get("blocks", []):
            for sentence in split_japanese_sentences(block.get("text", "")):
                for rule_id in detect_grammar_in_sentence(sentence):
                    if rule_id not in found and rule_id in GRAMMAR_RULES_BY_ID:
                        rule = GRAMMAR_RULES_BY_ID[rule_id]
                        found[rule_id] = {"label": rule["label"], "explanation_bg": rule["explanation_bg"], "explanation_en": rule["explanation_en"]}
    return [found[rule["id"]] for rule in GRAMMAR_RULES if rule["id"] in found]
def extract_ne_id(text: str) -> str:
    m = re.search(r"(ne\d{10,})", text or "")
    return m.group(1) if m else ""
def get_nhkeasier_items():
    r = get_http_session().get(NHKEASIER_FEED_URL, timeout=20)
    r.raise_for_status()
    soup = BeautifulSoup(r.text, "xml")
    items = {}
    for item in soup.find_all("item"):
        title = (item.title.get_text() if item.title else "").strip()
        post_link = (item.link.get_text() if item.link else "").strip()
        desc_raw = (item.description.get_text() if item.description else "").strip()
        desc_html = html_lib.unescape(desc_raw)
        desc_soup = BeautifulSoup(desc_html, "html.parser")
        audio_url = ""
        enclosure = item.find("enclosure")
        if enclosure and enclosure.get("url"):
            audio_url = enclosure.get("url").strip()
        if not audio_url:
            audio_tag = desc_soup.select_one("audio[src], audio source[src]")
            if audio_tag:
                audio_url = (audio_tag.get("src") or "").strip()
        image_url = ""
        itunes_img = item.find("itunes:image")
        if itunes_img and itunes_img.get("href"):
            image_url = itunes_img.get("href").strip()
        if not image_url:
            img_tag = desc_soup.select_one("img[src]")
            if img_tag:
                image_url = (img_tag.get("src") or "").strip()
        blocks = []
        for b in get_article_blocks(desc_soup):
            t = b["text"].strip()
            if not t:
                continue
            if t.lower() in {"original", "permalink"} or "Original" in t or "Permalink" in t:
                continue
            blocks.append(b)
        ne_id = ""
        original_link = ""
        for a in desc_soup.select("a[href]"):
            href = (a.get("href") or "").strip()
            if "/news/easy/ne" in href:
                original_link = href
                ne_id = extract_ne_id(href)
                break
        if not ne_id:
            ne_id = extract_ne_id(audio_url) or extract_ne_id(image_url) or extract_ne_id(desc_html)
        if ne_id:
            items[ne_id] = {
                "title": title,
                "blocks": blocks,
                "audio_url": audio_url,
                "image_url": image_url,
                "original_link": original_link,
                "post_link": post_link,
            }
    return items
def extract_easy_article_links_from_sitemap(n=4):
    r = get_http_session().get(EASY_SITEMAP_URL, timeout=20)
    r.raise_for_status()
    soup = BeautifulSoup(r.text, "xml")
    links = []
    seen = set()
    for loc in soup.find_all("loc"):
        url = (loc.get_text() or "").strip()
        if not url:
            continue
        parsed = urlparse(url)
        if "/news/easy/ne" not in parsed.path or not parsed.path.endswith(".html") or url in seen:
            continue
        seen.add(url)
        links.append(url)
        if len(links) >= n:
            break
    return links
def parse_article_from_nhk_easy(link: str):
    page = get_http_session().get(link, timeout=20)
    page.raise_for_status()
    psoup = BeautifulSoup(page.text, "html.parser")
    title_tag = psoup.select_one("h1")
    title = ""
    title_html = ""
    if title_tag:
        title = title_tag.get_text(" ", strip=True)
        title_html = "".join(str(x) for x in title_tag.contents).strip() or title
    if not title:
        og_title = psoup.select_one('meta[property="og:title"]')
        if og_title:
            title = (og_title.get("content") or "").strip()
    if not title:
        title = "NHK Easy Article"
    if not title_html:
        title_html = title
    image_url = ""
    for sel in ['meta[property="og:image"]', 'meta[name="og:image"]', "article img[src]", "main img[src]", "img[src]"]:
        el = psoup.select_one(sel)
        if not el:
            continue
        candidate = (el.get("content") or el.get("src") or "").strip()
        if candidate:
            image_url = urljoin(link, candidate)
            break
    audio_url = ""
    for sel in ["audio source[src]", "audio[src]", 'a[href$=".mp3"]', 'a[href*=".mp3"]']:
        el = psoup.select_one(sel)
        if not el:
            continue
        candidate = (el.get("src") or el.get("href") or "").strip()
        if candidate:
            audio_url = urljoin(link, candidate)
            break
    if not audio_url:
        mp3_match = re.search(r"https?://[^\"'\s]+\.mp3(?:\?[^\"'\s]*)?", page.text)
        if mp3_match:
            audio_url = mp3_match.group(0)
    if not audio_url:
        audio_field_match = re.search(r'"(?:audio|voice|sound|movie)Url"\s*:\s*"([^"]+)"', page.text, re.IGNORECASE)
        if audio_field_match:
            audio_url = urljoin(link, audio_field_match.group(1))
    content = psoup.select_one(".article-main__body") or psoup.select_one(".module--content") or psoup.select_one("#js-article-body") or psoup.select_one(".content--detail-body") or psoup.select_one("article") or psoup.select_one("main")
    filtered_blocks = []
    if content is not None:
        for bad in content.select("script, style, nav, footer, header, aside, form"):
            bad.decompose()
        for b in get_article_blocks(content):
            t = b["text"]
            if "share" in t.lower() or "follow us" in t.lower():
                continue
            filtered_blocks.append(b)
    if not filtered_blocks:
        payload_texts = []
        for txt in re.findall(r'"children":"([^"]{10,}?)"', page.text):
            if "NHK" in txt or "トップ" in txt or "ニュース・防災" in txt:
                continue
            if not re.search(r"[ぁ-んァ-ン一-龯]", txt):
                continue
            cleaned = txt.replace("\\n", " ").strip()
            if len(cleaned) >= 10:
                payload_texts.append(cleaned)
        seen_text = set()
        for t in payload_texts:
            if t in seen_text:
                continue
            seen_text.add(t)
            filtered_blocks.append({"html": t, "text": t})
            if len(filtered_blocks) >= 8:
                break
    if not filtered_blocks:
        desc_meta = psoup.select_one('meta[name="description"]')
        desc = (desc_meta.get("content") or "").strip() if desc_meta else ""
        if desc:
            filtered_blocks.append({"html": desc, "text": desc})
    if not filtered_blocks:
        return None
    vocab = extract_vocab_from_blocks(filtered_blocks)
    article = {"title": title, "title_html": title_html, "link": link, "image_url": image_url, "audio_url": audio_url, "blocks": filtered_blocks, "vocab": vocab}
    return prepare_article_render_data(article)


def build_article_from_fallback(link: str, fallback: dict):
    if not fallback or not fallback.get("blocks"):
        return None
    title = (fallback.get("title") or "NHK Easy Article").strip()
    article = {
        "title": title,
        "title_html": title,
        "link": link,
        "image_url": (fallback.get("image_url") or "").strip(),
        "audio_url": (fallback.get("audio_url") or "").strip(),
        "blocks": [{"html": b["html"], "text": b["text"]} for b in fallback.get("blocks") or [] if (b.get("text") or "").strip()],
        "vocab": extract_vocab_from_blocks(fallback.get("blocks") or []),
    }
    return prepare_article_render_data(article)


def get_articles(n=4):
    nhkeasier_items = {}
    try:
        nhkeasier_items = get_nhkeasier_items()
    except Exception as e:
        print(f"Could not load nhkeasier fallback feed: {e}")
    articles = []

    # Prefer nhkeasier feed because it contains full text blocks and mp3 audio.
    for ne_id, fallback in list(nhkeasier_items.items())[:n]:
        link = (fallback.get("original_link") or fallback.get("post_link") or "").strip()
        article = build_article_from_fallback(link, fallback)
        if article and article.get("blocks"):
            articles.append(article)

    if len(articles) >= n:
        return articles[:n]

    links = extract_easy_article_links_from_sitemap(max(n * 8, n))
    existing_links = {(a.get("link") or "").strip() for a in articles}
    max_workers = min(8, max(1, n * 2))
    with ThreadPoolExecutor(max_workers=max_workers) as executor:
        futures = {executor.submit(parse_article_from_nhk_easy, link): link for link in links if link not in existing_links}
        for future in as_completed(futures):
            link = futures[future]
            ne_id = extract_ne_id(link)
            fallback = nhkeasier_items.get(ne_id)
            try:
                article = future.result()
                if article and fallback and fallback.get("blocks"):
                    article["blocks"] = [{"html": b["html"], "text": b["text"]} for b in fallback["blocks"]]
                    article["vocab"] = extract_vocab_from_blocks(fallback["blocks"])
                    if fallback.get("audio_url"):
                        article["audio_url"] = fallback["audio_url"]
                    if fallback.get("image_url"):
                        article["image_url"] = fallback["image_url"]
                    prepare_article_render_data(article)
                if not article and fallback:
                    article = build_article_from_fallback(link, fallback)
                if article and article.get("blocks"):
                    articles.append(article)
                if len(articles) >= n:
                    break
            except Exception as e:
                if fallback:
                    article = build_article_from_fallback(link, fallback)
                    if article and article.get("blocks"):
                        articles.append(article)
                        print(f"Used nhkeasier fallback for {link} after error: {e}")
                        if len(articles) >= n:
                            break
                        continue
                print(f"Skipping article because of error: {e}")
                continue
    return articles[:n]
def wrap_vocab_words_in_html(html_fragment, vocab_items=None, vocab_lookup=None):
    if not html_fragment:
        return html_fragment

    soup = BeautifulSoup(html_fragment, "html.parser")
    vocab_lookup = dict(vocab_lookup or {})
    if not vocab_lookup:
        vocab_lookup = build_vocab_lookup(vocab_items or [])

    if not vocab_lookup:
        return html_fragment

    html_text = "".join(str(x) for x in soup.contents)

    visible_chars = []
    visible_ranges = []
    i = 0
    tag_stack = []
    text_start = None
    while i < len(html_text):
        ch = html_text[i]
        if ch == "<":
            if text_start is not None:
                current_tags = {tag for tag in tag_stack if tag}
                chunk = html_text[text_start:i]
                if not ({"rt", "rp", "script", "style"} & current_tags):
                    for offset, c in enumerate(chunk):
                        visible_chars.append(c)
                        visible_ranges.append((text_start + offset, text_start + offset + 1))
                text_start = None
            end = html_text.find(">", i)
            if end == -1:
                break
            raw_tag = html_text[i + 1:end].strip()
            if raw_tag.startswith("!--"):
                close = html_text.find("-->", i + 4)
                if close == -1:
                    break
                i = close + 3
                continue
            tag_name = raw_tag.lstrip("/").split(None, 1)[0].rstrip("/").lower()
            is_closing = raw_tag.startswith("/")
            is_self_closing = raw_tag.endswith("/") or tag_name in {"br", "img", "meta", "link", "input", "source"}
            if is_closing:
                for idx in range(len(tag_stack) - 1, -1, -1):
                    if tag_stack[idx] == tag_name:
                        del tag_stack[idx]
                        break
            elif not is_self_closing:
                tag_stack.append(tag_name)
            i = end + 1
            continue
        if text_start is None:
            text_start = i
        i += 1
    if text_start is not None:
        current_tags = {tag for tag in tag_stack if tag}
        chunk = html_text[text_start:i]
        if not ({"rt", "rp", "script", "style"} & current_tags):
            for offset, c in enumerate(chunk):
                visible_chars.append(c)
                visible_ranges.append((text_start + offset, text_start + offset + 1))

    visible_text = "".join(visible_chars)
    if not visible_text.strip():
        return html_text

    sorted_surfaces = sorted(
        [(surface, vocab_lookup[surface]) for surface in vocab_lookup.keys() if surface and contains_japanese(surface)],
        key=lambda pair: (-len(pair[0]), pair[0]),
    )

    matches = []
    cursor = 0
    while cursor < len(visible_text):
        best_surface = None
        best_item = None
        for surface, item in sorted_surfaces:
            if visible_text.startswith(surface, cursor):
                best_surface = surface
                best_item = item
                break
        if best_surface is None:
            cursor += 1
            continue
        start_html = visible_ranges[cursor][0]
        end_html = visible_ranges[cursor + len(best_surface) - 1][1]
        matches.append((start_html, end_html, best_item))
        cursor += len(best_surface)

    if not matches:
        return html_text

    rebuilt = []
    html_cursor = 0
    for start_html, end_html, item in matches:
        if start_html < html_cursor:
            continue
        rebuilt.append(html_text[html_cursor:start_html])
        span = make_dict_span(BeautifulSoup("", "html.parser"), item, html_text[start_html:end_html])
        rebuilt.append(str(span))
        html_cursor = end_html
    rebuilt.append(html_text[html_cursor:])
    return "".join(rebuilt)
def build_html(articles, grammar_points=None, build_version="", build_code="", generated_at=""):
    grammar_points = grammar_points or []
    html = """<!doctype html>
<html lang=\"ja\">
<head>
<meta charset=\"UTF-8\">
<meta name=\"viewport\" content=\"width=device-width, initial-scale=1.0\">
<meta http-equiv=\"Cache-Control\" content=\"no-cache, no-store, must-revalidate\">
<meta http-equiv=\"Pragma\" content=\"no-cache\">
<meta http-equiv=\"Expires\" content=\"0\">
<meta http-equiv=\"refresh\" content=\"7200\">
<title>最新ニュース</title>
<meta name=\"theme-color\" content=\"#0f1115\">
<meta name=\"app-version\" content=\"__BUILD_VERSION__\">
<link rel=\"manifest\" href=\"manifest.webmanifest?v=__BUILD_VERSION__\">
<link rel=\"icon\" type=\"image/x-icon\" href=\"favicon.ico?v=__BUILD_VERSION__\">
<link rel=\"icon\" type=\"image/png\" sizes=\"16x16\" href=\"favicon-16x16.png?v=__BUILD_VERSION__\">
<link rel=\"icon\" type=\"image/png\" sizes=\"32x32\" href=\"favicon-32x32.png?v=__BUILD_VERSION__\">
<link rel=\"apple-touch-icon\" href=\"apple-touch-icon.png?v=__BUILD_VERSION__\">
<style>
:root{--bg:#0f1115;--card:#171a21;--card2:#1d212b;--text:#e8ecf1;--muted:#aeb7c2;--accent:#8ab4ff;--border:#2a3040;--jp-panel:#12151c;--trans-text:#d2dae3;--popup:#202532;--jp-font:"Hiragino Mincho ProN","Hiragino Mincho Pro","Yu Mincho","MS PMincho",serif;--ui-font:system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif}
body.theme-light{--bg:#f7f7f5;--card:#ffffff;--card2:#f2f2ee;--text:#1d232a;--muted:#596572;--accent:#275cc7;--border:#d3d9e1;--jp-panel:#fcfcfb;--trans-text:#3c4652;--popup:#ffffff}
body.theme-sepia{--bg:#f3eadb;--card:#fbf4e7;--card2:#f4ead9;--text:#3c2f22;--muted:#6e5d4b;--accent:#8a5a22;--border:#d8c7b0;--jp-panel:#fffaf0;--trans-text:#4e3f31;--popup:#fffaf0}
*{box-sizing:border-box}
body{margin:0;background:var(--bg);color:var(--text);font-family:var(--ui-font);line-height:1.8}
.wrap{max-width:980px;margin:0 auto;padding:26px 16px 40px}
h1{margin:0 0 18px;color:var(--accent);font-size:2rem;text-align:center;font-family:var(--jp-font)}
.site-logo{display:block;width:100px;height:100px;object-fit:contain;margin:0 auto 14px auto}
.lang-top{max-width:260px;margin:0 auto 18px auto}
.lang-top select{width:100%;background:var(--card2);color:var(--text);border:1px solid var(--border);border-radius:12px;padding:10px 12px;font:inherit}
.lang-top .control-label{text-align:center}
.lang-hint{max-width:760px;margin:0 auto 10px auto;text-align:center;color:var(--muted);font-size:.95rem;line-height:1.6}
.update-hint{max-width:760px;margin:0 auto 10px auto;text-align:center;color:var(--muted);font-size:.95rem;line-height:1.6}
.author-info{max-width:760px;margin:0 auto 18px auto;text-align:center;color:var(--muted);font-size:.92rem;line-height:1.7;font-family:ui-monospace,SFMono-Regular,Menlo,Monaco,Consolas,"Liberation Mono","Courier New",monospace;white-space:pre-line}
.build-marker{max-width:760px;margin:20px auto 8px auto;text-align:center;color:var(--muted);font-size:.84rem;opacity:.9}
article{background:var(--card);border:1px solid var(--border);border-radius:18px;padding:22px;margin-bottom:24px}
h2{margin:0 0 10px;font-size:1.38rem;cursor:pointer;font-family:var(--jp-font);line-height:1.5}
.article-image{width:100%;max-height:420px;object-fit:cover;border-radius:12px;border:1px solid var(--border);display:block;margin:10px 0 14px}
.title-translation{display:none;color:var(--muted);margin:4px 0 16px}
.article-audio{width:100%;margin:0 0 10px}
.section-title{margin:18px 0 10px;font-size:1.05rem;color:var(--accent);font-weight:700}
.jp-block{background:var(--jp-panel);border:1px solid var(--border);border-radius:12px;padding:14px 16px;margin:14px 0 6px;font-size:1.08rem;font-family:var(--jp-font);word-break:break-word;overflow-wrap:anywhere}
.trans-block{color:var(--trans-text);padding:0 2px 8px 2px;margin-bottom:8px;border-bottom:1px dashed var(--border);display:none}
.trans-block.is-visible{display:block}
.grammar{background:var(--card);border:1px solid var(--border);border-radius:18px;padding:18px}
.grammar ul{list-style:none;padding:0;margin:10px 0 0}
.grammar li{padding:12px 14px;border:1px solid var(--border);border-radius:12px;background:var(--card2);margin-bottom:10px}
.grammar-rule{font-weight:700;color:var(--accent);font-family:var(--jp-font);display:block;margin-bottom:4px}
.downloads{display:flex;justify-content:center;gap:10px;flex-wrap:wrap;margin:22px 0}
.download-btn{display:inline-block;padding:10px 14px;border-radius:12px;border:1px solid var(--border);background:var(--card2);color:var(--text);text-decoration:none}
.contacts{text-align:center;color:var(--muted);margin-top:10px}
.bottom-controls{margin-top:22px;padding:14px;border:1px solid var(--border);border-radius:16px;background:var(--card)}
.control-grid{display:grid;grid-template-columns:repeat(2,minmax(0,1fr));gap:10px}
.control-grid select{width:100%;background:var(--card2);color:var(--text);border:1px solid var(--border);border-radius:12px;padding:10px 12px;font:inherit}
.control-label{font-size:.92rem;color:var(--muted);margin-bottom:6px}
.dict-word{text-decoration:underline;text-decoration-thickness:1.5px;text-underline-offset:3px;cursor:pointer;border-radius:4px}
.dict-word.is-active{background:rgba(138,180,255,.18)}

.shadow-sentence{display:block;margin:2px 0;padding-left:10px}
.shadow-sentence.shadow-active{border-left:3px solid #ff7a00}

.dict-popup{position:fixed;z-index:9999;display:none;max-width:min(96vw,440px);background:var(--popup);color:var(--text);border:1px solid var(--border);border-radius:12px;padding:10px 12px;box-shadow:0 12px 32px rgba(0,0,0,.28)}
.dict-popup .dw{font-weight:700;font-size:1.08rem;font-family:var(--jp-font);line-height:1.6;white-space:normal;word-break:break-word}
.dict-popup .dr{color:var(--accent);font-size:.95rem;margin-top:2px}
.dict-popup .dm{color:var(--text);margin-top:6px;line-height:1.65;white-space:normal;word-break:break-word}
ruby rt{font-size:.68em;color:var(--muted)}
</style>
</head>
<body class=\"theme-dark\">
<div class=\"wrap\">
<img class=\"site-logo\" src=\"android-chrome-192x192.png?v=__BUILD_VERSION__\" alt=\"NHK logo\" loading=\"lazy\">
<h1>最新ニュース</h1>
<div class=\"lang-top\">
  <div class=\"control-label\" data-ui=\"translation_language\"></div>
  <select id=\"lang-select\" onchange=\"setContentLanguage(this.value)\">
    <option value=\"bg\">🇧🇬 Български</option>
    <option value=\"en\">🇬🇧 English</option>
  </select>
</div>
<div class=\"lang-hint\" data-ui=\"help_hint\"></div>
<div class=\"update-hint\" data-ui=\"update_hint\"></div>
<div class=\"author-info\" data-bg=\"Създадено от Веселин Баев&#10;GitHub: vebaev&#10;Email: vebaev@gmail.com\" data-en=\"Created by Veselin Baev&#10;GitHub: vebaev&#10;Email: vebaev@gmail.com\"></div>
<div id=\"dict-popup\" class=\"dict-popup\" aria-hidden=\"true\"></div>
"""
    for idx, article in enumerate(articles, start=1):
        html += "<article>"
        num_map = {1:'1️⃣',2:'2️⃣',3:'3️⃣',4:'4️⃣'}
        prefix = num_map.get(idx, f'{idx}.')
        html += f"<h2 class='title-toggle'>{prefix} {article.get('title_html', article['title'])}</h2>"
        title_bg = html_lib.escape(article.get('title_translation_bg', ''), quote=True)
        title_en = html_lib.escape(article.get('title_translation_en', ''), quote=True)
        if title_bg or title_en:
            html += f"<div class='title-translation' data-bg='{title_bg}' data-en='{title_en}'></div>"
        if article.get("image_url"):
            html += f"<img class='article-image' src='{article['image_url']}' alt='{html_lib.escape(article['title'], quote=True)}' loading='lazy'/>"
        if article.get("audio_url"):
            html += f"<audio class='article-audio' controls preload='none' src='{article['audio_url']}'></audio>"
        html += "<div class='section-title' data-ui='text'></div>"
        for block in article["blocks"]:
            wrapped_html = block.get("wrapped_html") or block.get("html", "")
            html += f"<div class='jp-block'>{wrapped_html}</div>"
            block_bg = html_lib.escape(block.get('translation_bg', ''), quote=True)
            block_en = html_lib.escape(block.get('translation_en', ''), quote=True)
            if block_bg or block_en:
                html += f"<div class='trans-block' data-bg='{block_bg}' data-en='{block_en}'></div>"
        html += "</article>"
    html += "<div class='downloads'>"
    html += f"<a class='download-btn download-link' data-kind='anki_apkg' href='{DEFAULT_ANKI_APKG_FILENAME}' download></a>"
    html += f"<a class='download-btn download-link' data-kind='anki_tsv' href='{DEFAULT_ANKI_FILENAME}' download></a>"
    html += "</div>"
    if grammar_points:
        html += "<section class='grammar'><div class='section-title' data-ui='grammar_in_texts'></div><ul>"
        for g in grammar_points:
            html += f"<li><span class='grammar-rule'>{g['label']}</span><span class='grammar-expl' data-bg='{html_lib.escape(g.get('explanation_bg',''), quote=True)}' data-en='{html_lib.escape(g.get('explanation_en',''), quote=True)}'></span></li>"
        html += "</ul></section>"
    html += """
<div class='bottom-controls'>
  <div class='control-grid'>
    <div><div class='control-label' data-ui='theme'></div><select id='theme-select' onchange='setTheme(this.value)'><option value='theme-dark'>Dark</option><option value='theme-sepia'>Sepia</option><option value='theme-light'>Light</option></select></div>
    <div><div class='control-label' data-ui='japanese_font'></div><select id='font-select' onchange='setJapaneseFont(this.value)'><option value='mincho'>Mincho</option><option value='gothic'>Gothic</option></select></div>
  </div>
</div>
<div class='contacts'>vebaev.github.io</div>
<div class='build-marker'>Generated: __GENERATED_AT__</div>
</div>
<script>
const UI_TEXT={bg:{text:"Текст",grammar_in_texts:"Граматика в текстовете",theme:"Тема",japanese_font:"Японски шрифт",translation_language:"Език",help_hint:"ℹ️ Кликни върху абзац за превод или върху елемент в текста за обяснение.",update_hint:"⏱️ Новините се обновяват веднъж дневно около 14:00 ч. българско време (12:00 UTC).",anki_apkg:"Свали Anki deck (.apkg)",anki_tsv:"Свали Anki TSV",popup_type:"Тип",popup_translation:"Превод",popup_dictionary_form:"Речникова форма",popup_formation:"Образуване",popup_formula:"Формула"},en:{text:"Text",grammar_in_texts:"Grammar in the texts",theme:"Theme",japanese_font:"Japanese font",translation_language:"Language",help_hint:"ℹ️ Click a paragraph for translation or a text element for explanation.",update_hint:"⏱️ News updates once daily around 14:00 Bulgarian time (12:00 UTC).",anki_apkg:"Download Anki deck (.apkg)",anki_tsv:"Download Anki TSV",popup_type:"Type",popup_translation:"Translation",popup_dictionary_form:"Dictionary form",popup_formation:"Formation",popup_formula:"Formula"}};
const FILES={bg:{anki_apkg:"nhk_easy_elements_bg.apkg",anki_tsv:"anki_cards_bg.tsv"},en:{anki_apkg:"nhk_easy_elements_bg.apkg",anki_tsv:"anki_cards_bg.tsv"}};
function getContentLanguage(){return localStorage.getItem('nhk_content_lang')||'bg';}
function loadPrefs(){const theme=localStorage.getItem('nhk_theme')||'theme-dark';document.body.className=theme;const themeSel=document.getElementById('theme-select');if(themeSel)themeSel.value=theme;const jpFont=localStorage.getItem('nhk_jp_font')||'mincho';applyJapaneseFont(jpFont);const fontSel=document.getElementById('font-select');if(fontSel)fontSel.value=jpFont;const lang=getContentLanguage();const langSel=document.getElementById('lang-select');if(langSel)langSel.value=lang;applyContentLanguage(lang);}
function setTheme(theme){document.body.className=theme;localStorage.setItem('nhk_theme',theme);const meta=document.querySelector('meta[name="theme-color"]');if(meta){meta.setAttribute('content',theme==='theme-light'?'#f7f7f5':theme==='theme-sepia'?'#f3eadb':'#0f1115');}}
function applyJapaneseFont(kind){const font=kind==='gothic'?'"Hiragino Kaku Gothic ProN","Yu Gothic","Meiryo",sans-serif':'"Hiragino Mincho ProN","Hiragino Mincho Pro","Yu Mincho","MS PMincho",serif';document.documentElement.style.setProperty('--jp-font',font);}
function setJapaneseFont(kind){localStorage.setItem('nhk_jp_font',kind);applyJapaneseFont(kind);}
function setContentLanguage(lang){localStorage.setItem('nhk_content_lang',lang);applyContentLanguage(lang);closeDictPopup();}
function applyContentLanguage(lang){document.querySelectorAll('[data-ui]').forEach(el=>{const key=el.dataset.ui;if(UI_TEXT[lang]&&UI_TEXT[lang][key])el.textContent=UI_TEXT[lang][key];});document.querySelectorAll('.title-translation,.trans-block,.grammar-expl,.author-info').forEach(el=>{el.textContent=el.dataset[lang]||'';});document.querySelectorAll('.download-link').forEach(el=>{const kind=el.dataset.kind;el.textContent=UI_TEXT[lang][kind]||kind;el.setAttribute('href',FILES[lang][kind]);});}
function closeDictPopup(){const popup=document.getElementById('dict-popup');if(!popup)return;popup.style.display='none';popup.setAttribute('aria-hidden','true');document.querySelectorAll('.dict-word.is-active').forEach(el=>el.classList.remove('is-active'));}
function positionPopupNear(el,popup){const rect=el.getBoundingClientRect();popup.style.display='block';popup.setAttribute('aria-hidden','false');const popupRect=popup.getBoundingClientRect();let top=rect.bottom+8;let left=rect.left;if(left+popupRect.width>window.innerWidth-8)left=window.innerWidth-popupRect.width-8;if(left<8)left=8;if(top+popupRect.height>window.innerHeight-8)top=rect.top-popupRect.height-8;if(top<8)top=8;popup.style.left=left+'px';popup.style.top=top+'px';}
function esc(v){return (v||'').replace(/&/g,'&amp;').replace(/</g,'&lt;').replace(/>/g,'&gt;');}
function popupLine(label,value){return value?'<div class="dm"><b>'+esc(label)+':</b> '+esc(value)+'</div>':'';}
function showDictPopup(el){const popup=document.getElementById('dict-popup');if(!popup)return;const alreadyActive=el.classList.contains('is-active');closeDictPopup();if(alreadyActive)return;const lang=getContentLanguage();const ui=UI_TEXT[lang]||UI_TEXT.bg;const surface=(el.dataset.surface||'').trim();const lemma=(el.dataset.lemma||surface).trim();const reading=(el.dataset.reading||'').trim();const category=(lang==='en'?el.dataset.categoryEn:el.dataset.categoryBg||el.dataset.categoryEn||'').trim();const translation=(lang==='en'?el.dataset.translationEn:el.dataset.translationBg||el.dataset.translationEn||'').trim();const formation=(lang==='en'?el.dataset.formationEn:el.dataset.formationBg||el.dataset.formationEn||'').trim();const formula=(lang==='en'?el.dataset.formulaEn:el.dataset.formulaBg||el.dataset.formulaEn||'').trim();let html='<div class="dw">'+esc(surface)+(reading?' ['+esc(reading)+']':'')+'</div>';html+=popupLine(ui.popup_type,category);html+=popupLine(ui.popup_translation,translation);html+=popupLine(ui.popup_dictionary_form,lemma);html+=popupLine(ui.popup_formation,formation);html+=popupLine(ui.popup_formula,formula);popup.innerHTML=html;el.classList.add('is-active');positionPopupNear(el,popup);}


function splitSentenceParts(text){
  return (text || '').split(/(?<=[。！？?!])\\s*/).filter(function(s){return s && s.trim();});
}

function wrapBlockSentences(block){
  if(!block) return [];
  if(block.dataset.shadowPrepared === '1'){
    return Array.from(block.querySelectorAll('.shadow-sentence'));
  }

  const originalNodes = Array.from(block.childNodes);
  const frag = document.createDocumentFragment();
  let current = document.createElement('span');
  current.className = 'shadow-sentence';

  function flushCurrent(){
    if(!current.childNodes.length) return;
    frag.appendChild(current);
    current = document.createElement('span');
    current.className = 'shadow-sentence';
  }

  function appendSplitText(txt){
    const parts = splitSentenceParts(txt);
    if(!parts.length){
      if(txt) current.appendChild(document.createTextNode(txt));
      return;
    }
    parts.forEach(function(part){
      current.appendChild(document.createTextNode(part));
      if(/[。！？?!]\\s*$/.test(part)){
        flushCurrent();
      }
    });
  }

  originalNodes.forEach(function(node){
    if(node.nodeType === Node.TEXT_NODE){
      appendSplitText(node.textContent || '');
    } else {
      const clone = node.cloneNode(true);
      current.appendChild(clone);
      const t = (current.textContent || '').trim();
      if(/[。！？?!]\\s*$/.test(t)){
        flushCurrent();
      }
    }
  });

  flushCurrent();
  block.innerHTML = '';
  block.appendChild(frag);
  block.dataset.shadowPrepared = '1';
  return Array.from(block.querySelectorAll('.shadow-sentence'));
}

function sentenceWeight(text){
  let score = 0;
  for(const ch of (text || '')){
    if(/[一-龯]/.test(ch)) score += 1.8;
    else if(/[ぁ-ゖ]/.test(ch)) score += 1.1;
    else if(/[ァ-ヺー]/.test(ch)) score += 1.2;
    else if(/[、]/.test(ch)) score += 0.6;
    else if(/[。！？?!]/.test(ch)) score += 0.8;
    else score += 0.9;
  }
  return Math.max(score, 1);
}

function setupArticleShadowing(article){
  const audio = article.querySelector('.article-audio');
  if(!audio) return;

  const sentenceEls = [];
  article.querySelectorAll('.jp-block').forEach(function(block){
    wrapBlockSentences(block).forEach(function(el){ sentenceEls.push(el); });
  });
  if(!sentenceEls.length) return;

  let timings = [];

  function buildTimings(){
    const duration = audio.duration || 0;
    if(!duration || !isFinite(duration)) return;
    const weights = sentenceEls.map(function(el){ return sentenceWeight((el.textContent || '').trim()); });
    const total = weights.reduce(function(a,b){ return a+b; }, 0) || 1;
    let acc = 0;
    timings = weights.map(function(w, idx){
      const start = acc;
      acc += duration * (w / total);
      return { index: idx, start: start, end: acc };
    });
    if(timings.length){
      timings[0].start = 0;
      timings[timings.length - 1].end = duration;
    }
  }

  function clearActive(){
    sentenceEls.forEach(function(el){ el.classList.remove('shadow-active'); });
  }

  function updateHighlight(){
    if(!timings.length) buildTimings();
    if(!timings.length) return;
    const t = audio.currentTime || 0;
    let current = timings.find(function(seg){ return t >= seg.start && t < seg.end; });
    if(!current) current = timings[timings.length - 1];
    if(!current) return;
    clearActive();
    const el = sentenceEls[current.index];
    if(el) el.classList.add('shadow-active');
  }

  audio.addEventListener('loadedmetadata', buildTimings);
  audio.addEventListener('canplay', buildTimings);
  audio.addEventListener('play', updateHighlight);
  audio.addEventListener('timeupdate', updateHighlight);
  audio.addEventListener('seeked', updateHighlight);
  audio.addEventListener('pause', updateHighlight);
  audio.addEventListener('ended', clearActive);
}

function forceFreshReloadCheck(){fetch(window.location.pathname + '?v=' + encodeURIComponent(document.querySelector('meta[name="app-version"]')?.content || Date.now()), {cache:'no-store'}).then(r=>r.text()).then(html=>{const m=html.match(/<meta name=\"app-version\" content=\"([^\"]+)\"/);const current=document.querySelector('meta[name="app-version"]')?.content||'';if(m&&m[1]&&m[1]!==current){window.location.reload();}}).catch(function(){});}
document.addEventListener('DOMContentLoaded',function(){loadPrefs();document.querySelectorAll('article').forEach(function(article){setupArticleShadowing(article);});if('serviceWorker' in navigator){navigator.serviceWorker.register('./sw.js?v='+encodeURIComponent(document.querySelector('meta[name="app-version"]')?.content || ''),{updateViaCache:'none'}).then(function(reg){if(reg&&reg.update){reg.update();}}).catch(function(){});}forceFreshReloadCheck();setInterval(forceFreshReloadCheck,120000);document.querySelectorAll('.title-toggle').forEach(function(title){title.addEventListener('click',function(){const tr=title.nextElementSibling;if(!tr||!tr.classList.contains('title-translation'))return;tr.style.display=tr.style.display==='block'?'none':'block';});});document.querySelectorAll('.dict-word').forEach(function(el){el.addEventListener('click',function(event){event.stopPropagation();showDictPopup(el);});});document.addEventListener('click',function(){closeDictPopup();});document.querySelectorAll('.jp-block + .trans-block').forEach(function(trBlock){const jpBlock=trBlock.previousElementSibling;if(!jpBlock)return;jpBlock.style.cursor='pointer';jpBlock.addEventListener('click',function(event){if(event.target.closest('.dict-word'))return;trBlock.classList.toggle('is-visible');});});});
</script>
</body>
</html>"""
    html = html.replace("__BUILD_VERSION__", html_lib.escape(build_version, quote=True))
    html = html.replace("__GENERATED_AT__", html_lib.escape(generated_at, quote=True))
    return html

def write_pwa_files(output_dir, build_version=""):
    if not output_dir:
        return
    manifest = {
        "name": "NHK Easy News",
        "id": f"./?v={build_version}",
        "short_name": "NHK Easy",
        "start_url": f"./index.html?v={build_version}",
        "display": "standalone",
        "background_color": "#0f1115",
        "theme_color": "#0f1115",
        "icons": [
            {"src": "android-chrome-192x192.png", "sizes": "192x192", "type": "image/png"},
            {"src": "android-chrome-512x512.png", "sizes": "512x512", "type": "image/png"},
            {"src": "apple-touch-icon.png", "sizes": "180x180", "type": "image/png"}
        ]
    }
    with open(os.path.join(output_dir, "manifest.webmanifest"), "w", encoding="utf-8") as f:
        json.dump(manifest, f, ensure_ascii=False, indent=2)
    sw_js = "const CACHE_NAME='nhk-easy-'+(%r||Date.now());\nconst RUNTIME_HTML_CACHE=CACHE_NAME+'-html';\nself.addEventListener('install',e=>{self.skipWaiting();});\nself.addEventListener('activate',e=>{e.waitUntil(caches.keys().then(keys=>Promise.all(keys.filter(k=>k!==CACHE_NAME&&k!==RUNTIME_HTML_CACHE).map(k=>caches.delete(k)))).then(()=>self.clients.claim()));});\nself.addEventListener('fetch',e=>{if(e.request.method!=='GET')return;if(e.request.mode==='navigate'){e.respondWith(fetch(new Request(e.request,{cache:'reload'})).then(r=>{const copy=r.clone();caches.open(RUNTIME_HTML_CACHE).then(c=>c.put(e.request,copy)).catch(()=>{});return r;}).catch(async()=>{const cached=await caches.match(e.request);if(cached)return cached;return caches.match('./index.html');}));return;}e.respondWith(fetch(e.request,{cache:'no-store'}).catch(()=>caches.match(e.request)));});" % build_version
    with open(os.path.join(output_dir, "sw.js"), "w", encoding="utf-8") as f:
        f.write(sw_js)

def main():
    global DEEPL_API_KEY, GROQ_API_KEY, GROQ_MODEL
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default=DEFAULT_OUTPUT)
    parser.add_argument("--count", type=int, default=4)
    parser.add_argument("--deepl-key", default=os.environ.get("DEEPL_API_KEY", ""))
    parser.add_argument("--groq-key", default=os.environ.get("GROQ_API_KEY", ""))
    parser.add_argument("--groq-model", default=os.environ.get("GROQ_MODEL", "qwen/qwen3-32b"))
    args = parser.parse_args()

    DEEPL_API_KEY = (args.deepl_key or "").strip()
    GROQ_API_KEY = (args.groq_key or "").strip()
    GROQ_MODEL = (args.groq_model or "qwen/qwen3-32b").strip() or "qwen/qwen3-32b"
    build_version = str(int(time.time()))
    build_code = build_version[-4:] if len(build_version) >= 4 else build_version
    generated_at = datetime.now().astimezone().strftime("%Y-%m-%d %H:%M:%S %Z")
    output_dir = os.path.dirname(args.output)
    translation_cache_path = get_translation_cache_path(args.output)
    gemini_cache_path = get_gemini_cache_path(args.output)
    load_translation_cache(translation_cache_path)
    load_gemini_cache(gemini_cache_path)
    if output_dir:
        os.makedirs(output_dir, exist_ok=True)
        write_pwa_files(output_dir, build_version=build_version)

    articles = get_articles(args.count)
    if not articles:
        raise RuntimeError("No articles were extracted.")

    analyze_articles_with_groq(articles)
    for article in articles:
        prepare_article_render_data(article)
    grammar_points = build_grammar_points_from_analysis(articles)

    vocab_tsv_filename = DEFAULT_ANKI_FILENAME
    vocab_apkg_filename = DEFAULT_ANKI_APKG_FILENAME
    anki_seen_words_filename = DEFAULT_ANKI_SEEN_WORDS_FILENAME

    if output_dir:
        vocab_tsv_path = os.path.join(output_dir, vocab_tsv_filename)
        vocab_apkg_path = os.path.join(output_dir, vocab_apkg_filename)
        anki_seen_words_path = os.path.join(output_dir, anki_seen_words_filename)
    else:
        vocab_tsv_path = vocab_tsv_filename
        vocab_apkg_path = vocab_apkg_filename
        anki_seen_words_path = anki_seen_words_filename

    seen_words = load_seen_words(anki_seen_words_path)
    add_known_progress_to_articles(articles, seen_words)

    vocab_cards = build_analysis_anki_cards(articles, lang="bg")

    save_anki_tsv(vocab_cards, vocab_tsv_path)

    build_anki_apkg(vocab_cards, vocab_apkg_path, deck_name="NHK Easy Elements BG")

    save_seen_words(anki_seen_words_path, seen_words)

    html = build_html(articles, grammar_points=grammar_points, build_version=build_version, build_code=build_code, generated_at=generated_at)
    with open(args.output, "w", encoding="utf-8") as f:
        f.write(html)
    save_translation_cache(translation_cache_path)
    save_gemini_cache(gemini_cache_path)

if __name__ == "__main__":
    main()
