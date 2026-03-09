import os
import re
import argparse
import html as html_lib
import hashlib
import json
import uuid
from urllib.parse import urljoin, urlparse

import requests
from bs4 import BeautifulSoup
from googletrans import Translator

try:
    import fugashi
except Exception:
    fugashi = None

try:
    import genanki
except Exception:
    genanki = None


EASY_INDEX_URL = "https://news.web.nhk/news/easy/"
EASY_SITEMAP_URL = "https://news.web.nhk/news/easy/sitemap/sitemap.xml"
NHKEASIER_FEED_URL = "https://nhkeasier.com/feed/"
DEFAULT_OUTPUT = "docs/index.html"
DEFAULT_ANKI_FILENAME = "anki_cards.tsv"
DEFAULT_ANKI_APKG_FILENAME = "nhk_easy_vocab.apkg"
DEFAULT_ANKI_SEEN_WORDS_FILENAME = "anki_seen_words.json"

translator = Translator()
DEEPL_API_KEY = os.environ.get("DEEPL_API_KEY", "").strip()
_TRANSLATION_CACHE = {}
_TRANSLATION_STATS = {"deepl": 0, "google": 0}
PARTICLE_PREFIXES = ("が", "を", "に", "で", "は", "と", "へ", "や", "も", "の")
GODAN_I_TO_U = {
    "い": "う",
    "き": "く",
    "ぎ": "ぐ",
    "し": "す",
    "ち": "つ",
    "に": "ぬ",
    "び": "ぶ",
    "み": "む",
    "り": "る",
}
GODAN_A_TO_U = {
    "わ": "う",
    "か": "く",
    "が": "ぐ",
    "さ": "す",
    "た": "つ",
    "な": "ぬ",
    "ば": "ぶ",
    "ま": "む",
    "ら": "る",
}
_MECAB_TAGGER = None

# По-силен MeCab/UniDic grammar detector.
# Това не е пълен parser, но е по-силен от plain regex и покрива повече learner grammar.
GRAMMAR_RULES = [
    {"id": "te_iru", "label": "〜ている / 〜ています", "explanation": "Продължително действие или състояние."},
    {"id": "te_ita", "label": "〜ていた / 〜ていました", "explanation": "Продължително действие/състояние в миналото."},
    {"id": "te_oku", "label": "〜ておく", "explanation": "Правя нещо предварително."},
    {"id": "te_shimau", "label": "〜てしまう", "explanation": "Завършеност или нежелан резултат."},
    {"id": "te_miru", "label": "〜てみる", "explanation": "Опитвам да направя нещо."},
    {"id": "te_ageru", "label": "〜てあげる", "explanation": "Правя нещо за някого."},
    {"id": "te_kureru", "label": "〜てくれる", "explanation": "Някой прави нещо за мен/нас."},
    {"id": "te_morau", "label": "〜てもらう", "explanation": "Получавам услуга от някого."},
    {"id": "nai", "label": "〜ない", "explanation": "Отрицателна форма."},
    {"id": "nakereba_naranai", "label": "〜なければならない", "explanation": "Задължение: трябва да..."},
    {"id": "nakereba_ikenai", "label": "〜なければいけない", "explanation": "Задължение: трябва да..."},
    {"id": "nakutewa_naranai", "label": "〜なくてはならない", "explanation": "Задължение: трябва да..."},
    {"id": "beki", "label": "〜べき", "explanation": "Трябва/редно е да..."},
    {"id": "hazu_da", "label": "〜はずだ", "explanation": "Трябва да е така / очаква се."},
    {"id": "kamoshirenai", "label": "〜かもしれない", "explanation": "Вероятност: може би..."},
    {"id": "souda", "label": "〜そうだ", "explanation": "Изглежда че... / казват че..."},
    {"id": "rashii", "label": "〜らしい", "explanation": "Изглежда / по слухове / типично за."},
    {"id": "youda", "label": "〜ようだ / 〜ように", "explanation": "Прилика, сравнение, начин или цел."},
    {"id": "koto_ga_dekiru", "label": "〜ことができる", "explanation": "Възможност или умение: мога да..."},
    {"id": "koto_ni_naru", "label": "〜ことになる", "explanation": "Решение/резултат: решено е да..."},
    {"id": "you_ni_naru", "label": "〜ようになる", "explanation": "Промяна на състояние: започвам да мога / става така, че..."},
    {"id": "tsumori_da", "label": "〜つもりだ", "explanation": "Намерение."},
    {"id": "to_omou", "label": "〜と思う", "explanation": "Мнение: мисля, че..."},
    {"id": "to_iu", "label": "〜という", "explanation": "Назоваване или цитиране."},
    {"id": "tame_ni", "label": "〜ため(に)", "explanation": "Причина или цел."},
    {"id": "nagara", "label": "〜ながら", "explanation": "Едновременно действие: докато..."},
    {"id": "tari_tari", "label": "〜たり〜たりする", "explanation": "Непълен списък от действия."},
    {"id": "passive_rareru", "label": "受け身 (〜られる / 〜れる)", "explanation": "Страдателен залог."},
    {"id": "causative_saseru", "label": "使役 (〜させる / 〜せる)", "explanation": "Каузатив: карам/оставям някого да..."},
    {"id": "potential_rareru", "label": "可能形", "explanation": "Възможностна форма: мога да..."},
    {"id": "volitional", "label": "意向形 (〜よう / 〜おう)", "explanation": "Волево намерение: нека..., ще..."},
    {"id": "tai", "label": "〜たい", "explanation": "Желание: искам да..."},
    {"id": "kara_reason", "label": "〜から", "explanation": "Причина или отправна точка."},
    {"id": "made", "label": "〜まで", "explanation": "Граница във време/място: до."},
    {"id": "ni", "label": "〜に", "explanation": "Частица за посока, време, цел или непряк обект."},
]
GRAMMAR_RULES_BY_ID = {r["id"]: r for r in GRAMMAR_RULES}


def translate_text(text: str, dest: str = "bg") -> str:
    text = (text or "").strip()
    if not text:
        return ""
    cache_key = (text, dest, bool(DEEPL_API_KEY))
    if cache_key in _TRANSLATION_CACHE:
        return _TRANSLATION_CACHE[cache_key]

    if DEEPL_API_KEY:
        try:
            deepl_url = "https://api-free.deepl.com/v2/translate"
            if not DEEPL_API_KEY.endswith(":fx"):
                deepl_url = "https://api.deepl.com/v2/translate"

            resp = requests.post(
                deepl_url,
                headers={"Authorization": f"DeepL-Auth-Key {DEEPL_API_KEY}"},
                data={"text": text, "target_lang": dest.upper()},
                timeout=20,
            )
            resp.raise_for_status()
            data = resp.json()
            translations = data.get("translations") or []
            if translations and translations[0].get("text"):
                result = translations[0]["text"].strip()
                _TRANSLATION_STATS["deepl"] += 1
                _TRANSLATION_CACHE[cache_key] = result
                return result
        except Exception:
            pass

    try:
        result = translator.translate(text, dest=dest).text
        _TRANSLATION_STATS["google"] += 1
        _TRANSLATION_CACHE[cache_key] = result
        return result
    except Exception:
        return ""


def get_article_blocks(content):
    blocks = []
    for el in content.find_all(["p", "h2", "h3", "li"], recursive=True):
        txt = el.get_text(" ", strip=True)
        if not txt or len(txt) < 3:
            continue
        blocks.append({"text": txt, "html": "".join(str(x) for x in el.contents).strip()})
    return blocks


def extract_vocab_from_blocks(blocks):
    vocab_map = {}

    for block in blocks:
        soup = BeautifulSoup(block["html"], "html.parser")
        rubies = soup.find_all("ruby")

        for ruby in rubies:
            rb_text = ""
            rt_text = ""

            for child in ruby.contents:
                name = getattr(child, "name", None)
                if name == "rt":
                    rt_text += child.get_text("", strip=True)
                elif name == "rp":
                    continue
                else:
                    if hasattr(child, "get_text"):
                        rb_text += child.get_text("", strip=True)
                    else:
                        rb_text += str(child).strip()

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

            if word not in vocab_map:
                vocab_map[word] = reading

    vocab = []
    for word, reading in vocab_map.items():
        vocab.append({
            "word": word,
            "reading": reading,
            "meaning": translate_text(word, dest="bg"),
        })

    return vocab[:20]


def is_single_kanji_word(word: str) -> bool:
    return bool(re.fullmatch(r"[一-龯]", (word or "").strip()))


def is_known_vocab_item(word: str, known_items):
    return word in known_items or f"v:{word}" in known_items


def build_anki_cards(articles, grammar_points=None, seen_items=None):
    cards = []
    seen = set()
    known = set(seen_items or [])
    newly_added_items = set()

    for article in articles:
        for item in article.get("vocab", []):
            word = (item.get("word") or "").strip()
            reading = (item.get("reading") or "").strip()
            meaning = (item.get("meaning") or "").strip()
            if not word or not meaning or is_single_kanji_word(word) or word in seen or is_known_vocab_item(word, known):
                continue
            seen.add(word)
            newly_added_items.add(f"v:{word}")

            front = f"<ruby>{word}<rt>{reading}</rt></ruby>" if reading and reading != word else word
            cards.append((front, meaning))

    for g in grammar_points or []:
        label = (g.get("label") or "").strip()
        explanation = (g.get("explanation") or "").strip()
        if not label or not explanation:
            continue
        grammar_key = f"g:{label}"
        if grammar_key in known:
            continue
        newly_added_items.add(grammar_key)
        cards.append((f"Граматика: {label}", explanation))

    return cards, newly_added_items


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


def split_japanese_sentences(text: str):
    t = (text or "").strip()
    if not t:
        return []
    return [p.strip() for p in re.split(r"(?<=[。！？])\s*", t) if p.strip()]


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
        stable_int_id("nhk_easy_vocab_model"),
        "NHK Easy Vocab Model",
        fields=[{"name": "Front"}, {"name": "Back"}],
        templates=[{
            "name": "Card 1",
            "qfmt": "<div class='jp-word'>{{Front}}</div>",
            "afmt": "<div class='jp-word'>{{Front}}</div><hr id='answer'><div class='bg-meaning'>{{Back}}</div>",
        }],
        css="""
.card {font-family: Arial, sans-serif; font-size: 25px; text-align: center; color: black; background-color: white;}
.jp-word {font-size: 31px;}
.bg-meaning {font-size: 25px;}
.jp-word ruby rt {font-size: 14px;}
""",
    )

    deck = genanki.Deck(stable_int_id("nhk_easy_vocab_deck"), deck_name)
    for front, back in cards:
        deck.add_note(genanki.Note(model=model, fields=[front, back], guid=uuid.uuid4().hex))

    genanki.Package(deck).write_to_file(apkg_path)
    return True


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


def token_pos1(token) -> str:
    feat = token_feature(token)
    return getattr(feat, "pos1", "") or ""


def token_lemma(token) -> str:
    feat = token_feature(token)
    if feat is None:
        return ""
    for name in ("lemma", "dictionary_form", "lemma_form", "orthBase"):
        val = getattr(feat, name, "") or ""
        if val:
            return val.strip()
    return ""


def token_cform(token) -> str:
    feat = token_feature(token)
    for name in ("cForm", "conjugationForm"):
        val = getattr(feat, name, "") or ""
        if val:
            return val
    return ""


def token_ctype(token) -> str:
    feat = token_feature(token)
    for name in ("cType", "conjugationType"):
        val = getattr(feat, name, "") or ""
        if val:
            return val
    return ""


def is_target_pos(token) -> bool:
    pos1 = token_pos1(token)
    if pos1 in {"動詞", "形容詞"}:
        return True
    feat = str(token_feature(token))
    return "動詞" in feat or "形容詞" in feat


def lemma_equals(token, *values):
    s = token_surface(token)
    l = token_lemma(token)
    return s in values or l in values


def surface_in(token, *values):
    return token_surface(token) in values


def has_surface(tokens, idx, *values):
    return 0 <= idx < len(tokens) and token_surface(tokens[idx]) in values


def has_lemma(tokens, idx, *values):
    return 0 <= idx < len(tokens) and lemma_equals(tokens[idx], *values)


def contains_suffix_form(token, *parts):
    joined = "|".join(parts)
    s = token_surface(token)
    l = token_lemma(token)
    return any(p in s or p in l for p in parts)


def lemmatize_japanese(word: str) -> str:
    w = (word or "").strip()
    if not w:
        return w

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


def to_dictionary_form(word: str) -> str:
    w = (word or "").strip()
    if not w:
        return w

    for suffix in ["していました", "しています", "しました", "します", "して", "した"]:
        if w.endswith(suffix):
            return w[: -len(suffix)] + "する"

    for suffix in ["きました", "きます", "きて", "きた", "こない", "こなかった"]:
        if w.endswith(suffix):
            return w[: -len(suffix)] + "くる"

    for suffix in ["ました", "ます"]:
        if w.endswith(suffix):
            stem = w[: -len(suffix)]
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
            return w[: -len(src)] + dst

    for src, dst in [("かった", "い"), ("くて", "い"), ("くない", "い")]:
        if w.endswith(src) and len(w) > len(src):
            return w[: -len(src)] + dst

    return w


def grammar_hit(rule_id: str):
    rule = GRAMMAR_RULES_BY_ID.get(rule_id)
    return {"label": rule["label"], "explanation": rule["explanation"]} if rule else None


def detect_grammar_in_sentence(sentence: str):
    tagger = get_mecab_tagger()
    found = set()

    if tagger is None:
        # безопасен fallback
        raw_checks = [
            ("te_iru", r"てい(?:る|ます|た|ました)"),
            ("te_oku", r"てお(?:く|き|いた|きます|いた)"),
            ("te_shimau", r"てしま(?:う|います|った|いました)"),
            ("te_miru", r"てみ(?:る|ます|た|ました)"),
            ("nakereba_naranai", r"なければならない"),
            ("nakereba_ikenai", r"なければいけない"),
            ("nakutewa_naranai", r"なくてはならない"),
            ("beki", r"べき"),
            ("hazu_da", r"はず(?:だ|です)"),
            ("kamoshirenai", r"かもしれない"),
            ("souda", r"そう(?:だ|です)"),
            ("rashii", r"らしい"),
            ("youda", r"よう(?:だ|です|に)"),
            ("koto_ga_dekiru", r"ことができ(?:る|ます|た|ました)"),
            ("koto_ni_naru", r"ことにな(?:る|り|った|ります|りました)"),
            ("you_ni_naru", r"ようにな(?:る|り|った|ります|りました)"),
            ("tsumori_da", r"つもり(?:だ|です)"),
            ("to_omou", r"と思(?:う|います|った|いました)"),
            ("to_iu", r"という"),
            ("tame_ni", r"ため(?:に)?"),
            ("nagara", r"ながら"),
            ("tari_tari", r"たり.*たり"),
            ("tai", r"たい"),
        ]
        for rid, pat in raw_checks:
            if re.search(pat, sentence):
                found.add(rid)
        return found

    try:
        tokens = list(tagger(sentence))
    except Exception:
        return found

    n = len(tokens)
    surfaces = [token_surface(t) for t in tokens]
    lemmas = [token_lemma(t) for t in tokens]

    if "たり" in surfaces and surfaces.count("たり") >= 2:
        found.add("tari_tari")

    for i in range(n):
        s = surfaces[i]
        l = lemmas[i]
        cform = token_cform(tokens[i])
        ctype = token_ctype(tokens[i])

        if s == "ない":
            found.add("nai")

        if s == "たい" or l == "たい":
            found.add("tai")

        if s == "ながら":
            found.add("nagara")

        if s == "から":
            found.add("kara_reason")

        if s == "まで":
            found.add("made")

        if s == "に":
            found.add("ni")

        if s == "べき":
            found.add("beki")

        if s == "らしい":
            found.add("rashii")

        if s == "つもり" and i + 1 < n and has_lemma(tokens, i + 1, "だ", "です"):
            found.add("tsumori_da")

        if s in {"て", "で"} and i + 1 < n:
            if has_lemma(tokens, i + 1, "居る", "いる"):
                found.add("te_iru")
                if token_surface(tokens[i + 1]) in {"いた", "いました"} or "連用" in token_cform(tokens[i + 1]):
                    if token_surface(tokens[i + 1]).startswith("い"):
                        found.add("te_ita")
            if has_lemma(tokens, i + 1, "置く", "おく"):
                found.add("te_oku")
            if has_lemma(tokens, i + 1, "仕舞う", "しまう"):
                found.add("te_shimau")
            if has_lemma(tokens, i + 1, "見る", "みる"):
                found.add("te_miru")
            if has_lemma(tokens, i + 1, "上げる", "あげる"):
                found.add("te_ageru")
            if has_lemma(tokens, i + 1, "呉れる", "くれる"):
                found.add("te_kureru")
            if has_lemma(tokens, i + 1, "貰う", "もらう"):
                found.add("te_morau")

        if s == "こと" and i + 2 < n:
            if has_surface(tokens, i + 1, "が") and has_lemma(tokens, i + 2, "出来る", "できる"):
                found.add("koto_ga_dekiru")
            if has_surface(tokens, i + 1, "に") and has_lemma(tokens, i + 2, "成る", "なる"):
                found.add("koto_ni_naru")

        if s == "よう":
            if i + 1 < n and has_surface(tokens, i + 1, "に"):
                found.add("youda")
                if i + 2 < n and has_lemma(tokens, i + 2, "成る", "なる"):
                    found.add("you_ni_naru")
            if i + 1 < n and has_lemma(tokens, i + 1, "だ", "です"):
                found.add("youda")

        if s == "はず" and i + 1 < n and has_lemma(tokens, i + 1, "だ", "です"):
            found.add("hazu_da")

        if s == "そう":
            if i + 1 < n and (has_lemma(tokens, i + 1, "だ", "です") or token_pos1(tokens[i + 1]) == "助動詞"):
                found.add("souda")

        if s == "かも" and i + 2 < n and has_surface(tokens, i + 1, "しれ") and has_surface(tokens, i + 2, "ない"):
            found.add("kamoshirenai")

        if s == "と" and i + 1 < n and has_lemma(tokens, i + 1, "思う", "おもう"):
            found.add("to_omou")

        if s == "という" or (s == "と" and i + 1 < n and has_lemma(tokens, i + 1, "言う", "いう")):
            found.add("to_iu")

        if s == "ため":
            found.add("tame_ni")

        if s == "なけれ" and i + 3 < n and has_surface(tokens, i + 1, "ば"):
            if has_surface(tokens, i + 2, "なら") and has_surface(tokens, i + 3, "ない"):
                found.add("nakereba_naranai")
            if has_surface(tokens, i + 2, "いけ") and has_surface(tokens, i + 3, "ない"):
                found.add("nakereba_ikenai")

        if s == "なく" and i + 3 < n and has_surface(tokens, i + 1, "て") and has_surface(tokens, i + 2, "は"):
            if has_surface(tokens, i + 3, "なら") and i + 4 < n and has_surface(tokens, i + 4, "ない"):
                found.add("nakutewa_naranai")

        # Грубо разпознаване на potential/passive/causative по спрегната форма и лема.
        if "させ" in s or l == "させる":
            found.add("causative_saseru")
        if "られ" in s or l in {"られる", "れる"}:
            found.add("passive_rareru")

        # potential form rough guesses
        if l in {"出来る", "できる"}:
            found.add("potential_rareru")
        if token_pos1(tokens[i]) == "動詞":
            if s.endswith("れる") or s.endswith("られる") or s.endswith("える"):
                found.add("potential_rareru")

        # volitional rough guesses
        if token_pos1(tokens[i]) == "動詞" and (s.endswith("よう") or s.endswith("おう") or "意志推量形" in cform):
            found.add("volitional")

        # extra fallback from conjugation type/form
        if "可能" in ctype or "可能" in cform:
            found.add("potential_rareru")
        if "使役" in ctype or "使役" in cform:
            found.add("causative_saseru")
        if "受身" in ctype or "受身" in cform:
            found.add("passive_rareru")

    return found


def extract_grammar_points(articles):
    found = {}
    for article in articles:
        for block in article.get("blocks", []):
            for sentence in split_japanese_sentences(block.get("text", "")):
                for rule_id in detect_grammar_in_sentence(sentence):
                    if rule_id not in found:
                        hit = grammar_hit(rule_id)
                        if hit:
                            found[rule_id] = hit

    ordered = []
    for rule in GRAMMAR_RULES:
        item = found.get(rule["id"])
        if item:
            ordered.append(item)
    return ordered


def extract_ne_id(text: str) -> str:
    m = re.search(r"(ne\d{10,})", text or "")
    return m.group(1) if m else ""


def get_nhkeasier_items():
    r = requests.get(NHKEASIER_FEED_URL, timeout=20)
    r.raise_for_status()
    soup = BeautifulSoup(r.text, "xml")
    items = {}

    for item in soup.find_all("item"):
        title = (item.title.get_text() if item.title else "").strip()
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

        blocks = get_article_blocks(desc_soup)
        cleaned_blocks = []
        for b in blocks:
            t = b["text"].strip()
            if not t:
                continue
            if t.lower() in {"original", "permalink"} or "Original" in t or "Permalink" in t:
                continue
            cleaned_blocks.append(b)

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

        if not ne_id:
            continue

        items[ne_id] = {
            "title": title,
            "blocks": cleaned_blocks,
            "audio_url": audio_url,
            "image_url": image_url,
            "original_link": original_link,
        }

    return items


def extract_easy_article_links_from_sitemap(n=4):
    r = requests.get(EASY_SITEMAP_URL, timeout=20)
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
    page = requests.get(link, timeout=20)
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

    content = (
        psoup.select_one(".article-main__body")
        or psoup.select_one(".module--content")
        or psoup.select_one("#js-article-body")
        or psoup.select_one(".content--detail-body")
        or psoup.select_one("article")
        or psoup.select_one("main")
    )

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
    translated_blocks = [{
        "html": b["html"],
        "text": b["text"],
        "translation": translate_text(b["text"], dest="bg")
    } for b in filtered_blocks]

    return {
        "title": title,
        "title_html": title_html,
        "title_translation": translate_text(title, dest="bg"),
        "link": link,
        "image_url": image_url,
        "audio_url": audio_url,
        "blocks": translated_blocks,
        "vocab": vocab,
    }


def get_articles(n=4):
    links = extract_easy_article_links_from_sitemap(max(n * 8, n))
    nhkeasier_items = {}
    try:
        nhkeasier_items = get_nhkeasier_items()
    except Exception as e:
        print(f"Could not load nhkeasier fallback feed: {e}")

    articles = []
    for link in links:
        try:
            article = parse_article_from_nhk_easy(link)
            ne_id = extract_ne_id(link)
            fallback = nhkeasier_items.get(ne_id)

            if article and fallback and fallback.get("blocks"):
                article["blocks"] = []
                for b in fallback["blocks"]:
                    article["blocks"].append({
                        "html": b["html"],
                        "text": b["text"],
                        "translation": translate_text(b["text"], dest="bg"),
                    })
                article["vocab"] = extract_vocab_from_blocks(fallback["blocks"])
                if fallback.get("audio_url"):
                    article["audio_url"] = fallback["audio_url"]
                if fallback.get("image_url"):
                    article["image_url"] = fallback["image_url"]
                for b in fallback["blocks"]:
                    if "<ruby" in b["html"]:
                        article["title_html"] = b["html"]
                        break

            has_blocks = bool(article and article.get("blocks"))
            has_vocab = bool(article and article.get("vocab"))
            has_image = bool(article and article.get("image_url"))
            has_audio = bool(article and article.get("audio_url"))

            if article and has_blocks and has_vocab and has_image and has_audio:
                articles.append(article)
                if len(articles) >= n:
                    break
        except Exception as e:
            print(f"Skipping article because of error: {e}")
            continue

    return articles[:n]


def build_html(articles, anki_filename=DEFAULT_ANKI_FILENAME, anki_apkg_filename=DEFAULT_ANKI_APKG_FILENAME, grammar_points=None):
    grammar_points = grammar_points or []
    html = """
<!doctype html>
<html lang="ja">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>最新ニュース</title>
<link rel="manifest" href="manifest.webmanifest">
<link rel="icon" type="image/png" sizes="32x32" href="favicon-32x32.png">
<link rel="icon" type="image/png" sizes="16x16" href="favicon-16x16.png">
<link rel="apple-touch-icon" sizes="180x180" href="apple-touch-icon.png">
<meta name="theme-color" content="#0f1115">
<style>
:root{--bg:#0f1115;--card:#171a21;--card2:#1d212b;--text:#e8ecf1;--muted:#aeb7c2;--accent:#8ab4ff;--border:#2a3040;--jp-panel:#12151c;--trans-text:#d2dae3;--ring-track:#1e222c;--ring-inner:#ffffff;--rt-color:#9fb3c8;--jp-font:"Hiragino Mincho ProN","Hiragino Mincho Pro","Yu Mincho","MS PMincho",serif;}
*{box-sizing:border-box} body{margin:0;background:var(--bg);color:var(--text);font-family:system-ui,-apple-system,BlinkMacSystemFont,"Segoe UI",sans-serif;line-height:1.8;}
body.theme-light{--bg:#f3f4f6;--card:#ffffff;--card2:#f8fafc;--text:#111111;--muted:#4b5563;--accent:#1d4ed8;--border:#d1d5db;--jp-panel:#eef2f7;--trans-text:#111111;--ring-track:#d1d5db;--ring-inner:#ffffff;--rt-color:#5f6f84;}
body.theme-sepia{--bg:#f1e5cf;--card:#f7ebd8;--card2:#efe0c8;--text:#111111;--muted:#3f3a2f;--accent:#8a5a1f;--border:#c8b79a;--jp-panel:#ead9bf;--trans-text:#111111;--ring-track:#c8b79a;--ring-inner:#f7ebd8;--rt-color:#645640;}
.wrap{max-width:980px;margin:0 auto;padding:32px 16px 56px;}
.top-logo{display:block;width:100px;height:100px;margin:0 auto 10px;}
h1{margin:0 0 24px;color:var(--accent);font-size:2rem;text-align:center;}
.font-picker,.theme-picker{display:flex;align-items:center;justify-content:center;gap:10px}
.font-picker{margin:-8px 0 10px}.theme-picker{margin:0 0 22px}
.font-picker label,.theme-picker label{color:var(--muted);font-size:.92rem}
.font-picker select,.theme-picker select{background:var(--card2);color:var(--text);border:1px solid var(--border);border-radius:8px;padding:6px 10px}
article{background:var(--card);border:1px solid var(--border);border-radius:18px;padding:24px;margin-bottom:28px;box-shadow:0 8px 24px rgba(0,0,0,.22);}
h2{margin:0 0 6px;font-size:1.375rem}
.article-head{display:block;margin-bottom:6px}.article-head h2{margin:0;min-width:0;overflow-wrap:anywhere;word-break:break-word;line-height:1.4}
.known-progress{--p:0;--size:59px;width:var(--size);height:var(--size);border-radius:50%;position:relative;margin-top:8px;background:conic-gradient(from -90deg,#5f00ff 0%,#ff005a calc(var(--p) * 1%),var(--ring-track) calc(var(--p) * 1%),var(--ring-track) 100%)}
.known-progress::before{content:"";position:absolute;inset:6px;border-radius:50%;background:var(--ring-inner)}
.known-progress span{position:absolute;inset:0;display:flex;align-items:center;justify-content:center;color:#12151c;font-weight:700;font-size:.9rem;z-index:1}
@media (max-width:700px){.known-progress{--size:52px}}
.article-head h2 rt{font-size:.56em}
.article-media{margin:12px 0 14px}.article-image{width:100%;max-height:420px;object-fit:cover;border-radius:12px;border:1px solid var(--border);display:block;margin-bottom:10px}.article-audio{width:100%}
.meta{margin-bottom:18px;color:var(--muted);font-size:.95rem}.meta a{color:var(--accent);text-decoration:none}
.section-title{margin:20px 0 10px;font-size:1.05rem;color:var(--accent);font-weight:700}
.vocab{background:var(--card2);border:1px solid var(--border);border-radius:14px;padding:16px 18px;margin-bottom:20px}
.vocab ul{margin:10px 0 0;padding-left:20px;columns:2;column-gap:24px}.vocab li{margin:8px 0;break-inside:avoid}
@media (max-width:700px){.vocab ul{columns:1}}
.word{font-weight:700}.meaning{color:var(--muted)}
.jp-block{background:var(--jp-panel);border:1px solid var(--border);border-radius:12px;padding:14px 16px;margin:12px 0 6px;font-size:1.08rem}
.jp-block.is-clickable{cursor:pointer}.jp-block.is-clickable:focus{outline:2px solid var(--accent);outline-offset:2px}
.jp-block.is-clickable::after{content:"  (клик за превод)";color:var(--muted);font-size:.8em}
.bg-block{color:var(--trans-text);padding:0 2px 8px 2px;margin-bottom:8px;border-bottom:1px dashed var(--border);display:none}.bg-block.is-visible{display:block}
ruby{ruby-position:over} rt{font-size:.68em;color:var(--rt-color)}
.downloads{margin-top:20px;text-align:center}.downloads a{color:var(--accent);font-weight:700;text-decoration:none}
.grammar{background:var(--card);border:1px solid var(--border);border-radius:18px;padding:20px;margin-top:20px}
.grammar ul{margin:8px 0 0;padding-left:20px}.grammar li{margin:10px 0}.grammar-rule{font-weight:700}
.contacts{margin-top:18px;text-align:center;color:var(--muted);font-size:.78rem}
h1,.article-head h2,.jp-block,.word,.grammar-rule,ruby,rt{font-family:var(--jp-font)}
</style>
</head>
<body>
<div class="wrap">
<img class="top-logo" src="android-chrome-192x192.png" alt="Logo" width="100" height="100">
<h1>最新ニュース</h1>
<div class="font-picker"><label for="jp-font-select">Японски шрифт</label><select id="jp-font-select"><option value="mincho">Hiragino Mincho</option><option value="sans">Hiragino Sans</option></select></div>
<div class="theme-picker"><label for="theme-select">Тема</label><select id="theme-select"><option value="dark">Dark</option><option value="light">Light</option><option value="sepia">Sepia</option></select></div>
"""
    for article in articles:
        known_percent = int(article.get("known_percent", 0))
        known_count = int(article.get("known_count", 0))
        known_total = int(article.get("known_total", 0))
        progress_title = html_lib.escape(f"Познати думи: {known_count}/{known_total}")
        html += "<article>"
        html += "<div class='article-head'>"
        html += f"<h2>{article.get('title_html', article['title'])}</h2>"
        html += f"<div class='known-progress' style='--p:{known_percent};' title='{progress_title}' aria-label='{progress_title}'><span>{known_percent}%</span></div>"
        html += "</div>"
        html += f"<div class='meta'>{article['title_translation'] or ''}</div>"

        if article.get("image_url") or article.get("audio_url"):
            html += "<div class='article-media'>"
            if article.get("image_url"):
                html += f"<img class='article-image' src='{article['image_url']}' alt='{article['title']}' loading='lazy'/>"
            if article.get("audio_url"):
                html += f"<audio class='article-audio' controls preload='none' src='{article['audio_url']}'></audio>"
            html += "</div>"

        html += "<div class='section-title'>Речник</div><div class='vocab'><ul>"
        for item in article["vocab"]:
            word, reading, meaning = item["word"], item["reading"], item["meaning"]
            word_html = f"<ruby>{word}<rt>{reading}</rt></ruby>" if reading else word
            html += f"<li><span class='word'>{word_html}</span>{(' — <span class=\"meaning\">' + meaning + '</span>') if meaning else ''}</li>"
        html += "</ul></div><div class='section-title'>Текст</div>"

        for block in article["blocks"]:
            html += f"<div class='jp-block'>{block['html']}</div>"
            if block["translation"]:
                html += f"<div class='bg-block'>{block['translation']}</div>"
        html += "</article>"

    html += f"<div class='downloads'><a href='{anki_apkg_filename}' download>Свали Anki Карти</a> | <a href='{anki_filename}' download>TSV (backup)</a></div>"

    if grammar_points:
        html += "<section class='grammar'><div class='section-title'>Граматика в текстовете</div><ul>"
        for g in grammar_points:
            html += f"<li><span class='grammar-rule'>{g['label']}</span> — {g['explanation']}</li>"
        html += "</ul></section>"

    html += """
<div class='contacts'>Contacts: vebaev (at) gmail.com</div>
</div>
<script>
document.addEventListener('DOMContentLoaded', function() {
  if ('serviceWorker' in navigator) {
    window.addEventListener('load', function() {
      navigator.serviceWorker.register('./sw.js').catch(function() {});
    });
  }
  var jpFontSelect = document.getElementById('jp-font-select');
  var themeSelect = document.getElementById('theme-select');
  var rootStyle = document.documentElement.style;
  var jpFonts = {
    sans: '"Hiragino Sans","Hiragino Kaku Gothic ProN","Yu Gothic","Meiryo",sans-serif',
    mincho: '"Hiragino Mincho ProN","Hiragino Mincho Pro","Yu Mincho","MS PMincho",serif'
  };
  function applyJpFont(mode){
    var selected = jpFonts[mode] ? mode : 'mincho';
    rootStyle.setProperty('--jp-font', jpFonts[selected]);
    if (jpFontSelect) jpFontSelect.value = selected;
    try { localStorage.setItem('jpFontMode', selected); } catch (e) {}
  }
  if (jpFontSelect) {
    var savedFont = 'mincho';
    try { savedFont = localStorage.getItem('jpFontMode') || 'mincho'; } catch (e) {}
    applyJpFont(savedFont);
    jpFontSelect.addEventListener('change', function(){ applyJpFont(jpFontSelect.value); });
  }
  function applyTheme(mode){
    var selected = (mode === 'light' || mode === 'sepia') ? mode : 'dark';
    document.body.classList.remove('theme-dark', 'theme-light', 'theme-sepia');
    document.body.classList.add('theme-' + selected);
    if (themeSelect) themeSelect.value = selected;
    try { localStorage.setItem('themeMode', selected); } catch (e) {}
  }
  var savedTheme = 'dark';
  try { savedTheme = localStorage.getItem('themeMode') || 'dark'; } catch (e) {}
  applyTheme(savedTheme);
  if (themeSelect) themeSelect.addEventListener('change', function(){ applyTheme(themeSelect.value); });

  document.querySelectorAll('article').forEach(function(article) {
    var h2 = article.querySelector('h2');
    var firstJpBlock = article.querySelector('.jp-block');
    if (!h2 || !firstJpBlock) return;
    if (h2.querySelector('ruby')) return;
    if (!firstJpBlock.querySelector('ruby')) return;
    h2.innerHTML = firstJpBlock.innerHTML;
  });

  document.querySelectorAll('.jp-block + .bg-block').forEach(function(bgBlock) {
    var jpBlock = bgBlock.previousElementSibling;
    if (!jpBlock) return;
    jpBlock.classList.add('is-clickable');
    jpBlock.setAttribute('role', 'button');
    jpBlock.setAttribute('tabindex', '0');
    jpBlock.setAttribute('aria-expanded', 'false');
    function toggleTranslation() {
      var isVisible = bgBlock.classList.toggle('is-visible');
      jpBlock.setAttribute('aria-expanded', isVisible ? 'true' : 'false');
    }
    jpBlock.addEventListener('click', toggleTranslation);
    jpBlock.addEventListener('keydown', function(event) {
      if (event.key === 'Enter' || event.key === ' ') {
        event.preventDefault();
        toggleTranslation();
      }
    });
  });
});
</script>
</body>
</html>
"""
    return html


def main():
    global DEEPL_API_KEY

    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default=DEFAULT_OUTPUT)
    parser.add_argument("--count", type=int, default=4)
    parser.add_argument("--deepl-key", default=os.environ.get("DEEPL_API_KEY", ""))
    args = parser.parse_args()
    DEEPL_API_KEY = (args.deepl_key or "").strip()

    articles = get_articles(args.count)
    if not articles:
        raise RuntimeError("No articles were extracted.")

    print(f"Translation provider usage: DeepL={_TRANSLATION_STATS['deepl']} Google={_TRANSLATION_STATS['google']}")

    output_dir = os.path.dirname(args.output)
    if output_dir:
        os.makedirs(output_dir, exist_ok=True)

    grammar_points = extract_grammar_points(articles)

    anki_filename = DEFAULT_ANKI_FILENAME
    anki_apkg_filename = DEFAULT_ANKI_APKG_FILENAME
    anki_seen_words_filename = DEFAULT_ANKI_SEEN_WORDS_FILENAME
    if output_dir:
        anki_path = os.path.join(output_dir, anki_filename)
        anki_apkg_path = os.path.join(output_dir, anki_apkg_filename)
        anki_seen_words_path = os.path.join(output_dir, anki_seen_words_filename)
    else:
        anki_path = anki_filename
        anki_apkg_path = anki_apkg_filename
        anki_seen_words_path = anki_seen_words_filename

    seen_words = load_seen_words(anki_seen_words_path)
    add_known_progress_to_articles(articles, seen_words)
    anki_cards, newly_added_words = build_anki_cards(articles, grammar_points=grammar_points, seen_items=seen_words)
    save_anki_tsv(anki_cards, anki_path)
    build_anki_apkg(anki_cards, anki_apkg_path)
    save_seen_words(anki_seen_words_path, seen_words | newly_added_words)

    html = build_html(articles, anki_filename=anki_filename, anki_apkg_filename=anki_apkg_filename, grammar_points=grammar_points)
    with open(args.output, "w", encoding="utf-8") as f:
        f.write(html)


if __name__ == "__main__":
    main()
