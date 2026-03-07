#!/usr/bin/env python3
from __future__ import annotations

import argparse
import datetime as dt
import html
import json
import re
import sys
import time
import xml.etree.ElementTree as ET
from dataclasses import dataclass
from pathlib import Path
from typing import Iterable
from urllib.parse import urljoin

import requests
from bs4 import BeautifulSoup

FEED_URL = "https://nhkeasier.com/feed/"
DEFAULT_OUTPUT = "docs/index.html"
USER_AGENT = "Mozilla/5.0 (compatible; NHKEasyPipeline/1.0; +https://github.com/)"
TIMEOUT = 30


@dataclass
class NewsItem:
    title: str
    link: str
    published: str
    paragraphs_html: list[str]
    glossary: list[tuple[str, str, str]]


def fetch(url: str) -> str:
    r = requests.get(url, headers={"User-Agent": USER_AGENT}, timeout=TIMEOUT)
    r.raise_for_status()
    return r.text


def parse_feed(feed_xml: str, count: int) -> list[tuple[str, str, str]]:
    root = ET.fromstring(feed_xml)
    channel = root.find("channel")
    if channel is None:
        raise RuntimeError("RSS channel not found")
    items = []
    for item in channel.findall("item")[:count]:
        title = (item.findtext("title") or "").strip()
        link = (item.findtext("link") or "").strip()
        pubdate = (item.findtext("pubDate") or "").strip()
        if link:
            items.append((title, link, pubdate))
    return items


def rubyize_html(fragment: str) -> str:
    """Convert patterns like 漢字(かんじ) into ruby markup, preserving existing HTML."""
    def repl(match: re.Match[str]) -> str:
        base = match.group(1)
        reading = match.group(2)
        return f"<ruby>{html.escape(base)}<rt>{html.escape(reading)}</rt></ruby>"

    # Only convert likely Japanese bases; avoid numbers/URLs/etc.
    return re.sub(r"([一-龯々ヶ〆ヵぁ-んァ-ヴー]+)\(([ぁ-んァ-ヴー]+)\)", repl, fragment)


GLOSSARY_PATTERN = re.compile(r"([一-龯々ヶ〆ヵぁ-んァ-ヴー]+)\(([ぁ-んァ-ヴー]+)\)")


def extract_terms(text: str) -> list[tuple[str, str]]:
    seen: set[tuple[str, str]] = set()
    out: list[tuple[str, str]] = []
    for base, reading in GLOSSARY_PATTERN.findall(text):
        key = (base, reading)
        if key not in seen:
            seen.add(key)
            out.append(key)
    return out


def load_overrides(path: Path | None) -> dict[str, str]:
    if not path or not path.exists():
        return {}
    with path.open("r", encoding="utf-8") as f:
        data = json.load(f)
    return {str(k): str(v) for k, v in data.items()}


def build_glossary(paragraphs_text: Iterable[str], overrides: dict[str, str], max_terms: int) -> list[tuple[str, str, str]]:
    ordered_terms: list[tuple[str, str]] = []
    seen: set[tuple[str, str]] = set()
    for text in paragraphs_text:
        for base, reading in extract_terms(text):
            if (base, reading) not in seen:
                seen.add((base, reading))
                ordered_terms.append((base, reading))
    glossary = []
    for base, reading in ordered_terms[:max_terms]:
        meaning = overrides.get(base) or overrides.get(f"{base}|{reading}") or ""
        glossary.append((base, reading, meaning))
    return glossary


def parse_article(url: str, fallback_title: str, published: str, overrides: dict[str, str], max_terms: int) -> NewsItem:
    page = fetch(url)
    soup = BeautifulSoup(page, "html.parser")

    title = fallback_title
    h1 = soup.find(["h1", "h2"], class_=re.compile("title|entry-title", re.I)) or soup.find("h1")
    if h1:
        title = h1.get_text(" ", strip=True)

    content = soup.find(class_=re.compile("entry-content|post-content|article-body", re.I)) or soup
    paragraphs = []
    for p in content.find_all("p"):
        text = p.get_text(" ", strip=True)
        if not text:
            continue
        if len(text) < 8:
            continue
        paragraphs.append(text)

    if not paragraphs:
        raise RuntimeError(f"No paragraphs found in {url}")

    ruby_paragraphs = [rubyize_html(html.escape(p)) for p in paragraphs]
    glossary = build_glossary(paragraphs, overrides, max_terms=max_terms)
    return NewsItem(title=title, link=url, published=published, paragraphs_html=ruby_paragraphs, glossary=glossary)


CSS = """
:root {
  color-scheme: dark;
  --bg: #0b0f14;
  --panel: #121923;
  --panel-2: #182230;
  --text: #e8eef7;
  --muted: #9fb0c7;
  --border: #2a394d;
  --accent: #7cc4ff;
  --accent-2: #b7f0c0;
}
* { box-sizing: border-box; }
body {
  margin: 0;
  font-family: Inter, ui-sans-serif, system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
  background: linear-gradient(180deg, #091017 0%, var(--bg) 100%);
  color: var(--text);
  line-height: 1.75;
}
.container {
  max-width: 1100px;
  margin: 0 auto;
  padding: 32px 20px 80px;
}
header {
  margin-bottom: 28px;
}
header h1 {
  margin: 0 0 10px;
  font-size: 2rem;
}
header p {
  margin: 0;
  color: var(--muted);
}
.card {
  background: linear-gradient(180deg, var(--panel) 0%, var(--panel-2) 100%);
  border: 1px solid var(--border);
  border-radius: 18px;
  padding: 22px;
  box-shadow: 0 10px 30px rgba(0,0,0,.25);
  margin-bottom: 22px;
}
.meta {
  color: var(--muted);
  font-size: .95rem;
  margin-bottom: 10px;
}
h2 {
  margin: 0 0 14px;
  font-size: 1.45rem;
}
a { color: var(--accent); text-decoration: none; }
a:hover { text-decoration: underline; }
.glossary-title, .text-title {
  font-size: 1rem;
  letter-spacing: .02em;
  color: var(--accent-2);
  margin: 18px 0 10px;
  font-weight: 700;
}
.table-wrap { overflow-x: auto; }
table {
  width: 100%;
  border-collapse: collapse;
  border: 1px solid var(--border);
  border-radius: 12px;
  overflow: hidden;
  background: rgba(255,255,255,.02);
}
th, td {
  padding: 10px 12px;
  border-bottom: 1px solid var(--border);
  text-align: left;
  vertical-align: top;
}
th {
  color: var(--muted);
  font-weight: 600;
  background: rgba(255,255,255,.03);
}
.jp {
  font-size: 1.16rem;
  margin: 0 0 14px;
}
ruby { ruby-position: over; }
rt {
  font-size: .58em;
  color: #9fd8ff;
  font-weight: 500;
}
footer {
  margin-top: 28px;
  color: var(--muted);
  font-size: .92rem;
}
.badge {
  display: inline-block;
  padding: 4px 10px;
  border: 1px solid var(--border);
  border-radius: 999px;
  color: var(--muted);
  margin-right: 8px;
  margin-bottom: 8px;
}
"""


def render_html(items: list[NewsItem], generated_at: str) -> str:
    cards = []
    for idx, item in enumerate(items, start=1):
        rows = "\n".join(
            f"<tr><td>{html.escape(base)}</td><td>{html.escape(reading)}</td><td>{html.escape(meaning)}</td></tr>"
            for base, reading, meaning in item.glossary
        ) or '<tr><td colspan="3">No glossary terms found.</td></tr>'
        paragraphs = "\n".join(f'<p class="jp">{p}</p>' for p in item.paragraphs_html)
        cards.append(
            f"""
            <section class=\"card\">
              <div class=\"meta\">Article {idx} · {html.escape(item.published)}</div>
              <h2><a href=\"{html.escape(item.link)}\">{html.escape(item.title)}</a></h2>
              <div class=\"glossary-title\">Vocabulary</div>
              <div class=\"table-wrap\">
                <table>
                  <thead><tr><th>Word</th><th>Reading</th><th>Meaning</th></tr></thead>
                  <tbody>{rows}</tbody>
                </table>
              </div>
              <div class=\"text-title\">Text</div>
              {paragraphs}
            </section>
            """
        )
    return f"""<!doctype html>
<html lang=\"en\">
<head>
  <meta charset=\"utf-8\" />
  <meta name=\"viewport\" content=\"width=device-width, initial-scale=1\" />
  <title>NHK Easy Daily Digest</title>
  <style>{CSS}</style>
</head>
<body>
  <main class=\"container\">
    <header>
      <div class=\"badge\">Dark mode</div>
      <div class=\"badge\">Ruby furigana</div>
      <div class=\"badge\">Daily generated</div>
      <h1>NHK Easy Daily Digest</h1>
      <p>Generated at {html.escape(generated_at)}. Vocabulary appears before each article. Furigana is rendered with HTML ruby.</p>
    </header>
    {''.join(cards)}
    <footer>
      Source pages are linked in each article title. This page is generated automatically.
    </footer>
  </main>
</body>
</html>
"""


def main() -> int:
    parser = argparse.ArgumentParser(description="Generate a dark-mode NHK Easy daily digest HTML page.")
    parser.add_argument("--output", default=DEFAULT_OUTPUT, help="Output HTML path")
    parser.add_argument("--count", type=int, default=3, help="Number of latest articles to include")
    parser.add_argument("--glossary-overrides", default="glossary_overrides.json", help="Path to JSON glossary overrides")
    parser.add_argument("--max-glossary-terms", type=int, default=15, help="Max glossary terms per article")
    args = parser.parse_args()

    output_path = Path(args.output)
    overrides = load_overrides(Path(args.glossary_overrides))

    feed_xml = fetch(FEED_URL)
    feed_items = parse_feed(feed_xml, args.count)
    if not feed_items:
        raise RuntimeError("No feed items found")

    news_items = []
    for title, link, published in feed_items:
        try:
            news_items.append(parse_article(link, title, published, overrides, args.max_glossary_terms))
            time.sleep(1)
        except Exception as exc:
            print(f"Failed to parse {link}: {exc}", file=sys.stderr)

    if not news_items:
        raise RuntimeError("All articles failed to parse")

    output_path.parent.mkdir(parents=True, exist_ok=True)
    generated_at = dt.datetime.utcnow().strftime("%Y-%m-%d %H:%M UTC")
    output_path.write_text(render_html(news_items, generated_at), encoding="utf-8")
    print(f"Wrote {output_path}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
