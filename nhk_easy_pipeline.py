import requests
from bs4 import BeautifulSoup
import re
import os
import argparse

RSS = "https://nhkeasier.com/feed/"
OUTPUT = "docs/index.html"


def get_articles(n=3):
    r = requests.get(RSS, timeout=20)
    r.raise_for_status()

    soup = BeautifulSoup(r.text, "xml")
    items = soup.find_all("item")[:n]

    articles = []

    for i in items:
        try:
            link = i.link.text.strip()
            title = i.title.text.strip()

            page = requests.get(link, timeout=20)
            page.raise_for_status()
            psoup = BeautifulSoup(page.text, "html.parser")

            content = (
                psoup.select_one(".entry-content")
                or psoup.select_one("article")
                or psoup.select_one("main")
                or psoup.body
            )

            if content is None:
                print(f"Skipping article, no content found: {link}")
                continue

            for bad in content.select("script, style, nav, footer, header, aside"):
                bad.decompose()

            paragraphs = []
            for p in content.find_all(["p", "h2", "h3", "li"]):
                txt = p.get_text(" ", strip=True)
                if txt:
                    paragraphs.append(txt)

            text = "\n".join(paragraphs) if paragraphs else content.get_text("\n", strip=True)

            if not text.strip():
                print(f"Skipping article, empty text: {link}")
                continue

            articles.append({
                "title": title,
                "text": text,
                "link": link,
            })

        except Exception as e:
            print(f"Skipping article because of error: {e}")
            continue

    return articles


def extract_words(text):
    words = sorted(set(re.findall(r"[一-龯ぁ-んァ-ンー]{2,}", text)))

    vocab = []
    for w in words[:20]:
        vocab.append((w, "", ""))

    return vocab


def ruby(word, reading):
    return f"<ruby>{word}<rt>{reading}</rt></ruby>"


def build_html(articles):
    html = """
<!doctype html>
<html lang="ja">
<head>
<meta charset="UTF-8">
<meta name="viewport" content="width=device-width, initial-scale=1.0">
<title>NHK Easy Reader</title>
<style>
body{
    background:#111;
    color:#eee;
    font-family: system-ui, -apple-system, BlinkMacSystemFont, "Segoe UI", sans-serif;
    line-height:1.8;
    padding:40px 20px;
    max-width:900px;
    margin:auto;
}
h1{color:#8ab4ff}
h2{margin-top:0}
article{
    margin-bottom:60px;
    background:#181818;
    padding:24px;
    border-radius:14px;
    box-shadow:0 2px 12px rgba(0,0,0,.25);
}
ruby rt{
    color:#aaa;
    font-size:0.7em;
}
.vocab{
    background:#1f1f1f;
    padding:16px 20px;
    border-radius:10px;
    margin-bottom:20px;
}
.vocab ul{
    margin:10px 0 0 0;
    padding-left:20px;
}
p{
    white-space:pre-line;
}
a{
    color:#8ab4ff;
}
.meta{
    color:#aaa;
    font-size:.95rem;
    margin-bottom:14px;
}
</style>
</head>
<body>
<h1>NHK Easy Reader</h1>
"""

    for a in articles:
        vocab = extract_words(a["text"])

        html += "<article>"
        html += f"<h2>{a['title']}</h2>"
        html += f"<div class='meta'><a href='{a['link']}' target='_blank' rel='noopener noreferrer'>Source article</a></div>"

        html += "<div class='vocab'><b>Vocabulary</b><ul>"
        for w, r, m in vocab[:20]:
            if r:
                word_html = ruby(w, r)
            else:
                word_html = w

            if m:
                html += f"<li>{word_html} — {m}</li>"
            else:
                html += f"<li>{word_html}</li>"
        html += "</ul></div>"

        html += f"<p>{a['text']}</p>"
        html += "</article>"

    html += "</body></html>"
    return html


def main():
    parser = argparse.ArgumentParser()
    parser.add_argument("--output", default=OUTPUT)
    parser.add_argument("--count", type=int, default=3)
    args = parser.parse_args()

    articles = get_articles(args.count)

    if not articles:
        raise RuntimeError("No articles were extracted.")

    html = build_html(articles)

    output_dir = os.path.dirname(args.output)
    if output_dir:
        os.makedirs(output_dir, exist_ok=True)

    with open(args.output, "w", encoding="utf8") as f:
        f.write(html)


if __name__ == "__main__":
    main()
