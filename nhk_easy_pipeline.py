import requests
from bs4 import BeautifulSoup
from jamdict import Jamdict
import re

RSS = "https://nhkeasier.com/feed/"
OUTPUT = "docs/index.html"

jam = Jamdict()

def get_articles(n=3):
    r = requests.get(RSS)
    soup = BeautifulSoup(r.text, "xml")

    items = soup.find_all("item")[:n]

    articles = []

    for i in items:
        link = i.link.text
        title = i.title.text

        page = requests.get(link)
        psoup = BeautifulSoup(page.text, "html.parser")

        content = psoup.select_one(".entry-content")
        text = content.get_text()

        articles.append({
            "title": title,
            "text": text
        })

    return articles


def extract_words(text):

    words = set(re.findall(r"[一-龯]+", text))

    vocab = []

    for w in words:
        result = jam.lookup(w)

        if result.entries:
            meaning = result.entries[0].senses[0].gloss[0]
            reading = result.entries[0].kana_forms[0].text
            vocab.append((w, reading, meaning))

    return vocab


def ruby(word, reading):
    return f"<ruby>{word}<rt>{reading}</rt></ruby>"


def build_html(articles):

    html = """
<html>
<head>
<meta charset="UTF-8">
<style>
body{
background:#111;
color:#eee;
font-family:sans-serif;
line-height:1.7;
padding:40px;
max-width:900px;
margin:auto;
}
h1{color:#8ab4ff}
article{margin-bottom:60px}
ruby rt{color:#aaa;font-size:0.7em}
.vocab{
background:#1b1b1b;
padding:20px;
border-radius:8px;
margin-bottom:20px;
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

        html += "<div class='vocab'><b>Vocabulary</b><ul>"

        for w,r,m in vocab[:20]:
            html += f"<li>{ruby(w,r)} — {m}</li>"

        html += "</ul></div>"

        html += f"<p>{a['text']}</p>"

        html += "</article>"

    html += "</body></html>"

    return html


def main():

    articles = get_articles()

    html = build_html(articles)

    with open(OUTPUT,"w",encoding="utf8") as f:
        f.write(html)


if __name__ == "__main__":
    main()
