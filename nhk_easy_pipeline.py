
import os, re, argparse, html as html_lib, hashlib, json, uuid
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

EASY_SITEMAP_URL = 'https://news.web.nhk/news/easy/sitemap/sitemap.xml'
NHKEASIER_FEED_URL = 'https://nhkeasier.com/feed/'
DEFAULT_OUTPUT = 'docs/index.html'
DEFAULT_ANKI_FILENAME = 'anki_cards.tsv'
DEFAULT_ANKI_APKG_FILENAME = 'nhk_easy_vocab.apkg'
DEFAULT_ANKI_SEEN_WORDS_FILENAME = 'anki_seen_words.json'
translator = Translator()
DEEPL_API_KEY = os.environ.get('DEEPL_API_KEY', '').strip()
_TRANSLATION_CACHE = {}
_MECAB_TAGGER = None
PARTICLE_PREFIXES = ('が','を','に','で','は','と','へ','や','も','の')
GODAN_I_TO_U = {'い':'う','き':'く','ぎ':'ぐ','し':'す','ち':'つ','に':'ぬ','び':'ぶ','み':'む','り':'る'}
GODAN_A_TO_U = {'わ':'う','か':'く','が':'ぐ','さ':'す','た':'つ','な':'ぬ','ば':'ぶ','ま':'む','ら':'る'}

GRAMMAR_RULES = [
 {'id':'kedo','label':'けど / けれど (Clause + けど)','explanation':'Съюз за противопоставяне: но / обаче.'},
 {'id':'shikashi','label':'しかし (sentence connector)','explanation':'Обаче / въпреки това.'},
 {'id':'temo','label':'〜ても / 〜でも (V/A/N + ても・でも)','explanation':'Дори ако / дори и да.'},
 {'id':'nagara','label':'〜ながら (V-ますstem + ながら)','explanation':'Едновременно действие: докато...'},
 {'id':'tsutsu','label':'〜つつ (V-ますstem + つつ)','explanation':'Докато..., в хода на...'},
 {'id':'aida_ni','label':'間 / あいだ(に) (Clause/N + 間(に))','explanation':'Докато / през времето, когато...'},
 {'id':'uchi_ni','label':'うちに (Clause + うちに)','explanation':'Докато все още..., преди да се промени...'},
 {'id':'kara_reason','label':'〜から (Clause + から)','explanation':'Причина: защото / понеже.'},
 {'id':'node','label':'〜ので (Clause + ので)','explanation':'Причина: тъй като / понеже.'},
 {'id':'de_reason','label':'〜で (N/na-A + で)','explanation':'Причина/основание или средство.'},
 {'id':'sorede','label':'それで (sentence connector)','explanation':'И затова / поради това.'},
 {'id':'soshite','label':'そして (sentence connector)','explanation':'И / и след това.'},
 {'id':'yori','label':'〜より (X より Y)','explanation':'Сравнение: по-... от...'},
 {'id':'hou','label':'〜方 (X の方 / V-辞書形 + 方)','explanation':'Страна / начин; използва се и в сравнения.'},
 {'id':'hou_ga_ii','label':'〜方がいい (V-辞書形 / V-ない形 + 方がいい)','explanation':'По-добре е да...'},
 {'id':'noni','label':'〜のに (Clause + のに)','explanation':'Въпреки че / макар че.'},
 {'id':'you_ni','label':'〜ように (Clause + ように)','explanation':'Така че да..., по начин, че...'},
 {'id':'tame_ni','label':'〜ため(に) (N/Clause + ため(に))','explanation':'За да..., заради..., в името на...'},
 {'id':'sei_de','label':'〜せいで (N/Clause + せいで)','explanation':'По вина на..., заради (негативно).'},
 {'id':'okage_de','label':'〜おかげで (N/Clause + おかげで)','explanation':'Благодарение на...'},
 {'id':'mitai','label':'〜みたい (N/Clause + みたい)','explanation':'Изглежда като / сякаш.'},
 {'id':'rashii','label':'〜らしい (N/Clause + らしい)','explanation':'Изглежда / явно / характерно за.'},
 {'id':'ppoi','label':'〜っぽい (N stem + っぽい)','explanation':'Прилича на..., има оттенък на...'},
 {'id':'sou','label':'〜そう (V-ますstem/A-stem + そうだ)','explanation':'Изглежда, че... / на вид...'},
 {'id':'dame','label':'だめ (predicate)','explanation':'Не става / не бива / забранено е.'},
 {'id':'naranai','label':'〜ならない (...てはならない / なければならない)','explanation':'Не бива / не става; в комбинации може да означава задължение.'},
 {'id':'ikenai','label':'〜いけない (...てはいけない / なければいけない)','explanation':'Не бива / не става; в комбинации може да означава задължение.'},
 {'id':'nakereba_naranai','label':'〜なければならない (V-ない + ければならない)','explanation':'Трябва да...'},
 {'id':'nakereba_ikenai','label':'〜なければいけない (V-ない + ければいけない)','explanation':'Трябва да...'},
 {'id':'nakutewa_naranai','label':'〜なくてはならない (V-ない + くてはならない)','explanation':'Трябва да...'},
 {'id':'tari_tari','label':'〜たり〜たりする (V-た + り ... V-た + りする)','explanation':'Правя разни неща като...'},
 {'id':'dake','label':'〜だけ (X + だけ)','explanation':'Само / единствено.'},
 {'id':'nomi','label':'〜のみ (X + のみ)','explanation':'Само / единствено (по-формално).'},
 {'id':'bakari','label':'〜ばかり (X + ばかり)','explanation':'Само..., все...'},
 {'id':'shika_nai','label':'〜しか〜ない (X + しか + negative)','explanation':'Нищо друго освен..., само...'},
 {'id':'mou','label':'もう (adverb)','explanation':'Вече.'},
 {'id':'mada','label':'まだ (adverb)','explanation':'Още / все още.'},
 {'id':'mata','label':'また (adverb)','explanation':'Пак / отново / също така.'},
 {'id':'te_ii','label':'〜ていい / 〜でいい (V-te + いい)','explanation':'Разрешено е да... / приемливо е да...'},
 {'id':'temo_ii','label':'〜てもいい / 〜でもいい (V-te + も + いい)','explanation':'Може да... / разрешено е да...'},
 {'id':'to_suru','label':'〜とする (Clause + とする)','explanation':'Да приемем, че... / да считаме за... / правя като...'},
 {'id':'you_to_suru','label':'〜ようとする (V-意向形 + とする)','explanation':'Да се опитам да започна / на път да...'},
 {'id':'te_miru','label':'〜てみる (V-te + みる)','explanation':'Да пробвам да...'},
 {'id':'kke','label':'〜っけ (sentence-final)','explanation':'Беше ли..., как беше...'},
 {'id':'kana','label':'〜かな (sentence-final)','explanation':'Чудя се дали..., дали...'},
 {'id':'kai_dai','label':'〜かい / 〜だい (sentence-final)','explanation':'Разговорна въпросителна форма.'},
 {'id':'janai','label':'〜じゃない (sentence-final / tag)','explanation':'Не е ли..., нали...'},
 {'id':'jan','label':'〜じゃん (sentence-final)','explanation':'Нали / ето че / не е ли така.'},
 {'id':'causative_saseru','label':'使役 〜させる / 〜せる (V causative)','explanation':'Каузатив: карам/оставям някого да...'},
 {'id':'naru','label':'〜なる (N/Adj + になる)','explanation':'Става / оказва се / превръща се.'},
 {'id':'adverb_suru','label':'<наречие> + する (Adv + する)','explanation':'Наречие плюс する.'},
 {'id':'jibun','label':'自分 (reflexive marker)','explanation':'Себе си / собствен.'},
 {'id':'nakute','label':'〜なくて (V/A-ない + くて)','explanation':'Без да..., не и..., понеже не...'},
 {'id':'naide','label':'〜ないで (V-ない + で)','explanation':'Без да..., не правейки...'},
 {'id':'zu','label':'〜ず / 〜ずに (V-ない stem + ず(に))','explanation':'Без да...'},
 {'id':'te_shimau','label':'〜てしまう / 〜でしまう (V-te + しまう)','explanation':'Завършеност или нежелан резултат.'},
 {'id':'te_oku','label':'〜ておく / 〜でおく (V-te + おく)','explanation':'Правя нещо предварително.'},
 {'id':'te_iku','label':'〜ていく / 〜でいく (V-te + いく)','explanation':'Посока напред / развитие занапред.'},
 {'id':'te_kuru','label':'〜てくる / 〜でくる (V-te + くる)','explanation':'Идване / развитие към говорещия / до настоящето.'},
 {'id':'datte','label':'だって (connector / quotative)','explanation':'Защото..., дори..., цитирам / оправдавам се.'},
 {'id':'wake','label':'〜わけ (N/Clause + わけ)','explanation':'Причина / смисъл / следва, че...'},
 {'id':'hazu','label':'〜はず (Clause + はずだ)','explanation':'Би трябвало / очаква се.'},
 {'id':'beki','label':'〜べき (V-dictionary + べき)','explanation':'Трябва / редно е.'},
 {'id':'beki_datta','label':'〜べきだった (V-dictionary + べきだった)','explanation':'Трябвало е да...'},
 {'id':'beshi','label':'〜べし (classical / written)','explanation':'Трябва / следва (книжовно).'},
 {'id':'mono_da','label':'〜ものだ (Clause + ものだ)','explanation':'По принцип така е / естествено е / подобава.'},
 {'id':'kamoshirenai','label':'〜かもしれない (Clause + かもしれない)','explanation':'Може би...'},
 {'id':'kamo','label':'〜かも (Clause + かも)','explanation':'Може би... (разговорно).'},
 {'id':'koro','label':'〜ころ (time marker)','explanation':'Около даден момент / по времето, когато...'},
 {'id':'goro','label':'〜ごろ (time marker)','explanation':'Около (час/период).'},
 {'id':'kurai_gurai','label':'〜くらい / 〜ぐらい (amount / degree)','explanation':'Около / приблизително / до такава степен.'},
 {'id':'made','label':'〜まで (limit marker)','explanation':'До / чак до.'},
 {'id':'kara_made','label':'〜から〜まで (from ... to ...)','explanation':'От... до...'},
 {'id':'made_ni','label':'〜までに (deadline)','explanation':'До (краен срок).'},
 {'id':'hodo','label':'〜ほど (degree / extent)','explanation':'До такава степен / колкото...'},
 {'id':'sugiru','label':'〜すぎる (V/A-stem + すぎる)','explanation':'Прекалено / твърде много.'},
 {'id':'shichimi','label':'七味（しちみ） (lexical item)','explanation':'Лексикална единица: „седем вкуса“ / смес от подправки.'},
]
GRAMMAR_RULES_BY_ID = {r['id']: r for r in GRAMMAR_RULES}

def grammar_hit(rule_id):
    rule = GRAMMAR_RULES_BY_ID.get(rule_id)
    return {'label': rule['label'], 'explanation': rule['explanation']} if rule else None

def get_article_blocks(content):
    blocks=[]
    for el in content.find_all(['p','h2','h3','li'], recursive=True):
        txt=el.get_text(' ', strip=True)
        if txt and len(txt)>=3:
            blocks.append({'text':txt,'html':' '.join(str(x) for x in el.contents).strip()})
    return blocks

def get_mecab_tagger():
    global _MECAB_TAGGER
    if _MECAB_TAGGER is not None: return _MECAB_TAGGER
    if fugashi is None: return None
    try: _MECAB_TAGGER = fugashi.Tagger()
    except Exception: _MECAB_TAGGER = None
    return _MECAB_TAGGER

def token_feature(token): return getattr(token,'feature',None)
def token_surface(token): return getattr(token,'surface','') or ''
def token_lemma(token):
    feat=token_feature(token)
    if feat is None: return ''
    for name in ('lemma','dictionary_form','lemma_form','orthBase'):
        value=getattr(feat,name,'') or ''
        if value: return value.strip()
    return ''
def is_target_pos(token):
    feat=token_feature(token); pos1=getattr(feat,'pos1','') if feat is not None else ''
    return pos1 in {'動詞','形容詞'} or '動詞' in str(feat) or '形容詞' in str(feat)
def _s(tokens, idx): return token_surface(tokens[idx]) if 0 <= idx < len(tokens) else ''
def _l(tokens, idx): return token_lemma(tokens[idx]) if 0 <= idx < len(tokens) else ''
def _seq(tokens, start, end): return [token_surface(t) for t in tokens[start:end]]

def lemmatize_japanese(word):
    w=(word or '').strip()
    if not w: return w
    tagger=get_mecab_tagger()
    if tagger is None: return to_dictionary_form(w)
    try:
        tokens=list(tagger(w))
        if len(tokens)==1 and is_target_pos(tokens[0]):
            lemma=token_lemma(tokens[0])
            if lemma and lemma not in {'*',w}: return lemma
    except Exception:
        pass
    return to_dictionary_form(w)

def extract_following_okurigana(ruby_tag):
    sibling=ruby_tag.next_sibling
    while sibling is not None:
        txt=''
        if isinstance(sibling,str): txt=sibling
        elif hasattr(sibling,'get_text'): break
        txt=(txt or '').lstrip(' 　\n\t')
        if not txt:
            sibling=sibling.next_sibling; continue
        m=re.match(r'^([ぁ-んー]{1,8})',txt)
        if m: return m.group(1)
        return ''
    return ''

def to_dictionary_form(word):
    w=(word or '').strip()
    if not w: return w
    for suffix in ['していました','しています','しました','します','して','した']:
        if w.endswith(suffix): return w[:-len(suffix)] + 'する'
    for suffix in ['きました','きます','きて','きた','こない','こなかった']:
        if w.endswith(suffix): return w[:-len(suffix)] + 'くる'
    for suffix in ['ました','ます']:
        if w.endswith(suffix):
            stem=w[:-len(suffix)]
            if not stem: return w
            mapped=GODAN_I_TO_U.get(stem[-1])
            return stem[:-1]+mapped if mapped else stem+'る'
    if w.endswith('ない') and len(w)>2:
        stem=w[:-2]; mapped=GODAN_A_TO_U.get(stem[-1]) if stem else None
        return stem[:-1]+mapped if mapped else stem+'る'
    return w

def extract_vocab_from_blocks(blocks):
    vocab_map={}
    for block in blocks:
        soup=BeautifulSoup(block['html'],'html.parser')
        for ruby in soup.find_all('ruby'):
            rb_text=''; rt_text=''
            for child in ruby.contents:
                name=getattr(child,'name',None)
                if name=='rt': rt_text += child.get_text('',strip=True)
                elif name=='rp': continue
                else: rb_text += child.get_text('',strip=True) if hasattr(child,'get_text') else str(child).strip()
            rb_text=rb_text.strip(); rt_text=rt_text.strip()
            if not rb_text or not re.search(r'[一-龯]',rb_text): continue
            okurigana=extract_following_okurigana(ruby); word=rb_text; reading=rt_text
            if okurigana and okurigana.startswith(PARTICLE_PREFIXES): okurigana=''
            if okurigana:
                surface_word=rb_text+okurigana; surface_reading=(rt_text+okurigana).strip()
                word=lemmatize_japanese(surface_word); reading=to_dictionary_form(surface_reading)
            if word not in vocab_map: vocab_map[word]=reading
    return [{'word':w,'reading':r,'meaning':translate_text(w,dest='bg')} for w,r in list(vocab_map.items())[:20]]

def translate_text(text, dest='bg'):
    text=(text or '').strip()
    if not text: return ''
    cache_key=(text,dest,bool(DEEPL_API_KEY))
    if cache_key in _TRANSLATION_CACHE: return _TRANSLATION_CACHE[cache_key]
    try:
        result=translator.translate(text,dest=dest).text
        _TRANSLATION_CACHE[cache_key]=result
        return result
    except Exception:
        return ''

def split_japanese_sentences(text):
    t=(text or '').strip()
    return [p.strip() for p in re.split(r'(?<=[。！？])\s*',t) if p.strip()] if t else []

def detect_grammar_in_sentence(sentence):
    tagger=get_mecab_tagger(); found=set()
    if tagger is None:
        return found
    try:
        tokens=list(tagger(sentence))
    except Exception:
        return found
    surfaces=[token_surface(t) for t in tokens]; lemmas=[token_lemma(t) for t in tokens]
    for i,s in enumerate(surfaces):
        l=lemmas[i]
        if s in {'けど','けれど','けれども'}: found.add('kedo')
        if s=='しかし': found.add('shikashi')
        if s in {'ても','でも'} or (s in {'て','で'} and _s(tokens,i+1)=='も'): found.add('temo')
        if s=='ながら': found.add('nagara')
        if s=='つつ': found.add('tsutsu')
        if s in {'間','あいだ'}: found.add('aida_ni')
        if s=='うち' and _s(tokens,i+1)=='に': found.add('uchi_ni')
        if s=='から': found.add('kara_reason')
        if s=='ので': found.add('node')
        if s=='で' and i>0 and i+1<len(tokens): found.add('de_reason')
        if s=='それで': found.add('sorede')
        if s=='そして': found.add('soshite')
        if s=='より': found.add('yori')
        if s in {'方','ほう'}:
            found.add('hou')
            if _s(tokens,i+1)=='が' and _s(tokens,i+2) in {'いい','よい','良い'}: found.add('hou_ga_ii')
        if s=='のに': found.add('noni')
        if s=='よう' and _s(tokens,i+1)=='に': found.add('you_ni')
        if s=='ため' and _s(tokens,i+1) in {'','に'}: found.add('tame_ni')
        if s=='せい' and _s(tokens,i+1)=='で': found.add('sei_de')
        if s=='おかげ' and _s(tokens,i+1)=='で': found.add('okage_de')
        if s=='みたい': found.add('mitai')
        if s=='らしい': found.add('rashii')
        if s=='っぽい': found.add('ppoi')
        if s=='そう': found.add('sou')
        if s=='だめ': found.add('dame')
        if s=='なら' and _s(tokens,i+1)=='ない': found.add('naranai')
        if s=='いけ' and _s(tokens,i+1)=='ない': found.add('ikenai')
        if s=='なけれ' and _s(tokens,i+1)=='ば':
            if _s(tokens,i+2)=='なら' and _s(tokens,i+3)=='ない': found.add('nakereba_naranai')
            if _s(tokens,i+2)=='いけ' and _s(tokens,i+3)=='ない': found.add('nakereba_ikenai')
        if s=='なく' and _seq(tokens,i+1,i+5)==['て','は','なら','ない']: found.add('nakutewa_naranai')
        if s=='たり' and surfaces.count('たり')>=2: found.add('tari_tari')
        if s=='だけ': found.add('dake')
        if s=='のみ': found.add('nomi')
        if s=='ばかり': found.add('bakari')
        if s=='しか' and 'ない' in surfaces[i+1:]: found.add('shika_nai')
        if s=='もう': found.add('mou')
        if s=='まだ': found.add('mada')
        if s=='また': found.add('mata')
        if (s in {'て','で'} and _s(tokens,i+1) in {'いい','よい','良い'}) or s in {'ていい','でいい'}: found.add('te_ii')
        if s in {'ても','でも'} and _s(tokens,i+1) in {'いい','よい','良い'}: found.add('temo_ii')
        if s in {'て','で'} and _s(tokens,i+1)=='も' and _s(tokens,i+2) in {'いい','よい','良い'}: found.add('temo_ii')
        if s=='と' and _l(tokens,i+1) in {'為る','する'}: found.add('to_suru')
        if s=='よう' and _s(tokens,i+1)=='と' and _l(tokens,i+2) in {'為る','する'}: found.add('you_to_suru')
        if s in {'て','で'} and _l(tokens,i+1) in {'見る','みる'}: found.add('te_miru')
        if s=='っけ': found.add('kke')
        if s=='かな': found.add('kana')
        if s in {'かい','だい'}: found.add('kai_dai')
        if s=='じゃ' and _s(tokens,i+1)=='ない': found.add('janai')
        if s=='じゃん': found.add('jan')
        if 'させ' in s or l in {'させる','せる'}: found.add('causative_saseru')
        if l in {'成る','なる'} or s=='なる': found.add('naru')
        feat=token_feature(tokens[i]); pos1=getattr(feat,'pos1','') if feat is not None else ''
        if pos1=='副詞' and _l(tokens,i+1) in {'為る','する'}: found.add('adverb_suru')
        if s=='自分': found.add('jibun')
        if s=='なく' and _s(tokens,i+1)=='て': found.add('nakute')
        if s=='ない' and _s(tokens,i+1)=='で': found.add('naide')
        if s in {'ず','ずに'} or (s=='ず' and _s(tokens,i+1)=='に'): found.add('zu')
        if s in {'て','で'} and _l(tokens,i+1) in {'仕舞う','しまう'}: found.add('te_shimau')
        if s in {'て','で'} and _l(tokens,i+1) in {'置く','おく'}: found.add('te_oku')
        if s in {'て','で'} and _l(tokens,i+1) in {'行く','いく'}: found.add('te_iku')
        if s in {'て','で'} and _l(tokens,i+1) in {'来る','くる'}: found.add('te_kuru')
        if s=='だって': found.add('datte')
        if s=='わけ': found.add('wake')
        if s=='はず': found.add('hazu')
        if s=='べき':
            found.add('beki')
            if _s(tokens,i+1)=='だっ' and _s(tokens,i+2)=='た': found.add('beki_datta')
        if s=='べし': found.add('beshi')
        if s=='もの' and _s(tokens,i+1)=='だ': found.add('mono_da')
        if s=='かも' and _s(tokens,i+1)=='しれ' and _s(tokens,i+2)=='ない': found.add('kamoshirenai')
        elif s=='かも': found.add('kamo')
        if s=='ころ': found.add('koro')
        if s=='ごろ': found.add('goro')
        if s in {'くらい','ぐらい'}: found.add('kurai_gurai')
        if s=='まで':
            found.add('made')
            if _s(tokens,i+1)=='に': found.add('made_ni')
            if 'から' in surfaces[:i]: found.add('kara_made')
        if s=='ほど': found.add('hodo')
        if l=='過ぎる' or s=='すぎる': found.add('sugiru')
        if s=='七味': found.add('shichimi')
    return found

def extract_grammar_details(articles):
    details=[]
    for article in articles:
        entry={'title':article.get('title',''),'items':[]}
        for block in article.get('blocks',[]):
            for sentence in split_japanese_sentences(block.get('text','')):
                rule_ids=sorted(detect_grammar_in_sentence(sentence))
                if rule_ids:
                    entry['items'].append({'sentence':sentence,'grammar':[GRAMMAR_RULES_BY_ID[r]['label'] for r in rule_ids if r in GRAMMAR_RULES_BY_ID]})
        details.append(entry)
    return details

def extract_grammar_points(articles):
    found={}
    for article in articles:
        for block in article.get('blocks',[]):
            for sentence in split_japanese_sentences(block.get('text','')):
                for rule_id in detect_grammar_in_sentence(sentence):
                    if rule_id not in found and rule_id in GRAMMAR_RULES_BY_ID:
                        found[rule_id]=grammar_hit(rule_id)
    ordered=[]
    for rule in GRAMMAR_RULES:
        item=found.get(rule['id'])
        if item: ordered.append(item)
    return ordered

def extract_ne_id(text):
    m=re.search(r'(ne\d{10,})', text or '')
    return m.group(1) if m else ''

def get_nhkeasier_items():
    r=requests.get(NHKEASIER_FEED_URL,timeout=20); r.raise_for_status()
    soup=BeautifulSoup(r.text,'xml'); items={}
    for item in soup.find_all('item'):
        title=(item.title.get_text() if item.title else '').strip()
        desc_raw=(item.description.get_text() if item.description else '').strip()
        desc_html=html_lib.unescape(desc_raw); desc_soup=BeautifulSoup(desc_html,'html.parser')
        audio_url=''; enclosure=item.find('enclosure')
        if enclosure and enclosure.get('url'): audio_url=enclosure.get('url').strip()
        if not audio_url:
            audio_tag=desc_soup.select_one('audio[src], audio source[src]')
            if audio_tag: audio_url=(audio_tag.get('src') or '').strip()
        image_url=''; itunes_img=item.find('itunes:image')
        if itunes_img and itunes_img.get('href'): image_url=itunes_img.get('href').strip()
        if not image_url:
            img_tag=desc_soup.select_one('img[src]')
            if img_tag: image_url=(img_tag.get('src') or '').strip()
        blocks=[]
        for b in get_article_blocks(desc_soup):
            t=b['text'].strip()
            if t and t.lower() not in {'original','permalink'} and 'Original' not in t and 'Permalink' not in t: blocks.append(b)
        ne_id=''; original_link=''
        for a in desc_soup.select('a[href]'):
            href=(a.get('href') or '').strip()
            if '/news/easy/ne' in href:
                original_link=href; ne_id=extract_ne_id(href); break
        if not ne_id: ne_id=extract_ne_id(audio_url) or extract_ne_id(image_url) or extract_ne_id(desc_html)
        if ne_id: items[ne_id]={'title':title,'blocks':blocks,'audio_url':audio_url,'image_url':image_url,'original_link':original_link}
    return items

def extract_easy_article_links_from_sitemap(n=4):
    r=requests.get(EASY_SITEMAP_URL,timeout=20); r.raise_for_status()
    soup=BeautifulSoup(r.text,'xml'); links=[]; seen=set()
    for loc in soup.find_all('loc'):
        url=(loc.get_text() or '').strip()
        if not url: continue
        parsed=urlparse(url)
        if '/news/easy/ne' not in parsed.path or not parsed.path.endswith('.html') or url in seen: continue
        seen.add(url); links.append(url)
        if len(links)>=n: break
    return links

def parse_article_from_nhk_easy(link):
    page=requests.get(link,timeout=20); page.raise_for_status()
    psoup=BeautifulSoup(page.text,'html.parser')
    title_tag=psoup.select_one('h1'); title=''; title_html=''
    if title_tag:
        title=title_tag.get_text(' ',strip=True); title_html=' '.join(str(x) for x in title_tag.contents).strip() or title
    if not title:
        og_title=psoup.select_one('meta[property="og:title"]')
        if og_title: title=(og_title.get('content') or '').strip()
    if not title: title='NHK Easy Article'
    if not title_html: title_html=title
    image_url=''; audio_url=''
    content=psoup.select_one('.article-main__body') or psoup.select_one('.module--content') or psoup.select_one('#js-article-body') or psoup.select_one('.content--detail-body') or psoup.select_one('article') or psoup.select_one('main')
    filtered_blocks=[]
    if content is not None:
        for bad in content.select('script, style, nav, footer, header, aside, form'): bad.decompose()
        for b in get_article_blocks(content):
            t=b['text']
            if 'share' in t.lower() or 'follow us' in t.lower(): continue
            filtered_blocks.append(b)
    if not filtered_blocks:
        desc_meta=psoup.select_one('meta[name="description"]'); desc=(desc_meta.get('content') or '').strip() if desc_meta else ''
        if desc: filtered_blocks.append({'html':desc,'text':desc})
    if not filtered_blocks: return None
    vocab=extract_vocab_from_blocks(filtered_blocks)
    translated_blocks=[{'html':b['html'],'text':b['text'],'translation':translate_text(b['text'],dest='bg')} for b in filtered_blocks]
    return {'title':title,'title_html':title_html,'title_translation':translate_text(title,dest='bg'),'link':link,'image_url':image_url,'audio_url':audio_url,'blocks':translated_blocks,'vocab':vocab}

def get_articles(n=4):
    links=extract_easy_article_links_from_sitemap(max(n*8,n)); nhkeasier_items={}
    try: nhkeasier_items=get_nhkeasier_items()
    except Exception as e: print(f'Could not load nhkeasier fallback feed: {e}')
    articles=[]
    for link in links:
        try:
            article=parse_article_from_nhk_easy(link); ne_id=extract_ne_id(link); fallback=nhkeasier_items.get(ne_id)
            if article and fallback and fallback.get('blocks'):
                article['blocks']=[{'html':b['html'],'text':b['text'],'translation':translate_text(b['text'],dest='bg')} for b in fallback['blocks']]
                article['vocab']=extract_vocab_from_blocks(fallback['blocks'])
            if article and article.get('blocks') and article.get('vocab'):
                articles.append(article)
                if len(articles)>=n: break
        except Exception as e:
            print(f'Skipping article because of error: {e}')
    return articles[:n]

def is_single_kanji_word(word):
    return bool(re.fullmatch(r'[一-龯]', (word or '').strip()))
def is_known_vocab_item(word, known_items):
    return word in known_items or f'v:{word}' in known_items
def build_anki_cards(articles, grammar_points=None, seen_items=None):
    cards=[]; seen=set(); known=set(seen_items or []); newly_added_items=set()
    for article in articles:
        for item in article.get('vocab',[]):
            word=(item.get('word') or '').strip(); reading=(item.get('reading') or '').strip(); meaning=(item.get('meaning') or '').strip()
            if not word or not meaning or is_single_kanji_word(word) or word in seen or is_known_vocab_item(word, known): continue
            seen.add(word); newly_added_items.add(f'v:{word}')
            front=f'<ruby>{word}<rt>{reading}</rt></ruby>' if reading and reading != word else word
            cards.append((front,meaning))
    for g in grammar_points or []:
        label=(g.get('label') or '').strip(); explanation=(g.get('explanation') or '').strip()
        if not label or not explanation: continue
        grammar_key=f'g:{label}'
        if grammar_key in known: continue
        newly_added_items.add(grammar_key); cards.append((f'Граматика: {label}',explanation))
    return cards,newly_added_items
def load_seen_words(path):
    if not os.path.exists(path): return set()
    try:
        with open(path,'r',encoding='utf-8') as f: data=json.load(f)
        return {str(x).strip() for x in data if str(x).strip()} if isinstance(data,list) else set()
    except Exception: return set()
def save_seen_words(path, words):
    with open(path,'w',encoding='utf-8') as f: json.dump(sorted({w.strip() for w in words if w and w.strip()}),f,ensure_ascii=False,indent=2)
def save_anki_tsv(cards,path):
    with open(path,'w',encoding='utf-8') as f:
        for front,back in cards: f.write(f'{front}\t{back}\n')
def stable_int_id(seed, digits=10):
    digest=hashlib.sha1(seed.encode('utf-8')).hexdigest(); h=int(digest[:12],16); mod=10**digits
    return (h % mod) + (10**(digits-1))
def build_anki_apkg(cards, apkg_path, deck_name='NHK Easy Vocabulary'):
    if genanki is None: return False
    model=genanki.Model(stable_int_id('nhk_easy_vocab_model'),'NHK Easy Vocab Model',fields=[{'name':'Front'},{'name':'Back'}],templates=[{'name':'Card 1','qfmt':"<div class='jp-word'>{{Front}}</div>",'afmt':"<div class='jp-word'>{{Front}}</div><hr id='answer'><div class='bg-meaning'>{{Back}}</div>"}],css='.card{font-family:Arial,sans-serif;font-size:25px;text-align:center;color:black;background-color:white}.jp-word{font-size:31px}.bg-meaning{font-size:25px}.jp-word ruby rt{font-size:14px}')
    deck=genanki.Deck(stable_int_id('nhk_easy_vocab_deck'),deck_name)
    for front,back in cards: deck.add_note(genanki.Note(model=model,fields=[front,back],guid=uuid.uuid4().hex))
    genanki.Package(deck).write_to_file(apkg_path); return True

def build_html(articles, anki_filename=DEFAULT_ANKI_FILENAME, anki_apkg_filename=DEFAULT_ANKI_APKG_FILENAME, grammar_points=None):
    grammar_points=grammar_points or []
    html='<!doctype html><html lang="ja"><head><meta charset="UTF-8"><meta name="viewport" content="width=device-width, initial-scale=1.0"><title>最新ニュース</title></head><body><div class="wrap"><h1>最新ニュース</h1>'
    for article in articles:
        html += '<article>'
        html += f"<h2>{article.get('title_html', article['title'])}</h2>"
        html += f"<div>{article.get('title_translation','')}</div>"
        html += '<h3>Речник</h3><ul>'
        for item in article['vocab']:
            word=item['word']; reading=item['reading']; meaning=item['meaning']
            word_html=f'<ruby>{word}<rt>{reading}</rt></ruby>' if reading else word
            if meaning: html += f"<li>{word_html} — {meaning}</li>"
            else: html += f"<li>{word_html}</li>"
        html += '</ul><h3>Текст</h3>'
        for block in article['blocks']:
            html += f"<div>{block['html']}</div>"
            if block['translation']: html += f"<div>{block['translation']}</div>"
        html += '</article>'
    html += f"<div><a href='{anki_apkg_filename}' download>Свали Anki Карти</a> | <a href='{anki_filename}' download>TSV</a></div>"
    if grammar_points:
        html += '<section><h3>Граматика в текстовете</h3><ul>'
        for g in grammar_points: html += f"<li>{g['label']} — {g['explanation']}</li>"
        html += '</ul></section>'
    html += '</div></body></html>'
    return html

def main():
    global DEEPL_API_KEY
    parser=argparse.ArgumentParser()
    parser.add_argument('--output',default=DEFAULT_OUTPUT)
    parser.add_argument('--count',type=int,default=4)
    parser.add_argument('--deepl-key',default=os.environ.get('DEEPL_API_KEY',''))
    args=parser.parse_args()
    DEEPL_API_KEY=(args.deepl_key or '').strip()
    articles=get_articles(args.count)
    if not articles: raise RuntimeError('No articles were extracted.')
    output_dir=os.path.dirname(args.output)
    if output_dir: os.makedirs(output_dir,exist_ok=True)
    grammar_points=extract_grammar_points(articles)
    anki_filename=DEFAULT_ANKI_FILENAME; anki_apkg_filename=DEFAULT_ANKI_APKG_FILENAME; anki_seen_words_filename=DEFAULT_ANKI_SEEN_WORDS_FILENAME
    if output_dir:
        anki_path=os.path.join(output_dir,anki_filename); anki_apkg_path=os.path.join(output_dir,anki_apkg_filename); anki_seen_words_path=os.path.join(output_dir,anki_seen_words_filename)
    else:
        anki_path=anki_filename; anki_apkg_path=anki_apkg_filename; anki_seen_words_path=anki_seen_words_filename
    seen_words=load_seen_words(anki_seen_words_path)
    anki_cards,newly_added_words=build_anki_cards(articles,grammar_points=grammar_points,seen_items=seen_words)
    save_anki_tsv(anki_cards,anki_path); build_anki_apkg(anki_cards,anki_apkg_path); save_seen_words(anki_seen_words_path,seen_words | newly_added_words)
    html=build_html(articles,anki_filename=anki_filename,anki_apkg_filename=anki_apkg_filename,grammar_points=grammar_points)
    with open(args.output,'w',encoding='utf-8') as f: f.write(html)

if __name__=='__main__':
    main()
