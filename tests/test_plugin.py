"""Build real documents with leanblueprint + this plugin; the control document (the clean one with the declaration
of n removed) must be caught at every use of n, the clean one must pass, and links must point at the declaring item."""
import json
import re
import os
import shutil
import subprocess
import sys
from pathlib import Path

import pytest

FIX = Path(__file__).parent / "fixtures"
BIN = Path(sys.executable).parent


def build(tmp_path, name):
    for f in ("clean.tex", "control.tex"):
        shutil.copy(FIX / f, tmp_path / f)
    env = dict(os.environ, PATH=f"{BIN}:{os.environ['PATH']}")
    r = subprocess.run([str(BIN / "plastex"), "--plugins", "leanblueprint", "leanblueprint_symbols", "--",
                        f"{name}.tex"], cwd=tmp_path, env=env, capture_output=True, text=True, timeout=600)
    assert r.returncode == 0, r.stderr[-2000:]
    return json.loads((tmp_path / "symbols-report.json").read_text()), tmp_path


@pytest.mark.slow
def test_clean_document_passes(tmp_path):
    problems, out = build(tmp_path, "clean")
    assert problems == []
    html = (out / "clean" / "sect0001.html").read_text()
    assert r"\href{sect0001.html#def:matrix-unit}{M_e}" in html
    data = json.loads((out / "blueprint-data.json").read_text())
    assert {i["label"] for i in data["items"]} >= {"def:wiring", "def:matrix-unit", "lem:box"}


@pytest.mark.slow
def test_control_document_is_caught(tmp_path):
    problems, _ = build(tmp_path, "control")
    n_uses = {p["label"] for p in problems if p["kind"] == "undeclared" and p["detail"].startswith("n ")}
    assert n_uses == {"def:wiring", "def:stub", "def:matrix-unit"}


@pytest.mark.slow
def test_reader_css_and_lean_urls(tmp_path):
    """Options reader, css=URL and a status file with urls: both pages (the text and the dependency graph, which the
    package resources do not reach) link the theme and the stylesheet, and a Lean tag links to the given url instead
    of the mathlib docs."""
    src = (FIX / "clean.tex").read_text()
    src = src.replace(r"\usepackage{symbols}", r"\usepackage[reader,css=/fonts.css,status=status.json]{symbols}")
    src = src.replace(r"\begin{lemma}[the box]\label{lem:box}", r"\begin{lemma}[the box]\label{lem:box}\lean{X.box}")
    assert r"\lean{X.box}" in src
    (tmp_path / "reader.tex").write_text(src)
    (tmp_path / "status.json").write_text(json.dumps({"X.box": {"status": "verified", "url": "/src?path=X.lean&line=3"}}))
    env = dict(os.environ, PATH=f"{BIN}:{os.environ['PATH']}")
    r = subprocess.run([str(BIN / "plastex"), "--plugins", "leanblueprint", "leanblueprint_symbols", "--", "reader.tex"],
                       cwd=tmp_path, env=env, capture_output=True, text=True, timeout=600)
    assert r.returncode == 0, r.stderr[-2000:]
    out = tmp_path / "reader"
    page, graph = (out / "sect0001.html").read_text(), (out / "dep_graph_document.html").read_text()
    for html in (page, graph):
        assert html.count("styles/reader.css") == 1 and html.count('href="/fonts.css"') == 1
    assert "js/reader.js" in page and (out / "js" / "reader.js").exists()
    assert "/src?path=X.lean" in page and "find/#doc/X.box" not in page + graph


PROOF_DOC = r"""\documentclass{report}
\usepackage{amsmath, amsthm}
\usepackage[thms=definition+lemma+theorem+conjecture]{blueprint}
\usepackage[status=status.json]{symbols}
\theoremstyle{definition}
\newtheorem{definition}{Definition}[chapter]
\newtheorem{lemma}[definition]{Lemma}
\newtheorem{theorem}[definition]{Theorem}
\newtheorem{conjecture}[definition]{Conjecture}
\begin{document}
\chapter{C}
\begin{definition}\label{def:a}\defines[X.a]{a}{real number} Let $a=1$.\end{definition}
\begin{theorem}\label{thm:lean}\uses{def:a}\lean{X.ok} $a>0$.\end{theorem}
\begin{lemma}\label{lem:paper}\uses{def:a} $a\ge0$.\end{lemma}
\begin{proof} Since $a=1$.\end{proof}
\begin{lemma}\label{lem:stated}\uses{def:a}\lean{X.stated} $a\ne0$.\end{lemma}
\begin{lemma}\label{lem:bare}\uses{def:a} $a<2$.\end{lemma}
\begin{conjecture}\label{conj:c}\uses{def:a} $a<3$.\end{conjecture}
\begin{theorem}\label{thm:big}\uses{def:a}\contains{lem:paper, lem:bare} $a=1$.\end{theorem}
\end{document}
"""


@pytest.mark.slow
def test_proof_chips(tmp_path):
    """Each statement's heading says what its proof is: verified in Lean (by the status file, not by the Lean name
    alone), proof on paper, no proof yet; a conjecture says open. The JSON export carries the same."""
    (tmp_path / "p.tex").write_text(PROOF_DOC)
    (tmp_path / "status.json").write_text(json.dumps({"X.ok": "verified", "X.stated": {"status": "stated"}}))
    env = dict(os.environ, PATH=f"{BIN}:{os.environ['PATH']}")
    r = subprocess.run([str(BIN / "plastex"), "--plugins", "leanblueprint", "leanblueprint_symbols", "--", "p.tex"],
                       cwd=tmp_path, env=env, capture_output=True, text=True, timeout=600)
    assert r.returncode == 0, r.stderr[-2000:]
    assert "template error" not in r.stdout + r.stderr
    proof = {i["label"]: i["proof"] for i in json.loads((tmp_path / "blueprint-data.json").read_text())["items"]}
    assert proof["thm:lean"] == "verified" and proof["lem:paper"] == "paper"
    assert proof["lem:stated"] == "none" and proof["lem:bare"] == "none" and proof["conj:c"] == "open"
    assert proof["def:a"] is None
    items = {i["label"]: i for i in json.loads((tmp_path / "blueprint-data.json").read_text())["items"]}
    assert items["thm:lean"]["number"] == "1.2" and items["thm:lean"]["tex"] == "$a>0$."
    assert items["def:a"]["tex"] == "Let $a=1$."   # \defines (with its Lean name) and \label removed from the text
    syms = json.loads((tmp_path / "blueprint-data.json").read_text())["symbols"]
    assert {"sym": "a", "type": "real number", "label": "def:a", "lean": "X.a", "item": None} in syms
    assert items["thm:lean"]["where"] == {"chapter": "1 C"}
    assert items["thm:big"]["contains"] == ["lem:paper", "lem:bare"] and items["thm:big"]["tex"] == "$a=1$."
    html = (tmp_path / "p" / "sect0001.html").read_text()
    for cls, words in (("verified", "verified in Lean"), ("paper", "proof on paper"), ("none", "no proof yet"),
                       ("open", "open")):
        assert f'proofchip-{cls}">{words}<' in html, cls


def _build(tmp_path, tex, status=None, name="p"):
    (tmp_path / f"{name}.tex").write_text(tex)
    if status is not None:
        (tmp_path / "status.json").write_text(json.dumps(status))
    env = dict(os.environ, PATH=f"{BIN}:{os.environ['PATH']}")
    r = subprocess.run([str(BIN / "plastex"), "--plugins", "leanblueprint", "leanblueprint_symbols", "--", f"{name}.tex"],
                       cwd=tmp_path, env=env, capture_output=True, text=True, timeout=600)
    assert r.returncode == 0, r.stderr[-2000:]
    return {i["label"]: i for i in json.loads((tmp_path / "blueprint-data.json").read_text())["items"]}


@pytest.mark.slow
def test_approve_markers_and_card_hash(tmp_path):
    """Option approve: each labelled card carries a marker with its label and hash; the hash covers the card's proof,
    so editing only the proof changes it, and a card that did not change keeps its hash."""
    tex = PROOF_DOC.replace(r"\usepackage[status=status.json]{symbols}", r"\usepackage[status=status.json,approve]{symbols}")
    (tmp_path / "a").mkdir()
    a = _build(tmp_path / "a", tex, {"X.ok": "verified"})
    html = (tmp_path / "a" / "p" / "sect0001.html").read_text()
    assert f'data-label="lem:paper" data-sha="{a["lem:paper"]["sha"]}"' in html
    assert html.count('class="sym-approve"') == len([i for i in a.values() if i["sha"]])
    (tmp_path / "b").mkdir()
    b = _build(tmp_path / "b", tex.replace("Since $a=1$.", "Because $a=1$."), {"X.ok": "verified"})
    assert b["lem:paper"]["sha"] != a["lem:paper"]["sha"]
    assert b["thm:lean"]["sha"] == a["thm:lean"]["sha"]
    # everything the reader sees is in the hash (2026-11-16): the title, a declared symbol's type and Lean name, a tag line;
    # only \uses and \label are left out
    def variant(name, old, new_):
        assert old in tex, old
        (tmp_path / name).mkdir()
        return _build(tmp_path / name, tex.replace(old, new_), {"X.ok": "verified"})
    c = variant("c", r"\defines[X.a]{a}", r"\defines[X.b]{a}")
    assert c["def:a"]["sha"] != a["def:a"]["sha"]
    d = variant("d", "{real number}", "{integer}")
    assert d["def:a"]["sha"] != a["def:a"]["sha"] and d["def:a"]["tex"] == a["def:a"]["tex"]
    e = variant("e", r"\begin{lemma}\label{lem:bare}", r"\begin{lemma}[A title]\label{lem:bare}")
    assert e["lem:bare"]["sha"] != a["lem:bare"]["sha"]
    f = variant("f", r"\label{lem:bare}\uses{def:a}", r"\label{lem:bare}\uses{def:a,thm:lean}")
    assert f["lem:bare"]["sha"] == a["lem:bare"]["sha"]
    g = variant("g", r"\label{lem:stated}\uses{def:a}\lean{X.stated}", r"\label{lem:stated}\uses{def:a}\lean{X.other}")
    assert g["lem:stated"]["sha"] != a["lem:stated"]["sha"]
    assert "real number" in a["def:a"]["seen"] and "def:a" not in a["lem:bare"]["seen"]


@pytest.mark.slow
def test_contains_must_name_an_item(tmp_path):
    tex = PROOF_DOC.replace(r"\uses{def:a} $a<3$.", r"\uses{def:a}\contains{lem:nope} $a<3$.")
    _build(tmp_path, tex, {"X.ok": "verified"})
    rep = json.loads((tmp_path / "symbols-report.json").read_text())
    assert any(p["kind"] == "contains" and "lem:nope" in p["detail"] for p in rep)


@pytest.mark.slow
def test_subscripted_use_of_a_plain_symbol_links(tmp_path):
    """sigma declared plain, sigma_e used: the checker accepts it, so it must link (it did not, 2026-11-01)."""
    tex = PROOF_DOC.replace(r"Let $a=1$.", r"Let $a=1$ and $a_e=2$.")
    _build(tmp_path, tex, {"X.ok": "verified"})
    html = (tmp_path / "p" / "sect0001.html").read_text()
    assert re.search(r"\\href\{sect0001\.html#def:a\}\{a_e\}", html), "a_e not linked to def:a"


@pytest.mark.slow
def test_a_named_definition_must_introduce_its_name(tmp_path):
    tex = PROOF_DOC.replace(r"\begin{definition}\label{def:a}", r"\begin{definition}[the constant]\label{def:a}")
    _build(tmp_path, tex, {"X.ok": "verified"})
    rep = json.loads((tmp_path / "symbols-report.json").read_text())
    assert any(p["kind"] == "unnamed" and p["label"] == "def:a" for p in rep)
    (tmp_path / "b").mkdir()
    _build(tmp_path / "b", tex.replace("Let $a=1$.", r"The \defterm{constant} is $a=1$."), {"X.ok": "verified"})
    rep = json.loads((tmp_path / "b" / "symbols-report.json").read_text())
    assert not any(p["kind"] == "unnamed" for p in rep)
    # a title and a term with a formula in them (McKinsey-Sugar-Suppes, 2026-11-08: the term was stored as an object)
    (tmp_path / "c").mkdir()
    tex2 = tex.replace("[the constant]", "[$n$-dimensional constant]").replace("Let $a=1$.", r"The \defterm{$n$-dimensional constant} is $a=1$.")
    _build(tmp_path / "c", tex2, {"X.ok": "verified"})
    rep = json.loads((tmp_path / "c" / "symbols-report.json").read_text())
    assert not any(p["kind"] == "unnamed" for p in rep), rep


@pytest.mark.slow
def test_pages_carry_the_defined_terms(tmp_path):
    # symbols.js links a term's uses in other cards to its definition: every page carries the terms and their targets
    _, out = build(tmp_path, "clean")
    html = (out / "clean" / "sect0001.html").read_text()
    m = re.search(r"window\.symbolsTerms = (\[.*?\]);</script>", html)
    assert m, "no terms on the page"
    terms = {t: (url, label) for t, url, label in json.loads(m.group(1))}
    assert terms["matrix unit"][1] == "def:matrix-unit" and terms["matrix unit"][0].endswith("#def:matrix-unit")


@pytest.mark.slow
def test_lazymath_option(tmp_path):
    # lazymath=URL: formulas typeset as they come into view (MathJax's ui/lazy from URL), menu and MathML copy off
    src = (FIX / "clean.tex").read_text()
    m = re.search(r"\\usepackage(\[[^\]]*\])?\{symbols\}", src)
    opts = (m.group(1) or "[]")[1:-1]
    (tmp_path / "lazy.tex").write_text(src.replace(m.group(0), "\\usepackage[" + (opts + "," if opts else "") + "lazymath=/m]{symbols}"))
    for f in ("clean.tex", "control.tex"):
        shutil.copy(FIX / f, tmp_path / f)
    env = dict(os.environ, PATH=f"{BIN}:{os.environ['PATH']}")
    r = subprocess.run([str(BIN / "plastex"), "--plugins", "leanblueprint", "leanblueprint_symbols", "--", "lazy.tex"],
                       cwd=tmp_path, env=env, capture_output=True, text=True, timeout=600)
    assert r.returncode == 0, r.stderr[-2000:]
    html = (tmp_path / "lazy" / "index.html").read_text()
    assert "load: ['ui/lazy']" in html and '"/m"' in html and "assistiveMml: []" in html
    plain = build(tmp_path, "clean")[1] / "clean" / "index.html"
    assert "ui/lazy" not in plain.read_text()


@pytest.mark.slow
def test_planned_cards_are_plans(tmp_path):
    r"""A \planned card is a plan: its undeclared symbols and missing \defterm are not problems, it has no Approve
    button, its heading says planned, and the export marks it. A written card beside it is still checked."""
    src = (FIX / "clean.tex").read_text().replace(r"\usepackage{symbols}", r"\usepackage[approve]{symbols}")
    plan = (r"\begin{definition}[a later thing]\label{def:later}" "\n" r"\planned" "\n"
            r"Will define $\zeta_q$ from $\Xi$, with a term." "\n" r"\end{definition}" "\n")
    bad = r"\begin{definition}[a bad thing]\label{def:bad}" "\n" r"Uses $\Psi$." "\n" r"\end{definition}" "\n"
    bad += r"\begin{definition}[Axiom P1]\label{def:p1}" "\n" r"Every thing is a thing." "\n" r"\end{definition}" "\n"
    src = src.replace(r"\end{document}", plan + bad + r"\end{document}")
    (tmp_path / "planned.tex").write_text(src)
    env = dict(os.environ, PATH=f"{BIN}:{os.environ['PATH']}")
    r = subprocess.run([str(BIN / "plastex"), "--plugins", "leanblueprint", "leanblueprint_symbols", "--", "planned.tex"],
                       cwd=tmp_path, env=env, capture_output=True, text=True, timeout=600)
    assert r.returncode == 0, r.stderr[-2000:]
    problems = json.loads((tmp_path / "symbols-report.json").read_text())
    assert {p["label"] for p in problems} == {"def:bad"}
    html = "".join(f.read_text() for f in (tmp_path / "planned").glob("*.html"))
    later = re.search(r'<span class="sym-approve"[^>]*data-label="def:later"[^>]*>', html).group(0)
    bad_m = re.search(r'<span class="sym-approve"[^>]*data-label="def:bad"[^>]*>', html).group(0)
    assert 'data-planned="1"' in later and "data-planned" not in bad_m
    assert "proofchip-planned" in html
    data = json.loads((tmp_path / "blueprint-data.json").read_text())
    by = {i["label"]: i for i in data["items"]}
    assert by["def:later"]["planned"] is True and by["def:bad"]["planned"] is False
    assert r"\planned" not in by["def:later"]["tex"]


@pytest.mark.slow
def test_inline_numbering_is_a_problem_on_written_cards_and_advice_on_plans(tmp_path):
    r"""A written lemma that numbers its parts inline fails as unnumbered; the same lemma as an enumerate list passes;
    a planned card with inline numbering gets the advisory unnumbered-plan and no problem."""
    src = (FIX / "clean.tex").read_text()
    cards = (r"\begin{lemma}\label{lem:inline}" "\n" r"Then (1) $1=1$, and (2) $2=2$." "\n" r"\end{lemma}" "\n"
             r"\begin{lemma}\label{lem:listed}" "\n" r"Then" "\n" r"\begin{enumerate}" "\n" r"\item $1=1$;" "\n"
             r"\item $2=2$." "\n" r"\end{enumerate}" "\n" r"\end{lemma}" "\n"
             r"\begin{lemma}\label{thm:plan}" "\n" r"\planned" "\n" r"Will state (1) a bound and (2) a limit." "\n"
             r"\end{lemma}" "\n")
    _build(tmp_path, src.replace(r"\end{document}", cards + r"\end{document}"))
    problems = json.loads((tmp_path / "symbols-report.json").read_text())
    advisories = json.loads((tmp_path / "symbols-advisories.json").read_text())
    assert [(p["kind"], p["label"]) for p in problems] == [("unnumbered", "lem:inline")]
    assert ("unnumbered-plan", "thm:plan") in [(p["kind"], p["label"]) for p in advisories]
    assert not any(p["label"] == "lem:listed" for p in problems + advisories if p["kind"].startswith("unnumbered"))
    kinds = json.loads((tmp_path / "blueprint-data.json").read_text())["kinds"]
    assert kinds["unnumbered-plan"]["severity"] == "advisory" and kinds["unnumbered"]["severity"] == "problem"


ITEMS_DOC = r"""\documentclass{report}
\usepackage{amsmath, amsthm}
\usepackage{hyperref}
\usepackage{blueprint}
\usepackage{symbols}
\theoremstyle{definition}
\newtheorem{definition}{Definition}[chapter]
\newtheorem{lemma}[definition]{Lemma}
\begin{document}
\chapter{C}
\begin{definition}[unit and pair]\label{def:a}
\defines{u}{real number}
Let $u=1$.
\begin{enumerate}
\item The \defterm{unit} is $u$.
\item \defines{p}{pair of real numbers} The \defterm{pair} is $p=(u,u)$.
\begin{enumerate}\item first $p_1$ \item second\end{enumerate}
\end{enumerate}
Then:
\begin{enumerate}
\item third.
\end{enumerate}
\end{definition}
\begin{definition}[plain]\label{def:plain}
\uses{def:a}
\defines{q}{real number}
The \defterm{plain} number is $q=u$.
\end{definition}
\begin{lemma}\label{lem:b}
\uses{def:a, def:plain}
By Lemma~\ref{lem:b}(1), Definition~\ref{def:a}(2), \ref{def:a}(2.1), \itemref{def:a}{3}, \ref{def:a} (x), \ref{def:a}(see) and
\ref{def:plain}, \ref{def:plain}(1): a pair, a unit, a plain number, $p$, $u$, $q$.
\begin{enumerate}\item $u>0$. \item $q>0$.\end{enumerate}
\end{lemma}
\begin{lemma}\label{lem:bad}
\uses{def:a}
By Definition~\ref{def:a}(7), $u=1$.
\end{lemma}
\end{document}
"""


@pytest.mark.slow
def test_item_anchors_and_item_links(tmp_path):
    r"""Each item of a card's numbered lists has an anchor label--item-n (1-based, counted across the card's lists, nested
    label--item-n-m); a term or a symbol defined inside an item links to the item, one defined outside to the card;
    \ref{label}(n) and \itemref{label}{n} are one link to the item, the caption word before it taken in. Planted control:
    a reference to an item the card does not have (def:a(7)) is reported and links to the card."""
    items = _build(tmp_path, ITEMS_DOC)
    html = (tmp_path / "p" / "sect0001.html").read_text()
    ids = re.findall(r'<li id="([^"]+)"', html)
    assert ids == ["def:a--item-1", "def:a--item-2", "def:a--item-2-1", "def:a--item-2-2", "def:a--item-3",
                   "lem:b--item-1", "lem:b--item-2"]
    assert items["def:a"]["anchors"] == ids[:5] and items["def:plain"]["anchors"] == []
    # terms: inside an item -> the item; outside -> the card
    terms = {t: url for t, url, _ in json.loads(re.search(r"window\.symbolsTerms = (\[.*?\]);</script>", html).group(1))}
    assert terms["unit"] == "sect0001.html#def:a--item-1" and terms["pair"] == "sect0001.html#def:a--item-2"
    assert terms["plain"] == "sect0001.html#def:plain"
    assert items["def:a"]["term_items"] == {"unit": "def:a--item-1", "pair": "def:a--item-2"}
    # symbols: \defines inside item 2 -> the item; \defines before the list -> the card
    assert r"\href{sect0001.html#def:a--item-2}{p}" in html and r"\href{sect0001.html#def:a--item-2}{p_1}" in html
    assert r"\href{sect0001.html#def:a}{u}" in html and r"\href{sect0001.html#def:plain}{q}" in html
    syms = {s["sym"]: s["item"] for s in json.loads((tmp_path / "blueprint-data.json").read_text())["symbols"]}
    assert syms == {"u": None, "p": "def:a--item-2", "q": None}
    # item references: one link each, the caption taken in when it matches the card
    link = lambda href, text: f'href="sect0001.html#{href}">{text}</a>' in html   # noqa: E731
    assert link("lem:b--item-1", "Lemma&#160;1.3(1)")
    assert link("def:a--item-2", "Definition&#160;1.1(2)") and "Definition&#160;<a" not in html.split('id="lem:b"')[1].split('id="lem:bad"')[0]
    assert link("def:a--item-2-1", "1.1(2.1)") and link("def:a--item-3", "1.1(3)")
    assert '<a href="sect0001.html#def:a">1.1</a> (x)' in html and '<a href="sect0001.html#def:a">1.1</a>(see)' in html
    assert '<a href="sect0001.html#def:plain">1.2</a>,' in html
    # a card without a numbered list (parts written inline): the item reference links to the card, no problem
    assert link("def:plain", "1.2(1)")
    # planted control: no item 7 -> reported, linked to the card
    rep = json.loads((tmp_path / "symbols-report.json").read_text())
    assert [p["label"] for p in rep if p["kind"] == "itemref"] == ["lem:bad"], rep
    assert link("def:a", "Definition&#160;1.1(7)")
    # the source keeps the reference as written (the card's text and hash do not change)
    assert r"\ref{def:a}(2)" in items["lem:b"]["tex"] and r"\ref{def:a}(see)" in items["lem:b"]["tex"]
    assert r"\itemref{def:a}{3}" in items["lem:b"]["tex"]


STYLE_DOC = r"""\documentclass{report}
\usepackage{amsmath, amsthm}
\usepackage[thms=definition+lemma+theorem]{blueprint}
\usepackage{symbols}
\theoremstyle{definition}
\newtheorem{definition}{Definition}[chapter]
\newtheorem{lemma}[definition]{Lemma}
\newtheorem{theorem}[definition]{Theorem}
\begin{document}
\chapter{First}\label{ch:first}
The cards below, and Chapter~\ref{ch:second}, are free to say so: this is an introduction.
\begin{definition}[constant]\label{def:a}\defines{a}{real number}
  The \defterm{constant} is $a=1$. Each is a group.
\end{definition}
\begin{lemma}\label{lem:early}\uses{def:a}
  $a>0$, by \ref{lem:late}; see also Chapter~\ref{ch:second}.

  \textit{Status:} known.
\end{lemma}
\begin{proof}
  See \href{https://example.org}{a book}.
\end{proof}
\begin{lemma}\label{lem:ok}\uses{def:a}
  $a\ge0$.

  \textit{Status:} known.
  \textit{References:} \href{https://example.org/x}{a book}.
\end{lemma}
\begin{proof}
  The constant is one, and one is at least zero, because every positive number is at least zero and one is positive.
\end{proof}
\begin{definition}[positive constant]\label{def:pos}\uses{def:a}
  A \defterm{positive constant} is a constant that is greater than zero.
\end{definition}
\begin{definition}[constant of a group]\label{def:dup}
  The \defterm{constant of a group} is its unit.
\end{definition}
\chapter{Second}\label{ch:second}
\begin{lemma}\label{lem:late}\uses{def:a}
  $a<2$, proved in GRN/General/Box.lean as the next chapter shows. Proof: obvious.

  \textit{Status:} folklore.
\end{lemma}
\end{document}
"""


@pytest.mark.slow
def test_style_checks_on_a_built_page(tmp_path):
    """The style checks through plasTeX (which joins a card's lines): a forward reference (to a card and to a chapter),
    plan-of-the-book words, a project path, a Status outside the fixed list, a known result whose proof is only a
    reference; advisories apart (a duplicate concept among them, beside an instance that is not one) (symbols-advisories.json, blueprint-data.json), never in symbols-report.json. A chapter's
    introduction is free, and the clean lemma passes."""
    _build(tmp_path, STYLE_DOC)
    rep = json.loads((tmp_path / "symbols-report.json").read_text())
    got = {(p["kind"], p["label"]) for p in rep}
    assert ("forward-ref", "lem:early") in got
    assert sum(1 for p in rep if p["kind"] == "forward-ref" and p["label"] == "lem:early") == 2, rep   # the card, the chapter
    assert {("chapter-mention", "lem:early"), ("chapter-mention", "lem:late"), ("project-path", "lem:late"),
            ("tag-lines", "lem:late"), ("known-needs-why", "lem:early")} <= got, rep
    assert not [p for p in rep if p["label"] in ("lem:ok", "proof of lem:ok", "def:a")], rep
    assert all("severity" not in p for p in rep)
    adv = json.loads((tmp_path / "symbols-advisories.json").read_text())
    assert {(p["kind"], p["label"]) for p in adv} == {("proof-in-statement", "lem:late"), ("definition-states-fact", "def:a"),
                                                      ("duplicate-concept", "def:a"), ("duplicate-concept", "def:dup")}, adv
    # the instance (it \uses def:a and reads "a constant that") is not flagged; the duplicate names the other card
    assert any("def:dup" in p["detail"] for p in adv if p["label"] == "def:a")
    data = json.loads((tmp_path / "blueprint-data.json").read_text())
    assert data["advisories"] == adv and data["kinds"]["forward-ref"]["severity"] == "problem"
    assert data["kinds"]["long-card"]["severity"] == "advisory"


TERMS_DOC = r"""\documentclass{report}
\usepackage{amsmath, amsthm}
\usepackage{hyperref}
\usepackage{blueprint}
\usepackage{symbols}
\theoremstyle{definition}
\newtheorem{definition}{Definition}[chapter]
\newtheorem{lemma}[definition]{Lemma}
\termsynonyms{function, map}
\termalias{Heine property}{compact set}
\begin{document}
\chapter{C}
\begin{definition}[closed set and bounded set]\label{def:cb}
\binds{K}
\begin{enumerate}
\item A set $K$ is a \defterm{closed set} when it contains its limits.
\item A set $K$ is a \defterm{bounded set} when it lies in a ball.
\end{enumerate}
\end{definition}
\begin{definition}[compact set]\label{def:compact}
\uses{def:cb}
\binds{K}
A set $K$ is a \defterm[aliases={compactness}]{compact set} when it is closed and bounded.
\end{definition}
\begin{definition}[smooth function]\label{def:smooth}
A \defterm{smooth function} is one with derivatives of every order.
\end{definition}
\begin{lemma}\label{lem:uses}
\uses{def:compact, def:smooth}
\binds{V, x, K, f}
If $K$ is compact, a smooth map $f$ on $K$ is bounded. The space $V$ is closed under addition, and a simple computation
shows that $x$ is closed. By compactness, the Heine property holds.

\textit{References:} a compact note.
\end{lemma}
\end{document}
"""


@pytest.mark.slow
def test_term_links_on_a_built_page(tmp_path):
    r"""The term links decided at build time travel with each card's text (a hidden span.sym-terms), and the
    unlinked-term advisory is in blueprint-data.json: \defterm[aliases=...], \termalias, \termsynonyms; "closed under"
    and "a simple computation" not linked; "$x$ is closed" (lower case, no type) not linked and advised."""
    import html as H
    _build(tmp_path, TERMS_DOC)
    page = (tmp_path / "p" / "sect0001.html").read_text()
    spans = {m.group(1): json.loads(H.unescape(m.group(2))) for m in re.finditer(
        r'id="([^"]+)"[^>]*>(?:(?!_thmwrapper).)*?<span class="sym-terms" hidden data-links="([^"]*)"', page, re.S)}
    rows = {(r[6], r[2], r[7]) for r in spans["lem:uses"]}
    # first use per card: "compact" (predicative) before "compactness" (its alias); the Heine property (\termalias)
    assert rows == {("compact set", "compact", "predicative"), ("smooth function", "smooth map", "synonym")}
    assert not any(r[6] == "closed set" for r in spans["lem:uses"])
    assert {(r[6], r[2]) for r in spans["def:compact"]} == {("closed set", "closed"), ("bounded set", "bounded")}
    assert sorted(r[0].split("#")[1] for r in spans["def:compact"]) == ["def:cb--item-1", "def:cb--item-2"]
    data = json.loads((tmp_path / "blueprint-data.json").read_text())
    adv = [a for a in data["advisories"] if a["kind"] == "unlinked-term"]
    assert [a["label"] for a in adv] == ["lem:uses"] and "$x$" in adv[0]["detail"] and "closed" in adv[0]["detail"]
    assert data["kinds"]["unlinked-term"]["severity"] == "advisory"
    assert not json.loads((tmp_path / "symbols-report.json").read_text())


def _chromium():
    try:
        from playwright.sync_api import sync_playwright  # noqa: F401
    except ImportError:
        return None
    for p in sorted((Path.home() / ".cache" / "ms-playwright").glob("chromium-*/chrome-linux64/chrome"), reverse=True):
        return p
    return None


@pytest.mark.slow
@pytest.mark.skipif(_chromium() is None, reason="needs playwright and a Chromium")
def test_term_links_are_placed_by_the_page(tmp_path):
    """symbols.js places the decided links: the right occurrence of each word, nothing in the tag lines."""
    from playwright.sync_api import sync_playwright
    _build(tmp_path, TERMS_DOC)
    with sync_playwright() as p:
        b = p.chromium.launch(executable_path=str(_chromium()))
        pg = b.new_page()
        pg.goto((tmp_path / "p" / "sect0001.html").as_uri())
        pg.wait_for_function("() => document.querySelector('a.sym-term')")
        got = pg.evaluate("""() => [...document.querySelectorAll('#lem\\\\:uses a.sym-term')].map((a) =>
            [a.textContent, a.getAttribute('href').split('#')[1], (a.previousSibling || {}).textContent || ''])""")
        b.close()
    texts = {t for t, _, _ in got}
    assert texts == {"compact", "smooth map"}   # first use only; not "closed" (under addition), not "simple"
    # "If $K$ is compact", not the tag line's "a compact note"
    assert [(h, prev.endswith(" is ")) for t, h, prev in got if t == "compact"] == [("def:compact", True)]
