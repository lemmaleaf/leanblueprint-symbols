"""Term links (core.term_links): the forms a defined term links in, the uses it must not link, and the unlinked-term
advisory (user, 2026-11-19: "needs hyperlink" on compact, closed, bounded, simple, ideals, smooth maps)."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from leanblueprint_symbols.core import card_tokens, key_of, term_links  # noqa: E402

DEFS = [
    ("def:closed", r"A set is a \defterm{closed set} when ...; a \defterm{bounded set} when ..."),
    ("def:compact", r"A \defterm{compact set} is a closed set that is bounded."),
    ("def:lie", r"A \defterm{Lie algebra} is ...; its \defterm{ideal} is ..."),
    ("def:simple", r"A \defterm{simple Lie algebra} is a Lie algebra without proper ideals."),
    ("def:smooth", r"A \defterm{smooth function} is ..."),
    ("def:matrix", r"A \defterm{Hermitian matrix} is ..."),
    ("def:path", r"A \defterm{closed path} is a path that ends where it starts."),
]


def run(text, synonyms=(), aliases=None, types=None, binds=()):
    cards = [{"key": la, "label": la, "source": "\\begin{definition}" + src + "\\end{definition}", "pos": k}
             for k, (la, src) in enumerate(DEFS)]
    cards.append({"key": "lem:x", "label": "lem:x", "source": "\\begin{lemma}\\label{lem:x}" + text + "\\end{lemma}",
                  "pos": len(DEFS), "binds": list(binds)})
    terms = []
    for la, src in DEFS:
        import re
        for t in re.findall(r"\\defterm\{([^}]*)\}", src):
            terms.append({"term": t, "label": la, "aliases": (aliases or {}).get(t, [])})
    out = term_links(cards, terms, types=types or {}, synonyms=synonyms)
    linked = {(terms[r[0]]["term"], r[1], r[5]) for r in out["links"].get("lem:x", [])}
    adv = [a for a in out["advisories"] if a["label"] == "lem:x"]
    return linked, adv, out


def terms_of(linked):
    return {t for t, _, _ in linked}


def test_tokens_read_the_prose_only():
    toks = [w for w, _ in card_tokens(r"\begin{lemma}\label{x}\uses{y} If $K$ is closed, see \ref{y}. \emph{Yang--Mills}."
                                      r" \textit{Status:} known. \end{lemma}")]
    assert toks == ["if", "\ue000", "is", "closed", ",", "see", "\ue001", ".", "yang-mills", "."]


def test_plural_and_singular():
    linked, _, _ = run(r"The ideals of $\mathfrak g$ are trivial; the Hermitian matrices are diagonalizable.")
    assert ("ideal", "ideals", "exact") in linked and ("Hermitian matrix", "hermitian matrices", "inflected") in linked


def test_adjective_attributive():
    linked, _, _ = run(r"Every compact subset of $\mathbb R^n$ is ...; a closed and bounded set is ...")
    assert ("compact set", "compact", "attributive") in linked
    assert ("closed set", "closed", "attributive") in linked and ("bounded set", "bounded set", "exact") in linked


def test_adjective_predicative():
    linked, _, _ = run(r"If $K$ is compact and $\mathfrak g$ is simple, then ...")
    assert ("compact set", "compact", "predicative") in linked
    assert ("simple Lie algebra", "simple", "predicative") in linked
    linked, _, _ = run(r"The Lie algebra $\mathfrak h$ is simple; the set is closed and bounded.")
    assert {"simple Lie algebra", "closed set", "bounded set"} <= terms_of(linked)
    # a pronoun: the noun or formula it stands for, in its sentence
    linked, _, _ = run(r"A subset $K$ of $\mathbb R^m$ is nice when it is closed and bounded.")
    assert {"closed set", "bounded set"} <= terms_of(linked)
    # a declared type says what a formula is: a set (a subgroup is one), a map
    linked, _, _ = run(r"Since $G$ is closed, ...", types={key_of("G"): r"subgroup of $\mathrm U(n)$"})
    assert ("closed set", "closed", "predicative") in linked
    linked, _, _ = run(r"Let $M\colon[0,1]\to\mathbb R$ be smooth.")
    assert ("smooth function", "smooth", "predicative") in linked


def test_other_senses_do_not_link():
    linked, _, _ = run(r"The space $V$ is closed under addition. A simple computation shows that $x$ is simple to "
                       r"find; the proof is simple.")
    assert not terms_of(linked) & {"closed set", "simple Lie algebra"}
    # said of another kind of object
    linked, _, _ = run(r"A continuous function $f\colon K\to\mathbb R$ on a compact set $K$ is bounded.")
    assert "bounded set" not in terms_of(linked)
    linked, _, _ = run(r"A bounded operator $V$ is closed.")
    assert "closed set" not in terms_of(linked)
    linked, _, _ = run(r"Since $f$ is closed, ...")   # a lower-case letter is not written as a set is
    assert "closed set" not in terms_of(linked)
    linked, _, _ = run(r"Since $K$ is closed, ...", types={key_of("K"): "real number"})   # declared: not a set
    assert "closed set" not in terms_of(linked)


def test_the_longer_term_and_the_term_own_words_win():
    linked, _, _ = run(r"Let $C$ be a closed path. A closed set is ...")
    assert ("closed path", "closed path", "exact") in linked and ("closed set", "closed set", "exact") in linked
    # "closed" said of a formula a path and a set are both written as: the carrier wins over the other noun
    linked, _, _ = run(r"Then $K$ is closed.")
    assert ("closed set", "closed", "predicative") in linked and "closed path" not in terms_of(linked)


def test_first_use_per_card_and_not_in_the_defining_card():
    linked, _, out = run(r"$K$ is compact; a compact set is ...")
    assert [r[1] for r in out["links"]["lem:x"] if r[1].startswith("compact")] == ["compact"]
    # the card that defines "compact set" says "closed set" (linked) but not "compact" of itself
    own = out["links"].get("def:compact", [])
    assert not [r for r in own if r[1].startswith("compact")]


def test_aliases_and_synonyms():
    linked, adv, _ = run(r"A matter field is a smooth map $\psi$.")
    assert "smooth function" not in terms_of(linked)
    assert adv and "'smooth map'" in adv[0]["detail"] and "termsynonyms" in adv[0]["detail"]
    linked, adv, _ = run(r"A matter field is a smooth map $\psi$.", synonyms=[["function", "map"]])
    assert ("smooth function", "smooth map", "synonym") in linked and not adv
    linked, _, _ = run(r"By compactness, ...", aliases={"compact set": ["compactness"]})
    assert ("compact set", "compactness", "alias") in linked


def test_unlinked_term_advisory():
    _, adv, _ = run(r"Since $x$ is compact, ...")   # a formula of no declared type, not written as a set is
    assert [a["kind"] for a in adv] == ["unlinked-term"] and "no declared type" in adv[0]["detail"]
    _, adv, _ = run(r"It is compact.")   # nothing in the sentence says what "it" is
    assert adv and "said of 'it'" in adv[0]["detail"]
    _, adv, _ = run(r"Every compact space is ...")   # a near carrier
    assert adv and "'compact space'" in adv[0]["detail"]
    # no advisory where the term is linked in the card, nor for another sense
    _, adv, _ = run(r"It is compact. Every compact set is closed.")
    assert not [a for a in adv if "compact set" in a["detail"]]
    _, adv, _ = run(r"The space $V$ is closed under addition; a simple computation.")
    assert not adv


def test_other_forms_only_from_the_definition_on():
    """Before the defining card only the term as written links: "a term of the Leibniz formula" in a card before
    "terms" are defined is another sense; after it, the singular links."""
    def cards(first):
        lem = {"key": "lem:a", "label": "lem:a", "source": r"\begin{lemma}A term of the sum and the terms are ...\end{lemma}"}
        d = {"key": "def:t", "label": "def:t", "source": r"\begin{definition}The \defterm{terms} of $f$ ...\end{definition}"}
        seq = [lem, d] if first else [d, lem]
        return [dict(x, pos=k) for k, x in enumerate(seq)]
    for first, want in ((True, {("terms", "exact")}), (False, {("term", "inflected")})):
        out = term_links(cards(first), [{"term": "terms", "label": "def:t"}])
        assert {(r[1], r[5]) for r in out["links"]["lem:a"]} == want
