"""Positive controls: each defect found by hand in the Hill-class plan (2026-10-31) must be caught, and the
repaired text must pass clean."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent.parent))
from leanblueprint_symbols.core import check, key_of, name_key, tokens  # noqa: E402

WIRING = {"label": "def:wiring", "kind": "definition",
          "defines": [("n", "integer"), ("V", "set"), ("E", "finite set"), ("W", "annotated wiring"),
                      ("s", "map E -> V"), ("t", "map E -> V"), (r"\sigma", "sign map"), (r"\nu", "Hill map"),
                      ("E_j", "edges into j")],
          "binds": ["j"],
          "math": [r"n\ge1", r"V=\{1,\dots,n\}", r"W=(E,s,t,\sigma,\nu)", r"E_j=\{e: t(e)=j\}"],
          "text": "Fix an integer $n\\ge1$ and let $V=\\{1,\\dots,n\\}$."}
MATRIX_UNIT = {"label": "def:matrix-unit", "kind": "definition",
               "defines": [("M_e", r"matrix in $\mathbb R^{n\times n}$")], "binds": ["e", "k", "l"],
               "terms": ["matrix unit"],
               "math": [r"M_e\in\mathbb R^{n\times n}", r"(M_e)_{kl}=1", r"k=t(e)", r"l=s(e)"],
               "text": "For an edge $e$, the matrix unit of $e$ is ..."}


def kinds(problems):
    return sorted((p["kind"], p["label"]) for p in problems)


def test_tokens_keep_whole_symbols():
    assert ("A", True, "") in tokens(r"\det(I-A_{S_J})")
    assert ("h", True, "-") in tokens(r"h^-_{K,\nu}(x)")
    assert ("B", True, r"\mathrm{nd}") in tokens(r"B_k^{\mathrm{nd}}")
    assert (r"\tilde H", True, "") in tokens(r"\prod_e\tilde H_e")
    assert ("x", False, "") in tokens(r"x^2") and ("x", False, "2") not in tokens(r"x^2")
    assert (r"\mathcal E", False, "") in tokens(r"\mathcal E(x)_{ji}")
    assert not [t for t in tokens(r"\mathbb R^{n}") if t[0] == r"\mathbb R"]


def test_clean_passes():
    assert check([WIRING, MATRIX_UNIT]) == []


def test_undefined_n_is_caught():
    w = dict(WIRING, defines=[d for d in WIRING["defines"] if d[0] != "n"])
    found = [p for p in check([w, MATRIX_UNIT]) if p["kind"] == "undeclared" and p["detail"].startswith("n ")]
    assert {p["label"] for p in found} == {"def:wiring", "def:matrix-unit"}


def test_undefined_V_is_caught():
    w = dict(WIRING, defines=[d for d in WIRING["defines"] if d[0] != "V"])
    assert ("undeclared", "def:wiring") in kinds(check([w]))


def test_bound_variable_must_be_declared():
    m = dict(MATRIX_UNIT, binds=["k", "l"])           # "for an edge e" missing
    assert any(p["detail"].startswith("e ") for p in check([WIRING, m]))


def test_overloaded_eta_is_caught():
    elasticity = {"label": "def:elasticity", "kind": "definition", "defines": [(r"\eta_e", "elasticity at x")],
                  "binds": ["e"], "math": [r"\eta_e"], "text": ""}
    box_point = {"label": "lem:multi-affinity", "kind": "lemma", "defines": [(r"\eta_e", "a point of the box")],
                 "binds": ["e"], "math": [r"\eta_e"], "text": ""}
    assert ("redeclared", "lem:multi-affinity") in kinds(check([WIRING, elasticity, box_point]))


def test_untyped_declaration_is_caught():
    m = dict(MATRIX_UNIT, defines=[("M_e", "")])
    assert ("untyped", "def:matrix-unit") in kinds(check([WIRING, m]))


def test_term_before_definition_is_caught():
    early = {"label": "thm:uniqueness", "kind": "theorem", "math": [], "binds": [],
             "text": "Then I - E(x) is a P-matrix."}
    pdef = {"label": "def:pmatrix", "kind": "definition", "terms": ["P-matrix"], "math": [], "text": ""}
    assert ("term-before", "thm:uniqueness") in kinds(check([WIRING, early, pdef]))


def test_gloss_in_definition_is_caught():
    w = dict(WIRING, text=WIRING["text"] + " so that R^n has one coordinate per gene.")
    assert ("gloss", "def:wiring") in kinds(check([w]))


def test_proof_inherits_its_statement_bindings():
    lemma = {"label": "lem:box", "kind": "lemma", "binds": ["x", "e"], "math": [r"M_e x"], "text": ""}
    proof = {"label": "prf:box", "kind": "proof", "parent": "lem:box", "math": [r"M_e x"], "text": ""}
    assert check([WIRING, MATRIX_UNIT, lemma, proof]) == []


def test_binders_inside_a_formula():
    item = {"label": "lem:x", "kind": "lemma", "math": [r"\sum_{e\in E}M_e", r"\{i: i\in V\}", r"\forall j\ E_j"],
            "text": ""}
    assert check([WIRING, MATRIX_UNIT, item]) == []
    stray = dict(item, math=[r"\sum_{e\in E}M_e + q"])   # q is not bound anywhere
    assert any(p["detail"].startswith("q ") for p in check([WIRING, MATRIX_UNIT, stray]))


def test_scan_spans_cover_whole_symbols():
    from leanblueprint_symbols.core import scan
    src = r"\det(I-A_{S_J})+h^-_{K,\nu}(x)"
    spans = {src[a:b] for k, a, b in scan(src)}
    assert "A_{S_J}" in spans and r"h^-_{K,\nu}" in spans


def test_link_wraps_outermost_declared_symbols_only():
    from leanblueprint_symbols.core import link
    table = {("A", True, ""): "#def-corner", ("S", False, ""): "#def-S", ("x", False, ""): None}
    out = link(r"\det(I-A_{S_J}) + x", lambda k: table.get(k))
    assert out == r"\det(I-\href{#def-corner}{A_{S_J}}) + x"


def test_text_and_environment_names_are_not_symbols():
    assert tokens(r"\begin{cases}1 & \text{if } k=t(e)\end{cases}") == [("k", False, ""), ("t", False, ""), ("e", False, "")]


def test_component_of_a_declared_vector():
    item = {"label": "lem:c", "kind": "lemma", "binds": ["x"], "math": [r"x_{s(e)}", r"x_i"], "text": "",
            "defines": []}
    probs = check([WIRING, item])
    assert not [p for p in probs if p["detail"].startswith("x ")]


def test_scripts_after_spaces():
    assert ("\\sigma", True, "") in tokens(r"\sigma _e") and ("A", True, "") in tokens(r"A _{S}")


# the checks from the user's notes on the Hill book (2026-11-01): each catches its planted defect, and the repair passes

BOX_LEMMA = {"label": "lem:box", "kind": "lemma", "uses": ["def:wiring"],
             "defines": [(r"\mathcal I_e", "open interval")], "binds": ["e"],
             "math": [r"\mathcal I_e=(0,\nu_e)"], "text": ""}
MULTIAFFINE = {"label": "lem:multiaffine", "kind": "lemma", "uses": ["lem:box"], "binds": ["w", "e"],
               "math": [r"w_e\in\mathcal I_e"], "text": ""}


def test_definition_inside_a_lemma_used_elsewhere():
    assert ("local-def", "lem:box") in kinds(check([WIRING, BOX_LEMMA, MULTIAFFINE]))
    # used only by its own proof: a local definition, fine
    proof = {"label": "proof of lem:box", "kind": "proof", "parent": "lem:box", "math": [r"\mathcal I_e"], "text": ""}
    assert check([WIRING, BOX_LEMMA, proof]) == []
    # moved into a definition: fine
    box_def = {**BOX_LEMMA, "label": "def:box", "kind": "definition", "terms": []}
    assert check([WIRING, box_def, {**MULTIAFFINE, "uses": ["def:box"]}]) == []


def test_one_letter_two_roles():
    corner = {**BOX_LEMMA, "binds": ["e", r"z \in \{0,1\}^E"]}
    point = {**MULTIAFFINE, "binds": [r"z \in \mathbb R^E", "e"], "math": [r"z_e"]}
    assert ("two-roles", "lem:multiaffine") in kinds(check([WIRING, corner, point]))
    # the same type, or items that do not depend on each other: fine
    assert "two-roles" not in {p["kind"] for p in check([WIRING, corner, {**point, "binds": [r"z \in \{0,1\}^E", "e"]}])}
    assert "two-roles" not in {p["kind"] for p in check([WIRING, corner, {**point, "uses": ["def:wiring"]}])}


def test_symbol_without_a_uses_path():
    lemma = {"label": "lem:x", "kind": "lemma", "uses": [], "binds": ["e"], "math": [r"M_e"], "text": ""}
    assert ("uses", "lem:x") in kinds(check([WIRING, MATRIX_UNIT, lemma]))
    # through another item, or through its statement (a proof): fine
    mid = {"label": "lem:mid", "kind": "lemma", "uses": ["def:matrix-unit"], "math": [], "text": ""}
    assert check([WIRING, MATRIX_UNIT, mid, {**lemma, "uses": ["lem:mid"]}]) == []
    proof = {"label": "proof of lem:mid", "kind": "proof", "parent": "lem:mid", "uses": [], "binds": ["e"],
             "math": [r"M_e"], "text": ""}
    assert check([WIRING, MATRIX_UNIT, mid, proof]) == []
    # an item without a "uses" field (another front end) is not checked
    assert check([WIRING, MATRIX_UNIT, {k: v for k, v in lemma.items() if k != "uses"}]) == []


def test_proof_treats_every_part():
    st = {"label": "lem:p", "kind": "lemma", "parts": 3, "math": [], "text": ""}
    proof = {"label": "proof of lem:p", "kind": "proof", "parent": "lem:p", "math": [], "text": "(1) ... (3) ..."}
    assert ("proof-parts", "proof of lem:p") in kinds(check([st, proof]))
    assert check([st, {**proof, "text": "(1) a. (2) b. (3) c."}]) == []


def test_a_symbol_declared_here_is_not_a_use_of_another():
    # f^or_{W,theta} declared in this item is not a use of f_{W,theta} declared elsewhere
    model = {"label": "def:model", "kind": "definition", "defines": [("f_W", "map")], "math": [], "text": ""}
    orm = {"label": "def:or", "kind": "definition", "uses": [], "defines": [(r"f^{\mathrm{or}}_W", "map")],
           "math": [r"f^{\mathrm{or}}_W(x)"], "binds": ["x", "W"], "text": ""}
    assert check([model, orm]) == []


# The user's notes of 2026-11-01 to 11-05, made mechanical: each check catches the defect and passes the repair.
BEHAVIOUR = {"label": "def:behaviour", "kind": "definition", "terms": ["behaviour"], "math": [],
             "text": "A behaviour is ...", "names": ["behaviour"]}


def _card(source, **kw):
    return {"label": "lem:x", "kind": "lemma", "math": [], "text": "", "source": source, **kw}


def test_ref_after_linked_term():
    bad = _card(r"Each row is a behaviour (Definition~\ref{def:behaviour}).")
    assert kinds(check([BEHAVIOUR, bad])) == [("ref-after-term", "lem:x")]
    assert kinds(check([BEHAVIOUR, _card(r"Each row is a behaviours (Definition~\ref{def:behaviour}, part~2).")])) \
        == [("ref-after-term", "lem:x")]
    # repaired, or citing a formula rather than naming the term: clean
    assert check([BEHAVIOUR, _card(r"Each row is a behaviour.")]) == []
    assert check([BEHAVIOUR, _card(r"The sum is $\sum_e b_e$ (Definition~\ref{def:behaviour}).")]) == []
    assert check([BEHAVIOUR, _card(r"A behaviour is fixed. The sum is $b$ (Definition~\ref{def:behaviour}).")]) == []


def test_several_definitions_are_numbered():
    two = {"label": "def:mb", "kind": "definition", "math": [], "text": "", "names": ["matrix box", "matrix corner"]}
    assert kinds(check([two])) == [("unnumbered", "def:mb")]
    assert check([{**two, "parts": 2}]) == []
    assert check([{**two, "names": ["matrix box"]}]) == []


def test_inline_numbered_parts_are_a_list():
    r"""A statement that numbers its parts inline must be an enumerate list; a list, a reference to another card's
    item and an equation number are not inline numbering; a planned card gets the advisory, never the problem."""
    inline = _card(r"\begin{lemma}\label{lem:x} Let $f$ be smooth. Then (1) $f$ is bounded, and (2) $f$ is closed."
                   r"\end{lemma}")
    assert kinds(check([inline])) == [("unnumbered", "lem:x")]
    for k in ("theorem", "proposition", "corollary"):
        assert kinds(check([{**inline, "kind": k}])) == [("unnumbered", "lem:x")]
    listed = _card(r"\begin{lemma}\label{lem:x} Let $f$ be smooth. Then\begin{enumerate}\item $f$ is bounded;"
                   r"\item $f$ is closed.\end{enumerate}\end{lemma}", parts=2)
    assert check([listed]) == []
    refs = _card(r"By Lemma~\ref{lem:y}(1) and Lemma~\ref{lem:y}(2), and by parts (1) and (2) of it, $a=b$ "
                 r"(in $(1)$ and $(2)$), as \eqref{e1} shows.")
    assert check([refs]) == []
    assert check([_card(r"Then (1) holds.")]) == []          # a single number is not a list of parts
    assert check([{**inline, "kind": "remark"}]) == []        # only statements and definitions
    from leanblueprint_symbols.core import unnumbered, ADVISORY, KINDS
    plan = unnumbered([inline], plan=True)
    assert [(p["kind"], p["label"]) for p in plan] == [("unnumbered-plan", "lem:x")]
    assert "unnumbered-plan" in ADVISORY and "unnumbered" not in ADVISORY
    assert "inline" in KINDS["unnumbered"] and "advisory" in KINDS["unnumbered-plan"]
    two = {"label": "def:mb", "kind": "definition", "names": ["matrix box", "matrix corner"]}
    assert [p["kind"] for p in unnumbered([two], plan=True)] == ["unnumbered-plan"]


def test_remark_a_proof_relies_on():
    rem = {"label": "rem:c", "kind": "remark", "math": [], "text": ""}
    by_uses = _card("", uses=["rem:c"])
    by_ref = {"label": "proof of lem:x", "kind": "proof", "parent": "lem:x", "math": [], "text": "",
              "source": r"By Remark~\ref{rem:c}, ..."}
    assert kinds(check([rem, by_uses])) == [("remark-used", "rem:c")]
    assert kinds(check([rem, _card(""), by_ref])) == [("remark-used", "rem:c")]
    assert check([rem, _card("")]) == []


def test_an_operator_cannot_be_declared_and_the_check_still_runs():
    """A \\defines of \\times or |\\cdot| (McKinsey-Sugar-Suppes repairs, 2026-11-08) used to stop the build with a
    ValueError, so the reader only saw "the book does not build"; now it is a problem on the card, and the other
    checks of the book still run."""
    prod = {"label": "def:product", "kind": "definition", "defines": [(r"\times", "Cartesian product")], "binds": ["A", "B", r"|\cdot|"],
            "terms": ["Cartesian product"], "math": [r"A \times B", r"n"], "text": "The Cartesian product of $A$ and $B$."}
    ks = kinds(check([WIRING, prod]))
    assert ks.count(("undeclarable", "def:product")) == 2
    assert ("undeclared", "def:product") not in ks          # n is declared by WIRING; A and B are bound here
    assert ("untyped", "def:product") not in ks             # the operator's declaration is set aside, not judged
    both = [p for p in check([WIRING, prod]) if p["kind"] == "undeclarable"]
    assert both[0]["detail"].startswith(r"\times is an operator") and "defterm" in both[0]["detail"]


def test_an_equation_number_is_not_a_symbol():
    """McKinsey-Sugar-Suppes, Definition 1.13 (2026-11-08): \\tag{1} read as an undeclared symbol, and the model rewrote the paper's
    equation to dodge it. \\tag, \\notag, \\nonumber and \\label are layout."""
    assert tokens(r"x_{11} + x_{12} + \cdots \tag{1}") == tokens(r"x_{11} + x_{12} + \cdots")
    assert tokens(r"a = b \notag") == tokens(r"a = b") and tokens(r"a \nonumber") == tokens("a")
    assert tokens(r"a \label{eq:one}") == tokens("a")
    item = {"label": "def:series", "kind": "definition", "binds": ["x", "n"], "terms": [], "math": [r"x_{n1} + x_{n2} + \cdots \tag{2}"], "text": "A series."}
    assert ("undeclared", "def:series") not in kinds(check([WIRING, item]))


def test_an_accent_on_a_digit_is_a_symbol_of_its_own():
    """McKinsey-Sugar-Suppes, Definition 1.9 (2026-11-08): \\defines{\\bar 0_n} registered as declaring n, so a later
    \\defines{n} was "redeclared". The zero vector's key is its own, with a subscript; n inside it is a use of n."""
    assert key_of(r"\bar 0_n") == (r"\bar 0", True, "")
    assert ("n", False, "") in tokens(r"\alpha = \bar 0_n")
    zero = {"label": "def:zero", "kind": "definition", "defines": [(r"\bar 0_n", "the zero vector")], "binds": ["n"], "terms": [],
            "math": [r"\bar 0_n"], "text": "The zero vector."}
    dim = {"label": "def:dim", "kind": "definition", "defines": [("n", "positive integer")], "binds": [], "terms": [], "math": ["n"], "text": "The dimension."}
    assert ("redeclared", "def:dim") not in kinds(check([zero, dim]))


def test_a_title_with_a_formula_matches_its_term():
    """McKinsey-Sugar-Suppes 2.4 (2026-11-08): the title arrives typeset, the term as source; they must compare equal."""
    assert name_key("n-dimensional system of particle mechanics") == name_key(r"$n$-dimensional system of particle mechanics")
    assert name_key(r"\(\mathbb R\)-valued map") == name_key("R-valued map")
    assert name_key("The  Cartesian product") == "cartesian product"
    assert name_key("parallel vectors") != name_key("parallel")


# ---- style checks (core.style): the reading rules of the book made mechanical (2026-11-15), one planted defect each,
# and the correct text beside it passes

from leanblueprint_symbols.core import style  # noqa: E402


def card(label, kind, body, parent=None, env=None):
    env = env or kind
    return {"label": label, "kind": kind, "parent": parent,
            "source": f"\\begin{{{env}}}\\label{{{label}}}\n{body}\n\\end{{{env}}}" if kind != "proof"
            else f"\\begin{{proof}}\n{body}\n\\end{{proof}}"}


def found(items, kind=None):
    return sorted((p["kind"], p["label"]) for p in style(items) if kind is None or p["kind"] == kind)


def test_forward_reference_is_a_problem():
    a = card("lem:a", "lemma", r"$x>0$, by \ref{lem:b}.")
    b = card("lem:b", "lemma", r"$x\ge0$.")
    assert found([a, b], "forward-ref") == [("forward-ref", "lem:a")]
    assert found([b, a], "forward-ref") == []                         # cited after it comes: fine
    pa = card("proof of lem:b", "proof", r"By \ref{lem:b}(2) and \ref{lem:a}.", parent="lem:b")
    assert found([b, pa, a], "forward-ref") == [("forward-ref", "proof of lem:b")]   # its own statement is fine
    # the front end's resolution: a reference to a later section (no card), "at" its first card
    c = dict(card("lem:c", "lemma", r"See \ref{sec:x}."), cites=[{"ref": "sec:x", "item": None, "at": 3}])
    assert found([c], "forward-ref") == [("forward-ref", "lem:c")]
    assert style([c])[0]["severity"] == "problem"


def test_plan_of_the_book_in_a_card():
    for words in ("as Chapter 5 shows", "until Chapter~\\ref{ch:x}", "in later chapters", "the next chapter",
                  "the cards below make this precise", "see below.", "Section 3 explains", "is defined later",
                  "for now", "the remaining chapters lead to it", "proved so far"):
        assert found([card("lem:a", "lemma", f"$x>0$; {words}")], "chapter-mention") == [("chapter-mention", "lem:a")], words
    for words in ("$f$ is bounded below", "it keeps $P_j$ below $V_j$", "far below the threshold", "part 2 of the lemma",
                  "by (2), $x$ lies below $y$", "the level stays below one"):
        assert found([card("lem:a", "lemma", f"$x>0$, and {words}.")], "chapter-mention") == [], words
    for words in ("a box is admissible when the conditions below hold", "the two cases below: one, two"):
        assert found([card("def:a", "definition", f"$x>0$; {words}.")], "chapter-mention") == [], words
    # in a proof "below" and "we will" point inside the proof; the plan of the book is still caught there
    pr = card("proof of lem:a", "proof", r"We will show (3) below, and the bound below gives $x>0$.", parent="lem:a")
    assert found([card("lem:a", "lemma", "$x>0$."), pr], "chapter-mention") == []
    pr = card("proof of lem:a", "proof", r"As in Chapter~\ref{ch:x}.", parent="lem:a")
    assert found([card("lem:a", "lemma", "$x>0$."), pr], "chapter-mention") == [("chapter-mention", "proof of lem:a")]
    # a reference's own words ("Glimm-Jaffe, Chapter 6") are a tag line, not the card's text
    ok = card("lem:a", "lemma", "$x>0$.\n\n\\textit{Status:} known.\n\\textit{References:} \\href{https://x.org}{Glimm--Jaffe, Chapter 6}.")
    assert found([ok, card("proof of lem:a", "proof", "Because " + "the numbers are positive and add up " * 3, "lem:a")]) == []


def test_project_paths_in_a_card():
    for words in ("proved in GRN/General/Box.lean", "see tools/visit.py", "as docs/MODEL.md says", "from RC1.md",
                  "the file status.json"):
        assert found([card("def:a", "definition", f"An $x$ is ... ({words}).")], "project-path") == [("project-path", "def:a")], words
    ok = (r"An $x$ is positive. \href{https://en.wikipedia.org/wiki/Index.html}{Index}." "\n\n"
          r"\textit{In Lean:} \texttt{GRN.General.box} in GRN/General/Box.lean.")
    assert found([card("def:a", "definition", r"\lean{GRN.box}" + ok)], "project-path") == []


def test_tag_lines():
    good = "\n\n".join([r"$x>0$.", r"\textit{Status:} proved and rechecked in this project.",
                        r"\textit{In Lean:} \texttt{X.y}.", r"\textit{References:} \href{https://x.org}{a paper}."])
    assert found([card("thm:a", "theorem", good)], "tag-lines") == []
    joined = r"$x>0$. \textit{Status:} claimed elsewhere, not checked here. \textit{References:} \href{https://x.org}{x}."
    assert found([card("thm:a", "theorem", joined)], "tag-lines") == []    # plasTeX joins the lines: still tag lines
    for bad in (r"$x>0$. \textit{Status:} folklore.",                                    # not in the list
                r"$x>0$ (\textit{Status:} known) for every $x$.",                         # inside a sentence
                r"$x>0$. Status: known (elementary). More text.",                         # a sentence, no tag
                "\\textit{Status:} known.\n\nAnd then more of the statement.",            # text after the tag lines
                "\\begin{enumerate}\\item $x>0$. \\textit{Status:} open.\\end{enumerate}",   # inside a list
                "$x>0$.\n\n\\textit{Status:} open.\n\\textit{Status:} known."):           # twice
        assert set(found([card("thm:a", "theorem", bad)], "tag-lines")) == {("tag-lines", "thm:a")}, bad
    pr = card("proof of thm:a", "proof", r"Easy. \textit{Status:} known.", parent="thm:a")
    assert ("tag-lines", "proof of thm:a") in found([card("thm:a", "theorem", "$x>0$."), pr])


def test_known_needs_a_why():
    st = card("thm:a", "theorem", "$x>0$.\n\n\\textit{Status:} known.")
    assert found([st], "known-needs-why") == [("known-needs-why", "thm:a")]
    ref_only = card("proof of thm:a", "proof", r"See \href{https://x.org/abs/1}{Glimm and Jaffe}, Theorem 3.", parent="thm:a")
    assert found([st, ref_only], "known-needs-why") == [("known-needs-why", "thm:a")]
    short = card("proof of thm:a", "proof", r"By \ref{lem:b}(3), $U'=wUw^{-1}$, and $\operatorname{tr}(MUM^{-1})=\operatorname{tr}U$.",
                 parent="thm:a")
    assert found([st, short], "known-needs-why") == []                 # a short computation is a proof
    why = card("proof of thm:a", "proof", r"Why it is true (a sketch): $x$ is a square of a nonzero number, and a square "
               r"of a nonzero real number is positive, since the product of two numbers of the same sign is positive.",
               parent="thm:a")
    assert found([st, why], "known-needs-why") == []
    assert found([card("thm:a", "theorem", "$x>0$.\n\n\\textit{Status:} open.")], "known-needs-why") == []


def test_advisories():
    p = style([card("lem:a", "lemma", r"$x>0$. Proof: obvious.")])
    assert [(x["kind"], x["severity"]) for x in p] == [("proof-in-statement", "advisory")]
    assert found([card("lem:a", "lemma", r"$x>0$. From the proof of the lemma before, $y>0$.")]) == []
    five = "\\begin{enumerate}" + "".join(f"\\item ${k}>0$." for k in range(5)) + "\\end{enumerate}"
    assert found([card("lem:a", "lemma", five)]) == [("long-card", "lem:a")]
    assert found([card("lem:a", "lemma", five.replace("\\item $4>0$.", ""))]) == []
    nested = "\\begin{enumerate}\\item a \\begin{enumerate}" + "\\item b" * 6 + "\\end{enumerate}\\item c\\end{enumerate}"
    assert found([card("lem:a", "lemma", nested)]) == []                          # items of a nested list are not counted
    topics = "\\textbf{Sets.} \\begin{itemize}\\item $X$\\end{itemize} \\textbf{Maps.} \\begin{itemize}\\item $f$\\end{itemize}"
    assert found([card("not:a", "notation", topics)]) == [("long-card", "not:a")]
    assert found([card("def:g", "definition", r"A \defterm{group} is a set $G$ with a product. Each is a group. "
                       r"Example: the integers are a group.")]) == [("definition-states-fact", "def:g")]
    assert found([card("def:g", "definition", r"A \defterm{group} is a set $G$ with a product. It is called abelian "
                       r"when the product commutes.")]) == []


def test_duplicate_concept():
    """One concept defined in two cards is an advisory on both, each naming the other; a special case that depends on
    the general card and presents itself as an instance of it is not; a general term defined after a more specific one
    is in use came late."""
    lie = card("def:lie", "definition", r"The \defterm{Lie algebra} of $G$ is the set $\mathfrak g$ of matrices $X$ ...")
    dup = card("def:lie-mat", "definition", r"For a matrix group $G$, the \defterm{Lie algebras of a matrix group} "
               r"are the sets $\mathfrak g$ of $X$ with $e^{tX}\in G$.")
    got = style([lie, dup])
    assert {(p["kind"], p["label"], p["severity"]) for p in got} == {("duplicate-concept", "def:lie", "advisory"),
                                                                     ("duplicate-concept", "def:lie-mat", "advisory")}
    assert all(("def:lie-mat" if p["label"] == "def:lie" else "def:lie") in p["detail"] for p in got)
    # a planted instance: it \uses the general card and reads "is a Lie algebra"
    simple = card("def:simple", "definition", r"\uses{def:lie} A Lie algebra $\mathfrak g$ is a "
                  r"\defterm{simple Lie algebra} when its only ideals are $0$ and $\mathfrak g$.")
    assert found([lie, simple], "duplicate-concept") == []
    # the same text without the \uses, or with it but no instance phrasing, is flagged
    assert len(found([lie, card("def:simple", "definition", simple["source"].replace(r"\uses{def:lie}", ""))])) == 2
    bare = card("def:simple", "definition", r"\uses{def:lie} The \defterm{simple Lie algebra} $\mathfrak s$ is the set of $X$.")
    assert len(found([lie, bare], "duplicate-concept")) == 2
    # "invariant" twice (plural and case aside), "compact set" / "compact space", "ideal" / "ideal of a ring"
    assert len(found([card("def:a", "definition", r"An \defterm{invariant} is ..."),
                      card("def:b", "definition", r"The \defterm{Invariants} are ...")])) == 2
    assert len(found([card("def:a", "definition", r"A \defterm{compact set} is ..."),
                      card("def:b", "definition", r"A \defterm{compact space} is ...")])) == 2
    assert len(found([card("def:a", "definition", r"An \defterm{ideal} is ..."),
                      card("def:b", "definition", r"An \defterm{ideal of a ring} is ...")])) == 2
    # two qualifiers on one head are two concepts; a term in one card twice is not a duplicate
    assert found([card("def:a", "definition", r"A \defterm{continuous function} is ..."),
                  card("def:b", "definition", r"A \defterm{smooth function} is ...")]) == []
    assert found([card("def:g", "definition", r"A \defterm{group} ... it is an \defterm{abelian group} when ...")]) == []
    # stop words are words of their own, not of a term: "OR model" is not "model"
    p = style([card("def:m", "definition", r"The \defterm{model} is ..."),
               card("def:or", "definition", r"The \defterm{OR model} is ...")])
    assert {x["label"] for x in p} == {"def:m", "def:or"} and "variant" in p[1]["detail"]
    # a general term defined late: the special case is defined and used first
    early = card("def:cs", "definition", r"A \defterm{compact subset} of the plane is ...")
    use = card("lem:u", "lemma", r"\uses{def:cs} Every compact subsets of the plane is bounded.")
    late = card("def:c", "definition", r"A \defterm{subset} is ...")
    p = {x["label"]: x["detail"] for x in style([early, use, late])}
    assert set(p) == {"def:cs", "def:c"} and "comes late" in p["def:c"] and "lem:u" in p["def:c"]
    assert "comes late" not in p["def:cs"]


def test_long_card_counts_words_displays_and_proof_length():
    """Accretion caught mechanically (user, 2026-11-20): a statement past LIMITS words or displayed formulas, or a proof past
    LIMITS proof words, is a long card; the size of a card is core.size."""
    from leanblueprint_symbols.core import LIMITS, size
    long_words = " ".join(["word"] * (LIMITS["words"] + 1)) + "."
    assert found([card("lem:a", "lemma", long_words)]) == [("long-card", "lem:a")]
    assert found([card("lem:a", "lemma", " ".join(["word"] * LIMITS["words"]) + " $x$.")]) == []   # formulas are not words
    displays = " ".join(f"\\[x_{k}=0\\]" for k in range(LIMITS["displays"] + 1))
    assert found([card("lem:a", "lemma", "Then " + displays)]) == [("long-card", "lem:a")]
    assert found([card("lem:a", "lemma", "Then " + displays.split(" ", 1)[1])]) == []
    proof = " ".join(["step"] * (LIMITS["proof_words"] + 1))
    assert found([card("lem:a", "lemma", "$x>0$."), card("proof of lem:a", "proof", proof, parent="lem:a")]) == [("long-card", "lem:a")]
    assert found([card("lem:a", "lemma", "$x>0$."), card("proof of lem:a", "proof", "step " * 100, parent="lem:a")]) == []
    assert size(card("lem:a", "lemma", "One two \\[x=1\\] and $y$.\n\n\\textit{Status:} open.")["source"]) == {"items": 0, "words": 3, "displays": 1}


def test_formula_definition_is_a_weak_advisory():
    """A definition given by a formula is derived (a lemma shows it is the unique answer) or says why this formula."""
    bare = card("def:f", "definition", r"The \defterm{action} is \[S(A)=\frac{1}{2g^2}\int \operatorname{tr} F_{\mu\nu}F^{\mu\nu}\,dx.\]")
    assert found([bare], "formula-definition") == [("formula-definition", "def:f")]
    why = card("def:f", "definition", r"The \defterm{action} is \[S(A)=\frac{1}{2g^2}\int \operatorname{tr} F_{\mu\nu}F^{\mu\nu}\,dx;\] "
               r"this is the simplest gauge-invariant choice.")
    assert found([why], "formula-definition") == []
    lemma = card("lem:u", "lemma", "\\uses{def:f}\nThe action is the unique functional of degree two that is gauge invariant.")
    assert found([bare, lemma], "formula-definition") == []
    prose = card("def:f", "definition", "A \\defterm{group} is a set with an associative product, a unit and inverses: " + "more words " * 25)
    assert found([prose], "formula-definition") == []
    assert found([card("lem:f", "lemma", r"\[x=1\]")], "formula-definition") == []
