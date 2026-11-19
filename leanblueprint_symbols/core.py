"""Checker core for textbook-style mathematical documents (front-end independent).

An *item* is one numbered unit (definition, lemma, theorem, proof, remark, ...) given as a dict:

    {"label": "def:matrix-unit", "kind": "definition",
     "defines": [("M_e", "matrix in $\\mathbb R^{n\\times n}$")],   # symbols this item introduces, with types
     "binds": ["e", "k", "l"],          # symbols bound locally (for an edge e, ...)
     "terms": ["matrix unit"],          # terms this item defines (glossary)
     "math": ["M_e\\in\\mathbb R^{n\\times n}", ...],              # TeX of every formula, in order
     "text": "For an edge $e$, ...",    # the prose (for term and gloss checks)
     "parent": None,                    # for a proof: the label of its statement (inherits its symbols)
     "uses": ["def:wiring"],            # optional: the items it says it depends on (\\uses)
     "parts": 0}                        # optional: the number of numbered parts of a statement (\\item)

`check(items)` returns a list of problems (dicts with "kind", "label", "detail"), in document order:

    undeclared   a symbol used before any item declares it and not bound here
    redeclared   a symbol declared a second time (one meaning per symbol)
    untyped      a declaration without a type
    term-before  a glossary term used in an item before the item that defines it
    gloss        an explanatory phrase inside a definition or statement ("so that", "i.e.", ...)
    local-def    a symbol declared inside a lemma, theorem, remark, proof, ... and used by another item: a definition
                 used elsewhere belongs in a definition (or the notation) of its own
    two-roles    a letter bound with two different types (\\binds{w \\in \\mathcal B} here, \\binds{w \\in E} there) in
                 items that depend on each other: one letter, one role
    uses         a symbol used in an item whose declaring item the item does not depend on (\\uses, directly or
                 through other items; a proof also through its statement); notation items are exempt
    proof-parts  a statement in numbered parts whose proof does not treat each part ("(1)", "(2)", ...)
    ref-after-term  "(Definition~\\ref{L})" right after a term that L defines: the term is already a link to L
    unnumbered   a definition whose title names several things ("matrix box, matrix corner"), or a lemma, theorem,
                 proposition or corollary whose prose numbers its parts inline ("(1) ... (2) ..."), that is not a
                 numbered list, one item per definition or part (`unnumbered(items, plan=True)`: the same check on
                 planned cards, as the advisory unnumbered-plan)
    remark-used  a remark that another item depends on (\\uses) or that a proof cites (\\ref): a claim a proof
                 relies on is a lemma, with a proof

`style(items)` (the reading rules of a textbook made mechanical) returns findings with a "severity":

    forward-ref       a card cites (\\ref, \\itemref) a card or a section that comes later; chapter and section
                      introductions are free
    chapter-mention   a card mentions the plan of the book: "Chapter 5", "Section 3", "later chapters", "the next
                      chapter", "the cards below", "for now", "so far" (in a proof, "below" points inside the proof)
    project-path      a card names a project file or path (GRN/..., tools/..., x.lean, x.py, x.md, x.json); Lean
                      names belong in \\lean{} and the "In Lean:" tag line, link targets are not read
    tag-lines         \\textit{Status:}, \\textit{In Lean:}, \\textit{References:} only as tag lines at the end of
                      a statement (not inside a sentence, a list or a proof, no text after them, each once); a Status
                      is one of STATUS_VALUES
    known-needs-why   a statement whose Status is "known" has no proof block, or one that is only a reference
    advisory: proof-in-statement ("Proof:", "Why it is true", a QED mark in a statement), long-card (more than four
    top-level items; a notation card with more than six or more than one \\textbf topic), definition-states-fact (a
    sentence of a definition without its defined term that starts "Each ... is", "It is", "Every ... is", ...),
    duplicate-concept (two cards define terms with one head noun, the qualifiers of one among those of the other:
    "ideal" / "ideal of a ring", the same term twice; or one qualifier on two carriers: "compact set" / "compact space";
    not when the more specific card \\uses the other and reads "is a <general>", "a <general> ... that" or "the
    <general> of"; a general term defined after a more specific one is in use is reported on its card: it came late)

`term_links(cards, terms, types, synonyms)` decides where each defined term links in each card (exact, plural or
singular, a declared alias or head-noun synonym, or the term's adjective said of something it applies to) and returns
the unlinked-term advisories (the adjective used where the rule declined it); see the comment above it.

KINDS holds a sentence for each kind, for a reader of a report.

Optional fields for these: "source" (the item's TeX, for ref-after-term and remark-used) and "names" (the things
the item's title names, for unnumbered).

A bound symbol may carry a type: "w \\in \\mathcal B", "S \\subseteq E" or "w : point of the box" (the symbol
is what comes before the first \\in, \\subseteq or colon).

Symbols are matched by a normalized key: the base (a letter, a Greek or other command, \\mathcal X, \\mathrm{Word},
an accented base such as \\tilde H), whether it carries a subscript, and a decoration superscript (^-, ^+, ^{\\mathrm{nd}}).
A declaration "M_e" therefore covers M_e, M_{e'}, M_1; "A_S" covers A_E and A_{S_J}; "h^-" covers h^-_{K,\\nu}; a
plain power x^2 is not a decoration and does not change the key.
"""
from __future__ import annotations

import re

STANDARD = {
    r"\mathbb R", r"\mathbb N", r"\mathbb Z", r"\mathbb C", r"\mathbb Q",
    r"\dots", r"\ldots", r"\cdots", r"\vdots", r"\ddots", r"\in", r"\notin", r"\ni", r"\sum", r"\prod", r"\int",
    r"\le", r"\ge", r"\leq", r"\geq", r"\neq", r"\ne", r"\times", r"\to", r"\mapsto", r"\subseteq", r"\subset",
    r"\supseteq", r"\cup", r"\cap", r"\setminus", r"\emptyset", r"\varnothing", r"\infty", r"\pm", r"\mp", r"\cdot",
    r"\circ", r"\det", r"\log", r"\exp", r"\max", r"\min", r"\sup", r"\inf", r"\lim", r"\sqrt", r"\frac", r"\dfrac",
    r"\tfrac", r"\partial", r"\nabla", r"\forall", r"\exists", r"\iff", r"\implies", r"\Rightarrow", r"\Leftarrow",
    r"\Leftrightarrow", r"\Longrightarrow", r"\Longleftrightarrow", r"\land", r"\lor", r"\neg", r"\wedge", r"\vee",
    r"\approx", r"\equiv", r"\dashv", r"\vdash", r"\leftrightarrow", r"\mid", r"\sqcup", r"\sqsubseteq", r"\colon", r"\ast", r"\sim", r"\ll", r"\gg", r"\prime", r"\top", r"\square", r"\qquad", r"\quad",
}
LAYOUT = {  # commands that only shape the formula
    r"\left", r"\right", r"\bigl", r"\bigr", r"\Bigl", r"\Bigr", r"\biggl", r"\biggr", r"\big", r"\Big", r"\,",
    r"\;", r"\!", r"\displaystyle", r"\textstyle", r"\limits", r"\nolimits", r"\begin", r"\end", r"\cases",
    r"\\", r"\{", r"\}", r"\|", r"\langle", r"\rangle", r"\lvert", r"\rvert", r"\lVert", r"\rVert", r"\href",
    r"\notag", r"\nonumber",
}
# an equation's number or label is not a symbol, nor are the letters inside it (2026-11-08: a paper's \tag{1} read as an
# undeclared symbol, and the model rewrote the equation to dodge the checker)
ARG_SKIPPED = {r"\tag", r"\label"}
ACCENTS = {r"\tilde", r"\hat", r"\bar", r"\overline", r"\underline", r"\widetilde", r"\widehat", r"\vec", r"\dot"}
FONTS = {r"\mathcal", r"\mathbb", r"\mathrm", r"\mathbf", r"\mathsf", r"\mathfrak", r"\operatorname", r"\boldsymbol"}
GLOSS = [r"\bi\.e\.", r"\bso that\b", r"\bin words\b", r"\bthis is why\b", r"\bnote that\b",
         r"\bthis is the only place\b", r"\bin other words\b", r"\bthat is to say\b"]
STATEMENT_KINDS = {"definition", "lemma", "theorem", "proposition", "corollary", "conjecture"}


def _mask(src: str) -> str:
    r"""The same string with regions that hold no symbols blanked out (same length, so positions match):
    words in \text{...}, environment names in \begin{...}/\end{...}, link targets in \href{...}."""
    out = list(src)
    for m in re.finditer(r"\\(?:text|textrm|mbox|textit|textbf)\s*\{[^{}]*\}|\\(?:begin|end)\s*\{[^{}]*\}|"
                         r"\\href\s*\{[^{}]*\}", src):
        for k in range(m.start(), m.end()):
            out[k] = " "
    return "".join(out)


def _group(s: str, i: int) -> tuple[str, int, int]:
    """The argument starting at s[i]: a {braced group}, a \\command, or one character.
    Returns (text, start of text, end of the argument)."""
    while i < len(s) and s[i] == " ":
        i += 1
    if i >= len(s):
        return "", i, i
    if s[i] == "{":
        depth, j = 0, i
        while j < len(s):
            depth += {"{": 1, "}": -1}.get(s[j], 0)
            if depth == 0:
                return s[i + 1:j], i + 1, j + 1
            j += 1
        return s[i + 1:], i + 1, len(s)
    if s[i] == "\\":
        m = re.match(r"\\[A-Za-z]+|\\.", s[i:])
        return m.group(0), i, i + len(m.group(0))
    return s[i], i, i + 1


def _norm(x: str) -> str:
    return re.sub(r"\s+", " ", x).strip()


def scan(src: str) -> list[tuple[tuple[str, bool, str], int, int]]:
    """Every symbol occurrence in a formula: (key, start, end), positions in `src`. A symbol's span covers its whole
    written form, sub- and superscripts included; symbols inside those scripts are listed too (nested spans)."""
    return _scan(_mask(src), 0, len(src))


def _scan(s: str, lo: int, hi: int) -> list:
    out = []
    i = lo
    while i < hi:
        c = s[i]
        start = i
        base = None
        if c == "\\":
            cmd, _, j = _group(s, i)
            if cmd in FONTS:
                arg, _, j = _group(s, j)
                base = f"{cmd}{{{_norm(arg)}}}" if cmd in (r"\operatorname", r"\mathrm") else f"{cmd} {_norm(arg)}"
            elif cmd in ACCENTS:
                arg, a0, j = _group(s, j)
                inner = _scan(s, a0, a0 + len(arg))
                # an accent on a digit (\bar 0_n, the zero vector) is a symbol of its own, its scripts its own: it used to have
                # no base, and the n of its subscript passed for the declared symbol (2026-11-08, "redeclared: n")
                base = f"{cmd} {inner[0][0][0]}" if inner else f"{cmd} {_norm(arg)}" if _norm(arg) else None
                out.extend(inner[1:])
            elif cmd in ARG_SKIPPED:   # the command and its argument
                if j < hi and s[j] == "*":
                    j += 1
                _, _, j = _group(s, j) if j < hi and s[j] == "{" else (None, None, j)
                i = j
                continue
            elif cmd in LAYOUT or cmd in STANDARD or not cmd[1:].isalpha():
                i = j
                continue
            else:
                base = cmd
            i = j
        elif c.isalpha():
            base, i = c, i + 1
        else:
            i += 1
            continue
        if base is None:
            continue
        has_sub, deco = False, ""
        while True:   # scripts may follow after spaces (plasTeX writes "\\sigma _e")
            k = i
            while k < hi and s[k] == " ":
                k += 1
            if k >= hi or s[k] not in "_^'":
                break
            i = k
            if s[i] == "'":
                base += "'"
                i += 1
                continue
            mark = s[i]
            arg, a0, i = _group(s, i + 1)
            if mark == "_":
                has_sub = True
                out.extend(_scan(s, a0, a0 + len(arg)))
            else:
                a = _norm(arg)
                if a in ("-", "+", r"\top", "*", r"\prime") or a.startswith(r"\mathrm"):
                    deco = a
                else:
                    out.extend(_scan(s, a0, a0 + len(arg)))
        if base not in STANDARD:
            out.append(((base, has_sub, deco), start, i))
    return out


def tokens(src: str) -> list[tuple[str, bool, str]]:
    """The keys of `scan`, in order."""
    return [k for k, _, _ in scan(src)]


def link(src: str, resolve) -> str:
    r"""Wrap each outermost symbol occurrence that `resolve(key)` maps to a URL in \href{url}{...}. Symbols nested in
    the scripts of a linked symbol are left as they are (the outer link covers them)."""
    spans = [(a, b, resolve(k)) for k, a, b in scan(src)]
    spans = [t for t in spans if t[2]]
    spans.sort(key=lambda t: (t[0], -(t[1] - t[0])))
    chosen, end = [], -1
    for a, b, url in spans:
        if a >= end:
            chosen.append((a, b, url))
            end = b
    for a, b, url in reversed(chosen):
        src = src[:a] + r"\href{" + url + "}{" + src[a:b] + "}" + src[b:]
    return src


BINDERS = [
    r"\\\{\s*([A-Za-z](?:_[A-Za-z])?)\s*(?::|\\in|\\mid|\|)",                       # {e : ...}, {x in ...}
    r"\\(?:sum|prod|max|min|sup|inf|bigcup|bigcap|lim)\s*_\{?\s*([A-Za-z](?:_[A-Za-z])?)\s*(?:\\in|=|:|\\to|,|\})",
    r"\\(?:forall|exists)\s*([A-Za-z](?:_[A-Za-z])?)",
]


def bound_in(src: str) -> set:
    """Variables a formula binds itself (set-builder, big operators, quantifiers)."""
    keys = set()
    for pat in BINDERS:
        for m in re.finditer(pat, src):
            keys.add(key_of(m.group(1)))
    return keys


def key_of(decl: str) -> tuple[str, bool, str]:
    t = tokens(decl)
    if not t:
        raise ValueError(f"cannot read a symbol from {decl!r}")
    return t[-1]


def _matches(use, declared: set) -> bool:
    base, sub, deco = use
    # x_i is a component of a declared x: indexing a declared plain symbol is a use of it
    return (use in declared or (base, sub, "") in declared or bool(deco and (base, False, deco) in declared)
            or bool(sub and (base, False, deco) in declared))


BIND_TYPE = re.compile(r"\\in\b|\\subseteq\b|\\colon|:")


def split_bind(b: str) -> tuple[str, str]:
    """A bound symbol and its type, if it carries one: "w \\in \\mathcal B" -> ("w", "\\in \\mathcal B")."""
    m = BIND_TYPE.search(b)
    if not m:
        return b.strip(), ""
    return b[:m.start()].strip(), _norm(b[m.start():].lstrip(":").strip())


def _which(use, declared):
    """The declared key a use resolves to (the same order as _matches), or None."""
    base, sub, deco = use
    for k in (use, (base, sub, ""), (base, False, deco) if deco else None, (base, False, deco) if sub else None):
        if k is not None and k in declared:
            return k
    return None


EXEMPT_FROM_USES = {"notation"}
DEFINING_KINDS = {"definition", "notation"}


def name_key(text: str) -> str:
    r"""A definition's name as words, for comparing a title with a \defterm: formula delimiters and braces dropped, a
    command's backslash dropped, spaces collapsed, lower case, no leading article. The title reaches the checker typeset
    ("n-dimensional system") and the term as source ("$n$-dimensional system"); both read the same here (2026-11-08)."""
    t = re.sub(r"\\[()\[\]]|\$", "", text)
    t = re.sub(r"\\(?:mathrm|text|textbf|emph|mathbf|mathbb|mathcal|mathfrak|mathsf|operatorname)\s*\{?([^{}\s]*)\}?", r"\1", t)   # a font: its letters
    t = re.sub(r"\\([A-Za-z]+)", r"\1", t).replace("{", "").replace("}", "")
    t = re.sub(r"\s+", " ", t).strip().lower()
    return re.sub(r"^(the|a|an) ", "", t)


def undeclarable(items: list[dict]) -> tuple[list[dict], list[dict]]:
    r"""Operators and delimiters (\times, \cdot, |\cdot|, \langle\rangle) are notation, not symbols: a \defines or
    \binds of one is reported ("undeclarable") and set aside, so the rest of the check still runs instead of stopping
    the build. The items come back with those declarations removed."""
    problems, out = [], []
    for it in items:
        it2 = dict(it)
        for field, sym_of in (("defines", lambda d: d[0]), ("binds", lambda b: split_bind(b)[0])):
            keep = []
            for d in it.get(field, []):
                sym = sym_of(d)
                if tokens(sym):
                    keep.append(d)
                else:
                    problems.append({"kind": "undeclarable", "label": it["label"],
                                     "detail": f"{sym} is an operator or a delimiter, not a symbol, so it cannot be declared: "
                                               "name the operation with \\defterm and explain its notation in a notation block, or declare the "
                                               "function by the letter the text gives it"})
            if field in it2 or keep:
                it2[field] = keep
        out.append(it2)
    return out, problems


def check(items: list[dict]) -> list[dict]:
    items, problems = undeclarable(items)
    problems += _check(items)
    by = {it["label"]: it for it in items}
    # the dependency closure: what each item depends on, directly or through others; a proof through its statement
    deps: dict[str, set] = {}

    def closure(label, seen=()):
        if label in deps:
            return deps[label]
        it = by.get(label)
        out = set()
        if it is None or label in seen:
            return out
        direct = set(it.get("uses", [])) | ({it["parent"]} if it.get("parent") else set())
        for d in direct:
            out |= {d} | closure(d, seen + (label,))
        deps[label] = out
        return out

    declared: dict[tuple, str] = {}
    kinds = {it["label"]: it.get("kind") for it in items}
    users: dict[tuple, set] = {}
    for it in items:
        label = it["label"]
        own = {key_of(sym) for sym, _ in it.get("defines", [])}
        local = {key_of(split_bind(b)[0]) for b in it.get("binds", [])
                 + (by[it["parent"]].get("binds", []) if it.get("parent") in by else [])}
        seen = set()
        for src in it.get("math", []):
            for use in tokens(src):
                k = _which(use, declared)
                if k is None or k in seen or _matches(use, own) or _matches(use, local) \
                        or use in bound_in(src):
                    continue
                seen.add(k)
                src_label = declared[k]
                users.setdefault(k, set()).add(label)
                if "uses" in it and kinds.get(src_label) not in EXEMPT_FROM_USES and src_label != label \
                        and src_label not in closure(label):
                    problems.append({"kind": "uses", "label": label,
                                     "detail": f"{k[0]} is declared in {src_label}, which {label} does not depend on"})
        for sym, _ in it.get("defines", []):
            declared.setdefault(key_of(sym), label)
    for k, label in declared.items():
        it = by[label]
        if it.get("kind") in DEFINING_KINDS:
            continue
        own_family = {label, it.get("parent")} | {x["label"] for x in items if x.get("parent") == label}
        others = sorted(users.get(k, set()) - own_family)
        if others:
            problems.append({"kind": "local-def", "label": label,
                             "detail": f"{k[0]} is declared inside this {it.get('kind')} and used in {', '.join(others)}: "
                                       "give it a definition of its own"})
    # one letter, one role: the same letter bound with two different types in items that depend on each other
    typed: dict[str, dict] = {}
    for it in items:
        for b in it.get("binds", []):
            sym, ty = split_bind(b)
            if ty:
                typed.setdefault(it["label"], {})[key_of(sym)] = (sym, ty)
    for a in typed:
        for b in typed:
            if a >= b or not (a in closure(b) or b in closure(a)):
                continue
            for k in typed[a].keys() & typed[b].keys():
                if typed[a][k][1] != typed[b][k][1]:
                    problems.append({"kind": "two-roles", "label": b,
                                     "detail": f"{typed[b][k][0]} is {typed[b][k][1]} here and {typed[a][k][1]} in {a}"})
    # a statement in numbered parts: its proof treats each part
    for it in items:
        st = by.get(it.get("parent"))
        n = (st or {}).get("parts", 0)
        if it.get("kind") != "proof" or n < 2:
            continue
        missing = [str(i) for i in range(1, n + 1) if f"({i})" not in it.get("text", "")]
        if missing:
            problems.append({"kind": "proof-parts", "label": it["label"],
                             "detail": f"{st['label']} has {n} parts; the proof has no ({'), ('.join(missing)})"})
    problems += _writing(items)
    return problems


def _strip_math(tex: str) -> str:
    tex = re.sub(r"\$\$.*?\$\$|\$[^$]*\$|\\\(.*?\\\)|\\\[.*?\\\]", " ", tex, flags=re.S)
    return re.sub(r"\s+", " ", tex)


REF = re.compile(r"\(\s*Definitions?~?\s*\\ref\{([^}]+)\}(?:\s*,\s*part~?\s*\S+?)?\s*\)")


def _writing(items: list[dict]) -> list[dict]:
    """Reading rules made mechanical (docs: the user's notes of 2026-11-01 to 11-05)."""
    problems = []
    terms = {it["label"]: [t.lower() for t in it.get("terms", [])] for it in items}
    for it in items:
        src = it.get("source") or ""
        for m in REF.finditer(src):
            target = m.group(1)
            before = _strip_math(src[max(0, m.start() - 160):m.start()]).lower()
            before = re.split(r"[.;:]\s", before)[-1][-80:]     # the same clause, just before the reference
            hit = [t for t in terms.get(target, []) if target != it["label"]
                   and re.search(r"\b" + re.escape(t) + r"(s|es)?\b", before)]
            if hit:
                problems.append({"kind": "ref-after-term", "label": it["label"],
                                 "detail": f"'{hit[0]}' is already a link to {target}: drop \"{m.group(0).strip()}\""})
        problems += unnumbered([it])
    remarks = {it["label"] for it in items if it.get("kind") == "remark"}
    for it in items:
        if it["label"] in remarks:
            continue
        cited = set(it.get("uses", []))
        if it.get("kind") == "proof":
            cited |= set(re.findall(r"\\ref\{([^}]+)\}", it.get("source") or ""))
        for r in sorted(cited & remarks):
            problems.append({"kind": "remark-used", "label": r,
                             "detail": f"{it['label']} relies on it: a remark nothing depends on, or a lemma with a proof"})
    return problems


PART_KINDS = ("lemma", "theorem", "proposition", "corollary")
# a reference to an item of a card ("\\ref{lem:x}(2)", "\\itemref{lem:x}{2}", "part (2) of"), not a part of this card
ITEM_REF = re.compile(r"\\(?:ref|cref|Cref|autoref)\s*\{[^}]*\}\s*~?\s*\(\s*\d+[a-z]?\s*\)|\\itemref\s*\{[^}]*\}\s*\{[^}]*\}|"
                      r"\\eqref\s*\{[^}]*\}|\b(?:parts?|items?|conditions?|equations?|steps?|cases?)\s*~?\s*\(\s*\d+\s*\)"
                      r"(?:\s*(?:,|and|or|to|--|-)\s*\(\s*\d+\s*\))*", re.I)


def _inline_parts(src: str) -> list[str]:
    """The inline part numbers "(1)", "(2)", ... of a card's prose, in order, when it numbers its parts inline:
    a "(1)" followed later by a "(2)", outside formulas, references to items and its numbered lists."""
    body = _no_math(_tag_split(_body(src))[0])
    body = re.sub(r"\\begin\{(enumerate|itemize)\}.*?\\end\{\1\}", " ", body, flags=re.S)
    body = ITEM_REF.sub(" ", body)
    nums = [m.group(1) for m in re.finditer(r"(?<![\w\\])\(\s*(\d)\s*\)", body)]
    if "1" in nums and "2" in nums[nums.index("1") + 1:]:
        return nums
    return []


def unnumbered(items: list[dict], plan: bool = False) -> list[dict]:
    """A card of several definitions (its title names two or more things), or a statement (lemma, theorem,
    proposition, corollary) that numbers its parts inline ("(1) ... (2) ..."), without a numbered list (one \\item per
    definition or part). Kind "unnumbered" on written cards; with plan=True (planned cards) kind "unnumbered-plan",
    an advisory."""
    out = []
    kind = "unnumbered-plan" if plan else "unnumbered"
    for it in items:
        if it.get("parts", 0) >= 2:
            continue
        names = it.get("names") or []
        if it.get("kind") == "definition" and len(names) >= 2:
            out.append({"kind": kind, "label": it["label"],
                        "detail": f"it defines {len(names)} things ({', '.join(names)}): an enumerate list, one \\item "
                                  f"per definition"})
        elif it.get("kind") in PART_KINDS and _inline_parts(it.get("source") or ""):
            out.append({"kind": kind, "label": it["label"],
                        "detail": "its parts are numbered inline (\"(1) ... (2) ...\"): an enumerate list, one \\item "
                                  "per part"})
    return out


def _check(items: list[dict]) -> list[dict]:
    problems: list[dict] = []
    declared: dict[tuple, str] = {}          # key -> label of the declaring item
    scope: dict[str, set] = {}               # label -> keys declared or bound in that item
    terms_at: dict[str, int] = {}            # term -> index of the defining item
    for idx, it in enumerate(items):
        for term in it.get("terms", []):
            terms_at.setdefault(term.lower(), idx)
    for idx, it in enumerate(items):
        label = it["label"]
        own = set()
        for sym, ty in it.get("defines", []):
            k = key_of(sym)
            if not str(ty).strip():
                problems.append({"kind": "untyped", "label": label, "detail": sym})
            if k in declared and declared[k] != label:
                problems.append({"kind": "redeclared", "label": label,
                                 "detail": f"{sym} (first declared in {declared[k]})"})
            own.add(k)
        local = {key_of(split_bind(b)[0]) for b in it.get("binds", [])}
        if it.get("parent") in scope:
            local |= scope[it["parent"]]
        visible = set(declared) | own | local
        seen = set()
        for src in it.get("math", []):
            here = visible | bound_in(src)
            for use in tokens(src):
                if use in seen:
                    continue
                seen.add(use)
                if not _matches(use, here):
                    problems.append({"kind": "undeclared", "label": label, "detail": f"{use[0]} in {src.strip()}"})
        for sym, _ in it.get("defines", []):
            declared.setdefault(key_of(sym), label)
        scope[label] = own | local
        text = it.get("text", "")
        for term, at in terms_at.items():
            if at > idx and re.search(r"\b" + re.escape(term) + r"\b", text, re.I):
                problems.append({"kind": "term-before", "label": label,
                                 "detail": f"'{term}' used before {items[at]['label']} defines it"})
        if it.get("kind") in STATEMENT_KINDS:
            for pat in GLOSS:
                m = re.search(pat, text, re.I)
                if m:
                    problems.append({"kind": "gloss", "label": label, "detail": m.group(0)})
    return problems


# ---- style checks: the book's reading rules made mechanical (user, 2026-11-15: "rules must be enforced mechanically, not by
# instructions to models, because prompt rules drift"). Each finding carries a severity: "problem" (the page is not done;
# symbols-report.json, the strict option) or "advisory" (a second look; reported apart, never blocks).

STATUS_VALUES = ("known", "proved and rechecked in this project", "claimed elsewhere, not checked here", "open")
TAGS = ("Status", "In Lean", "References")
ADVISORY = {"proof-in-statement", "long-card", "definition-states-fact", "duplicate-concept", "unlinked-term",
            "unnumbered-plan"}
# what each kind means, in words a reader of a report can act on (exported with the data: blueprint-data.json "kinds")
KINDS = {
    "undeclared": "a symbol is used before any card declares it (\\defines) and is not bound here (\\binds)",
    "redeclared": "a symbol is declared a second time: one meaning per symbol",
    "untyped": "a declaration has no type",
    "undeclarable": "an operator or a delimiter is declared as a symbol",
    "term-before": "a term is used before the card that defines it",
    "gloss": "an explanatory phrase (\"i.e.\", \"so that\", \"note that\") inside a statement",
    "local-def": "a symbol declared inside a lemma, theorem, remark or proof is used by another card: give it a definition",
    "two-roles": "a letter is bound with two different types in cards that depend on each other",
    "uses": "a symbol is used without a \\uses path to the card that declares it",
    "proof-parts": "a statement in numbered parts has a proof that skips a part",
    "ref-after-term": "\"(Definition~\\ref{...})\" right after a term that is already a link to it",
    "unnumbered": "a card of several definitions (its title names two or more things), or a statement that numbers "
                  "its parts inline (\"(1) ... (2) ...\"), is not a numbered list: write an enumerate list, one \\item "
                  "per definition or part, so each has its number, its anchor and its link",
    "unnumbered-plan": "advisory: the plan of a planned card numbers several definitions or parts inline: when the card "
                       "is written, it is an enumerate list, one \\item per definition or part (the same rule as "
                       "unnumbered; a plan is never a problem)",
    "remark-used": "a remark that a proof relies on: make it a lemma with a proof",
    "unnamed": "a named definition does not introduce its name as a term (\\defterm)",
    "contains": "a \\contains names no card",
    "itemref": "a reference to an item the card does not have",
    "forward-ref": "a card cites a card or a section that comes later in the book: cards build on what comes before",
    "chapter-mention": "a card mentions the plan of the book (\"Chapter 5\", \"below\", \"later chapters\"): signposts go in "
                       "chapter and section introductions",
    "project-path": "a card names a project file or path (tools/..., x.lean, x.md): cards hold mathematics only; Lean "
                    "names go in \\lean{} and the \"In Lean:\" tag line",
    "tag-lines": "Status, In Lean and References are tag lines at the end of the statement (\\textit{Status:} ...), with a "
                 "Status from the fixed list, never words of its sentences",
    "known-needs-why": "a result with status known needs a proof block with a sketch of why it is true, not only a reference",
    "proof-in-statement": "advisory: a proof or a sketch seems to sit inside the statement; it goes in the proof block",
    "long-card": "advisory: a long card (more than four items; a notation card with more than six items or more than "
                 "one topic): consider splitting it",
    "definition-states-fact": "advisory: a definition seems to state a fact; facts go in a lemma, where they are proved",
    "duplicate-concept": "advisory: two cards seem to define one concept (\"compact set\" and \"compact space\", "
                         "\"ideal\" and \"ideal of a ring\"), or a special case is defined and used before its general "
                         "concept: define a concept once, in the generality the book uses, and present special cases as "
                         "instances of it",
    "unlinked-term": "advisory: a card uses a defined term's adjective (\"compact\" of \"compact set\") where the linking "
                     "rule declined it (said of \"it\", of a formula of unknown kind, of a near noun: \"compact space\"), "
                     "and no form of the term is linked in the card: add an alias or a synonym, or reword",
}


def _braced(s: str, i: int) -> int:
    """The end (one past the closing brace) of the {group} starting at s[i] == '{'."""
    depth = 0
    for j in range(i, len(s)):
        depth += {"{": 1, "}": -1}.get(s[j], 0) if (j == 0 or s[j - 1] != "\\") else 0
        if depth == 0:
            return j + 1
    return len(s)


def _commands(s: str, names, keep_arg=None) -> str:
    r"""`s` with each \name[opt]{arg}... removed (all its braced arguments); with keep_arg=k, its k-th argument (0-based)
    stays in place of the command. Newlines inside a removed command are kept, so line numbers stay."""
    pat = re.compile(r"\\(" + "|".join(re.escape(n) for n in names) + r")(?![A-Za-z])")
    out, i = [], 0
    while True:
        m = pat.search(s, i)
        if not m:
            out.append(s[i:])
            return "".join(out)
        out.append(s[i:m.start()])
        j = m.end()
        args = []
        while True:
            k = j
            while k < len(s) and s[k] in " \t":
                k += 1
            if k < len(s) and s[k] == "[" and not args:
                e = s.find("]", k)
                j = e + 1 if e >= 0 else len(s)
                continue
            if k < len(s) and s[k] == "{":
                e = _braced(s, k)
                args.append(s[k + 1:e - 1])
                j = e
                continue
            break
        gone = s[m.start():j]
        kept = args[keep_arg] if keep_arg is not None and len(args) > keep_arg else ""
        out.append(kept + "\n" * (gone.count("\n") - kept.count("\n")))
        i = j


META_CMDS = ("label", "uses", "lean", "leanok", "notready", "mathlibok", "discussion", "proves", "defines", "binds",
             "contains", "planned")
MATH_RE = re.compile(r"\$\$.*?\$\$|\$(?:\\.|[^$\\])*\$|\\\(.*?\\\)|\\\[.*?\\\]|"
                     r"\\begin\{(equation|align|gather|multline|eqnarray)(\*?)\}.*?\\end\{\1\2\}", re.S)


def _body(src: str) -> str:
    r"""A card's TeX without its environment lines, comments and metadata (\label, \uses, \defines, ...); \defterm{x} is x."""
    src = re.sub(r"(?<!\\)%[^\n]*", "", src)
    src = re.sub(r"^\s*\\begin\{[^}]*\}(\[[^\]\n]*(?:\[[^\]\n]*\][^\]\n]*)*\])?", "", src)
    src = re.sub(r"\\end\{[^}]*\}\s*$", "", src)
    src = _commands(src, META_CMDS)
    return _commands(src, ("defterm",), keep_arg=0)


def _no_math(tex: str, mark: str = " MATH ") -> str:
    """Formulas replaced by a mark (their newlines kept)."""
    return MATH_RE.sub(lambda m: mark + "\n" * m.group(0).count("\n"), tex)


TAG = re.compile(r"\\textit\s*\{\s*([A-Z][A-Za-z ]{0,30}?)\s*:\s*\}")


def _tag_split(body: str) -> tuple[str, list[tuple[str, str]], list[str]]:
    """A statement's text before its tag lines, the tag lines ((name, value)), and complaints about their place. A tag
    line starts with \\textit{Name:}; the tag lines run from the first one to the end of the statement, each value up to
    the next tag. (plasTeX joins a card's lines, keeping only paragraph breaks, so a tag is found by its command, not by
    its line.) Complaints: a tag that sits inside a sentence, and text after the tag lines."""
    tags_at = list(TAG.finditer(body))
    if not tags_at:
        return body, [], []
    head = body[:tags_at[0].start()]
    bad = []
    before = head.rstrip()
    if before and not re.search(r"(?:[.!?)]|\\\]|\\end\{[^}]*\}|\$\$|\n\s*\n)\s*$", head):
        bad.append(f"\"{tags_at[0].group(1)}:\" inside a sentence (\"...{_clean_words(before)[-40:]}\")")
    tags = []
    for a, b in zip(tags_at, tags_at[1:] + [None]):
        val = body[a.end():b.start() if b else len(body)]
        parts = re.split(r"\n\s*\n", val, maxsplit=1)
        tail = parts[1].strip() if len(parts) > 1 else ""
        m = re.search(r"\\(?:end|begin)\s*\{|\\item\b", parts[0])
        if m:
            tail = (parts[0][m.start():] + " " + tail).strip()
            parts[0] = parts[0][:m.start()]
        tags.append((a.group(1), parts[0].strip()))
        if tail:
            bad.append(f"text after the tag lines (\"{_clean_words(tail)[:60]}\")")
    return head, tags, bad


def _clean_words(s: str) -> str:
    return re.sub(r"\s+", " ", s).strip()


CHAPTER_PATTERNS = [
    r"\b(?:chapters?|sections?)\s*~?\s*(?:\d|\\ref\b|[IVX]+\b)",
    r"§\s*\d",
    r"\b(?:later|earlier|previous|preceding|next|following|coming|remaining|subsequent|last|final|other) "
    r"(?:chapters?|sections?|cards?)\b",
    r"\b(?:this|that|the present|the next|the previous) (?:chapter|section)\b",
    r"\bthe rest of (?:the|this) (?:book|chapter|section)\b",
    r"\b(?:see|shown|proved|proven|defined|discussed|treated|explained|introduced|stated|made precise|return(?:s|ed)?|"
    r"come back|comes|used|needed) later\b",
    r"\blater in (?:the|this) (?:book|chapter|section)\b",
    r"\b(?:the|this) book will\b",
    r"\bfor now\b", r"\bso far\b",
]
# "below" as a signpost to later cards ("the cards below", "the lattice measure below"), not "bounded below", "$P_j$ below
# $V_j$", "far below the threshold", nor a pointer inside the card ("the conditions below:"); not read in a proof, where
# "below" points inside the proof
BELOW_PATTERNS = [
    r"(?<!bounded )(?<!from )(?<!far )(?<!stays )(?<!stay )(?<!remains )(?<!lies )(?<!lie )(?<!falls )(?<!drops )"
    r"(?<!goes )(?<!just )(?<!strictly )(?<!MATH )(?<!is )(?<!are )(?<!be )\bbelow\b"
    r"(?!\s*(?:MATH|the\b|a\b|an\b|its\b|their\b|\d|zero\b|one\b|threshold|level|that\b|which\b|:|hold))",
]
CHAPTER_RE = re.compile("|".join(f"(?:{p})" for p in CHAPTER_PATTERNS), re.I)
BELOW_RE = re.compile("|".join(f"(?:{p})" for p in BELOW_PATTERNS), re.I)
BELOW_INSIDE = re.compile(r"\b(?:conditions?|properties|property|cases?|formulas?|equations?|list|items?|parts?|steps?) below$",
                          re.I)
PROJECT_DIRS = ("GRN", "tools", "texts", "docs", "specs", "prover", "runs", "biolean", "tests", "Proofs", "src", "scripts",
                "third_party")
PROJECT_RE = re.compile(
    r"(?<![\w.:/-])(?:[\w-]+/)*[\w-]+\.(?:lean|py|md|json|tex|sh|js|mjs|ts|toml|ya?ml|txt|csv|ipynb|jinja2s?|html|css)\b"
    r"|(?<![\w.:/-])(?:" + "|".join(PROJECT_DIRS) + r")/")
PROOF_IN_STATEMENT = re.compile(r"(?:^|(?<=[.:;]\s)|(?<=\())(?:Proof|Proof sketch|Sketch)\b|\b[Ww]hy it is true\b|"
                                r"\b[Ss]ketch of (?:the|a) proof\b|\\qed\b|\\qedhere\b|\\blacksquare\b|∎|"
                                r"\\(?:Box|square)\s*\$?\s*$", re.M)
FACT_RE = re.compile(r"^(?:each|every|all|both|it|they|these|this|the (?:two|three|four)(?= ))\b[^.;]*?\b(?:is|are|has|have|forms?|"
                     r"satisf(?:y|ies)|contains?)\b", re.I)


def _sentences(s: str) -> list[str]:
    return [x.strip() for x in re.split(r"(?<=[.;:])\s+(?=[A-Z$\\])", s) if x.strip()]


def _top_items(body: str) -> int:
    """The number of \\item lines at the first level of a card's lists (itemize, enumerate, description)."""
    depth, n = 0, 0
    for m in re.finditer(r"\\(begin|end)\{(?:enumerate|itemize|description)\}|\\item\b", body):
        if m.group(1) == "begin":
            depth += 1
        elif m.group(1) == "end":
            depth -= 1
        elif depth == 1:
            n += 1
    return n


def _ref_only(proof_prose: str) -> bool:
    """A proof that is only a pointer: no formula, and under a dozen words once links and references are taken out
    ("See Glimm and Jaffe, Theorem 3."). A short computation ("By (3), $U'=\\omega U\\omega^{-1}$, and the trace ...")
    is a proof."""
    t = _commands(proof_prose, ("href",), keep_arg=None)
    t = _commands(t, ("cite", "ref", "itemref", "eqref", "cref", "Cref", "url"))
    if re.search(r"\bMATH\b", t):
        return False
    return len(re.findall(r"[A-Za-z]{2,}", t)) < 12


def style(items: list[dict]) -> list[dict]:
    """The style checks (forward-ref, chapter-mention, project-path, tag-lines, known-needs-why; advisory:
    proof-in-statement, long-card, definition-states-fact, duplicate-concept). Each item needs "label", "kind", "source", and for a proof
    "parent"; optionally "pos" (its place in the book, default its index in `items`) and "cites": what its references
    point at, [{"ref": label as written, "item": label of the card it lies in, "at": that card's place}] (a reference
    to a section: the place of the first card after its start). Without "cites", the \\ref and \\itemref labels in the source that name items are used. Optional "terms" and
    "uses" (for duplicate-concept; default: the source's \\defterm and \\uses). Findings carry "severity"."""
    out = []
    pos = {it["label"]: k for k, it in enumerate(items)}
    proofs = {it.get("parent"): it for it in items if it.get("kind") == "proof" and it.get("parent")}

    def add(kind, label, detail):
        out.append({"kind": kind, "label": label, "detail": detail,
                    "severity": "advisory" if kind in ADVISORY else "problem"})

    for k0, it in enumerate(items):
        k = it.get("pos", k0)
        label, kind = it["label"], it.get("kind")
        body = _body(it.get("source") or "")
        head, tags, misplaced = _tag_split(body)
        is_proof = kind == "proof"
        # forward-ref: what the card cites comes before it (a proof: before it, its own statement excepted)
        cites = it.get("cites")
        if cites is None:
            cites = [{"ref": r, "item": r, "at": items[pos[r]].get("pos", pos[r])} for r in
                     re.findall(r"\\(?:ref|itemref|eqref|cref|Cref|autoref)\s*\{([^}]+)\}", it.get("source") or "") if r in pos]
        seen = set()
        for c in cites:
            if c.get("at") is None or c["at"] <= k or (c.get("item") is not None and c["item"] in (label, it.get("parent"))) \
                    or c["ref"] in seen:
                continue
            seen.add(c["ref"])
            add("forward-ref", label, f"cites {c['ref']}, which comes later in the book"
                                      + ("" if c.get("item") else " (a chapter or section)"))
        # card text: the prose without formulas, links' targets, and the tag lines
        prose = _no_math(head)
        prose_nolinks = _commands(prose, ("href",), keep_arg=None)
        prose_nolinks = _commands(prose_nolinks, ("url",))
        hits = [m.group(0) for m in CHAPTER_RE.finditer(prose_nolinks)]
        if not is_proof:
            hits += [m.group(0) for m in BELOW_RE.finditer(prose_nolinks)
                     if not BELOW_INSIDE.search(prose_nolinks[max(0, m.start() - 40):m.end()])]
        for h in hits:
            add("chapter-mention", label, f"\"{_clean_words(h)}\": the plan of the book goes in a chapter or "
                                          "section introduction, not in a card")
        prose_paths = _commands(_commands(_no_math(head), ("href",), keep_arg=1), ("url",))
        for m in PROJECT_RE.finditer(prose_paths + "\n" + "\n".join(v for n, v in tags if n != "In Lean")):
            add("project-path", label, f"\"{m.group(0)}\": a card names no project file or path")
        # tag lines: only at the end of a statement, Status from the fixed list
        names = [n for n, _ in tags]
        for n, v in tags:
            if n == "Status":
                val = re.sub(r"\s*\.\s*$", "", _clean_words(v))
                if val not in STATUS_VALUES:
                    add("tag-lines", label, f"Status \"{val}\" is not one of: " + "; ".join(STATUS_VALUES))
            if is_proof and n in TAGS:
                add("tag-lines", label, f"\"{n}:\" in a proof: tag lines end the statement")
        for n in TAGS:
            if names.count(n) > 1:
                add("tag-lines", label, f"two \"{n}:\" tag lines")
        for b in misplaced if any(n in TAGS for n in names) else []:
            add("tag-lines", label, f"{b}: tag lines end the statement, each on a line of its own")
        for m in re.finditer(r"\\textit\{\s*(" + "|".join(TAGS) + r")\s*:\s*\}|\b(Status|In Lean|References)\s*:",
                             _commands(prose, ("href",))):
            add("tag-lines", label, f"\"{m.group(1) or m.group(2)}:\" inside the text: it is a tag line of its own, at the "
                                    "end of the statement")
        status = next((re.sub(r"\s*\.\s*$", "", _clean_words(v)) for n, v in tags if n == "Status"), None)
        if status == "known" and not is_proof:
            pr = proofs.get(label)
            if pr is None:
                add("known-needs-why", label, "status known and no proof block: add a short sketch of why it is true")
            elif _ref_only(_no_math(_body(pr.get("source") or ""))):
                add("known-needs-why", label, "status known and the proof block is only a reference: add a short sketch "
                                              "of why it is true")
        # advisory
        if not is_proof:
            m = PROOF_IN_STATEMENT.search(_commands(prose, ("href",)))
            if m:
                add("proof-in-statement", label, f"\"{_clean_words(m.group(0))}\" in the statement: a proof or a sketch goes "
                                                 "in the proof block")
            n_items = _top_items(body)
            heads = len(re.findall(r"\\textbf\s*\{", head))
            if kind == "notation" and (n_items > 6 or heads > 1):
                add("long-card", label, f"a notation card with {n_items} items and {heads} topic headings: one topic per "
                                        "notation card, just before its first use")
            elif kind != "notation" and n_items > 4:
                add("long-card", label, f"{n_items} items: consider splitting the card")
        if kind == "definition":   # a sentence with the defined term in it defines; the others are read for facts
            marked = re.sub(r"\\defterm\s*(?:\[[^\]]*\]\s*)?\{", r"\\defterm{DEFTERM ", it.get("source") or "")
            flat = _commands(_no_math(_tag_split(_body(marked))[0]), ("href",))
            flat = re.sub(r"\\item\b", "\n\n", flat)
            for para in re.split(r"\n\s*\n", flat):
                for s in _sentences(_clean_words(para)):
                    if re.match(r"(?:examples?|for example|for instance)\b", s, re.I):
                        continue
                    if "DEFTERM" not in s and FACT_RE.match(s) and not re.search(r"\b(?:called|call|write|written|denote[sd]?|stands? for|means|"
                                                          r"let|is said|we say|defined)\b", s, re.I):
                        add("definition-states-fact", label, f"\"{s[:80]}\": a fact in a definition; state it in a lemma")
    for f in duplicate_concepts(items):
        add("duplicate-concept", f["label"], f["detail"])
    return out


# ---- duplicate-concept (advisory): "define a concept once, in the generality the book uses" (user, 2026-11-17).
# A term is read as its words without stop words, each singular: a head noun (the last word before the first
# preposition) and its qualifiers (the other words). Two terms of different cards name one concept when their heads
# agree and the qualifiers of one are among those of the other ("ideal" / "ideal of a ring", "Lie algebra" / "Lie
# algebra of a matrix group", "invariant" twice), or when their qualifiers agree and both heads are carriers
# ("compact set" / "compact space"). A different qualifier on each side ("continuous function" / "smooth function") is
# two concepts. Not flagged: the more specific card depends on the general one (\uses, directly or through other cards)
# and presents itself as an instance of it: its text says "is a <general>", "a <general> ... that" or "the <general>
# of" (an adjective may stand between: "is a simple Lie algebra").

TERM_STOP = {"a", "an", "the", "of", "on", "in", "for", "to", "with", "and", "by", "at", "from", "its", "their",
             "this", "that", "throughout", "over", "under", "between", "into", "as", "is", "are", "be"}
TERM_PREPS = {"of", "on", "in", "for", "throughout", "over", "under", "between", "at", "from", "with", "into"}
CARRIERS = {"set", "subset", "space", "subspace", "map", "mapping", "function", "operator", "matrix", "sequence"}
_IRREGULAR = {"matrices": "matrix", "vertices": "vertex", "indices": "index", "simplices": "simplex", "bases": "basis",
              "axes": "axis", "data": "datum", "criteria": "criterion"}


def _singular(w: str) -> str:
    if w in _IRREGULAR:
        return _IRREGULAR[w]
    if len(w) > 4 and w.endswith("ies"):
        return w[:-3] + "y"
    if len(w) > 4 and re.search(r"(?:ss|ch|sh|x|z)es$", w):
        return w[:-2]
    if len(w) > 3 and w.endswith("s") and not re.search(r"(?:ss|us|is|ics)$", w):
        return w[:-1]
    return w


def _term_words(term: str) -> list[str]:
    """A term's words: formulas dropped, lower case, punctuation off (a hyphenated word stays one word)."""
    t = name_key(re.sub(r"\$[^$]*\$|\\\(.*?\\\)", " ", term))
    return [w for w in (x.strip(".,;:()'\"`-") for x in t.replace("\u2013", "-").split()) if w]


def term_shape(term: str):
    """(head, qualifiers) of a term, both singular and without stop words; None for a term with no content word."""
    words = _term_words(term)
    first = next((k for k, w in enumerate(words) if w in TERM_PREPS and k > 0), len(words))
    pre = [_singular(w) for w in words[:first] if w not in TERM_STOP]
    post = [_singular(w) for w in words[first:] if w not in TERM_STOP]
    if not pre:
        return None
    head = pre[-1]
    if len(head) < 2:
        return None
    return head, frozenset(pre[:-1] + post) - {head}


def _phrase_re(term: str) -> str:
    """A regex for a term's words in running text: each word singular or plural, any spacing."""
    parts = []
    for w in _term_words(term):
        one = _singular(w)
        if w in ("a", "an", "the"):
            parts.append("(?:an?|the)")
        elif w in TERM_STOP:
            parts.append(re.escape(w))
        elif w in _IRREGULAR or one in _IRREGULAR.values():
            many = next((k for k, v in _IRREGULAR.items() if v == one), w)
            parts.append("(?:" + re.escape(one) + "|" + re.escape(many) + ")")
        elif one.endswith("y") and len(one) > 3:
            parts.append(re.escape(one[:-1]) + "(?:y|ies)")
        else:
            parts.append(re.escape(one) + "(?:s|es)?")
    return r"\s+".join(parts)


def _plain(src: str) -> str:
    """A card's prose for reading terms: formulas as MATH, \\defterm{x} as x, no tag lines, lower case, one line."""
    return _clean_words(_commands(_no_math(_tag_split(_body(src or ""))[0]), ("href",), keep_arg=1)).lower()


def _presents_as_instance(text: str, general: str) -> bool:
    g = _phrase_re(general)
    adj = r"(?:[\w-]+\s+){0,3}?"
    return bool(re.search(r"\b(?:is|are|be|being)\s+(?:an?\s+|the\s+|one\s+)?" + adj + g + r"\b", text)
                or re.search(r"\b(?:an?|any|every|each)\s+" + adj + g + r"\b(?:[^.;]{0,80}?)\b(?:that|which|whose|"
                             r"such that|in which|with|where)\b", text)
                or re.search(r"\bthe\s+" + g + r"\s+of\b", text))


def duplicate_concepts(items: list[dict]) -> list[dict]:
    """The duplicate-concept advisories: findings {"label", "detail", "other"}. Each item: "label", "kind", "source";
    optionally "terms" (default: the \\defterm arguments of its source), "uses" (default: its \\uses), "pos"."""
    cards = [it for it in items if it.get("kind") != "proof"]
    pos = {it["label"]: it.get("pos", k) for k, it in enumerate(items)}
    terms, uses, text = {}, {}, {}
    for it in cards:
        src = it.get("source") or ""
        terms[it["label"]] = it["terms"] if it.get("terms") is not None else \
            [src[m.end():_braced(src, m.end() - 1) - 1] for m in re.finditer(r"\\defterm\s*(?:\[[^\]]*\]\s*)?\{", src)]
        uses[it["label"]] = set(it["uses"]) if it.get("uses") is not None else \
            {u.strip() for m in re.finditer(r"\\uses\s*\{([^}]*)\}", src) for u in m.group(1).split(",") if u.strip()}
        text[it["label"]] = _plain(src)

    reach_memo: dict[str, set] = {}

    def reach(label):
        if label not in reach_memo:
            reach_memo[label] = set()
            out, todo = set(), list(uses.get(label, ()))
            while todo:
                u = todo.pop()
                if u not in out:
                    out.add(u)
                    todo += list(uses.get(u, ()))
            reach_memo[label] = out
        return reach_memo[label]

    defs = [(it["label"], t, term_shape(t)) for it in cards for t in terms[it["label"]]]
    defs = [d for d in defs if d[2] is not None]
    found: dict[tuple[str, str], dict] = {}
    for i, (la, ta, (ha, qa)) in enumerate(defs):
        for lb, tb, (hb, qb) in defs[i + 1:]:
            if la == lb:
                continue
            if ha == hb and qa == qb:
                rel = "same"
            elif ha == hb and qa < qb:
                rel, gen, spec = "nested", (la, ta), (lb, tb)
            elif ha == hb and qb < qa:
                rel, gen, spec = "nested", (lb, tb), (la, ta)
            elif qa == qb and qa and ha in CARRIERS and hb in CARRIERS:
                rel = "carrier"
            else:
                continue
            if rel == "nested":
                instance = gen[0] in reach(spec[0]) and _presents_as_instance(text[spec[0]], gen[1])
            elif rel == "carrier":
                instance = any(g[0] in reach(s[0]) and _presents_as_instance(text[s[0]], g[1])
                               for g, s in (((la, ta), (lb, tb)), ((lb, tb), (la, ta))))
            else:
                instance = False
            late = ""
            if rel == "nested" and pos[spec[0]] < pos[gen[0]]:
                used = [it["label"] for it in cards if pos[it["label"]] < pos[gen[0]] and it["label"] != spec[0]
                        and re.search(r"\b" + _phrase_re(spec[1]) + r"\b", text[it["label"]])]
                late = (f"; the general term '{gen[1]}' comes late: the more specific '{spec[1]}' is defined before it, in "
                        f"{spec[0]}" + (f", and used in {', '.join(used[:4])}" + (" ..." if len(used) > 4 else "")
                                         if used else "") + ": define the general concept first")
            if instance and not late:
                continue
            for me, mine, other, theirs in ((la, ta, lb, tb), (lb, tb, la, ta)):
                key = (me, other)
                if key in found:
                    continue
                if instance:   # only the late general definition is reported, on its own card
                    if me != gen[0]:
                        continue
                    detail = late[2].upper() + late[3:]
                elif rel == "same":
                    detail = f"'{mine}' is also defined in {other}: define a concept once"
                elif rel == "carrier":
                    detail = (f"'{mine}' and '{theirs}' in {other} seem to be one concept on two carriers: define it once, "
                              f"in the generality the book uses")
                elif me == spec[0] and late:
                    detail = (f"'{mine}' is a variant of '{theirs}', which is defined later, in {other}: define the general "
                              f"concept first and present this one as an instance of it")
                elif me == spec[0]:
                    one = re.sub(r"\S+$", lambda m: _singular(m.group(0)), theirs)
                    art = "an" if one[:1].lower() in "aeiou" else "a"
                    how = (f"\"{art} {one} ... that\"" if other in reach(me) else
                           f"\\uses{{{other}}} and \"{art} {one} ... that\"")
                    detail = (f"'{mine}' is a variant of '{theirs}', defined in {other}: present it as an instance of it "
                              f"({how}), or define the concept once")
                else:
                    detail = (f"'{mine}' has a variant '{theirs}', defined in {other}, which does not present itself as an "
                              f"instance of it: define the concept once" + (late if me == gen[0] else ""))
                found[key] = {"label": me, "other": other, "detail": detail}
    return sorted(found.values(), key=lambda f: (pos.get(f["label"], 0), f["other"]))


# ---- term links: where a defined term is linked, and the unlinked-term advisory (user, 2026-11-19: the most frequent
# reader comment was "needs hyperlink" on compact, closed, bounded, simple, ideals, smooth maps). The decisions are made
# here, on a card's words; the page (symbols.js) only places them (window.symbolsTermLinks), so what is linked and what
# the advisory reports are one computation.
#
# A card's text is read as tokens: words (lower case), FORMULA for a formula, LINK for a link (\ref, \cite, \href, ...),
# and the punctuation .,;:!?() . Headings, tag lines and the card's metadata are not read. A term links at its first use
# in each card but the one that defines it (and that card's proof), in one of these forms:
#   exact      the term as written, or with "s"/"es" (linked in every card, before its definition too)
#   inflected  its words, each in the singular or the plural ("ideals", "matrices", "joined path" for "joined paths")
#   alias      a variant the book declares: \defterm[aliases={compact, compactness}]{compact set}, \termalias{x}{term}
#   synonym    its head noun replaced by one the book declares equivalent: \termsynonyms{function, map} makes "smooth
#              map" a use of "smooth function"
#   adjective  for a term "A head" with an adjective A ("compact set", "simple Lie algebra"): the word A alone, when
#              it is said of something the term applies to:
#                attributive  A followed by the head or a noun of its family ("compact subset", "closed and bounded set")
#                predicative  "<subject> is/are/be A" (also "is closed and bounded"), A not followed by more words of
#                             its predicate ("closed under addition", "simple to check" are other senses), the subject
#                             being the head or its family ("the set is compact"), or a formula for an object of that
#                             kind: its declared type (\defines, \binds{K \subseteq X}) names the head or its family,
#                             or, with no type declared, it is written as such objects are (a capital for a set, a
#                             group or a matrix, a lower-case letter for a map, \mathfrak for a Lie algebra)
# The forms but the first link only in cards from the term's definition on (before it, a form other than the term as
# written is more likely another sense). A longer term wins over a shorter one on the same words, a term's own words
# over another's adjective form, and an adjective form that two terms claim on the same occurrence links neither.
# unlinked-term (advisory): a card after the term's defining card uses the term's adjective in one of those places yet
# the rule declined it, and no form of the term is linked in the card: said of "it"/"they", of a formula with no type
# that is not written as such objects are, of a noun of a near carrier ("compact space" for "compact set", "smooth map"
# for "smooth function"), or claimed by two terms. The detail gives the reason, for an alias, a synonym or a rewording.

FORMULA, LINK = "\ue000", "\ue001"
LINK_CMDS = ("ref", "itemref", "eqref", "cref", "Cref", "autoref", "pageref", "cite", "citep", "citet", "url", "href",
             "hyperref")
TOKEN_RE = re.compile(r"[^\W\d_][\w']*(?:-[\w']+)*|[\ue000\ue001]|[.,;:!?()]")
# a carrier noun's family: the nouns that name the same kind of object ("compact subset" is a use of "compact set");
# the class groups near carriers, for the advisory ("compact space" when only "compact set" is defined)
CARRIER_FAMILY = {"set": {"set", "subset"}, "subset": {"set", "subset"}, "space": {"space"}, "subspace": {"subspace"},
                  "map": {"map", "mapping"}, "mapping": {"map", "mapping"}, "function": {"function"},
                  "operator": {"operator"}, "matrix": {"matrix"}, "sequence": {"sequence"}}
CARRIER_CLASS = {"set": "set", "subset": "set", "space": "set", "subspace": "set", "map": "map", "mapping": "map",
                 "function": "map", "operator": "map", "matrix": "matrix", "sequence": "sequence"}
HEAD_CLASS = {"algebra": "algebra", "subalgebra": "algebra", "ideal": "algebra", "group": "group", "subgroup": "group"}
ADJ_WORDS = {"simple", "compact", "open", "closed", "smooth", "free", "prime", "dense", "convex", "exact", "finite",
             "perfect", "proper", "real", "complex", "positive", "negative", "regular", "singular", "stable", "unique",
             "connected", "bounded", "invertible", "linear", "nondegenerate", "acyclic", "normal", "solvable",
             "nilpotent", "semisimple", "reductive", "discrete", "continuous", "differentiable", "local", "global",
             "special", "abelian", "unitary", "orthogonal", "hermitian", "symmetric", "diagonal", "triangular",
             "cyclic", "injective", "surjective", "bijective", "trivial", "maximal", "minimal", "admissible", "balanced"}
ADJ_SUFFIX = re.compile(r"(?:al|ic|ous|ive|ed|able|ible|ar|ary|ent|ant|ful|less|ian|ean)$")
COPULAS = {"is", "are", "be", "being", "been", "was", "were", "remains", "remain", "becomes", "become", "stays"}
ADVERBS = {"not", "also", "then", "thus", "therefore", "hence", "both", "still", "again", "always", "itself",
           "themselves", "moreover", "so", "indeed", "automatically", "clearly", "again"}
COORD = {"and", "or", ","}
PRONOUNS = {"it", "they", "this", "these", "those", "each", "both", "all"}
RELATIVE = {"that", "which", "who"}
# a word after a predicative adjective that carries its predicate on in another sense
PRED_BLOCK = {"under", "to", "by", "with", "from", "of", "on", "at", "above", "below", "enough", "away", "off", "up",
              "down", "than", "definite", "semidefinite", "into", "onto", "toward", "towards", "relative", "w.r.t"}
# a type naming one of these is a set, for "closed", "compact", "bounded" (a group, a space, an algebra are sets)
SET_LIKE = {"set", "subset", "sets", "subsets", "group", "subgroup", "groups", "subgroups", "space", "subspace", "spaces",
            "subspaces", "algebra", "subalgebra", "interval", "intervals", "ball", "sphere", "manifold", "region", "domain"}
# where a subject's clause starts, looking back from it
CLAUSE_START = {"that", "which", "where", "when", "whenever", "if", "iff", "since", "because", "and", "or", "so", "then",
                "let", "suppose", "assume", "hence", "thus", "while", "whereas", "but", "unless"}
PREPOSITIONS = TERM_PREPS | {"to", "by", "through", "within", "onto", "along", "around", "about"}


def _plural(w: str) -> str:
    inv = {v: k for k, v in _IRREGULAR.items()}
    if w in inv:
        return inv[w]
    if re.search(r"[^aeiou]y$", w):
        return w[:-1] + "ies"
    if re.search(r"(?:s|x|z|ch|sh)$", w):
        return w + "es"
    return w + "s"


def _forms(w: str) -> set:
    """A word in the singular and the plural."""
    one = _singular(w)
    out = {w, one, _plural(one)}
    if one == "index":
        out.add("indexes")
    return out


def _adj_like(w: str) -> bool:
    return len(w) > 2 and (w in ADJ_WORDS or bool(ADJ_SUFFIX.search(w)))


def _commands_marked(s: str, names, mark: str) -> str:
    """\\name[opt]{arg}... replaced by `mark`."""
    pat = re.compile(r"\\(" + "|".join(re.escape(n) for n in names) + r")(?![A-Za-z])\*?")
    out, i = [], 0
    while True:
        m = pat.search(s, i)
        if not m:
            out.append(s[i:])
            return "".join(out)
        out.append(s[i:m.start()])
        j = m.end()
        while True:
            k = j
            while k < len(s) and s[k] in " \t":
                k += 1
            if k < len(s) and s[k] == "[":
                e = s.find("]", k)
                j = e + 1 if e >= 0 else len(s)
                continue
            if k < len(s) and s[k] == "{":
                j = _braced(s, k)
                continue
            break
        out.append(mark)
        i = j


def card_tokens(src: str) -> list[tuple[str, str]]:
    """A card's text as tokens (sig, formula source): a word in lower case, FORMULA, LINK or a punctuation mark. Its
    environment lines, metadata, comments and tag lines are not read; \\defterm{x} reads as x."""
    head = _tag_split(_body(src or ""))[0]
    maths = []

    def math(m):
        maths.append(m.group(0))
        return f" {FORMULA}{len(maths) - 1}{FORMULA} "
    t = MATH_RE.sub(math, head)
    t = _commands_marked(t, LINK_CMDS, f" {LINK} ")
    t = re.sub(r"\\(?:begin|end)\s*\{[^}]*\}|\\item\b(?:\s*\[[^\]]*\])?|\\\\", " ", t)
    t = re.sub(r"\\[`'^\"~=.](?:\{(\w)\}|(\w))|\\[uvHtcdbkr]\s*\{(\w)\}", lambda m: m.group(1) or m.group(2) or m.group(3), t)   # an accent: its letter
    t = re.sub(r"\\[A-Za-z]+\*?|\\.", " ", t)
    t = t.replace("~", " ").replace("---", "-").replace("--", "-").replace("``", " ").replace("''", " ")
    t = t.replace("{", " ").replace("}", " ").replace("\u2019", "'").replace("\u2013", "-").replace("\u2014", "-")
    out = []
    for m in re.finditer(FORMULA + r"(\d+)" + FORMULA + r"|" + TOKEN_RE.pattern, t):
        if m.group(1) is not None:
            out.append((FORMULA, maths[int(m.group(1))]))
        else:
            out.append((m.group(0).lower(), ""))
    return out


def _formula_inner(src: str) -> str:
    s = src.strip()
    for a, b in (("$$", "$$"), ("$", "$"), ("\\(", "\\)"), ("\\[", "\\]")):
        if s.startswith(a) and s.endswith(b) and len(s) >= len(a) + len(b):
            return s[len(a):len(s) - len(b)].strip()
    return s


def _written_as(inner: str, cls: str) -> bool:
    """A formula written as an object of the class is written (no type declared)."""
    s = re.sub(r"^\\href\s*\{[^}]*\}\s*\{", "", inner).strip()
    upper = bool(re.match(r"(?:\\math(?:cal|bb|scr|bf|sf)\s*\{?\s*[A-Za-z]|\\(?:mathrm|operatorname)\s*\{?\s*[A-Z]|[A-Z](?![A-Za-z])|\\(?:Gamma|Delta|Theta|"
                          r"Lambda|Xi|Pi|Sigma|Phi|Psi|Omega)\b)", s))
    lower = bool(re.match(r"(?:[a-z](?![A-Za-z])|\\(?:alpha|beta|gamma|delta|epsilon|varepsilon|zeta|eta|theta|iota|"
                          r"kappa|lambda|mu|nu|xi|pi|rho|sigma|tau|phi|varphi|chi|psi|omega)\b)", s))
    frak = s.startswith("\\mathfrak")
    if cls == "set":
        return (upper or s.startswith("\\{") or bool(re.match(r"[\[(][^,]*,[^,]*[\])]$", s))
                or bool(re.search(r"\\subseteq|\\subset\b", s)))
    if cls == "map":
        return lower or bool(re.search(r"\\colon|\\to\b", s))
    if cls == "algebra":
        return frak
    if cls in ("group", "matrix"):
        return upper or s.startswith("\\mathrm")
    if cls == "sequence":
        return s.startswith("(")
    return upper or frak


def _typed_as(inner: str, cls: str, fam: set, types: dict):
    """True or False when the formula's first symbol has a declared type (it names the family, or not); None when not."""
    if cls == "set" and re.search(r"\\subseteq|\\subset\b", inner):
        return True
    keys = tokens(inner)
    if not keys:
        return None
    ty = None
    k = keys[0]
    for kk in (k, (k[0], k[1], ""), (k[0], False, k[2]), (k[0], False, "")):
        if types.get(kk):
            ty = types[kk]
            break
    if not ty:
        return None
    words = set(re.findall(r"[a-z]+", name_key(ty)))
    if cls == "set" and (re.search(r"\\subseteq|\\subset\b", ty) or words & SET_LIKE):
        return True
    return bool(words & {f for w in fam for f in _forms(w)})


class _Term:
    def __init__(self, idx, term, label, aliases, synonyms):
        self.idx, self.term, self.label = idx, term, label
        self.ok = "$" not in term and "\\(" not in term
        words = _term_words(term) if self.ok else []
        self.ok = self.ok and bool(words)
        self.n_words = len(words)
        w0 = " ".join(words)   # the term as written, and with "s" or "es" (what was linked before the other forms)
        self.written = {w0, w0 + "s", w0 + "es"}

        def seq(ws):
            return [({"a", "an", "the"} if w in ("a", "an", "the") else {w}) if w in TERM_STOP else _forms(w) for w in ws]
        self.variants = []   # (kind, [set of words per position])
        if self.ok:
            self.variants.append(("exact", seq(words)))
        for a in aliases:
            aw = _term_words(a)
            if aw:
                self.variants.append(("alias", seq(aw)))
        first = next((k for k, w in enumerate(words) if w in TERM_PREPS and k > 0), len(words))
        pre = [k for k in range(first) if words[k] not in TERM_STOP]
        self.adj = None
        if pre:
            hp = pre[-1]
            head = _singular(words[hp])
            syn = set()
            for g in synonyms:
                if head in g:
                    syn |= set(g) - {head}
            if syn:
                s = seq(words)
                s[hp] = set().union(*(_forms(x) for x in syn))
                self.variants.append(("synonym", s))
            if len(pre) >= 2 and first == len(words) and pre[0] == 0 and _adj_like(words[0]):
                fam = {head} | CARRIER_FAMILY.get(head, set()) | syn
                cls = CARRIER_CLASS.get(head) or HEAD_CLASS.get(head) or "other"
                near = {c for c, k in CARRIER_CLASS.items() if k == cls} - fam if head in CARRIER_CLASS else set()
                self.adj = {"word": words[0], "head": head, "fam": fam, "cls": cls,
                            "famforms": set().union(*(_forms(x) for x in fam)),
                            "nearforms": set().union(*(_forms(x) for x in near)) if near else set()}


def _adjective_at(toks, i, t: _Term, types):
    """At toks[i] (the adjective of t): ("link", how, strength) / ("decline", reason, advisable) / None (not a use of the
    term). Strength 2: the noun or a declared type says what it is said of; 1: only how the formula is written."""
    a = t.adj
    nxt = toks[i + 1][0] if i + 1 < len(toks) else ""
    # attributive: the head or its family follows, possibly after "and B" / ", B"
    if nxt in a["famforms"]:
        return ("link", "attributive", 2)
    if nxt in COORD and i + 3 < len(toks) and toks[i + 2][0] not in (FORMULA, LINK) and toks[i + 3][0] in a["famforms"]:
        return ("link", "attributive", 2)
    if nxt in a["nearforms"]:
        return ("decline", f"'{a['word']} {nxt}': '{nxt}' is not a noun of '{t.term}' (declare it with \\termsynonyms or "
                           f"an alias, or define '{a['word']} {_singular(nxt)}')", True)
    # predicative: <subject> <copula> [adverbs] [B and] A
    j = i - 1
    if j >= 1 and toks[j][0] in COORD and toks[j - 1][0] not in (FORMULA, LINK) and TOKEN_RE.fullmatch(toks[j - 1][0]):
        j -= 2
    while j >= 0 and toks[j][0] in ADVERBS:
        j -= 1
    if j < 0 or toks[j][0] not in COPULAS:
        return None
    if nxt in PRED_BLOCK:
        return None   # the predicate goes on in another sense: "closed under addition", "simple to check", "bounded by"
    s = j - 1
    while s >= 0 and toks[s][0] in ADVERBS:
        s -= 1
    return _said_of(toks, s, t, types, True)


def _object_of_preposition(toks, s) -> bool:
    """The formula at toks[s] is the object of a preposition ("a function on a compact set $K$ is bounded", "every
    sequence in $K$ is bounded"): not the subject of what follows."""
    for q in range(s - 1, max(-1, s - 6), -1):
        w = toks[q][0]
        if w in CLAUSE_START or not re.match(r"\w", w):
            return False
        if w in PREPOSITIONS:
            return True
    return False


def _said_of(toks, s, t, types, first):
    """Whether toks[s], the subject of "is <adjective>", is a thing t applies to (see _adjective_at)."""
    a = t.adj
    subj, src = (toks[s] if s >= 0 else ("", ""))
    strong = 2 if first else 1
    if subj == FORMULA:
        if _object_of_preposition(toks, s):
            return None
        before = toks[s - 1][0] if s >= 1 else ""
        if before in a["famforms"]:   # "the set $K$ is compact"
            return ("link", "predicative", strong)
        if before in NOUNS and not (a["cls"] == "set" and before in SET_LIKE):
            return None               # "a bounded operator $V$ is unitary": said of another kind of object
        inner = _formula_inner(src)
        typed = _typed_as(inner, a["cls"], a["fam"], types)
        if typed:
            return ("link", "predicative", strong)
        if typed is None and _written_as(inner, a["cls"]):
            return ("link", "predicative", 1)
        if typed is None and first:
            return ("decline", f"'{a['word']}' is said of ${inner[:30]}$, which has no declared type and is not written as "
                               f"a {a['head']} is (declare its type with \\defines or \\binds{{... \\in ...}}, or write "
                               f"'the {a['head']} ${inner[:30]}$ is {a['word']}')", True)
        return None
    if subj in a["famforms"]:
        return ("link", "predicative", strong)
    if a["cls"] == "set" and subj in SET_LIKE:   # "the groups are compact": a group is a set
        return ("link", "predicative", 1)
    if subj in a["nearforms"]:
        return ("decline", f"'the {subj} is {a['word']}': '{subj}' is not a noun of '{t.term}' (declare it with "
                           f"\\termsynonyms or an alias)", True) if first else None
    if not first:
        return None
    if subj in RELATIVE and s >= 1:   # "a set that is not bounded", "the loop itself, which is": what it stands for
        q = s - 1
        while q > 0 and (toks[q][0] == "," or toks[q][0] in ADVERBS):
            q -= 1
        return _said_of(toks, q, t, types, False)
    if subj in PRONOUNS:   # "it", "they": the nearest formula or noun before it in its sentence that it can stand for
        for q in range(s - 1, -1, -1):
            w = toks[q][0]
            if w in (".", ";", "?", "!"):
                break
            if w == FORMULA and _object_of_preposition(toks, q):
                continue
            if w == FORMULA or w in a["famforms"] or w in NOUNS or (a["cls"] == "set" and w in SET_LIKE):
                return _said_of(toks, q, t, types, False)   # what it stands for: of the kind, or not
        return ("decline", f"'{a['word']}' is said of '{subj}', which may be anything: name the {a['head']} ('the "
                           f"{a['head']} is {a['word']}', '$X$ is {a['word']}')", True)
    return None


NOUNS = {f for w in list(CARRIER_CLASS) + list(HEAD_CLASS) + ["vector", "number", "point", "element", "curve", "path",
                                                              "field", "representation", "transformation", "form"]
         for f in _forms(w)}


def _phrase_at(toks, i, seq) -> bool:
    return i + len(seq) <= len(toks) and all(toks[i + k][0] in seq[k] for k in range(len(seq)))


def term_links(cards: list[dict], terms: list[dict], types: dict | None = None, synonyms=()) -> dict:
    """Where each defined term links, card by card, and the unlinked-term advisories.

    cards: [{"key": the card's HTML id, "label", "source", "pos" (its place), "parent" (a proof: its statement's label),
             "checked" (False for a planned card: linked, never reported)}]
    terms: [{"term", "label" (its defining card), "aliases": [...]}], in any order.
    types: {symbol key: declared type} (the book's \\defines); a card's own \\binds with a type are read from its "binds".
    synonyms: groups of head nouns the book declares equivalent ([{"map", "function"}]).
    Returns {"links": {key: [[term index, text, before, after, k, kind], ...]}, "advisories": [...]}: a link is the
    k-th occurrence (0-based) of the words `text` between the tokens `before` and `after` ("" at an end)."""
    types = dict(types or {})
    syn = [set(_singular(w.strip().lower()) for w in g if w.strip()) for g in synonyms]
    T = [_Term(k, t["term"], t["label"], t.get("aliases") or [], syn) for k, t in enumerate(terms)]
    T = [t for t in T if t.ok]
    order = sorted(T, key=lambda t: (-len(t.term), t.idx))
    pos = {c["label"]: c.get("pos", k) for k, c in enumerate(cards)}
    by_label = {c["label"]: c for c in cards}
    links, advisories = {}, []
    for c in cards:
        toks = card_tokens(c.get("source") or "")
        if not toks:
            continue
        ctypes = dict(types)
        for b in list(c.get("binds") or []) + list((by_label.get(c.get("parent")) or {}).get("binds") or []):
            sym, ty = split_bind(b)
            if ty:
                try:
                    ctypes[key_of(sym)] = ty
                except ValueError:
                    pass
        own = {c["label"], c.get("parent")}
        exact, adj, declined = [], [], []
        own_exact = []
        after = lambda t: pos.get(c["label"], 0) >= pos.get(t.label, 0) or (  # noqa: E731
            c.get("parent") is not None and pos.get(c["parent"], 0) >= pos.get(t.label, 0))
        for t in T:
            for kind, seq in t.variants:
                for i in range(len(toks)):
                    if _phrase_at(toks, i, seq):
                        text = " ".join(w for w, _ in toks[i:i + len(seq)])
                        if kind == "exact" and text not in t.written:
                            kind1 = "inflected"
                        else:
                            kind1 = kind
                        # before the definition only the term as written links (as it always did): another form there
                        # is more likely another sense ("a term of the Leibniz formula" before "terms" are defined)
                        if t.label not in own and kind1 != "exact" and not after(t):
                            continue
                        (own_exact if t.label in own else exact).append((i, i + len(seq), t, kind1))
            if t.adj and (t.label in own or after(t)):   # own terms too: they claim their adjective from the others
                for i, (w, _) in enumerate(toks):
                    if w == t.adj["word"]:
                        r = _adjective_at(toks, i, t, ctypes)
                        if r and r[0] == "link":
                            adj.append((i, i + 1, t, r[1], r[2]))
                        elif r and t.label not in own:
                            declined.append((i, t, r[1]))
        # a term's own words win over another term's adjective form; of the terms that claim an adjective on one
        # occurrence, the one with the stronger evidence (a noun or a type over the way a formula is written; for the
        # way it is written, a carrier or an algebra over another noun); a tie links none
        adj = [m for m in adj if not any(e[0] <= m[0] < e[1] for e in exact + own_exact)]
        rank = lambda m: (m[4], 0 if m[2].adj["cls"] == "other" else 1)  # noqa: E731
        at = {}
        for m in adj:
            at.setdefault(m[0], []).append(m)
        adj, claimed = [], {e for m in exact + own_exact for e in range(m[0], m[1])}
        for i, ms in at.items():
            best = max(rank(m) for m in ms)
            top = [m for m in ms if rank(m) == best]
            names = sorted({m[2].term for m in top})
            if len(names) == 1:
                claimed.add(i)
                if top[0][2].label not in own:
                    adj.append(top[0][:4])
                continue
            for m in top:
                if m[2].label not in own:
                    declined.append((i, m[2], f"'{m[2].adj['word']}' here may belong to " + " or to ".join(
                        f"'{x}'" for x in names) + f": write the noun ('{m[2].term}')"))
        # a longer term wins on the same words, at every use of it ("edge elasticities" is not a use of "elasticity");
        # in the card that defines the longer term its words still link to the terms they are made of ("gauge group")
        span = [(m[0], m[1], m[2]) for m in exact]
        exact = [m for m in exact if not any(a < m[1] and m[0] < b and b - a > m[1] - m[0] for a, b, _ in span)]
        cands = {}
        for m in exact + adj:
            cands.setdefault(m[2].idx, []).append(m)
        chosen = []
        for t in order:
            for m in sorted(cands.get(t.idx, []), key=lambda m: m[0]):
                if not any(m[0] < b and a < m[1] for a, b, _, _ in chosen):
                    chosen.append(m)
                    break
        sig = [w for w, _ in toks]
        out = []
        for a, b, t, kind in sorted(chosen, key=lambda m: m[0]):
            text = " ".join(sig[a:b])
            before, after = (sig[a - 1] if a > 0 else ""), (sig[b] if b < len(sig) else "")
            k = sum(1 for p in range(a) if " ".join(sig[p:p + b - a]) == text and (sig[p - 1] if p > 0 else "") == before
                    and (sig[p + b - a] if p + b - a < len(sig) else "") == after)
            out.append([t.idx, text, before, after, k, kind])
        if out:
            links[c["key"]] = out
        if c.get("checked", True):
            linked = {m[2].idx for m in chosen}
            reported, by_at = set(), {}
            for i, t, reason in sorted(declined, key=lambda d: d[0]):
                if t.idx in linked or t.idx in reported or pos.get(c["label"], 0) <= pos.get(t.label, 0):
                    continue
                if i in claimed:   # another term's words, or its adjective form
                    continue
                if c.get("parent") is not None and pos.get(c["parent"], 0) <= pos.get(t.label, 0):
                    continue   # a proof of a card that comes before the term's definition
                reported.add(t.idx)
                by_at.setdefault(i, []).append((t, reason))
            for i, found in sorted(by_at.items()):
                ctx = " ".join("$...$" if w == FORMULA else "[link]" if w == LINK else w for w, _ in toks[max(0, i - 4):i + 4])
                word = found[0][0].adj["word"]
                which = " or ".join(f"'{t.term}' ({t.label})" for t, _ in found)
                reason = found[0][1] if len(found) == 1 else "; ".join(dict.fromkeys(r for _, r in found))
                advisories.append({"kind": "unlinked-term", "label": c["label"], "severity": "advisory",
                                   "detail": f"\"...{ctx}...\": '{word}' is not linked to {which}: {reason}"})
    return {"links": links, "advisories": advisories}
