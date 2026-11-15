r"""plasTeX package `symbols`: declared, checked and hyperlinked symbols for Lean blueprints.

Load it after the blueprint package:

    \usepackage{blueprint}
    \usepackage[strict]{symbols}

Commands (inside a definition, lemma, theorem, ... or proof):

    \defines{M_e}{matrix in $\mathbb R^{n\times n}$}   this item introduces the symbol M_e, of the given type
    \binds{e,k,l}                                        symbols bound locally here ("for an edge e")
    \defterm{matrix unit}                                this item defines the term; renders as the term itself
    \contains{thm:a, thm:b}                              this result implies those (they are its special cases): the
                                                         implication edges a frontier is computed from (\uses says
                                                         what an item relies on, \contains what it generalizes)

The style checks (core.style) read each card's text: a citation of a later card or section (forward-ref), the plan of
the book in a card (chapter-mention), a project path (project-path), tag lines out of place or a Status outside the
fixed list (tag-lines), a known result without a sketch (known-needs-why); and, as advisories (symbols-advisories.json
and blueprint-data.json "advisories", never a problem, never stopped by strict): a proof inside a statement, a long
card, a fact in a definition.

After parsing, the checker (leanblueprint_symbols.core) reports undeclared, redeclared and untyped symbols, terms
used before their definition, and explanatory phrases inside statements; a symbol declared inside a lemma or proof but used elsewhere, a letter
bound in two roles (\binds{w \in \mathcal B}: a bound symbol may carry its type), a symbol used without a \uses
path to the item that declares it, a statement in numbered parts whose proof skips a part; and a definition with a name (its title)
that does not introduce that name as a term in its text (\defterm). It writes, next to the output directory:

    symbols-report.json   the problems
    symbols-advisories.json  the advisories (a second look; they never make a page not done)
    symbols.diagnose      a \defines line to complete for every undeclared symbol
    blueprint-data.json   items, symbols, dependency edges and status, for other applications

Options:
    strict          stop the build when the checker reports a problem
    status=FILE     JSON {lean declaration name: status} or {name: {"status": ..., "url": ...}}; nodes are coloured
                    from it instead of \leanok, and a given url replaces the declaration's documentation link
    reader          the reader theme: a reading column, light and dark, a contents panel and text size (reader.css,
                    reader.js; also styles the dependency graph page)
    css=URL         one more stylesheet linked from every page (e.g. locally served fonts)
    approve         an Approve button at the foot of each labelled card, bound to a hash of the card's source (its
                    proof included); approvals live in the browser, or with a host page that provides
                    window.symbolsApprovalHost (see symbols.js)
    lazymath=URL    typeset formulas only as they come into view (MathJax 3.2's ui/lazy, loaded from URL/ui/lazy.js),
                    with MathJax's menu and its hidden MathML copy off: a long page opens several times faster
    envs=a+b+c      environments that are items (default: definition, lemma, theorem, proposition, corollary,
                    remark, example, notation, proof)

Every lemma, theorem, proposition and corollary carries a chip saying what its proof is: "verified in Lean" (every
Lean declaration it names is verified, by the status file, or \leanok without one), "proof on paper" (a proof
follows it in the text), or "no proof yet"; a conjecture's chip says "open".

Each item of a labelled card's numbered lists gets an HTML id, <label>--item-<n> (1-based; nested <label>--item-<n>-<m>);
a term or symbol defined inside an item links to the item, and \ref{label}(3) (or \itemref{label}{3}) is one link to item 3.

In the HTML output, every symbol whose declaration is known links to the item that declares it; following such a link
opens a preview of the item in place (symbols.js), with "Go to" and "Back to where you were".
"""
from __future__ import annotations

import hashlib
import json
import re
from pathlib import Path

from plasTeX import Command
from plasTeX.Base.LaTeX.Crossref import ref as _BaseRef
from plasTeX.Base.LaTeX import Math as M
from plasTeX.Logging import getLogger
from plasTeX.PackageResource import PackageCss, PackageJs, PackageProcessFilecontents, PackageTemplateDir

from jinja2 import Template

from leanblueprint_symbols import core

log = getLogger()
PKG = Path(__file__).parent
STATIC = PKG.parent / "static"
DEFAULT_ENVS = ["definition", "lemma", "theorem", "proposition", "corollary", "conjecture", "remark", "example",
                "notation", "proof"]
# what a statement's heading says about its proof (the chip), most established first
PROOF_STATES = {"verified": "verified in Lean", "paper": "proof on paper", "none": "no proof yet", "open": "open",
                "planned": "planned"}
PROOF_KINDS = {"lemma", "theorem", "proposition", "corollary"}
# a title that only numbers the item, as an imported paper does ("Definition 3", "Axiom P1", "Theorem 2.4")
NUMBERING = re.compile(r"(Definition|Axiom|Theorem|Lemma|Proposition|Corollary|Remark|Example|Postulate|Principle)\s+[A-Za-z]?[0-9][0-9.a-z]*'?")
STATUS_COLORS = {"verified": ("#1CAC78", "Dark green"), "stated": ("#B0ECA3", "Light green"),
                 "sorry-free": ("#A3D6FF", "Light blue"), "missing": ("#FFAA33", "Orange")}


def _text(x) -> str:
    """The TeX of an argument; plasTeX turns ' into a typographic quote in text arguments: undo that."""
    t = x.source if hasattr(x, "source") else str(x)
    return t.replace("\u2019", "'").replace("\u2018", "`")


def _split(src: str) -> list[str]:
    """Split a comma-separated list at top-level commas (commas inside braces stay)."""
    out, depth, cur = [], 0, ""
    for ch in src:
        depth += {"{": 1, "}": -1}.get(ch, 0)
        if ch == "," and depth == 0:
            out.append(cur)
            cur = ""
        else:
            cur += ch
    out.append(cur)
    return [re.sub(r"\s+", " ", x).strip() for x in out if x.strip()]


class defines(Command):
    r"""\defines[lean name]{symbol}{type}: the optional Lean name is the declaration the symbol stands for"""
    args = "[ lean:str ] sym type"

    def digest(self, tokens):
        Command.digest(self, tokens)
        sym = re.sub(r"\s+", " ", _text(self.attributes["sym"])).strip()
        self.userdata["symbols_sym"] = sym   # the node stays in the tree: the list item it sits in is found from it
        self.parentNode.userdata.setdefault("defines", []).append((sym, _text(self.attributes["type"]).strip()))
        if self.attributes.get("lean"):
            self.parentNode.userdata.setdefault("defines_lean", []).append((sym, self.attributes["lean"].strip()))


class binds(Command):
    r"""\binds{a,b,...}"""
    args = "syms"

    def digest(self, tokens):
        Command.digest(self, tokens)
        self.parentNode.userdata.setdefault("binds", []).extend(_split(_text(self.attributes["syms"])))


class contains(Command):
    r"""\contains{label, label, ...}: the results this one implies"""
    args = "refs:str"

    def digest(self, tokens):
        Command.digest(self, tokens)
        refs = [x.strip() for x in str(self.attributes["refs"]).split(",") if x.strip()]
        self.parentNode.userdata.setdefault("contains", []).extend(refs)


class planned(Command):
    r"""\planned: a placeholder card. Its text is a plan of what the card will say, not the card, so the checker does not
    read it (its symbols are not declared yet), it gets no Approve button (its foot keeps the host's buttons), and its heading says "planned"."""
    args = ""

    def digest(self, tokens):
        Command.digest(self, tokens)
        self.parentNode.userdata["planned"] = True


class defterm(Command):
    r"""\defterm{term}"""
    args = "term"   # not :str, which turns a term with a formula into "<plasTeX.TeXFragment object ...>" (2026-11-08)

    def digest(self, tokens):
        Command.digest(self, tokens)
        node = self.parentNode
        while node is not None and node.nodeName in ("par", "#document-fragment"):
            node = node.parentNode
        term = self.attributes["term"]
        # a term with a formula in it arrives as a fragment, not a string: its source is the term as written (2026-11-08: it
        # was stored as "<plasTeX.TeXFragment object ...>", and matched no title and linked nothing)
        term = term if isinstance(term, str) else (getattr(term, "source", None) or getattr(term, "textContent", "") or "")
        term = re.sub(r"\s+", " ", term)
        self.userdata["symbols_term"] = term.strip()   # the list item it sits in is found from this node
        self.parentNode.userdata.setdefault("terms", []).append(term.strip())


ITEM_PART = re.compile(r"[0-9]{1,3}(?:[.-][0-9]{1,3}){0,3}")


class ref(_BaseRef):
    r"""\ref{label}, and \ref{label}(3): a reference to item 3 of a card's numbered list (\ref{label}(2.1) for item 1 of
    the list inside item 2). The "(3)" must follow the brace at once and hold only numbers; it becomes part of one link
    to the item's anchor ("Lemma 1.20(3)": a "Lemma~" written just before it, matching the card's own caption, is taken
    into the link). Anything else after the brace ("\ref{x} (see)", "\ref{x}(a)") is left as text."""

    def invoke(self, tex):
        res = _BaseRef.invoke(self, tex)
        toks = []
        try:
            for t in tex.itertokens():
                toks.append(t)
                if len(toks) == 1 and not (t == "(" and t.catcode == t.CC_OTHER):
                    break
                if t == ")" or len(toks) > 16:
                    break
        except Exception:   # never break parsing over a peek
            pass
        part = "".join(str(t) for t in toks[1:-1]) if len(toks) >= 3 and toks[-1] == ")" else None
        if part is not None and ITEM_PART.fullmatch(part) and all(t.catcode == t.CC_OTHER for t in toks):
            self.userdata["symbols_part"] = part
        else:
            tex.pushTokens(toks)
        return res

    @property
    def source(self):
        s = _BaseRef.source.fget(self)
        part = self.userdata.get("symbols_part")
        return s + f"({part})" if part else s

    @property
    def symbols_url(self):
        """The link of an item reference: the item's anchor on the card's page, or the card when it has no such item."""
        return _item_ref_url(self)


class itemref(Command):
    r"""\itemref{label}{3}: the same as \ref{label}(3)."""
    args = "label:idref part:str"
    macroName = "itemref"

    def digest(self, tokens):
        Command.digest(self, tokens)
        self.userdata["symbols_part"] = str(self.attributes.get("part", "")).strip()

    @property
    def symbols_url(self):
        """The link of an item reference: the item's anchor on the card's page, or the card when it has no such item."""
        return _item_ref_url(self)


def _item_ref_url(node) -> str:
    target = (getattr(node, "idref", None) or {}).get("label")
    url = (getattr(target, "url", None) or f"#{getattr(target, 'id', '')}") if target is not None else ""
    a = node.userdata.get("symbols_part_anchor")
    return _at(url, a) if a else url


def item_anchor(label: str, path) -> str:
    """The HTML id of an item of a card's numbered list: label--item-2 (1-based), label--item-2-1 nested."""
    return f"{label}--item-" + "-".join(str(k) for k in path)


def _number_items(card, ids, label) -> list:
    """Give each item of a card's numbered lists (enumerate) its anchor (userdata symbols_item), counted from 1 across
    the card's top-level lists in order (a list resumed after text goes on counting), nested lists within their item.
    Returns the anchors in document order."""
    def near(node, names):
        p = node.parentNode
        while p is not None and p is not card:
            if p.nodeName in names:
                return p
            p = p.parentNode
        return None
    lists = [e for e in card.getElementsByTagName("enumerate") if _owner(e.parentNode, ids) is card]
    out = []

    def walk(lst, path, k):
        for it in lst.childNodes:
            if getattr(it, "nodeName", "") != "item":
                continue
            k += 1
            here = path + [k]
            it.userdata["symbols_item"] = item_anchor(label, here)
            out.append(it.userdata["symbols_item"])
            sub = 0
            for e in lists:
                if near(e, ("item",)) is it:
                    sub = walk(e, here, sub)
        return k

    top = 0
    for e in lists:
        if near(e, ("enumerate",)) is None:
            top = walk(e, [], top)
    return out


def _item_of(node, card):
    """The anchor of the list item of `card` that holds `node`, or None."""
    p = node.parentNode
    while p is not None and p is not card:
        a = getattr(p, "userdata", {}).get("symbols_item")
        if a:
            return a
        p = p.parentNode
    return None


def _at(url: str, anchor: str) -> str:
    """A card's url with its fragment replaced by an item's anchor."""
    return url.split("#", 1)[0] + "#" + anchor


def _owner(node, items):
    """The item a node belongs to: the nearest enclosing node that is one of `items` (a set of ids)."""
    while node is not None:
        if id(node) in items:
            return node
        node = node.parentNode
    return None


def ProcessOptions(options, document):
    envs = options.get("envs", "").split("+") if options.get("envs") else DEFAULT_ENVS
    strict = "strict" in options
    status_file = options.get("status")
    document.addPackageResource(PackageTemplateDir(path=PKG / "renderer_templates"))
    reader = "reader" in options
    extra_css = options.get("css")
    lazymath = options.get("lazymath")
    res = [PackageCss(path=STATIC / "symbols.css"), PackageJs(path=STATIC / "symbols.js")]
    if reader:
        res += [PackageCss(path=STATIC / "reader.css"), PackageJs(path=STATIC / "reader.js")]
    document.addPackageResource(res)

    def terms_script() -> str:
        """The defined terms and where each is defined, for symbols.js to link their uses in other cards:
        window.symbolsTerms = [[term, url, label], ...], longest first (so 'corner matrix' wins over 'corner')."""
        if "terms_js" not in state:
            out = []
            for it in state.get("items", []):
                node = state.get("by_label", {}).get(it["label"])
                url = getattr(node, "url", None) if node is not None else None
                for t in it.get("terms", []):   # a term defined inside a list item links to that item
                    if url:
                        a = it.get("term_items", {}).get(t)
                        out.append([t, _at(url, a) if a else url, it["label"]])
            out.sort(key=lambda x: -len(x[0]))
            state["terms_js"] = "<script>window.symbolsTerms = " + json.dumps(out).replace("</", "<\\/") + ";</script>\n"
        return state["terms_js"]

    def head_links(doc, s: str) -> str:
        """Every HTML page (the dependency graph pages too, which the package resources do not reach) links the
        reader theme and the extra stylesheet once, and carries the defined terms (terms_script)."""
        if "</head>" not in s:
            return s
        add = "" if "window.symbolsTerms" in s else terms_script()
        if lazymath and "ui/lazy" not in s and "MathJax = {" in s:
            s = s.replace("MathJax = {", "MathJax = { loader: { load: ['ui/lazy'], paths: { mathjax: " + json.dumps(lazymath)
                          + " } }, options: { enableMenu: false, renderActions: { assistiveMml: [] } },", 1)
        if extra_css and extra_css not in s:
            add += f'<link rel="stylesheet" href="{extra_css}" />\n'
        if reader and "styles/reader.css" not in s:
            add += '<link rel="stylesheet" href="styles/reader.css" />\n'
        return s.replace("</head>", add + "</head>", 1) if add else s

    document.addPackageResource(PackageProcessFilecontents(data=head_links))

    def absorb_caption(doc, s: str) -> str:
        """'Lemma~\\ref{x}(3)' reads as one link, 'Lemma 1.20(3)': the word just before an item reference, when it is
        the card's own caption (or its plural), moves into the link. Done on the page, not the tree, so the card's source
        and its hash stay as written."""
        if "sym-itemref" not in s:
            return s

        def move(m):
            word, cap = m.group(1), m.group(3)
            if cap and word.lower() in (cap.lower(), cap.lower() + "s"):
                return m.group(0)[len(word) + len(m.group(2)):].replace('">', '">' + word + "&#160;", 1)
            return m.group(0)
        return re.sub(r'(\w+)(&#160;|\xa0| )<a class="sym-itemref" data-cap="([^"]*)" href="[^"]*">', move, s)

    document.addPackageResource(PackageProcessFilecontents(data=absorb_caption))
    state = document.userdata.setdefault("symbols", {})

    def collect() -> list:
        nodes = document.getElementsByTagName(tuple(envs))
        ids = {id(n) for n in nodes}
        items = []
        for n in nodes:
            if getattr(n, "tagName", n.nodeName) == "proof":
                parent = n.userdata.get("proves")
                parent_label = parent.id if parent is not None else None
            else:
                parent_label = None
            # \defines etc. digest into the paragraph that holds them: gather from the item's whole subtree
            defs, bnds, terms = list(n.userdata.get("defines", [])), list(n.userdata.get("binds", [])), \
                list(n.userdata.get("terms", []))
            leans = list(n.userdata.get("defines_lean", []))
            is_planned = bool(n.userdata.get("planned"))
            conts = list(n.userdata.get("contains", []))
            for d in n.allChildNodes if hasattr(n, "allChildNodes") else []:
                if d is n or _owner(d.parentNode, ids) is not n:
                    continue
                defs += d.userdata.get("defines", []) if hasattr(d, "userdata") else []
                bnds += d.userdata.get("binds", []) if hasattr(d, "userdata") else []
                terms += d.userdata.get("terms", []) if hasattr(d, "userdata") else []
                leans += d.userdata.get("defines_lean", []) if hasattr(d, "userdata") else []
                conts += d.userdata.get("contains", []) if hasattr(d, "userdata") else []
                is_planned = is_planned or bool(getattr(d, "userdata", {}).get("planned"))
            maths = [m for m in n.getElementsByTagName(("math", "displaymath", "equation", "equation*", "align",
                                                         "align*")) if _owner(m.parentNode, ids) is n]
            kind = getattr(n, "tagName", n.nodeName)
            label = n.id
            if re.fullmatch(r"a\d+", label or ""):     # no \label: name it by what it is
                label = f"proof of {parent_label}" if parent_label else kind
            uses = [u.id for u in n.userdata.get("uses", []) if getattr(u, "id", None)]
            # numbered parts: the \item lines of the statement's own top-level list
            src = n.source or ""
            parts = len(re.findall(r"\\item\b", src)) if src.count("\\begin{enumerate}") == 1 else 0
            title = getattr(n, "title", None)
            # item-level anchors (a labelled card only: an unlabelled one has no stable name), and the item each term
            # and symbol is defined in, when it is defined inside one
            anchors, term_items, sym_items = [], {}, {}
            if n.id and not re.fullmatch(r"a\d+", n.id):
                anchors = _number_items(n, ids, n.id)
                for d in n.getElementsByTagName(("defterm", "defines")):
                    if _owner(d.parentNode, ids) is not n:
                        continue
                    a = _item_of(d, n)
                    if a and d.userdata.get("symbols_term"):
                        term_items.setdefault(d.userdata["symbols_term"], a)
                    if a and d.userdata.get("symbols_sym"):
                        sym_items.setdefault(d.userdata["symbols_sym"], a)
            n.userdata["symbols_anchors"] = anchors
            names = [x.strip() for x in re.split(r",| and ", title.textContent) if x.strip()] \
                if title is not None and kind == "definition" else []
            items.append({"label": label, "kind": kind, "defines": defs, "source": src, "names": names, "binds": bnds, "terms": terms, "leans": dict(leans), "contains": conts,
                          "uses": uses, "parts": parts, "planned": is_planned,
                          "anchors": anchors, "term_items": term_items, "sym_items": sym_items,
                          "math": [m.source for m in maths], "text": n.textContent, "parent": parent_label,
                          "node": n})
        return items

    def check() -> None:
        items = collect()
        # a planned card (\planned) is a plan, not mathematics: the checks read only the written cards and their proofs
        planned_labels = {it["label"] for it in items if it.get("planned")}
        written = [it for it in items if not it.get("planned") and it.get("parent") not in planned_labels]
        problems = core.check([{k: v for k, v in it.items() if k not in ("node", "leans", "contains", "planned", "anchors", "term_items", "sym_items")} for it in written])
        for it in written:   # a definition with a name introduces that name as a term in its text (user, 2026-11-01)
            title = getattr(it["node"], "title", None)
            if it["kind"] != "definition" or title is None:
                continue
            if NUMBERING.fullmatch(title.textContent.strip()):   # an imported paper's own label ("Definition 3", "Axiom P1"), not a name
                continue
            names = [core.name_key(x) for x in re.split(r",| and ", title.textContent) if x.strip()]
            terms = {core.name_key(t) for t in it.get("terms", [])}   # a formula in the title or the term reads the same in both
            norm = lambda w: re.sub(r"(es|s)$", "", w)  # noqa: E731  (plural or not)
            missing = [n for n in names if not any(norm(n) == norm(t) or norm(n) in norm(t) for t in terms)]
            if missing:
                problems.append({"kind": "unnamed", "label": it["label"],
                                 "detail": f"its name ({', '.join(missing)}) is not introduced as a term (\\defterm) in its text"})
        # the style checks (core.style): what each written card cites, and where it sits in the book
        item_ids = {id(it["node"]): k for k, it in enumerate(items)}
        place, seen_items = {}, 0
        for nd in document.getElementsByTagName(tuple(envs) + ("part", "chapter", "section", "subsection", "subsubsection")):
            if id(nd) in item_ids:
                seen_items = item_ids[id(nd)] + 1
            else:
                place[id(nd)] = seen_items   # a section: the first card after its start
        cites: dict[int, list] = {}
        for r in document.getElementsByTagName(("ref", "itemref", "eqref", "cref", "Cref", "autoref", "pageref")):
            target = (getattr(r, "idref", None) or {}).get("label")
            owner = _owner(r.parentNode, item_ids)
            if target is None or owner is None:
                continue   # a reference in a chapter or section introduction is free
            home = _owner(target, item_ids)
            if home is not None:
                at, item = item_ids[id(home)], items[item_ids[id(home)]]["label"]
            elif id(target) in place:
                at, item = place[id(target)], None
            else:
                continue
            cites.setdefault(id(owner), []).append({"ref": getattr(target, "id", None) or "?", "item": item, "at": at})
        try:
            style = core.style([{"label": it["label"], "kind": it["kind"], "source": it["source"], "parent": it["parent"],
                                 "pos": item_ids[id(it["node"])], "cites": cites.get(id(it["node"]), [])} for it in written])
        except Exception as e:   # never break a build over the style checks; say they did not run
            style = [{"kind": "style-error", "label": "the text", "detail": f"the style checks did not run: {e!r}",
                      "severity": "problem"}]
        problems += [{k: v for k, v in p.items() if k != "severity"} for p in style if p["severity"] == "problem"]
        advisories = [p for p in style if p["severity"] == "advisory"]
        labels = {it["label"] for it in items}
        for it in items:   # a \contains naming no item, or the item itself
            for c in it.get("contains", []):
                if c not in labels or c == it["label"]:
                    problems.append({"kind": "contains", "label": it["label"],
                                     "detail": f"{c}: {'no such item' if c not in labels else 'an item cannot contain itself'}"})
        by_label = {it["label"]: it["node"] for it in items}
        # references to items (\ref{label}(3), \itemref{label}{3}): the item's anchor, or the card when it has no such
        # item; reported when the card has a numbered list without that item (parts written inline, "(1) ... (2) ...",
        # have no anchors: the reference links to the card and is not a problem)
        for r in document.getElementsByTagName(("ref", "itemref")):
            part = r.userdata.get("symbols_part")
            target = (getattr(r, "idref", None) or {}).get("label")
            if not part or target is None:
                continue
            anchor = item_anchor(target.id, re.split(r"[.-]", part))
            if anchor in target.userdata.get("symbols_anchors", []):
                r.userdata["symbols_part_anchor"] = anchor   # the url is known only at render time (symbols_url)
            elif target.userdata.get("symbols_anchors"):   # a list without that item: a broken reference
                owner = _owner(r.parentNode, {id(it["node"]) for it in items})
                where = next((it["label"] for it in items if it["node"] is owner), "the text")
                problems.append({"kind": "itemref", "label": where,
                                 "detail": f"{target.id}({part}): the card has no item {part}; linked to the card"})
        table = {}
        for it in items:
            for sym, ty in it["defines"]:
                if not core.tokens(sym):   # an operator declared by mistake: reported by the checker, not a symbol
                    continue
                table.setdefault(core.key_of(sym), {"sym": sym, "type": ty, "label": it["label"],
                                                     "lean": it.get("leans", {}).get(sym),
                                                     "item": it.get("sym_items", {}).get(sym)})
        state.update(items=items, problems=problems, advisories=advisories, table=table, by_label=by_label)
        outdir = Path(document.userdata.get("working-dir", ".")).resolve()
        (outdir / "symbols-report.json").write_text(json.dumps(problems, indent=1) + "\n")
        # advisories: a second look, never a problem (not in symbols-report.json, not stopped by strict)
        (outdir / "symbols-advisories.json").write_text(json.dumps(advisories, indent=1) + "\n")
        diag = sorted({p["detail"].split(" in ")[0] for p in problems if p["kind"] == "undeclared"})
        (outdir / "symbols.diagnose").write_text("".join(f"\\defines{{{d}}}{{}}\n" for d in diag))
        for p in problems:
            log.warning(f"symbols: {p['kind']} in {p['label']}: {p['detail']}")
        for p in advisories:
            log.info(f"symbols: advisory {p['kind']} in {p['label']}: {p['detail']}")
        log.info(f"symbols: {len(table)} symbols declared, {len(problems)} problems, {len(advisories)} advisories")
        if strict and problems:
            raise SystemExit(f"symbols: {len(problems)} problems (strict); see symbols-report.json")

    document.addPostParseCallbacks(160, check)

    # links: every math node's MathJax source gets \href around declared symbols
    def resolve(key):
        T = state.get("table", {})
        # the symbol itself, then without its decoration, then (a subscripted use of a symbol declared plain: sigma_e for
        # sigma) its base: the checker accepts that use as declared, so it must link too (2026-11-01: sigma_e, nu_e
        # were declared but not linked)
        entry = T.get(key) or T.get((key[0], key[1], "")) or (T.get((key[0], False, "")) if key[1] else None)
        if entry is None:
            return None
        node = state["by_label"].get(entry["label"])
        url = getattr(node, "url", None) if node is not None else None
        url = url or (f"#{entry['label']}" if entry["label"] else None)
        return _at(url, entry["item"]) if url and entry.get("item") else url

    for cls in (M.MathEnvironment, M.math):
        prop = cls.__dict__.get("mathjax_source")
        if prop is None or cls.__dict__.get("_symbols_linked", False):
            continue

        def make(orig):
            def linked(self):
                src = orig.fget(self)
                try:
                    return core.link(src, resolve)
                except Exception:   # never break rendering over a link
                    return src
            return property(linked)
        setattr(cls, "mathjax_source", make(prop))
        cls._symbols_linked = True

    # status colours from the verifier, when given
    if status_file:
        raw = json.loads(Path(status_file).read_text())
        status = {k: (v["status"] if isinstance(v, dict) else v) for k, v in raw.items()}
        urls = {k: v["url"] for k, v in raw.items() if isinstance(v, dict) and v.get("url")}
        dep = document.userdata.setdefault("dep_graph", {})

        def node_status(node):
            decls = node.userdata.get("leandecls", [])
            if not decls:
                return None
            st = [status.get(d, "missing") for d in decls]
            for s in ("missing", "stated", "sorry-free"):
                if s in st:
                    return s
            return "verified"

        def colorizer(node):
            s = node_status(node)
            return STATUS_COLORS[s][0] if s else ""

        def apply_status():
            dep["colorizer"] = colorizer
            dep["fillcolorizer"] = colorizer
            dep.setdefault("legend", []).append(
                ("colours", "from the project verifier: dark green = verified, light green = stated, light blue = "
                            "sorry-free (not verified), orange = Lean declaration missing"))
            state["node_status"] = node_status

        document.addPostParseCallbacks(170, apply_status)

        def apply_urls():
            """After leanblueprint's make_lean_data (150): the status file's url for each declaration that has one."""
            for graph in dep.get("graphs", {}).values():
                for node in graph.nodes:
                    node.userdata["lean_urls"] = [(d, urls.get(d, u)) for d, u in node.userdata.get("lean_urls", [])]

        if urls:
            document.addPostParseCallbacks(160, apply_urls)

    # the proof chip on each statement's heading (leanblueprint's header-extras hook)
    def proof_state(node):
        kind = getattr(node, "thmName", None) or getattr(node, "tagName", "")
        if node.userdata.get("planned") or any(getattr(d, "userdata", {}).get("planned") for d in getattr(node, "allChildNodes", [])):
            return "planned"
        if kind == "conjecture":
            return "open"
        if kind not in PROOF_KINDS:
            return None
        decls = node.userdata.get("leandecls", [])
        if "node_status" in state:
            lean_ok = bool(decls) and state["node_status"](node) == "verified"
        else:
            proof = node.userdata.get("proved_by")
            lean_ok = bool(node.userdata.get("leanok")) and (proof is None or bool(proof.userdata.get("leanok")))
        if lean_ok:
            return "verified"
        return "paper" if node.userdata.get("proved_by") is not None else "none"

    def apply_proof_states():
        for node in document.getElementsByTagName(tuple(envs)):
            st = proof_state(node)
            if st:
                node.userdata["symbols_proof"] = st
                node.userdata["symbols_proof_text"] = PROOF_STATES[st]
        state["proof_state"] = lambda n: n.userdata.get("symbols_proof")

    document.addPostParseCallbacks(175, apply_proof_states)

    # a hash of each card's source (with its proof), for approvals bound to what was read
    approve = "approve" in options

    def card_sha(node) -> str:
        r"""A hash of what the reader sees: the item's text and its proof's, without labels, \uses, \lean and other
        metadata (a metadata edit is not a change of the card)."""
        src = body_tex(node.source or "")
        proof = node.userdata.get("proved_by")
        if proof is not None:
            src += "\n" + body_tex(proof.source or "")
        return hashlib.sha256(src.encode()).hexdigest()[:16]

    def apply_shas():
        for node in document.getElementsByTagName(tuple(e for e in envs if e != "proof")):
            if node.id and not re.fullmatch(r"a\d+", node.id):
                node.userdata["symbols_sha"] = card_sha(node)
                if approve:   # a planned card keeps the marker (a host finds cards by it) but gets no Approve button
                    node.userdata["symbols_approve"] = True
                    node.userdata["symbols_planned"] = node.userdata.get("symbols_proof") == "planned"

    document.addPostParseCallbacks(176, apply_shas)
    marker = Template('{% if obj.userdata.symbols_approve %}<span class="sym-approve" hidden data-label="{{ obj.id }}" '
                      'data-sha="{{ obj.userdata.symbols_sha }}"{% if obj.userdata.symbols_planned %} data-planned="1"{% endif %}>'
                      '</span>{% endif %}')
    document.userdata.setdefault("thm_header_extras_tpl", []).append(marker)
    chip = Template('{% if obj.userdata.symbols_proof %}<span class="proofchip proofchip-{{ obj.userdata.symbols_proof }}">'
                    '{{ obj.userdata.symbols_proof_text }}</span>{% endif %}')
    document.userdata.setdefault("thm_header_extras_tpl", []).append(chip)

    # an item's text for other applications: its TeX without the environment and the metadata commands
    META = ("label", "uses", "lean", "leanok", "notready", "proves", "mathlibok", "discussion", "defines", "binds",
            "contains", "planned")

    def body_tex(src: str) -> str:
        src = re.sub(r"^\\begin\{[^}]*\}(\[[^\]]*\])?", "", src.strip())
        src = re.sub(r"\\end\{[^}]*\}$", "", src)
        out, i = [], 0
        while i < len(src):
            m = re.match(r"\\([A-Za-z]+)\s*", src[i:])
            if m and m.group(1) in META + ("defterm",):
                j = i + m.end()
                if j < len(src) and src[j] == "[":   # an optional argument (\defines[lean name]{...}{...})
                    j = src.index("]", j) + 1
                groups = []
                while j < len(src) and src[j] == "{" and len(groups) < (2 if m.group(1) == "defines" else 1):
                    depth, k = 0, j
                    while k < len(src):
                        depth += {"{": 1, "}": -1}.get(src[k], 0)
                        if depth == 0:
                            break
                        k += 1
                    groups.append(src[j + 1:k])
                    j = k + 1
                    while j < len(src) and src[j] in " \t" and m.group(1) != "defterm":
                        j += 1
                if m.group(1) == "defterm" and groups:
                    out.append(groups[0])
                i = j
                continue
            out.append(src[i])
            i += 1
        return re.sub(r"\n\s*\n\s*", "\n\n", "".join(out)).strip()

    def section_of(node) -> dict:
        """The chapter and section an item sits in (number and title), for applications that group items."""
        out = {}
        p = node.parentNode
        while p is not None:
            if getattr(p, "nodeName", "") in ("chapter", "section", "subsection") and getattr(p, "title", None) is not None:
                ref = p.ref.textContent if getattr(p, "ref", None) is not None else ""
                out.setdefault(p.nodeName, f"{ref} {p.title.textContent}".strip())
            p = p.parentNode
        return out

    # machine-readable output
    def export() -> None:
        items = state.get("items", [])
        out = {"items": [], "symbols": [], "problems": state.get("problems", []), "advisories": state.get("advisories", []),
               "kinds": {k: {"severity": "advisory" if k in core.ADVISORY else "problem", "means": v}
                         for k, v in core.KINDS.items()}}
        for it in items:
            n = it["node"]
            uses = [u.id for u in n.userdata.get("uses", [])]
            out["items"].append({"label": it["label"], "kind": it["kind"],
                                 "title": _text(n.title) if getattr(n, "title", None) else None,
                                 "lean": n.userdata.get("leandecls", []), "uses": uses, "parent": it["parent"],
                                 "defines": [s for s, _ in it["defines"]], "terms": it["terms"],
                                 "status": state["node_status"](n) if "node_status" in state else None,
                                 "proof": n.userdata.get("symbols_proof"), "sha": n.userdata.get("symbols_sha"),
                                 "number": n.ref.textContent if getattr(n, "ref", None) is not None else None,
                                 "tex": body_tex(n.source or ""), "where": section_of(n), "contains": it.get("contains", []),
                                 "planned": bool(it.get("planned")), "anchors": it.get("anchors", []),
                                 "term_items": it.get("term_items", {})})
        for key, e in state.get("table", {}).items():
            out["symbols"].append({"sym": e["sym"], "type": e["type"], "label": e["label"], "lean": e.get("lean"),
                                   "item": e.get("item")})
        outdir = Path(document.userdata.get("working-dir", ".")).resolve()
        (outdir / "blueprint-data.json").write_text(json.dumps(out, indent=1) + "\n")

    document.addPostParseCallbacks(180, export)
