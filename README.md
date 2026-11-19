# leanblueprint-symbols

Declared, checked and hyperlinked symbols for [Lean blueprints](https://github.com/PatrickMassot/leanblueprint).

A blueprint links each statement to its Lean declaration and draws the dependency graph between statements. This
plugin works one level down, on the symbols inside formulas:

* **Declarations.** An item says which symbols it introduces, with their types: `\defines{M_e}{matrix in $\mathbb R^{n\times n}$}`,
  optionally with the Lean declaration the symbol stands for: `\defines[GRN.General.cornerMatrix]{A_S}{...}` (exported with the symbols).
  Symbols bound locally are listed with `\binds{e,k,l}`, optionally with their types (`\binds{w \in \mathcal B, S \subseteq E}`), and defined terms are marked where they are defined with
  `\defterm{matrix unit}`.
* **Containment.** `\contains{thm:a, thm:b}` on a result says it implies those (they are its special cases), beside
  `\uses` (what it relies on); exported per item, so an application can compute a frontier (the results nothing else
  contains). A `\contains` naming no item is a checker problem.
* **Checks at build time.** The checker reports every symbol used before any item declares it, a symbol declared twice
  (one meaning per symbol), a declaration without a type, a defined term used before its definition, and explanatory
  phrases ("i.e.", "so that", ...) inside definitions and statements. A `\defines` or `\binds` of an operator or a delimiter (`\times`, `|\cdot|`) is reported as undeclarable and set aside (the operation is named by its term; the check goes on). A definition with a name (its title) must introduce that name as a
  `\defterm` in its text, so the reader meets the name before the mathematics. Structure checks: a symbol declared
  inside a lemma, theorem, remark or proof but used by another item (it belongs in a definition of its own); a letter
  bound with two different types in items that depend on each other (one letter, one role); a symbol used in an item
  with no `\uses` path to the item that declares it (notation items exempt; a proof depends on its statement); a
  statement in numbered parts whose proof has no "(k)" for some part. Writing checks: "(Definition~\ref{L})" right
  after a term that L defines (the term is already a link); a card of several definitions (its title names two or more things), or a
  lemma, theorem, proposition or corollary that numbers its parts inline ("(1) ... (2) ..."), that is not an enumerate
  list with one `\item` per definition or part (`unnumbered`; on a planned card the advisory `unnumbered-plan`); a remark that another item `\uses` or a proof cites (it should be a lemma). A card
  marked `\planned` is a placeholder whose text is a plan: the checks skip it, it has no Approve button, and its heading
  says "planned". `symbols.diagnose` lists a `\defines` line to
  complete for each undeclared symbol; the `strict` option stops the build on any problem.
* **Style checks** (the reading rules of a textbook made mechanical). Problems: a card that cites (`\ref`,
  `\itemref`) a card or a section that comes later in the book (`forward-ref`; chapter and section introductions are
  free); the plan of the book inside a card, "Chapter 5", "Section 3", "later chapters", "the next chapter", "the cards
  below", "for now", "so far" (`chapter-mention`); a project file or path, `tools/x.py`, `GRN/`, `Box.lean`, `RC1.md`
  (`project-path`; link targets, `\lean{}` and the "In Lean:" tag line are not read); `\textit{Status:}`,
  `\textit{In Lean:}` and `\textit{References:}` anywhere but as tag lines at the end of a statement, or a Status that is
  not one of "known", "proved and rechecked in this project", "claimed elsewhere, not checked here", "open"
  (`tag-lines`); a statement with Status "known" whose proof block is missing or only a reference (`known-needs-why`).
  **Advisories**, a second look that never makes a page not done (not in `symbols-report.json`, not stopped by
  `strict`; written to `symbols-advisories.json` and `blueprint-data.json` "advisories"): a proof or a sketch inside a
  statement (`proof-in-statement`), a card with more than four top-level items or a notation card with more than six or
  more than one topic heading (`long-card`), a sentence of a definition that states a fact, "Each is a group"
  (`definition-states-fact`), one concept defined in two cards (`duplicate-concept`: two `\defterm`s with one head
  noun, the qualifiers of one among those of the other, case, plurals and stop words aside: "ideal" and "ideal of a
  ring", "invariant" twice; or one qualifier on two carriers, "compact set" and "compact space"; not when the more
  specific card `\uses` the other and presents itself as an instance, "is a Lie algebra", "a model ... that", "the
  corner of"; a general term defined after a more specific one is already in use is reported on its card as late),
  a term's adjective used where it is not linked (`unlinked-term`, see Linked terms). `blueprint-data.json` "kinds" gives each kind's severity and what it means.
* **Linked terms.** The first use of a defined term in each card but the one that defines it links to that card, with
  the same preview as a symbol (after MathJax, so TeX source is never touched). Which words link is decided at build
  time, card by card (`core.term_links`), and travels with the card's text (a hidden `span.sym-terms`); every page also
  carries the terms (`window.symbolsTerms`). A term links in these forms:
  * its words, each in the singular or the plural: "ideals" for `ideal`, "matrices" for `Hermitian matrix`;
  * an alias the book declares: `\defterm[aliases={compactness, Heine property}]{compact set}`, or anywhere in the
    text or the preamble `\termalias{compactness}{compact set}`;
  * its head noun replaced by one the book declares equivalent: `\termsynonyms{function, map}` makes "smooth map" a use
    of `smooth function` (and the reverse);
  * for a term made of an adjective and a noun ("compact set", "simple Lie algebra"), the adjective alone when it is
    said of something the term applies to: before the noun or its family ("compact subset", "closed and bounded
    set"), or after "is"/"are"/"be" ("$K$ is compact", "the set is closed and bounded", "$\mathfrak g$ is simple", "a
    set that is not bounded", "it is compact" when "it" stands for a set in its sentence). Said of a formula, the
    formula must be of that kind: its declared type (`\defines`, a typed `\binds{K \subseteq X}`) names the noun or a
    set-like noun (group, space, algebra: they are sets), or, with no type declared, it is written as such objects are
    (a capital for a set, a group or a matrix; a lower-case letter or `f\colon A\to B` for a map; `\mathfrak` for a
    Lie algebra). Not linked: "closed under addition", "simple to check", "bounded by" (the predicate goes on in
    another sense), "a simple computation" (another noun), "$f$ is bounded" (`f` is not written as a set), "a function
    on a compact set $K$ is bounded" (`K` is the object of "on", not the subject), "a bounded operator $V$ is
    closed" (said of an operator).

  A longer term wins over a shorter one on the same words, everywhere ("edge elasticities" is a use of `edge
  elasticity`, not of `elasticity`; in the card that defines the longer term its words still link to their own
  terms), a term's own words win over another term's adjective, and an adjective two terms claim equally ("closed" of
  `$K$` for `closed set` and `closed path`) goes to the carrier (set, map, matrix, algebra, group) or else to neither.
  Nothing is linked inside formulas, links, headings or tag lines. The advisory `unlinked-term` reports a card, after
  the term's definition, that uses the term's adjective where the rule declined it and links no form of the term:
  "smooth map" when only `smooth function` is defined, said of "it" with nothing in the sentence to stand for, of a
  formula with no type that is not written as such objects are, or claimed by two terms; the detail names the reason
  (add an alias or a synonym, or reword).
* **Item-level links.** Each item of a labelled card's numbered lists (`enumerate`) has an anchor: `<label>--item-<n>`,
  counted from 1 across the card's top-level lists in order (a list resumed after text goes on counting), and
  `<label>--item-<n>-<m>` for item m of a list nested in item n (`def:path--item-2`, `def:path--item-2-1`). A term
  (`\defterm`) or a symbol (`\defines`) written inside an item links to that item; one written outside the lists links
  to the card. A reference to an item is written `\ref{label}(3)` (nested: `\ref{label}(2.1)`), or `\itemref{label}{3}`:
  one link to the item's anchor, reading "1.20(3)"; a caption word written just before it that matches the card
  ("Lemma~\ref{lem:x}(3)", also "Lemmas~") is taken into the link: "Lemma 1.20(3)". The "(3)" must follow the brace at
  once and hold only numbers (`\ref{x} (see)` and `\ref{x}(a)` stay text). A card whose parts are written inline,
  "(1) ... (2) ...", has no item anchors: the reference links to the card. A reference to an item a card with a list does
  not have is a checker problem (`itemref`) and links to the card. The anchors are exported (`items[].anchors`,
  `items[].term_items`, `symbols[].item`). Load `symbols` after `hyperref`, which brings back plasTeX's own `\ref`.
* **Hyperlinked formulas.** Every declared symbol in every formula links to the item that declares it. Following a
  link opens a preview of that item where you are, with "Go to" and "Back to where you were". A tap that lands a
  few pixels beside a small symbol still counts.
* **Lean status from your own checker.** With `status=FILE`, dependency-graph nodes are coloured from a JSON file
  your project writes (for example from its verifier), not from hand-written `\leanok`. An entry may also give a URL
  for the declaration, which replaces the link to the mathlib documentation.
* **What each statement's proof is.** Every lemma, theorem, proposition and corollary carries a chip: "verified in
  Lean" (each Lean declaration it names is verified, by the status file, or `\leanok` without one), "proof on
  paper" (a proof follows it in the text) or "no proof yet". A `conjecture` environment is an item too; its chip says
  "open". The labels Theorem, Lemma, ... say how much a result matters; the chip says whether it is proved.
* **Approvals** (option `approve`): an Approve button at the foot of each labelled card, bound to a hash of
  everything the reader sees of the card: its kind, title, statement, each `\defines` with its type and Lean name,
  `\defterm`, `\binds`, the tag lines (`\lean`, `\leanok`, ...) and its proof. Only `\label` and `\uses` are left
  out. A card edited after its approval shows "changed since you approved it". (plasTeX drops comments before the hash
  is taken; a host that wants every byte covered hashes the comments itself.)
  Approvals stay in the browser unless a host page stores them: a page embedding the text sets
  `window.symbolsApprovalHost = {load, set}` on the text's window and calls `window.symbolsApprovals.refresh()`.
  The hashes are also in `blueprint-data.json` (`items[].sha`), with the text each covers (`items[].seen`).
* **Reader theme** (option `reader`): a reading column, light and dark modes, items set off by kind, a contents panel
  with a filter, the current section, the text size, and item tools that work on touch screens. The dependency graph
  page gets the same theme.
* **Machine-readable output.** `blueprint-data.json` holds the items, their dependencies, Lean names, symbols and
  status, each item's chapter and section, its text and a hash of what the reader sees (everything but `\label` and `\uses`) for other applications, and the advisories and the meaning of each kind; `symbols-report.json` holds the
  checker's problems, `symbols-advisories.json` its advisories.

## Use

```latex
\usepackage{blueprint}
\usepackage[reader,status=status.json]{symbols}

\begin{definition}[matrix unit]\label{def:matrix-unit}
  \uses{def:wiring}
  \defines{M_e}{matrix in $\mathbb R^{n\times n}$}
  \binds{e,k,l}
  For an edge $e$, the \defterm{matrix unit} of $e$ is $M_e\in\mathbb R^{n\times n}$ with $(M_e)_{kl}=1$ if
  $k=t(e)$ and $l=s(e)$, and $0$ otherwise.
\end{definition}
```

```sh
pip install git+https://github.com/lemmaleaf/leanblueprint-symbols
plastex --plugins leanblueprint leanblueprint_symbols -- web.tex
```

### Options

| option | effect |
|---|---|
| `strict` | stop the build when the checker reports a problem (advisories never stop it) |
| `lazymath=URL` | typeset formulas only as they come into view (MathJax 3.2's `ui/lazy`, loaded from `URL/ui/lazy.js`), with MathJax's menu and hidden MathML copy off: a page of ~1300 formulas settled in ~6 s instead of ~18 s on a phone-speed CPU |
| `status=FILE` | JSON `{lean name: status}` or `{lean name: {"status": ..., "url": ...}}`; status is `verified`, `stated`, `sorry-free` or `missing` |
| `reader` | the reader theme (reader.css, reader.js), also on the dependency graph page |
| `approve` | an Approve button on each labelled card (see Approvals) |
| `css=URL` | one more stylesheet linked from every page (for example locally served fonts) |
| `envs=a+b+c` | the environments that are items (default: definition, lemma, theorem, proposition, corollary, conjecture, remark, example, notation, proof); add `conjecture` to blueprint's `thms` option to put conjectures in the graph |

### Matching rules

Symbols are matched by a key: the base (a letter, a Greek or other command, `\mathcal X`, `\mathrm{Word}`, an
accented base such as `\tilde H`), whether it carries a subscript, and a decoration superscript (`^-`, `^+`,
`^{\mathrm{nd}}`). A declaration `M_e` therefore covers `M_e`, `M_{e'}` and `M_1`; a plain power `x^2` does not
change the key. Variables bound inside a formula (set-builder notation, big operators, quantifiers) count as bound
there. A proof sees the symbols its statement declares and binds.

The checker core (`leanblueprint_symbols.core`) does not depend on plasTeX: it takes a list of items as dicts and can
serve other front ends.

## Status

Early (0.x). Tested with leanblueprint 0.0.20 and plasTeX 3.1.

## License

Apache-2.0.
