// leanblueprint-symbols: a link to an item on this page (a symbol in a formula, "Lemma 1.6") opens a preview of that
// item where you are; "Go to" jumps there and "Back to where you were" returns. A tap that lands just beside a small
// symbol in a formula counts as a tap on it. Ctrl/Cmd/Shift-click follows the link directly.
(function () {
  const KEY = 'sym-back-stack', SLOP = 8;
  function stack() { try { return JSON.parse(sessionStorage.getItem(KEY) || '[]'); } catch (e) { return []; } }
  function save(s) { try { sessionStorage.setItem(KEY, JSON.stringify(s.slice(-50))); } catch (e) {} }
  function remember() { const s = stack(); s.push({ page: location.pathname, y: Math.round(window.scrollY) }); save(s); showBack(); }

  function showBack() {
    let b = document.getElementById('sym-back');
    if (!stack().length) { if (b) b.remove(); return; }
    if (b) return;
    b = document.createElement('button'); b.id = 'sym-back'; b.type = 'button';
    b.textContent = '← Back to where you were';
    b.addEventListener('click', () => {
      const s = stack(); const top = s.pop(); save(s);
      if (!top) return;
      if (top.page === location.pathname) { window.scrollTo(0, top.y); showBack(); }
      else location.href = top.page + '#sym-y-' + top.y;
    });
    document.body.appendChild(b);
  }

  function hrefOf(a) { return a.getAttribute('href') || a.getAttribute('xlink:href') || a.getAttribute('data-mjx-href') || ''; }
  // the element a link points to, when it is on this page
  function targetOf(href) {
    const i = href.indexOf('#');
    if (i < 0 || /^[a-z]+:/i.test(href)) return null;
    const path = href.slice(0, i);
    const here = location.pathname.split('/').pop() || 'index.html';
    if (path && path !== here) return null;
    return document.getElementById(decodeURIComponent(href.slice(i + 1)));
  }
  // the item (or heading) that holds an element
  function itemOf(el) { return el.closest('div[class*="_thmwrapper"], div.proof_wrapper') || el; }

  // a click in a formula that missed every link by a few pixels: the nearest link within SLOP
  function nearLink(e) {
    if (e.target.closest && e.target.closest('button, input, #sym-pop, #r-toc, #r-bar')) return null;
    const x = e.clientX, y = e.clientY, near = (r) => r.left - SLOP <= x && x <= r.right + SLOP && r.top - SLOP <= y && y <= r.bottom + SLOP;
    let best = null, bd = SLOP + 1;
    document.querySelectorAll('mjx-container').forEach((box) => {
      if (!near(box.getBoundingClientRect())) return;
      box.querySelectorAll('a').forEach((a) => {
      const r = a.getBoundingClientRect();
        const d = Math.max(r.left - x, 0, x - r.right) + Math.max(r.top - y, 0, y - r.bottom);
        if (d < bd) { bd = d; best = a; }
      });
    });
    return best;
  }

  // ---- the preview
  let pop = null;
  function closePop() { if (pop) { pop.remove(); pop = null; } }
  function heading(item) {
    const h = item.querySelector(':scope > div[class$="_thmheading"]');
    if (!h) return (item.textContent || '').trim().slice(0, 60);
    const q = (s) => ((h.querySelector('span[class$="' + s + '"]') || {}).textContent || '').trim();
    return (q('_thmcaption') + ' ' + q('_thmlabel')).trim();
  }
  // with lazy typesetting (option lazymath) a card far from the reader is not typeset yet: typeset its formulas now,
  // through MathJax's own lazy queue (the ids its observer would add when they come into view)
  async function typesetWithin(el) {
    const mj = window.MathJax, doc = mj && mj.startup && mj.startup.document;
    if (!doc || !doc.lazySet || !doc.lazyHandleSet) return;
    const ids = [...el.querySelectorAll('mjx-lazy[data-mjx-lazy]')].map((n) => n.getAttribute('data-mjx-lazy'))
      .filter((id) => doc.lazyList && doc.lazyList.get(id));
    if (!ids.length) return;
    ids.forEach((id) => doc.lazySet.add(id));
    doc.lazyHandleSet();
    try { await doc.lazyPromise; } catch (e) { /* shown untypeset rather than not at all */ }
  }
  window.symbolsTypesetWithin = typesetWithin;
  async function openPop(target, x, y) {
    const item = itemOf(target);
    closePop();
    await typesetWithin(item);
    pop = document.createElement('div');
    pop.id = 'sym-pop'; pop.setAttribute('role', 'dialog'); pop.setAttribute('aria-label', 'Preview of ' + heading(item));
    const body = item.cloneNode(true);
    body.querySelectorAll('.thm_header_hidden_extras, .thm_header_extras, .modal-container').forEach((n) => n.remove());
    body.querySelectorAll('[id]').forEach((n) => n.removeAttribute('id'));
    body.removeAttribute('id');
    body.querySelectorAll('.proof_content').forEach((n) => { n.style.display = ''; });
    pop.innerHTML = '<div class="sym-pop-head"><button type="button" class="sym-go">Go to ' + esc(heading(item)) + ' →</button>' +
      '<button type="button" class="sym-x" aria-label="Close">✕</button></div><div class="sym-pop-body"></div>';
    pop.querySelector('.sym-pop-body').appendChild(body);
    pop.querySelector('.sym-x').addEventListener('click', closePop);
    pop.querySelector('.sym-go').addEventListener('click', () => { closePop(); jump(target); });
    document.body.appendChild(pop);
    if (window.matchMedia('(max-width: 600px)').matches) pop.classList.add('sheet');
    else {
      const w = pop.offsetWidth, h = pop.offsetHeight, vw = window.innerWidth, vh = window.innerHeight;
      pop.style.left = Math.min(Math.max(8, x - w / 2), vw - w - 8) + 'px';
      pop.style.top = (y + 18 + h < vh - 8 ? y + 18 : Math.max(8, y - 14 - h)) + 'px';
    }
    pop.querySelector('.sym-go').focus({ preventScroll: true });
  }
  function jump(target) {
    remember();
    if (window.readerOpenProof) window.readerOpenProof(target);   // a target inside a folded proof: open it
    if (location.hash === '#' + target.id) target.scrollIntoView({ block: 'start' });
    else location.hash = target.id;
    flash(itemOf(target)); flashItem(target);
  }
  // a link to one item of a card's numbered list (an anchor label--item-3): that item is marked too
  function flashItem(el) { if (el.tagName === 'LI' && /--item-/.test(el.id)) flash(el); }
  function flash(el) { el.classList.remove('sym-hit'); void el.offsetWidth; el.classList.add('sym-hit'); }

  document.addEventListener('click', (e) => {
    if (e.button !== 0) return;
    const inPop = pop && e.target.closest('#sym-pop');
    if (pop && !inPop) closePop();
    if (inPop && e.target.closest('.sym-pop-head')) return;
    let a = e.target.closest('a[href], [data-mjx-href]');
    if (!a) {
      for (let n = e.target; n && n !== document; n = n.parentNode) if (n.tagName && n.tagName.toLowerCase() === 'a') { a = n; break; }
    }
    if (!a) a = nearLink(e);
    if (!a || a.id === 'sym-back') return;
    const dlg = a.closest('div.modal-container');   // a "Uses" or "Lean" dialog: close it as its link is followed
    if (dlg) dlg.style.display = 'none';
    const target = targetOf(hrefOf(a));
    if (!target) return;
    if (e.ctrlKey || e.metaKey || e.shiftKey) return;
    e.preventDefault(); e.stopPropagation();
    if (dlg || a.closest('#r-toc, .thm_header_hidden_extras')) jump(target);
    else openPop(target, e.clientX, e.clientY);
  }, true);
  document.addEventListener('keydown', (e) => { if (e.key === 'Escape') closePop(); });
  window.addEventListener('resize', () => { if (pop && !pop.classList.contains('sheet')) closePop(); });

  // ---- defined terms: the first use of a term in each other card links to the card that defines it (the same
  // preview as a symbol). Run after MathJax has typeset, so TeX source in text nodes is never touched.
  // Which words link is decided at build time (core.term_links: plurals, aliases, synonyms, a term's adjective said of
  // something it applies to) and travels with the card's text: <span class="sym-terms" hidden data-links="[[url, label,
  // text, before, after, k, term, form], ...]">, the k-th occurrence of the words `text` between the tokens `before` and
  // `after`. The page reads a card's text as the build does: words in lower case, a formula, a link, punctuation;
  // headings and tag lines are not read. A page built without those decisions links the exact text of each term.
  const FORMULA = '', LINK = '';
  const TOK = /\\\([\s\S]*?\\\)|\\\[[\s\S]*?\\\]|[\p{L}][\p{L}\p{N}_']*(?:-[\p{L}\p{N}_']+)*|[.,;:!?()]/gu;
  const NOREAD = 'script, style, button, .sym-foot, [class$="_thmheading"], .proof_heading, h1, h2, h3, h4, ' +
    '.thm_header_hidden_extras, .modal-container';
  const TAGLINE = /^(Status|In Lean|References):$/;
  function isTagLine(p) {   // a tag line: a paragraph that starts with <i>Status:</i>, <i>In Lean:</i> or <i>References:</i>
    const f = p.firstElementChild;
    if (!f || f.tagName !== 'I' || !TAGLINE.test(f.textContent.trim())) return false;
    for (let n = p.firstChild; n && n !== f; n = n.nextSibling) if (n.nodeType === 3 && n.nodeValue.trim()) return false;
    return true;
  }
  function cardTokens(card) {
    const toks = [];
    let stop = false;
    (function walk(el) {
      for (const n of el.childNodes) {
        if (stop) return;
        if (n.nodeType === 3) {
          const v = n.nodeValue.replace(/[‐‑–—]/g, '-').replace(/[‘’]/g, "'");
          for (const m of v.matchAll(TOK)) {
            const w = m[0];
            toks.push({ sig: w[0] === '\\' ? FORMULA : w.toLowerCase(), node: w[0] === '\\' ? null : n, a: m.index, b: m.index + w.length });
          }
        } else if (n.nodeType === 1) {
          if (n.matches(NOREAD)) continue;
          const tag = n.tagName.toLowerCase();
          if (tag === 'mjx-container' || tag === 'mjx-lazy') { toks.push({ sig: FORMULA }); continue; }
          if (tag === 'a') { toks.push({ sig: LINK }); continue; }
          if (tag === 'p' && isTagLine(n)) { stop = true; return; }
          walk(n);
        }
      }
    })(card);
    return toks;
  }
  // the token where a decided link starts: the k-th occurrence of its words between its neighbours; failing that (the
  // page reads a word the build did not, or the reverse), the first between the same next token, then the same previous
  function findLink(toks, text, before, after, k) {
    const words = text.split(' '), n = words.length;
    const at = (i) => i + n <= toks.length && words.every((w, j) => toks[i + j].sig === w && toks[i + j].node);
    const sig = (i) => (i >= 0 && i < toks.length ? toks[i].sig : '');
    const hits = [];
    for (let i = 0; i < toks.length; i++) if (at(i)) hits.push(i);
    const full = hits.filter((i) => sig(i - 1) === before && sig(i + n) === after);
    if (full.length > k) return full[k];
    return hits.find((i) => sig(i + n) === after) ?? hits.find((i) => sig(i - 1) === before) ?? -1;
  }
  function placeLink(toks, i, n, row) {
    const s = toks[i], e = toks[i + n - 1];
    const doc = s.node.ownerDocument, r = doc.createRange();
    r.setStart(s.node, s.a); r.setEnd(e.node, e.b);
    const a = doc.createElement('a');
    a.className = 'sym-term'; a.href = row[0]; a.title = 'defined in ' + row[1];
    if (row[6]) a.dataset.term = row[6];
    if (row[7]) a.dataset.form = row[7];
    a.appendChild(r.extractContents());
    r.insertNode(a);
  }
  function linkDecided(card, rows) {
    const toks = cardTokens(card), spots = [];
    for (const row of rows) {
      const i = findLink(toks, row[2], row[3], row[4], row[5] || 0);
      const n = row[2].split(' ').length;
      if (i >= 0 && !spots.some((x) => x.i < i + n && i < x.i + x.n)) spots.push({ i, n, row });
    }
    // last first: a link placed later in a text node leaves the offsets of the earlier ones as they were
    spots.sort((x, y) => y.i - x.i).forEach((x) => { try { placeLink(toks, x.i, x.n, x.row); } catch (e) { /* left unlinked */ } });
  }
  function linkExact(card, T) {
    const re = (t) => new RegExp('\\b' + t.replace(/[.*+?^${}()|[\]\\]/g, '\\$&') + '(?:s|es)?\\b', 'i');
    const SKIP = 'a, mjx-container, script, style, button, .sym-foot, [class$="_thmheading"], h1, h2, h3, h4, .sym-term';
    const own = card.id || (card.previousElementSibling || {}).id || '';
    const done = new Set();
    for (const [term, url, label] of T) {
      if (label === own || done.has(url + term)) continue;
      const rx = re(term);
      const walk = document.createTreeWalker(card, NodeFilter.SHOW_TEXT, {
        acceptNode: (n) => (n.parentElement && !n.parentElement.closest(SKIP) && rx.test(n.nodeValue)
          ? NodeFilter.FILTER_ACCEPT : NodeFilter.FILTER_REJECT) });
      const node = walk.nextNode();
      if (!node) continue;
      const m = node.nodeValue.match(rx), i = m.index;
      const a = document.createElement('a');
      a.className = 'sym-term'; a.href = url; a.textContent = m[0];
      a.title = 'defined in ' + label;
      const rest = node.splitText(i); rest.nodeValue = rest.nodeValue.slice(m[0].length);
      node.parentNode.insertBefore(a, rest);
      done.add(url + term);
    }
  }
  // cards: the cards to link (default: every card of the page); a host that swaps a card's text calls this on it
  function decided(card) {
    const sp = card.querySelector(':scope > [class$="_thmcontent"] > .sym-terms, :scope > .proof_content > .sym-terms');
    if (!sp) return null;
    try { return JSON.parse(sp.dataset.links || '[]'); } catch (e) { return []; }
  }
  function linkTerms(cards) {
    const T = window.symbolsTerms || [];
    const all = cards || document.querySelectorAll('div[class*="_thmwrapper"], div.proof_wrapper');
    const any = !!document.querySelector('.sym-terms');   // a page built with the decisions: no exact-text fallback
    all.forEach((card) => {
      if (card.querySelector('a.sym-term')) return;   // linked already
      const rows = decided(card);
      if (rows) linkDecided(card, rows); else if (!any && T.length) linkExact(card, T);
    });
  }
  window.symbolsLinkTerms = linkTerms;
  function afterMath(f) {
    const mj = window.MathJax;
    if (mj && mj.startup && mj.startup.promise) mj.startup.promise.then(f).catch(f); else f();
  }

  window.addEventListener('load', () => {
    afterMath(linkTerms);
    const m = location.hash.match(/^#sym-y-(\d+)$/);
    if (m) { window.scrollTo(0, +m[1]); history.replaceState(null, '', location.pathname); }
    else if (location.hash.length > 1) {
      const el = document.getElementById(decodeURIComponent(location.hash.slice(1)));
      if (el) { el.scrollIntoView({ block: 'start' }); flash(itemOf(el)); flashItem(el); }
    }
    showBack();
  });
  // ---- approvals (option approve): an Approve button at the foot of each labelled card, bound to the card's hash.
  // A host page (one embedding this page in a frame, say) can store them by setting, on this window,
  //   window.symbolsApprovalHost = { load: () => Promise<{label: {status, sha}}>, set: (label, sha, ok) => Promise<bool> }
  // and then calling window.symbolsApprovals.refresh(). Without a host they stay in this browser (localStorage).
  const AKEY = 'sym-approvals:' + location.pathname;
  const local = {
    load: async () => { try { return JSON.parse(localStorage.getItem(AKEY) || '{}'); } catch (e) { return {}; } },
    set: async (label, sha, ok) => {
      try { const m = JSON.parse(localStorage.getItem(AKEY) || '{}');
        m[label] = { status: ok ? 'ok' : 'none', sha, at: new Date().toISOString() };
        localStorage.setItem(AKEY, JSON.stringify(m)); return true; } catch (e) { return false; }
    },
  };
  const host = () => window.symbolsApprovalHost || local;
  let marks = {};
  function cards() {
    return [...document.querySelectorAll('.sym-approve[data-label]')].map((m) => ({
      m, label: m.dataset.label, sha: m.dataset.sha, card: m.closest('div[class*="_thmwrapper"]') }));
  }
  function stateOf(c) {
    const a = marks[c.label];
    return !a || a.status !== 'ok' ? 'none' : a.sha === c.sha ? 'ok' : 'changed';
  }
  function paint() {
    for (const c of cards()) {
      if (!c.card) continue;
      // the foot of the statement's card; the hash covers its proof too, so an edited proof shows as changed
      let foot = c.card.querySelector(':scope > .sym-foot');
      if (!foot) {
        foot = document.createElement('div'); foot.className = 'sym-foot';
        foot.innerHTML = '<span class="sym-astate" aria-live="polite"></span><button type="button" class="sym-abtn sym-approve-btn"></button>';
        c.card.appendChild(foot);
        // the card as it is when tapped, not as it was when the foot was made: a host may swap the card's text in place
        // and its hash with it (2026-11-08: Approve after such a swap signed the old hash and was refused)
        foot.querySelector('.sym-approve-btn').addEventListener('click', () => toggle(cards().find((x) => x.label === c.label) || c));
      }
      // its own button by class: a host page may add buttons to the foot (before this one), and "the first button"
      // would then be one of those, relabelled (2026-11-01: the console's Note button read "Approve")
      const b0 = foot.querySelector('.sym-approve-btn');
      if (c.m.dataset.planned === '1') {   // a plan of a card, not the card: nothing to approve yet
        foot.dataset.state = 'planned'; b0.hidden = true; foot.querySelector('.sym-astate').textContent = '';
        c.card.classList.add('sym-planned'); continue;
      }
      const st = stateOf(c), b = b0, t = foot.querySelector('.sym-astate');
      foot.dataset.state = st;
      c.card.classList.toggle('sym-approved', st === 'ok');
      t.textContent = st === 'ok' ? '✓ Approved' : st === 'changed' ? 'Changed since you approved it' : '';
      b.textContent = st === 'ok' ? 'Withdraw' : st === 'changed' ? 'Approve again' : 'Approve';
      b.setAttribute('aria-label', b.textContent + ' ' + c.label);
    }
    document.dispatchEvent(new CustomEvent('symbols:approvals', { detail: marks }));
  }
  async function toggle(c) {
    const ok = stateOf(c) !== 'ok';
    const b = c.card.querySelector('.sym-foot .sym-approve-btn'); b.disabled = true;
    try {
      if (await host().set(c.label, c.sha, ok)) marks[c.label] = { status: ok ? 'ok' : 'none', sha: c.sha };
    } catch (e) { /* the host said why (a toast) */ }
    b.disabled = false; paint();
  }
  async function refresh() { try { marks = (await host().load()) || {}; } catch (e) { marks = {}; } paint(); }
  window.symbolsApprovals = { refresh, state: (label) => marks[label] };
  // in a frame, give the host a moment to install itself (it calls refresh), so the browser's own store is not used
  // by mistake; on its own, the page paints at once
  function start() { if (window.parent === window) refresh(); else setTimeout(() => { if (!window.symbolsApprovalHost) refresh(); }, 2000); }
  if (document.querySelector('.sym-approve')) {
    if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', start); else start();
  }

  function esc(s) { return String(s).replace(/[&<>"]/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c])); }
})();
