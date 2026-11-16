// A fast drop-in for marked 18.1.3: parse(markdown) returns exactly the HTML
// marked renders with its defaults (GFM on, breaks off). Dependency-free,
// single pass over blocks, inline content parsed with a delimiter stack.
// Written from scratch in this session (CommonMark + GFM behaviour as
// observed from marked's own outputs, not copied from its source).

// ---------------------------------------------------------------- utilities

const CODE_AMP = 38, CODE_LT = 60, CODE_GT = 62, CODE_QUOT = 34, CODE_APOS = 39;
const CODE_BACKSLASH = 92, CODE_BACKTICK = 96, CODE_LBRACKET = 91, CODE_RBRACKET = 93;
const CODE_BANG = 33, CODE_STAR = 42, CODE_UNDER = 95, CODE_TILDE = 126, CODE_LT2 = 60;
const CODE_NL = 10, CODE_SPACE = 32, CODE_TAB = 9;

// ASCII punctuation (backslash-escapable).
function isPunct(ch) {
  return (ch >= 33 && ch <= 47) || (ch >= 58 && ch <= 64) ||
    (ch >= 91 && ch <= 96) || (ch >= 123 && ch <= 126);
}
function isSpace(ch) { return ch === ' ' || ch === '\t' || ch === '\n' || ch === '\r'; }
function isDigit(ch) { return ch >= 48 && ch <= 57; }
function isAlpha(ch) { return (ch >= 65 && ch <= 90) || (ch >= 97 && ch <= 122); }
function isAlnum(ch) { return isAlpha(ch) || isDigit(ch); }
// A "word" character for autolink boundaries: letter, digit, underscore.
function isWord(ch) { return isAlnum(ch) || ch === 95; }

// Escape &, <, >, ", ' in text. A & that begins something looking like an
// entity reference (&name; &#123; &#x1f;) is left alone; any other & becomes
// &amp;. Named entities are never decoded by marked in text; numeric
// references are decoded by the inline scanner before this runs.
const ENTITY_LIKE = /^#\d{1,7};|^#[xX][0-9a-fA-F]{1,6};|^\w+;/;
export function escapeText(s) {
  let out = '';
  let start = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    let rep = null;
    if (c === CODE_AMP) {
      if (!ENTITY_LIKE.test(s.slice(i + 1, i + 33))) rep = '&amp;';
    } else if (c === CODE_LT) rep = '&lt;';
    else if (c === CODE_GT) rep = '&gt;';
    else if (c === CODE_QUOT) rep = '&quot;';
    else if (c === CODE_APOS) rep = '&#39;';
    if (rep !== null) {
      out += s.slice(start, i) + rep;
      start = i + 1;
    }
  }
  return out + s.slice(start);
}

// Escape everything (code spans and code blocks): no entity preservation.
export function escapeCode(s) {
  let out = '';
  let start = 0;
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    let rep = null;
    if (c === CODE_AMP) rep = '&amp;';
    else if (c === CODE_LT) rep = '&lt;';
    else if (c === CODE_GT) rep = '&gt;';
    else if (c === CODE_QUOT) rep = '&quot;';
    else if (c === CODE_APOS) rep = '&#39;';
    if (rep !== null) {
      out += s.slice(start, i) + rep;
      start = i + 1;
    }
  }
  return out + s.slice(start);
}

// Decode a numeric character reference at s[i] == '&'. Returns [codePoint, length]
// or null when it is not a valid reference (wrong digit count, bad digits).
function numericRef(s, i) {
  if (s.charCodeAt(i) !== CODE_AMP || s.charCodeAt(i + 1) !== 35) return null; // &#...
  let j = i + 2;
  let hex = false;
  if (s[j] === 'x' || s[j] === 'X') { hex = true; j++; }
  const digits = j;
  let cp = 0;
  while (j < s.length) {
    const c = s.charCodeAt(j);
    if (hex ? ((c >= 48 && c <= 57) || (c >= 65 && c <= 70) || (c >= 97 && c <= 102))
            : (c >= 48 && c <= 57)) {
      cp = cp * (hex ? 16 : 10) + (c <= 57 ? c - 48 : (c <= 70 ? c - 55 : c - 87));
      j++;
    } else break;
  }
  const ndigits = j - digits;
  if (ndigits === 0 || ndigits > (hex ? 6 : 7)) return null;
  if (s.charCodeAt(j) !== 59) return null; // ';'
  if (cp === 0 || cp > 0x10FFFF || (cp >= 0xD800 && cp <= 0xDFFF)) cp = 0xFFFD;
  return [cp, j + 1 - i];
}

// Normalise a link label: collapse whitespace runs to one space, trim, lowercase.
function normLabel(s) {
  // unescape backslash escapes, collapse whitespace, fold case.
  // Unicode case folding maps ß and ẞ to ss (so [ẞ] matches [SS]).
  return s.replace(/\\([!-/:-@[-`{-~])/g, '$1').replace(/\s+/g, ' ').trim().toLowerCase().replace(/ß/g, 'ss');
}

// Encode a link destination the way marked does: encodeURI-style, but a
// valid percent-encoding (% followed by two hex digits) is preserved, not
// re-encoded to %25.
function encodeDest(dest) {
  let out = '';
  for (let i = 0; i < dest.length; i++) {
    const c = dest[i];
    if (c === '%' && i + 2 < dest.length &&
        /^[0-9a-fA-F]$/.test(dest[i + 1]) && /^[0-9a-fA-F]$/.test(dest[i + 2])) {
      out += dest.slice(i, i + 3);
      i += 2;
      continue;
    }
    out += encodeURI(c);
  }
  return out;
}

// ---------------------------------------------------------------- inline parser
//
// Scans inline source into a flat doubly-linked list of nodes, resolves links
// while scanning, then runs the delimiter-stack emphasis pass. Node kinds:
//   txt  {s, pre}      literal text (pre: already escaped, emit as-is)
//   code {s}           code span content (escapeCode at render)
//   html {s}           raw HTML, emitted as-is
//   br                 hard break -> <br>
//   delim {ch, n, open, close}  emphasis run; leftover ones render literally
//   aStart {href, title}  link open marker; aEnd closes it
//   img {src, title, alt}
//   em {tag, kids}     emphasis wrapper (kids: array of nodes)

function mkNode(t, o) {
  const n = { t, prev: null, next: null };
  if (o) Object.assign(n, o);
  return n;
}

// Unicode punctuation test (for flanking rules): ASCII punct, else \p{P} or
// \p{S}. The spec counts Unicode symbols (currency like $ £ €, math, etc.)
// as punctuation for emphasis flanking.
const UNICODE_PUNCT = /[\p{P}\p{S}]/u;
function isPunctCode(cp) {
  if (cp < 128) return isPunct(cp);
  return UNICODE_PUNCT.test(String.fromCodePoint(cp));
}
function charKindAt(s, i) {
  // 0 = whitespace/start/end, 1 = punctuation, 2 = other.
  // Whitespace is Unicode whitespace (incl. nbsp U+00A0), not just ASCII.
  if (i < 0 || i >= s.length) return 0;
  const cp = s.codePointAt(i);
  if (cp === 32 || cp === 9 || cp === 10 || cp === 13) return 0;
  if (/\s/.test(String.fromCodePoint(cp))) return 0;
  return isPunctCode(cp) ? 1 : 2;
}

// A code span: opening run of n backticks at s[i]. Returns [content, endIndex]
// or null when no matching run exists.
function matchCodeSpan(s, i, n) {
  let j = i + n;
  while (j < s.length) {
    if (s.charCodeAt(j) === CODE_BACKTICK) {
      let k = j;
      while (k < s.length && s.charCodeAt(k) === CODE_BACKTICK) k++;
      if (k - j === n) {
        let content = s.slice(i + n, j);
        content = content.replace(/\n/g, ' ');
        if (content.length >= 2 && content[0] === ' ' && content[content.length - 1] === ' ' &&
          content.trim() !== '') {
          content = content.slice(1, -1);
        }
        return [content, k];
      }
      j = k;
    } else j++;
  }
  return null;
}

// Parse a link destination starting at s[i] (after '(' or after ': ' in a def).
// Returns [dest, nextIndex] or null. Handles <...> and bare destinations.
function parseDest(s, i) {
  const n = s.length;
  if (i >= n) return null;
  if (s.charCodeAt(i) === CODE_LT) {
    let j = i + 1;
    let dest = '';
    while (j < n) {
      const c = s.charCodeAt(j);
      if (c === CODE_LT || c === CODE_NL) return null;
      if (c === CODE_GT) return [dest, j + 1];
      if (c === CODE_BACKSLASH && j + 1 < n && isPunct(s.charCodeAt(j + 1))) {
        dest += s[j + 1];
        j += 2;
      } else {
        dest += s[j];
        j++;
      }
    }
    return null;
  }
  // Bare destination: no spaces/control chars, balanced parens.
  // An empty destination () is valid: href="".
  if (s.charCodeAt(i) === 41) return ['', i];
  let j = i;
  let depth = 0;
  let dest = '';
  while (j < n) {
    const c = s.charCodeAt(j);
    if (c === CODE_SPACE || c === CODE_TAB || c === CODE_NL || c < 32) break;
    if (c === 40) { depth++; dest += s[j]; j++; continue; } // (
    if (c === 41) { // )
      if (depth === 0) break;
      depth--; dest += s[j]; j++; continue;
    }
    if (c === CODE_BACKSLASH && j + 1 < n && isPunct(s.charCodeAt(j + 1))) {
      dest += s[j + 1];
      j += 2;
      continue;
    }
    dest += s[j];
    j++;
  }
  if (dest === '' || depth !== 0) return null;
  return [dest, j];
}

// Parse a link title starting at s[i] (after the destination and whitespace).
// Returns [title, nextIndex] or null. Titles are "...", '...' or (...).
function parseTitle(s, i) {
  const n = s.length;
  if (i >= n) return null;
  const c = s.charCodeAt(i);
  let close;
  if (c === CODE_QUOT) close = CODE_QUOT;
  else if (c === CODE_APOS) close = CODE_APOS;
  else if (c === 40) close = 41;
  else return null;
  let j = i + 1;
  let title = '';
  while (j < n) {
    const ch = s.charCodeAt(j);
    if (ch === close) return [title, j + 1];
    if (ch === CODE_NL) {
      if (close === 41) return null; // (title) cannot span lines
      title += '\n';
      j++;
      continue;
    }
    if (ch === CODE_BACKSLASH && j + 1 < n && isPunct(s.charCodeAt(j + 1))) {
      title += s[j + 1];
      j += 2;
      continue;
    }
    title += s[j];
    j++;
  }
  return null;
}

// Skip spaces/tabs/newlines. Returns the index after them.
function skipWs(s, i) {
  while (i < s.length) {
    const c = s.charCodeAt(i);
    if (c === 32 || c === 9 || c === 10) i++;
    else break;
  }
  return i;
}

// Try to parse an inline link's ( ... ) part starting at s[i] == '('.
// Returns {dest, title, end} or null.
function parseInlineLinkTail(s, i) {
  // i points at '('
  let j = skipWs(s, i + 1);
  const d = parseDest(s, j);
  if (!d) return null;
  const dest = d[0];
  j = d[1];
  let title = null;
  const j2 = skipWs(s, j);
  // a title must be preceded by whitespace; a title glued to the
  // destination makes the link invalid
  if (j2 > j && j2 < s.length && (s.charCodeAt(j2) === CODE_QUOT || s.charCodeAt(j2) === CODE_APOS || s.charCodeAt(j2) === 40)) {
    const t = parseTitle(s, j2);
    if (!t) return null;
    title = t[0];
    j = t[1];
  } else {
    j = j2;
  }
  j = skipWs(s, j);
  if (j >= s.length || s.charCodeAt(j) !== 41) return null; // ')'
  return { dest, title, end: j + 1 };
}

// Try to match an autolink <...> at s[i] == '<'. Returns {href, text, end} or null.
function matchAngleAutolink(s, i) {
  const n = s.length;
  let j = i + 1;
  // scheme: 2-32 chars, letter first, then letter/digit/+/-/.
  let k = j;
  if (k < n && isAlpha(s.charCodeAt(k))) {
    k++;
    while (k < n && (isAlnum(s.charCodeAt(k)) || s[k] === '+' || s[k] === '-' || s[k] === '.')) k++;
    if (k - j >= 2 && k - j <= 32 && k < n && s.charCodeAt(k) === 58) { // ':'
      // scan to '>'
      let e = k + 1;
      while (e < n && s.charCodeAt(e) !== CODE_GT && s.charCodeAt(e) !== CODE_LT && s.charCodeAt(e) !== CODE_SPACE && s.charCodeAt(e) !== CODE_NL) e++;
      if (e < n && s.charCodeAt(e) === CODE_GT && e > k + 1) {
        return { href: s.slice(j, e), text: s.slice(j, e), end: e + 1 };
      }
    }
  }
  // email: local@domain
  let e = j;
  while (e < n && s.charCodeAt(e) !== CODE_GT && s.charCodeAt(e) !== CODE_LT && s.charCodeAt(e) !== CODE_SPACE && s.charCodeAt(e) !== CODE_NL) e++;
  if (e < n && s.charCodeAt(e) === CODE_GT) {
    const body = s.slice(j, e);
    if (isEmail(body)) return { href: 'mailto:' + body, text: body, end: e + 1 };
  }
  return null;
}

const EMAIL_RE = /^[a-zA-Z0-9.!#$%&'*+\/=?^_`{|}~-]+@[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)*$/;
function isEmail(s) { return EMAIL_RE.test(s); }

// Try to match raw HTML at s[i] == '<'. Returns the end index or null.
function matchRawHtml(s, i) {
  const n = s.length;
  if (s.startsWith('<!--', i)) {
    const e = s.indexOf('-->', i + 4);
    if (e === -1) return null;
    return e + 3;
  }
  if (s.startsWith('<?', i)) {
    const e = s.indexOf('?>', i + 2);
    if (e === -1) return null;
    return e + 2;
  }
  if (s.startsWith('<![CDATA[', i)) {
    const e = s.indexOf(']]>', i + 9);
    if (e === -1) return null;
    return e + 3;
  }
  if (s.startsWith('<!', i)) {
    // declaration: <! + letter
    if (i + 2 < n && isAlpha(s.charCodeAt(i + 2))) {
      const e = s.indexOf('>', i + 2);
      if (e === -1) return null;
      return e + 1;
    }
    return null;
  }
  // tag: <name ...> or </name ...>
  let j = i + 1;
  let closing = false;
  if (s.charCodeAt(j) === 47) { closing = true; j++; } // '/'
  if (j >= n || !isAlpha(s.charCodeAt(j))) return null;
  while (j < n && (isAlnum(s.charCodeAt(j)) || s.charCodeAt(j) === 45)) j++; // name
  // attributes
  while (j < n) {
    const c = s.charCodeAt(j);
    if (c === CODE_SPACE || c === CODE_TAB || c === CODE_NL) { j++; continue; }
    if (c === CODE_GT) return j + 1;
    if (c === 47 && j + 1 < n && s.charCodeAt(j + 1) === CODE_GT) return j + 2; // '/>'
    // attribute name
    if (!(isAlpha(c) || c === 95 || c === 58 || isDigit(c) || c === 45 || c === 46)) return null;
    while (j < n) {
      const a = s.charCodeAt(j);
      if (isAlnum(a) || a === 95 || a === 58 || a === 45 || a === 46) j++;
      else break;
    }
    // optional = value
    let k = j;
    while (k < n && (s.charCodeAt(k) === CODE_SPACE || s.charCodeAt(k) === CODE_TAB)) k++;
    if (k < n && s.charCodeAt(k) === 61) { // '='
      k++;
      while (k < n && (s.charCodeAt(k) === CODE_SPACE || s.charCodeAt(k) === CODE_TAB)) k++;
      if (k < n && (s.charCodeAt(k) === CODE_QUOT || s.charCodeAt(k) === CODE_APOS)) {
        const q = s.charCodeAt(k);
        k++;
        while (k < n && s.charCodeAt(k) !== q) k++;
        if (k >= n) return null;
        j = k + 1;
      } else {
        // unquoted value: no space, ", ', =, <, >, `
        let m = k;
        while (m < n) {
          const v = s.charCodeAt(m);
          if (v === CODE_SPACE || v === CODE_TAB || v === CODE_NL || v === CODE_QUOT || v === CODE_APOS || v === 61 || v === CODE_LT || v === CODE_GT || v === CODE_BACKTICK) break;
          m++;
        }
        if (m === k) return null;
        j = m;
      }
    } else {
      j = k;
    }
  }
  return null;
}

// Scan an extended autolink (GFM): www.xxx or user@host. Called when s starts
// with 'www.' at i, or when an email may start at i. Returns {href, text, end}
// or null. The preceding character must not be a word character (checked by
// the caller for www.; for email the local part must start at i).
function matchWww(s, i) {
  const n = s.length;
  if (!s.startsWith('www.', i)) return null;
  let j = i + 4;
  // domain: labels of alnum/hyphen separated by '.', at least one '.', TLD 2+ letters
  const start = j;
  while (j < n) {
    const c = s.charCodeAt(j);
    if (isAlnum(c) || c === 45 || c === 46) j++;
    else break;
  }
  let domain = s.slice(start, j);
  // trim trailing dots / hyphens
  domain = domain.replace(/[.-]+$/, '');
  if (!domain.includes('.')) return null;
  const tld = domain.slice(domain.lastIndexOf('.') + 1);
  if (tld.length < 2 || !/^[A-Za-z]+$/.test(tld)) return null;
  // labels must not start/end with '-'
  const labels = domain.split('.');
  for (const lab of labels) {
    if (lab === '' || lab.startsWith('-') || lab.endsWith('-')) return null;
  }
  j = start + domain.length;
  // optional path: any chars except whitespace and '<'
  let end = j;
  while (end < n) {
    const c = s.charCodeAt(end);
    if (c === CODE_SPACE || c === CODE_TAB || c === CODE_NL || c === CODE_LT) break;
    end++;
  }
  let url = s.slice(i, end);
  url = trimAutolink(url);
  if (url === '') return null;
  return { href: 'http://' + url, text: url, end: i + url.length };
}

function matchEmailAt(s, i) {
  const n = s.length;
  // local part
  let j = i;
  while (j < n && /[a-zA-Z0-9.!#$%&'*+\/=?^_`{|}~-]/.test(s[j])) j++;
  if (j === i || j >= n || s.charCodeAt(j) !== 64) return null; // '@'
  const local = s.slice(i, j);
  // domain
  let k = j + 1;
  const dstart = k;
  while (k < n && (isAlnum(s.charCodeAt(k)) || s.charCodeAt(k) === 45 || s.charCodeAt(k) === 46)) k++;
  let domain = s.slice(dstart, k).replace(/[.-]+$/, '');
  if (!domain.includes('.')) return null;
  const tld = domain.slice(domain.lastIndexOf('.') + 1);
  if (tld.length < 2 || !/^[A-Za-z]+$/.test(tld)) return null;
  const labels = domain.split('.');
  for (const lab of labels) {
    if (lab === '' || lab.startsWith('-') || lab.endsWith('-')) return null;
  }
  let email = local + '@' + domain;
  email = trimAutolink(email);
  if (email === '' || !email.includes('@')) return null;
  return { href: 'mailto:' + email, text: email, end: i + email.length };
}

// Trim trailing punctuation and unbalanced parens from an autolink URL.
function trimAutolink(url) {
  // End before an & that begins an entity-like reference.
  const amp = url.search(/&(?=(#\d{1,7}|#[xX][0-9a-fA-F]{1,6}|\w+);)/);
  if (amp !== -1) url = url.slice(0, amp);
  // A '(' with no matching ')' ends the URL before it.
  let depth = 0;
  for (let i = 0; i < url.length; i++) {
    if (url[i] === '(') depth++;
    else if (url[i] === ')') depth--;
  }
  if (depth > 0) {
    const open = url.lastIndexOf('(');
    if (open !== -1) url = url.slice(0, open);
  }
  // Strip trailing punctuation: ? ! . , : ; * _ ~ ' "
  // and unbalanced ')'.
  let changed = true;
  while (changed && url !== '') {
    changed = false;
    const last = url[url.length - 1];
    if ('?!.,:;*_~\'"'.includes(last)) { url = url.slice(0, -1); changed = true; continue; }
    if (last === ')') {
      let d = 0;
      for (let i = 0; i < url.length; i++) {
        if (url[i] === '(') d++;
        else if (url[i] === ')') d--;
      }
      if (d < 0) { url = url.slice(0, -1); changed = true; }
    }
  }
  return url;
}

// Plain-text rendering of a node range (for image alt text): text and code
// content kept, emphasis markers and link structure dropped, newlines -> space.
function plainText(nodes) {
  let out = '';
  for (const nd of nodes) {
    if (nd.t === 'txt') out += nd.s;
    else if (nd.t === 'code') out += nd.s;
    else if (nd.t === 'em') out += plainText(nd.kids);
    else if (nd.t === 'br') out += ' ';
    else if (nd.t === 'aStart' || nd.t === 'aEnd') { /* drop */ }
    else if (nd.t === 'img') out += nd.alt;
    else if (nd.t === 'html') { /* drop raw html from alt */ }
  }
  return out.replace(/\n/g, ' ');
}

// The inline scanner. Returns the head node of the flat list.
function scanInline(src, refs) {
  const n = src.length;
  let head = null, tail = null;
  let buf = ''; // current text run
  const delims = []; // delimiter nodes in document order
  const brackets = []; // open bracket nodes {node, img, bang}
  let prevChar = -1; // char code before the current scan position (for flanking)

  function flushText() {
    if (buf !== '') {
      const t = mkNode('txt', { s: buf });
      buf = '';
      if (!head) head = t;
      else { tail.next = t; t.prev = tail; }
      tail = t;
    }
  }
  function pushNode(node) {
    flushText();
    if (!head) head = node;
    else { tail.next = node; node.prev = tail; }
    tail = node;
  }
  function push(node) { pushNode(node); }
  function appendText(s) { buf += s; }

  // Try to form a link or image ending at src[i] == ']'. Returns the index
  // just past the link tail, or null when no link forms (']' is literal).
  function tryFormLink(i) {
    if (brackets.length === 0) return null;
    const br = brackets[brackets.length - 1];
    // The link text is the nodes after br up to the current tail (flush the
    // text buffer first so trailing text is inside the link).
    flushText();
    let dest = null, title = null, end = -1;
    const after = i + 1;
    if (after < n && src.charCodeAt(after) === 40) { // '(' inline link
      const t = parseInlineLinkTail(src, after);
      if (!t) return null;
      dest = t.dest; title = t.title; end = t.end;
    } else {
      // Reference link: [label], [] (collapsed), or shortcut.
      let label = null;
      if (after < n && src.charCodeAt(after) === CODE_LBRACKET) {
        // parse [label] with balanced brackets
        let j = after + 1;
        let depth = 1;
        while (j < n && depth > 0) {
          if (src.charCodeAt(j) === CODE_LBRACKET) depth++;
          else if (src.charCodeAt(j) === CODE_RBRACKET) depth--;
          j++;
        }
        if (depth !== 0) return null;
        label = src.slice(after + 1, j - 1);
        end = j;
        if (label === '') label = null; // collapsed: use link text
      }
      if (label === null) {
        // collapsed or shortcut: label is the link text
        label = plainText(rangeNodes(br.next, tail));
      }
      const ref = refs.get(normLabel(label));
      if (!ref) return null;
      dest = ref.dest; title = ref.title;
      if (end === -1) end = i + 1;
    }
    // A link cannot contain a link, but it CAN contain an image.
    let nd = br.next;
    while (nd) {
      if (nd.t === 'aStart' || nd.t === 'aEnd') return null;
      nd = nd.next;
    }
    // Remove this bracket and any brackets opened after it from the stack.
    const brIdx = brackets.indexOf(br);
    brackets.length = brIdx;
    if (br.img) {
      // Image: alt text from the bracket's nodes, then replace the whole
      // range [bang, br .. tail] with a single img node.
      const inner = rangeNodes(br.next, tail);
      const alt = plainText(inner);
      // remove delimiter nodes inside the image from the delimiter stack
      for (const x of inner) {
        if (x.t === 'delim') {
          const di = delims.indexOf(x);
          if (di !== -1) delims.splice(di, 1);
        }
      }
      // unlink the '!' node
      const bang = br.bang;
      if (bang.prev) bang.prev.next = br; else head = br;
      br.prev = bang.prev;
      // unlink the inner nodes
      br.next = null;
      tail = br;
      br.t = 'img';
      br.src = dest; br.title = title; br.alt = alt;
      delete br.bracket; delete br.img; delete br.bang;
      return end;
    }
    // Link: turn the bracket node into aStart, append aEnd after the text.
    br.t = 'aStart';
    br.href = dest; br.title = title;
    delete br.bracket; delete br.img; delete br.bang;
    const endNode = mkNode('aEnd');
    if (!head) head = endNode;
    else { tail.next = endNode; endNode.prev = tail; }
    tail = endNode;
    return end;
  }

  // Nodes from `from` to `to` inclusive (both may be null).
  function rangeNodes(from, to) {
    const out = [];
    let nd = from;
    while (nd) {
      out.push(nd);
      if (nd === to) break;
      nd = nd.next;
    }
    return out;
  }

  let i = 0;
  while (i < n) {
    const c = src.charCodeAt(i);
    // --- backslash escapes ---
    if (c === CODE_BACKSLASH) {
      if (i + 1 < n && src.charCodeAt(i + 1) === CODE_NL) {
        // backslash-newline: hard break
        push(mkNode('br'));
        i += 2;
        prevChar = CODE_NL;
        continue;
      }
      if (i + 1 < n && isPunct(src.charCodeAt(i + 1))) {
        const ch = src[i + 1];
        pushNode(mkNode('txt', { s: escapeText(ch), pre: true }));
        i += 2;
        prevChar = src.charCodeAt(i - 1);
        continue;
      }
      appendText('\\');
      i++;
      prevChar = CODE_BACKSLASH;
      continue;
    }
    // --- code spans ---
    if (c === CODE_BACKTICK) {
      let j = i;
      while (j < n && src.charCodeAt(j) === CODE_BACKTICK) j++;
      const run = j - i;
      const m = matchCodeSpan(src, i, run);
      if (m) {
        push(mkNode('code', { s: m[0] }));
        i = m[1];
        prevChar = CODE_BACKTICK;
        continue;
      }
      appendText('`'.repeat(run));
      i = j;
      prevChar = CODE_BACKTICK;
      continue;
    }
    // --- angle autolinks / raw html ---
    if (c === CODE_LT) {
      const auto = matchAngleAutolink(src, i);
      if (auto) {
        push(mkNode('aStart', { href: auto.href, title: null }));
        push(mkNode('txt', { s: auto.text }));
        push(mkNode('aEnd'));
        i = auto.end;
        prevChar = CODE_GT;
        continue;
      }
      const h = matchRawHtml(src, i);
      if (h !== null) {
        push(mkNode('html', { s: src.slice(i, h) }));
        i = h;
        prevChar = CODE_GT;
        continue;
      }
      appendText('<');
      i++;
      prevChar = CODE_LT;
      continue;
    }
    // --- images / links: '!' + '[' ---
    if (c === CODE_BANG && i + 1 < n && src.charCodeAt(i + 1) === CODE_LBRACKET) {
      const bang = mkNode('txt', { s: '!' });
      pushNode(bang);
      const br = mkNode('txt', { s: '[' });
      br.bracket = true;
      br.img = true;
      br.bang = bang;
      pushNode(br);
      brackets.push(br);
      i += 2;
      prevChar = CODE_LBRACKET;
      continue;
    }
    // --- '[' bracket ---
    if (c === CODE_LBRACKET) {
      const br = mkNode('txt', { s: '[' });
      br.bracket = true;
      br.img = false;
      pushNode(br);
      brackets.push(br);
      i++;
      prevChar = CODE_LBRACKET;
      continue;
    }
    // --- ']' : try to form a link or image ---
    if (c === CODE_RBRACKET) {
      const formed = tryFormLink(i);
      if (formed !== null) {
        i = formed;
        prevChar = CODE_RBRACKET;
        continue;
      }
      appendText(']');
      i++;
      prevChar = CODE_RBRACKET;
      continue;
    }
    // --- emphasis / strikethrough delimiters ---
    if (c === CODE_STAR || c === CODE_UNDER || c === CODE_TILDE) {
      let j = i;
      while (j < n && src.charCodeAt(j) === c) j++;
      const run = j - i;
      if (c === CODE_TILDE && run > 2) {
        appendText('~'.repeat(run));
        i = j;
        prevChar = CODE_TILDE;
        continue;
      }
      // flanking
      const before = charKindAt(src, i - 1);
      const after = charKindAt(src, j);
      const leftFlank = after !== 0 && !(after === 1 && before !== 0 && before !== 1);
      const rightFlank = before !== 0 && !(before === 1 && after !== 0 && after !== 1);
      let open, close;
      if (c === CODE_UNDER) {
        open = leftFlank && (!rightFlank || before === 1);
        close = rightFlank && (!leftFlank || after === 1);
      } else {
        open = leftFlank;
        close = rightFlank;
      }
      const d = mkNode('delim', { ch: String.fromCharCode(c), n: run, open, close });
      push(d);
      delims.push(d);
      i = j;
      prevChar = c;
      continue;
    }
    // --- extended autolinks: www. ---
    if (c === 119 && src.startsWith('www.', i) && !isWord(prevChar)) {
      const w = matchWww(src, i);
      if (w) {
        push(mkNode('aStart', { href: w.href, title: null }));
        push(mkNode('txt', { s: w.text }));
        push(mkNode('aEnd'));
        i = w.end;
        prevChar = src.charCodeAt(i - 1);
        continue;
      }
    }
    // --- extended autolinks: email ---
    if (c !== CODE_SPACE && c !== CODE_TAB && c !== CODE_NL && !isWord(prevChar)) {
      const e = matchEmailAt(src, i);
      if (e) {
        push(mkNode('aStart', { href: e.href, title: null }));
        push(mkNode('txt', { s: e.text }));
        push(mkNode('aEnd'));
        i = e.end;
        prevChar = src.charCodeAt(i - 1);
        continue;
      }
    }
    // --- numeric character reference ---
    if (c === CODE_AMP) {
      const r = numericRef(src, i);
      if (r) {
        appendText(String.fromCodePoint(r[0]));
        i += r[1];
        prevChar = CODE_AMP;
        continue;
      }
      appendText('&');
      i++;
      prevChar = CODE_AMP;
      continue;
    }
    // --- newline: hard or soft break ---
    if (c === CODE_NL) {
      // trailing spaces in the current text run?
      let spaces = 0;
      let k = buf.length - 1;
      while (k >= 0 && buf[k] === ' ') { spaces++; k--; }
      if (spaces >= 2) {
        buf = buf.slice(0, buf.length - spaces);
        push(mkNode('br'));
        // the newline is consumed by the hard break
      } else {
        appendText('\n');
      }
      i++;
      prevChar = CODE_NL;
      continue;
    }
    // --- plain text run ---
    let j = i;
    while (j < n) {
      const d = src.charCodeAt(j);
      if (d === CODE_BACKSLASH || d === CODE_BACKTICK || d === CODE_LT || d === CODE_LBRACKET ||
        d === CODE_RBRACKET || d === CODE_STAR || d === CODE_UNDER || d === CODE_TILDE ||
        d === CODE_AMP || d === CODE_NL || d === CODE_BANG) break;
      // a www. autolink can start here: stop the run so the autolink
      // branch gets a chance (otherwise the run swallows it as text)
      if (d === 119 && src.startsWith('www.', j)) break;
      j++;
    }
    if (j === i) j = i + 1; // a single char that is special only in context (e.g. '!')
    appendText(src.slice(i, j));
    prevChar = src.charCodeAt(j - 1);
    i = j;
  }
  // flush remaining text
  flushText();
  return { head, delims };
}

// ---------------------------------------------------------------- emphasis
//
// The delimiter-stack pass (CommonMark Appendix A, generalised to ~).
// Delimiters are linked into a chain via dPrev/dNext; the node list is a
// separate doubly-linked list. Forming emphasis wraps the nodes between an
// opener and a closer into an em/strong/del node.

function processEmphasis(head, delims) {
  if (delims.length === 0) return head;
  // link the delimiter chain
  for (let i = 0; i < delims.length; i++) {
    delims[i].dPrev = i > 0 ? delims[i - 1] : null;
    delims[i].dNext = i + 1 < delims.length ? delims[i + 1] : null;
  }
  const bottom = {}; // ch -> delimiter node (do not look past it), or null
  let current = delims[0];
  while (current) {
    if (!current.close) { current = current.dNext; continue; }
    // find the nearest opener of the same char, walking back
    const b = bottom[current.ch] || null;
    let opener = current.dPrev;
    let found = null;
    let sawOpener = false;
    while (opener && opener !== b) {
      if (opener.ch === current.ch && opener.open) {
        sawOpener = true;
        const odd = (opener.close || current.open) &&
          ((opener.n + current.n) % 3 === 0) &&
          (opener.n % 3 !== 0 || current.n % 3 !== 0);
        if (!odd) { found = opener; break; }
      }
      opener = opener.dPrev;
    }
    if (found) {
      const use = (found.n >= 2 && current.n >= 2) ? 2 : 1;
      const tag = current.ch === '~' ? 'del' : (use === 2 ? 'strong' : 'em');
      // gather the nodes between opener and closer
      const kids = [];
      let nd = found.next;
      let bad = false;
      let aDepth = 0;
      while (nd && nd !== current) {
        if (nd.t === 'aStart') aDepth++;
        else if (nd.t === 'aEnd') aDepth--;
        kids.push(nd);
        nd = nd.next;
      }
      if (aDepth !== 0) {
        // emphasis would straddle a link boundary: do not form here.
        // Do not move the bottom marker: the opener may still pair with
        // a later closer past the link.
        current = current.dNext;
        continue;
      }
      // splice the em node in place of the range
      const em = mkNode('em', { tag, kids });
      const before = found.prev;
      const after = current.next;
      // opener: keep it (reduced) or remove it
      found.n -= use;
      if (found.n > 0) {
        if (before) before.next = found; else head = found;
        found.prev = before;
        found.next = em;
        em.prev = found;
      } else {
        if (before) before.next = em; else head = em;
        em.prev = before;
        dropDelim(found, delims, bottom);
      }
      // closer: keep it (reduced) or remove it
      current.n -= use;
      const closerLeft = current.n > 0;
      const nextDelim = current.dNext;
      if (closerLeft) {
        em.next = current;
        current.prev = em;
        if (after) after.prev = current;
        current.next = after;
      } else {
        em.next = after;
        if (after) after.prev = em;
        dropDelim(current, delims, bottom);
      }
      // A closer that still has delimiters left must be re-examined: its
      // remaining run can close another (outer) opener, e.g. the last *
      // of *** after a ** strong. Advancing past it loses that pairing.
      current = closerLeft ? current : nextDelim;
    } else {
      // No opener for this closer. Only move the bottom marker when no
      // candidate opener was seen at all: an opener rejected by the rule
      // of 3 for THIS closer (its n differs) may still pair with a later
      // closer, so it must stay reachable.
      if (current.open && !sawOpener) bottom[current.ch] = current.dPrev;
      current = current.dNext;
    }
  }
  return head;
}

// Remove a delimiter from the delimiter chain and array only. The caller
// has already re-spliced the node list, so prev/next are left alone.
// If it was a bottom marker, the bottom moves to the delimiter before it.
function dropDelim(d, delims, bottom) {
  const idx = delims.indexOf(d);
  if (idx !== -1) delims.splice(idx, 1);
  if (bottom) {
    for (const k of Object.keys(bottom)) {
      if (bottom[k] === d) bottom[k] = d.dPrev;
    }
  }
  if (d.dPrev) d.dPrev.dNext = d.dNext;
  if (d.dNext) d.dNext.dPrev = d.dPrev;
  d.dPrev = null; d.dNext = null;
}

// Render the flat node list to HTML.
function renderNodes(head) {
  let out = '';
  let nd = head;
  while (nd) {
    switch (nd.t) {
      case 'txt':
        out += nd.pre ? nd.s : escapeText(nd.s);
        break;
      case 'code':
        out += '<code>' + escapeCode(nd.s) + '</code>';
        break;
      case 'html':
        out += nd.s;
        break;
      case 'br':
        out += '<br>';
        break;
      case 'delim':
        out += nd.ch.repeat(nd.n);
        break;
      case 'aStart': {
        out += '<a href="' + escapeText(encodeDest(nd.href)) + '"';
        if (nd.title !== null && nd.title !== undefined) out += ' title="' + escapeText(nd.title) + '"';
        out += '>';
        break;
      }
      case 'aEnd':
        out += '</a>';
        break;
      case 'img': {
        out += '<img src="' + escapeText(encodeDest(nd.src)) + '" alt="' + escapeText(nd.alt) + '"';
        if (nd.title !== null && nd.title !== undefined) out += ' title="' + escapeText(nd.title) + '"';
        out += '>';
        break;
      }
      case 'em':
        out += '<' + nd.tag + '>' + renderKids(nd.kids) + '</' + nd.tag + '>';
        break;
    }
    nd = nd.next;
  }
  return out;
}

function renderKids(kids) {
  let out = '';
  for (const nd of kids) {
    switch (nd.t) {
      case 'txt': out += nd.pre ? nd.s : escapeText(nd.s); break;
      case 'code': out += '<code>' + escapeCode(nd.s) + '</code>'; break;
      case 'html': out += nd.s; break;
      case 'br': out += '<br>'; break;
      case 'delim': out += nd.ch.repeat(nd.n); break;
      case 'aStart': {
        out += '<a href="' + escapeText(encodeDest(nd.href)) + '"';
        if (nd.title !== null && nd.title !== undefined) out += ' title="' + escapeText(nd.title) + '"';
        out += '>';
        break;
      }
      case 'aEnd': out += '</a>'; break;
      case 'img': {
        out += '<img src="' + escapeText(encodeDest(nd.src)) + '" alt="' + escapeText(nd.alt) + '"';
        if (nd.title !== null && nd.title !== undefined) out += ' title="' + escapeText(nd.title) + '"';
        out += '>';
        break;
      }
      case 'em': out += '<' + nd.tag + '>' + renderKids(nd.kids) + '</' + nd.tag + '>'; break;
    }
  }
  return out;
}

// Fast path: inline text with no markup at all. Returns the HTML, or null
// when the text needs the full parser.
function fastInline(src) {
  // No backslash, backtick, <, [, ], !, *, _, ~, & and no 2-space hard break.
  // Also bail when an extended autolink may be present (www. or an email
  // with @): those are only detected by the full scan, so the fast path
  // would silently drop them.
  if (src.includes('www.') || src.includes('@')) return null;
  for (let i = 0; i < src.length; i++) {
    const c = src.charCodeAt(i);
    if (c === 92 || c === 96 || c === 60 || c === 91 || c === 93 || c === 33 ||
      c === 42 || c === 95 || c === 126 || c === 38) return null;
    if (c === 32 && src.charCodeAt(i + 1) === 32) {
      // two spaces: only a hard break if a newline follows later on this run
      let j = i;
      while (src.charCodeAt(j) === 32) j++;
      if (src.charCodeAt(j) === 10) return null;
      i = j - 1;
    }
  }
  return escapeText(src);
}

// The inline entry point.
function parseInline(src, refs) {
  if (src === '') return '';
  const fast = fastInline(src);
  if (fast !== null) return fast;
  const { head, delims } = scanInline(src, refs);
  const h2 = processEmphasis(head, delims);
  return renderNodes(h2);
}

// ---------------------------------------------------------------- line cursor
// A cursor over one source line, with partial-tab support: a tab advances to
// the next multiple of 4 columns; when a tab is consumed as a single space
// (after '>' or as indentation) the rest of it stays as a partial tab of
// spaces. Tabs inside content are preserved as-is.

function makeCursor(s) { return { s, i: 0, col: 0, part: 0 }; }
function curChar(c) {
  if (c.part > 0) return ' ';
  return c.i < c.s.length ? c.s[c.i] : '';
}
function curAdvance(c, n) {
  while (n > 0) {
    if (c.part > 0) {
      const take = Math.min(n, c.part);
      c.part -= take; c.col += take; n -= take;
      if (c.part === 0) c.i++;
    } else if (c.i < c.s.length) {
      const ch = c.s[c.i];
      if (ch === '\t') {
        const w = 4 - (c.col % 4);
        if (w <= n) { c.i++; c.col += w; n -= w; }
        else { c.part = w - n; c.col += n; n = 0; }
      } else { c.i++; c.col += 1; n -= 1; }
    } else break;
  }
}
function curSpaces(c) {
  let n = 0, col = c.col;
  let j = c.i;
  if (c.part > 0) { n += c.part; col += c.part; j++; }
  for (; j < c.s.length; j++) {
    const ch = c.s[j];
    if (ch === ' ') { n++; col++; }
    else if (ch === '\t') { const w = 4 - (col % 4); n += w; col += w; }
    else break;
  }
  return n;
}
function curRest(c) {
  if (c.part > 0) return ' '.repeat(c.part) + c.s.slice(c.i + 1);
  return c.s.slice(c.i);
}
// Like curRest, but expand leading tabs to spaces. Used for paragraph
// content: inside a container the offset is past column 0 and a leading
// tab expands to the next tab stop; at the top level (col 0) the raw
// line is kept (a tab in a continuation line stays a tab).
function curRestExpanded(c) {
  const rest = curRest(c);
  if (c.col === 0 && c.part === 0) return rest;
  let col = c.col;
  let i = 0;
  let out = '';
  while (i < rest.length) {
    const ch = rest[i];
    if (ch === ' ') { out += ' '; col++; i++; }
    else if (ch === '\t') { const w = 4 - (col % 4); out += ' '.repeat(w); col += w; i++; }
    else break;
  }
  return out + rest.slice(i);
}
function curBlank(c) {
  for (let j = c.i; j < c.s.length; j++) {
    const ch = c.s[j];
    if (ch !== ' ' && ch !== '\t') return false;
  }
  return true;
}
function curSnap(c) { return { i: c.i, col: c.col, part: c.part }; }
function curRestore(c, s) { c.i = s.i; c.col = s.col; c.part = s.part; }

// ---------------------------------------------------------------- block parser

const BLOCK_TAGS = new Set(('address article aside base basefont blockquote body caption center col colgroup dd details dialog dir div dl dt fieldset figcaption figure footer form frame frameset h1 h2 h3 h4 h5 h6 head header hr html iframe legend li link main menu menuitem nav noframes ol optgroup option p param section source summary table tbody td tfoot th thead title tr track ul').split(' '));

// A setext underline at the start of s (after up to 3 spaces): returns 1 for
// '=', 2 for '-', else 0. Only the marker char and spaces may follow.
function setextLevel(s) {
  let i = 0, spaces = 0;
  while (i < s.length && s[i] === ' ' && spaces < 3) { i++; spaces++; }
  if (i >= s.length) return 0;
  const ch = s[i];
  if (ch !== '=' && ch !== '-') return 0;
  let j = i;
  while (j < s.length && s[j] === ch) j++;
  while (j < s.length && (s[j] === ' ' || s[j] === '\t')) j++;
  if (j !== s.length) return 0;
  return ch === '=' ? 1 : 2;
}

// A thematic break: 3+ of the same * - _ with only spaces between.
function isThematicBreak(s) {
  let i = 0, spaces = 0;
  while (i < s.length && s[i] === ' ' && spaces < 3) { i++; spaces++; }
  if (i >= s.length) return false;
  const ch = s[i];
  if (ch !== '*' && ch !== '-' && ch !== '_') return false;
  let count = 0;
  while (i < s.length) {
    if (s[i] === ch) { count++; i++; }
    else if (s[i] === ' ' || s[i] === '\t') i++;
    else return false;
  }
  return count >= 3;
}

// ATX heading: returns {level, content} or null. s is the line from the
// block-start position (up to 3 leading spaces already stripped by caller).
function atxHeading(s) {
  let i = 0;
  while (i < s.length && s[i] === '#') i++;
  if (i === 0 || i > 6) return null;
  if (i < s.length && s[i] !== ' ' && s[i] !== '\t') return null;
  let content = s.slice(i).replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
  // closing sequence of #'s preceded by a space (or the whole content)
  const m = content.match(/^(.*?)[ \t]+#+$/);
  if (m) content = m[1].replace(/[ \t]+$/, '');
  else if (/^#+$/.test(content)) content = '';
  return { level: i, content };
}

// Fence start: returns {char, len, info} or null.
function fenceStart(s) {
  let i = 0, spaces = 0;
  while (i < s.length && s[i] === ' ' && spaces < 3) { i++; spaces++; }
  if (i >= s.length) return null;
  const ch = s[i];
  if (ch !== '`' && ch !== '~') return null;
  let j = i;
  while (j < s.length && s[j] === ch) j++;
  const len = j - i;
  if (len < 3) return null;
  const info = s.slice(j).replace(/^[ \t]+/, '').replace(/[ \t]+$/, '');
  if (ch === '`' && info.includes('`')) return null;
  return { char: ch, len, info };
}

// Is this line a closing fence for the given fence?
function isClosingFence(s, fence) {
  let i = 0, spaces = 0;
  while (i < s.length && s[i] === ' ' && spaces < 3) { i++; spaces++; }
  let j = i;
  while (j < s.length && s[j] === fence.char) j++;
  if (j - i < fence.len) return false;
  while (j < s.length && (s[j] === ' ' || s[j] === '\t')) j++;
  return j === s.length;
}

// HTML block start: returns {type, endTag} or null. type 1-6 (can interrupt
// a paragraph) and 7 (cannot). endTag is the closing marker for types 1-5.
function htmlBlockStart(s) {
  let i = 0, spaces = 0;
  while (i < s.length && s[i] === ' ' && spaces < 3) { i++; spaces++; }
  if (i >= s.length || s[i] !== '<') return null;
  const rest = s.slice(i);
  const low = rest.toLowerCase();
  // type 1: script, pre, style, textarea
  for (const tag of ['script', 'pre', 'style', 'textarea']) {
    if (low.startsWith('<' + tag)) {
      const after = rest[1 + tag.length];
      if (after === undefined || after === ' ' || after === '\t' || after === '\n' || after === '>') {
        return { type: 1, endTag: '</' + tag };
      }
    }
  }
  if (low.startsWith('<!--')) return { type: 2, endTag: '-->' };
  if (low.startsWith('<?')) return { type: 3, endTag: '?>' };
  if (low.startsWith('<!') && low.length > 2 && /[a-z]/.test(low[2])) return { type: 4, endTag: '>' };
  if (low.startsWith('<![cdata[')) return { type: 5, endTag: ']]>' };
  // type 6: block tag (open or close), followed by space/tab/newline/> or end
  let m = low.match(/^<\/?([a-z][a-z0-9-]*)/);
  if (m && BLOCK_TAGS.has(m[1])) {
    const after = rest[m[0].length];
    if (after === undefined || after === ' ' || after === '\t' || after === '\n' || after === '>' || after === '/') {
      return { type: 6, endTag: null };
    }
  }
  // type 7: a complete open or closing tag, nothing else on the line
  m = rest.match(/^<\/?[a-zA-Z][a-zA-Z0-9-]*(?:\s+[^<>]*)?\/?>[ \t]*$/);
  if (m) return { type: 7, endTag: null };
  return null;
}

// Do two list markers (or a marker and a list node) belong to the same
// list? Unordered lists must share the bullet char; ordered lists must
// share the delimiter.
function sameListKind(a, b) {
  if (a.ordered !== b.ordered) return false;
  if (a.ordered) return a.delim === b.delim;
  return a.bullet === b.bullet;
}

function listMarker(s) {
  let i = 0, spaces = 0;
  while (i < s.length && s[i] === ' ' && spaces < 3) { i++; spaces++; }
  if (i >= s.length) return null;
  const ch = s[i];
  if (ch === '-' || ch === '+' || ch === '*') {
    if (i + 1 < s.length && s[i + 1] !== ' ' && s[i + 1] !== '\t') return null;
    return { ordered: false, start: 1, markerLen: 1, indent: i, bullet: ch, delim: null };
  }
  if (ch >= '0' && ch <= '9') {
    let j = i;
    while (j < s.length && s[j] >= '0' && s[j] <= '9') j++;
    if (j - i > 9) return null;
    if (j < s.length && (s[j] === '.' || s[j] === ')')) {
      if (j + 1 < s.length && s[j + 1] !== ' ' && s[j + 1] !== '\t') return null;
      return { ordered: true, start: parseInt(s.slice(i, j), 10), delim: s[j], markerLen: j - i + 1, indent: i, bullet: null };
    }
  }
  return null;
}

// ---------------------------------------------------------------- link ref defs

// Try to parse one link reference definition starting at text[pos].
// Returns {label, dest, title, end} or null. Handles multi-line dest/title.
function tryParseDef(text, pos) {
  const n = text.length;
  let i = pos;
  // up to 3 leading spaces
  let sp = 0;
  while (i < n && text[i] === ' ' && sp < 3) { i++; sp++; }
  if (i >= n || text[i] !== '[') return null;
  // label: balanced brackets, line breaks allowed (they collapse to
  // spaces when the label is normalised), <= 999 chars. A label cannot
  // contain an unescaped [ (an escaped \[ is fine, it becomes a literal
  // [ in the label).
  let j = i + 1;
  let depth = 1;
  let label = '';
  while (j < n && depth > 0) {
    const c = text[j];
    if (c === '\\' && j + 1 < n && isPunct(text.charCodeAt(j + 1))) {
      label += text[j + 1];
      j += 2;
      continue;
    }
    if (c === '[') return null;
    else if (c === ']') { depth--; if (depth === 0) break; }
    label += c;
    j++;
  }
  if (depth !== 0 || label === '' || label.length > 999) return null;
  j++; // past ']'
  if (j >= n || text[j] !== ':') return null;
  j++;
  // skip spaces/tabs; if EOL, one newline + spaces/tabs
  j = skipInlineWs(text, j);
  if (j < n && text[j] === '\n') {
    j++;
    j = skipInlineWs(text, j);
  }
  const d = parseDest(text, j);
  if (!d) return null;
  const dest = d[0];
  const destEnd = d[1];
  // Optional title after the destination. A title must be preceded by
  // whitespace (or a newline). If the title is on a later line and is
  // invalid (or followed by junk), the title is dropped and the
  // definition ends at the end of the destination's line. If the title
  // is on the same line as the destination and is invalid (or followed
  // by junk), the whole definition is invalid.
  let title = null;
  let end = null;
  let j2 = skipInlineWs(text, destEnd);
  let hasNl = false;
  if (j2 < n && text[j2] === '\n') { hasNl = true; j2++; j2 = skipInlineWs(text, j2); }
  if (j2 > destEnd && j2 < n && (text[j2] === '"' || text[j2] === "'" || text[j2] === '(')) {
    const t = parseTitle(text, j2);
    if (t) {
      const after = skipInlineWs(text, t[1]);
      if (after >= n || text[after] === '\n') {
        title = t[0];
        end = after;
        if (end < n) end++; // consume the newline
      } else if (hasNl) {
        // title on a later line, followed by junk: drop the title
        end = null;
      } else {
        return null; // title on the same line, followed by junk
      }
    } else if (!hasNl) {
      return null; // title on the same line that does not parse
    }
    // title on a later line that does not parse: drop it (end stays null)
  }
  if (end === null) {
    // no (valid) title: the definition ends at the end of the
    // destination's line (only spaces/tabs may follow the destination)
    const e = skipInlineWs(text, destEnd);
    if (e < n && text[e] === '\n') {
      end = e + 1;
    } else if (e >= n) {
      end = e;
    } else {
      return null; // junk after the destination on its line
    }
  }
  return { label, dest, title, end };
}

function skipInlineWs(text, i) {
  while (i < text.length && (text[i] === ' ' || text[i] === '\t')) i++;
  return i;
}

// Strip leading link reference definitions from a paragraph's text.
// Returns the remaining text. Updates refs (first definition wins).
function stripDefs(text, refs) {
  let pos = 0;
  while (pos < text.length) {
    const def = tryParseDef(text, pos);
    if (!def) break;
    const key = normLabel(def.label);
    if (!refs.has(key)) refs.set(key, { dest: def.dest, title: def.title });
    pos = def.end;
  }
  return text.slice(pos);
}

// ---------------------------------------------------------------- tables

// Split a table row line into cells on unescaped '|'. Leading/trailing
// empty cells (from edge pipes) are dropped. Returns null when the line
// has no cell separator structure.
function splitRow(line) {
  const cells = [];
  let cur = '';
  for (let i = 0; i < line.length; i++) {
    const c = line[i];
    if (c === '\\' && i + 1 < line.length && line[i + 1] === '|') {
      cur += '\\|';
      i++;
      continue;
    }
    if (c === '|') {
      cells.push(cur);
      cur = '';
      continue;
    }
    cur += c;
  }
  cells.push(cur);
  // drop a leading empty cell (leading pipe) and a trailing empty cell
  if (cells.length > 0 && cells[0].trim() === '') cells.shift();
  if (cells.length > 0 && cells[cells.length - 1].trim() === '') cells.pop();
  return cells.map((x) => x.trim());
}

// Is this line a table delimiter row? Returns the alignments array or null.
function delimiterRow(line) {
  const cells = splitRow(line);
  if (cells.length === 0) return null;
  const aligns = [];
  for (const cell of cells) {
    const m = cell.match(/^(:?)-+(:?)$/);
    if (!m) return null;
    if (m[1] === ':' && m[2] === ':') aligns.push('center');
    else if (m[2] === ':') aligns.push('right');
    else if (m[1] === ':') aligns.push('left');
    else aligns.push(null);
  }
  return aligns;
}

// ---------------------------------------------------------------- block parsing

// Does the line (from a block-start position) begin a block that would
// interrupt a paragraph? Setext underlines, ATX/fenced-code/HTML
// (types 1-6)/thematic-break starts, blockquotes, and non-empty list
// items (ordered lists only from 1) all interrupt. Used both for the
// paragraph-interruption check and for lazy-continuation decisions:
// a line that interrupts a paragraph is never a lazy continuation.
function interruptsPara(s) {
  if (setextLevel(s)) return true;
  if (atxHeading(s) || fenceStart(s) || isThematicBreak(s)) return true;
  const html = htmlBlockStart(s);
  if (html && html.type !== 7) return true;
  if (s.trimStart().startsWith('>')) return true;
  const lm = listMarker(s);
  if (lm) {
    const after = s.slice(lm.indent + lm.markerLen);
    if (after.trim() !== '') {
      if (!lm.ordered || lm.start === 1) return true;
    }
  }
  return false;
}

function parseBlocks(lines, refs) {
  const doc = { t: 'doc', children: [] };
  const stack = [doc];
  let lastBlank = false;

  function addBlock(b) {
    const parent = stack[stack.length - 1];
    parent.children.push(b);
    // looseness: a blank line before this block inside a list item, or
    // before a new item in a list, makes the list loose. The flag is
    // consumed here: it means "a blank line since the last block was added".
    if (lastBlank) {
      if (parent.t === 'item' && parent.children.length > 1) {
        const list = stack[stack.length - 2];
        if (list && list.t === 'list') list.tight = false;
      } else if (parent.t === 'list' && b.t === 'item' && parent.children.length > 1) {
        parent.tight = false;
      }
    }
    lastBlank = false;
    return b;
  }

  function finalize(b) {
    if (b.t === 'para') {
      const text = stripDefs(b.lines.join('\n'), refs);
      // table? first line header, second line delimiter
      const ls = text.split('\n');
      if (ls.length >= 2) {
        const head = splitRow(ls[0]);
        const aligns = delimiterRow(ls[1]);
        if (head.length > 0 && aligns && aligns.length === head.length) {
          const rows = [];
          for (let k = 2; k < ls.length; k++) {
            const cells = splitRow(ls[k]);
            while (cells.length < head.length) cells.push('');
            rows.push(cells.slice(0, head.length));
          }
          b.t = 'table';
          b.align = aligns;
          b.header = head;
          b.rows = rows;
          delete b.lines;
          return;
        }
      }
      if (text === '') {
        // paragraph of only definitions: remove it from its parent
        const parent = stack[stack.length - 1];
        const idx = parent.children.indexOf(b);
        if (idx !== -1) parent.children.splice(idx, 1);
        return;
      }
      b.text = text;
      delete b.lines;
    }
    if (b.t === 'code') {
      if (b.fenced) {
        // strip exactly one trailing newline when the last content line
        // was blank (content ends with \n\n, or is a single blank line)
        if (b.content === '\n' || b.content.endsWith('\n\n')) {
          b.content = b.content.slice(0, -1);
        }
      } else if (b.content !== '') {
        // indented code: strip all trailing blank lines
        b.content = b.content.replace(/\n+$/, '') + '\n';
      }
    }
    if (b.t === 'html' && b.stripNl && b.content.endsWith('\n')) {
      // an HTML block followed by a blank line has no trailing newline
      b.content = b.content.slice(0, -1);
    }
    if (b.t === 'list') b.closed = true;
  }

  function closeTo(depth) {
    while (stack.length - 1 > depth) {
      const b = stack.pop();
      finalize(b);
    }
  }

  let li = 0;
  while (li < lines.length) {
    const cur = makeCursor(lines[li]);
    // whether this source line is blank (only whitespace): a line that is
    // blank only after its container markers are consumed (e.g. a bare
    // `>` blockquote line) is NOT a blank line, and must not loosen a
    // list or close an empty item
    const srcBlank = /^[ \t]*$/.test(lines[li]);
    // ---- Phase 1: match open containers ----
    let depth = 0;
    let lazy = false;
    let j = 1;
    while (j < stack.length) {
      const b = stack[j];
      if (b.t === 'list') {
        // a list always matches (it consumes no input itself)
        depth = j;
        j++;
        continue;
      }
      if (b.t === 'quote') {
        const snap = curSnap(cur);
        let sp = 0;
        while (sp < 3 && curChar(cur) === ' ') { curAdvance(cur, 1); sp++; }
        if (curChar(cur) === '>') {
          curAdvance(cur, 1);
          // the optional space after '>' consumes one column, even when
          // it is a tab (leaving a partial tab behind)
          if (curChar(cur) === ' ' || curChar(cur) === '\t') curAdvance(cur, 1);
          depth = j;
          j++;
          continue;
        }
        curRestore(cur, snap);
        // a line that would interrupt a paragraph (setext, ATX, fence,
        // thematic break, HTML, blockquote, interrupting list) is never
        // a lazy continuation: the container closes instead. A marker
        // for any enclosing list is likewise a new item, not lazy text.
        if (stack[stack.length - 1].t === 'para' && !curBlank(cur)) {
          let newItem = false;
          const lm0 = listMarker(curRest(cur));
          if (lm0) {
            // a list marker is never a lazy continuation of a paragraph
            // that lives inside a list: it either continues the enclosing
            // list (same kind) or starts a new list (different bullet or
            // delimiter), it never becomes paragraph text
            for (let k = 1; k < stack.length - 1; k++) {
              if (stack[k].t === 'list') { newItem = true; break; }
            }
          }
          if (!newItem && !interruptsPara(curRest(cur))) lazy = true;
        }
        break;
      }
      if (b.t === 'item') {
        if (curBlank(cur)) {
          depth = j;
          j++;
          continue;
        }
        // An empty list item that is followed by a blank line accepts no
        // further content: an indented line after the blank line is a
        // separate block, not part of the item.
        const emptyAfterBlank = b.children.length === 0 && lastBlank;
        if (curSpaces(cur) >= b.indent && !emptyAfterBlank) {
          curAdvance(cur, b.indent);
          depth = j;
          j++;
          continue;
        }
        if (stack[stack.length - 1].t === 'para' && !curBlank(cur)) {
          let newItem = false;
          const lm0 = listMarker(curRest(cur));
          if (lm0) {
            // a list marker is never a lazy continuation of a paragraph
            // that lives inside a list: it either continues the enclosing
            // list (same kind) or starts a new list (different bullet or
            // delimiter), it never becomes paragraph text
            for (let k = 1; k < stack.length - 1; k++) {
              if (stack[k].t === 'list') { newItem = true; break; }
            }
          }
          if (!newItem && !interruptsPara(curRest(cur))) lazy = true;
        }
        break;
      }
      break;
    }
    if (lazy) {
      const top = stack[stack.length - 1];
      // a lazy continuation line has 4 columns of leading indent stripped
      // (the indented-code threshold); fewer than 4 columns are kept
      if (curSpaces(cur) >= 4) curAdvance(cur, 4);
      top.lines.push(curRestExpanded(cur));
      li++;
      continue;
    }
    // If every container matched and the top block is a leaf, keep the
    // leaf open: phase 2 decides whether this line continues it or
    // closes it. (Without this, closeTo would end every multi-line
    // paragraph and code block after its first line.)
    if (stack.length > 1) {
      const topB = stack[stack.length - 1];
      if ((topB.t === 'para' || topB.t === 'code' || topB.t === 'html') &&
          depth === stack.length - 2) {
        depth = stack.length - 1;
      }
    }
    closeTo(depth);

    // ---- Phase 2: consume this line (may loop for new containers) ----
    let done = false;
    while (!done) {
      const top = stack[stack.length - 1];
      if (curBlank(cur)) {
        if (top.t === 'code') {
          // blank line inside code: content, not a structural blank
          top.content += '\n';
          done = true;
          break;
        }
        if (top.t === 'para') {
          stack.pop();
          finalize(top);
        } else if (top.t === 'html') {
          // Only HTML block types 6 and 7 end at a blank line. Types 1-5
          // (script/pre/style/textarea/comment/processing-instruction and
          // block tags that end at a closing tag) keep blank lines as
          // content until their end tag.
          if (top.type === 6 || top.type === 7) {
            top.stripNl = true;
            stack.pop();
            finalize(top);
          } else {
            top.content += '\n';
          }
        }
        // only a real source-blank line counts as a blank line for
        // looseness / empty-item purposes
        if (srcBlank) lastBlank = true;
        done = true;
        break;
      }

      if (top.t === 'para') {
        // setext underline? Convert the paragraph node in place (it is
        // already in its parent's children; do not leave a stale copy).
        // A paragraph made only of link reference definitions has no
        // content to be a heading: the underline is then an ordinary
        // paragraph line instead.
        const lvl = setextLevel(curRest(cur));
        if (lvl) {
          const text = stripDefs(top.lines.join('\n'), refs);
          if (text !== '') {
            top.t = 'heading';
            top.level = lvl;
            top.content = text;
            delete top.lines;
            stack.pop();
            done = true;
            break;
          }
          // else: fall through and add this line to the paragraph
        }
        // interrupting block starts?
        const rest = curRest(cur);
        if (interruptsPara(rest)) {
          stack.pop();
          finalize(top);
          continue; // re-process the line as a new block
        }
        top.lines.push(curRestExpanded(cur));
        done = true;
        break;
      }

      if (top.t === 'code' && top.fenced) {
        if (isClosingFence(curRest(cur), top.fence)) {
          // the closing fence line is consumed by the code block
          stack.pop();
          finalize(top);
          done = true;
          break;
        }
        top.content += curRest(cur) + '\n';
        done = true;
        break;
      }

      if (top.t === 'code' && !top.fenced) {
        if (curSpaces(cur) >= 4) {
          curAdvance(cur, 4);
          top.content += curRest(cur) + '\n';
          done = true;
          break;
        }
        stack.pop();
        finalize(top);
        continue;
      }

      if (top.t === 'html') {
        const line = curRest(cur);
        // type 7 is a single complete tag: it ends after its first line,
        // so a following line is never part of it
        if (top.type === 7) {
          stack.pop();
          finalize(top);
          continue;
        }
        top.content += line + '\n';
        if (top.endTag && line.toLowerCase().includes(top.endTag.toLowerCase())) {
          // the trailing newline is stripped only if the next line is a
          // real blank line; no next line means end-of-input (keep it)
          let strip = false;
          if (li + 1 < lines.length && /^[ \t]*$/.test(lines[li + 1])) strip = true;
          top.stripNl = strip;
          stack.pop();
          finalize(top);
        }
        done = true;
        break;
      }

      // top is a container (doc/quote/list/item): try block starts.
      // A list can only contain items: if this line is not a new item of
      // the same list, close the list and re-process the line above it.
      // When the open list is on top, this line is either a new item of
      // that list (skip straight to the list code below) or the list ends.
      let topListItem = false;
      if (top.t === 'list') {
        const snap = curSnap(cur);
        let sp = 0;
        while (sp < 3 && curChar(cur) === ' ') { curAdvance(cur, 1); sp++; }
        const lm2 = listMarker(curRest(cur));
        curRestore(cur, snap);
        const sameList = lm2 && lm2.indent === 0 && sameListKind(lm2, top);
        if (!sameList) {
          stack.pop();
          finalize(top);
          continue;
        }
        topListItem = true;
      }
      const rest = curRest(cur);
      if (!topListItem) {
      const atx = atxHeading(rest);
      if (atx) {
        addBlock({ t: 'heading', level: atx.level, content: atx.content });
        done = true;
        break;
      }
      const fence = fenceStart(rest);
      if (fence) {
        const code = { t: 'code', fenced: true, fence, info: fence.info, content: '' };
        addBlock(code);
        stack.push(code);
        done = true;
        break;
      }
      const html = htmlBlockStart(rest);
      if (html) {
        const hb = { t: 'html', type: html.type, endTag: html.endTag, content: rest + '\n' };
        addBlock(hb);
        // a block whose first line already contains its end tag is
        // complete (one-line comment <!-- --> or <script>x</script>);
        // a type-7 block is a single complete tag by definition. Push
        // only blocks that still need more lines, or they absorb the
        // lines that follow as raw HTML.
        const endsNow = html.type === 7 || (html.endTag && rest.toLowerCase().includes(html.endTag.toLowerCase()));
        if (endsNow) {
          let strip = false;
          if (li + 1 < lines.length && /^[ \t]*$/.test(lines[li + 1])) strip = true;
          hb.stripNl = strip;
          finalize(hb);
        } else {
          stack.push(hb);
        }
        done = true;
        break;
      }
      if (isThematicBreak(rest)) {
        addBlock({ t: 'hr' });
        done = true;
        break;
      }
      // blockquote
      {
        const snap = curSnap(cur);
        let sp = 0;
        while (sp < 3 && curChar(cur) === ' ') { curAdvance(cur, 1); sp++; }
        if (curChar(cur) === '>') {
          curAdvance(cur, 1);
          if (curChar(cur) === ' ' || curChar(cur) === '\t') curAdvance(cur, 1);
          const q = { t: 'quote', children: [] };
          addBlock(q);
          stack.push(q);
          continue; // re-process the rest of the line inside the quote
        }
        curRestore(cur, snap);
      }
      }
      // list (cursor-based: measure the marker + following whitespace in
      // columns, so tabs expand correctly)
      {
        const snap = curSnap(cur);
        let sp = 0;
        while (sp < 3 && curChar(cur) === ' ') { curAdvance(cur, 1); sp++; }
        const lm = listMarker(curRest(cur));
        if (lm && lm.indent === 0) {
          // columns of whitespace after the marker (tabs expand from the
          // marker's column)
          const markerCol = cur.col;
          let k = lm.markerLen;
          let cols = 0;
          const rs = curRest(cur);
          while (k < rs.length && (rs[k] === ' ' || rs[k] === '\t')) {
            if (rs[k] === ' ') { cols++; k++; }
            else { const w = 4 - ((markerCol + lm.markerLen + cols) % 4); cols += w; k++; }
          }
          const empty = k >= rs.length;
          let contentIndent;
          if (empty) contentIndent = lm.markerLen + 1;
          else if (cols >= 1 && cols <= 4) contentIndent = lm.markerLen + cols;
          else contentIndent = lm.markerLen + 1;
          // item content column, measured from the block-start position
          const itemIndent = sp + contentIndent;
          // find or create the list. If the open list itself is on top,
          // this item belongs to it; otherwise reuse a same-type list
          // that is the previous sibling of the current container.
          let list = null;
          if (stack[stack.length - 1].t === 'list' && sameListKind(lm, stack[stack.length - 1])) {
            list = stack[stack.length - 1];
          } else {
            const parent = stack[stack.length - 1];
            const sibs = parent.children;
            if (sibs.length > 0) {
              const last = sibs[sibs.length - 1];
              if (last.t === 'list' && sameListKind(lm, last) && !last.closed) {
                list = last;
              }
            }
          }
          if (!list) {
            list = { t: 'list', ordered: lm.ordered, start: lm.start, delim: lm.delim || null, bullet: lm.bullet || null, tight: true, children: [], closed: false };
            addBlock(list);
          }
          const item = { t: 'item', children: [], indent: itemIndent };
          if (lastBlank && list.children.length > 0) list.tight = false;
          lastBlank = false;
          list.children.push(item);
          // push the list only if it is not already the stack top
          // (reusing the open list); the item is always pushed
          if (stack[stack.length - 1] !== list) stack.push(list);
          stack.push(item);
          // consume the marker + content indent (the cursor is already
          // past the marker's leading spaces, so only contentIndent)
          curAdvance(cur, contentIndent);
          if (empty) {
            // an empty item: the rest of the line is not a blank line
            done = true;
            break;
          }
          continue; // re-process the rest of the line inside the item
        }
        curRestore(cur, snap);
      }
      // indented code (only when no paragraph is open — top is a container)
      if (curSpaces(cur) >= 4) {
        curAdvance(cur, 4);
        const code = { t: 'code', fenced: false, content: curRest(cur) + '\n' };
        addBlock(code);
        stack.push(code);
        done = true;
        break;
      }
      // paragraph
      {
        const p = { t: 'para', lines: [] };
        addBlock(p);
        stack.push(p);
        p.lines.push(curRestExpanded(cur));
        done = true;
        break;
      }
    }
    li++;
  }
  closeTo(0);
  // mark lists closed (for the sibling check above)
  return doc.children;
}

// ---------------------------------------------------------------- rendering

function renderBlocks(blocks, refs) {
  let out = '';
  for (const b of blocks) out += renderBlock(b, refs);
  return out;
}

function renderBlock(b, refs) {
  switch (b.t) {
    case 'para':
      return '<p>' + parseInline(b.text, refs) + '</p>\n';
    case 'heading':
      return '<h' + b.level + '>' + parseInline(b.content, refs) + '</h' + b.level + '>\n';
    case 'code': {
      if (b.fenced) {
        let lang = '';
        if (b.info) {
          // the info string's first word, with backslash escapes resolved
          const word = b.info.split(/[ \t]/)[0].replace(/\\([!-/:-@[-`{-~])/g, '$1');
          if (word) lang = ' class="language-' + escapeText(word) + '"';
        }
        return '<pre><code' + lang + '>' + escapeCode(b.content) + '</code></pre>\n';
      }
      return '<pre><code>' + escapeCode(b.content) + '</code></pre>\n';
    }
    case 'html':
      return b.content;
    case 'hr':
      return '<hr>\n';
    case 'quote':
      return '<blockquote>\n' + renderBlocks(b.children, refs) + '</blockquote>\n';
    case 'list': {
      const tag = b.ordered ? 'ol' : 'ul';
      const start = b.ordered && b.start !== 1 ? ' start="' + b.start + '"' : '';
      let out = '<' + tag + start + '>\n';
      for (const item of b.children) out += renderItem(item, b.tight, refs);
      return out + '</' + tag + '>\n';
    }
    case 'table': {
      let out = '<table>\n<thead>\n<tr>\n';
      for (let i = 0; i < b.header.length; i++) {
        const a = b.align[i];
        out += '<th' + (a ? ' align="' + a + '"' : '') + '>' + parseInline(b.header[i], refs) + '</th>\n';
      }
      out += '</tr>\n</thead>\n';
      if (b.rows.length > 0) {
        out += '<tbody>';
        for (const row of b.rows) {
          out += '<tr>\n';
          for (let i = 0; i < row.length; i++) {
            const a = b.align[i];
            out += '<td' + (a ? ' align="' + a + '"' : '') + '>' + parseInline(row[i], refs) + '</td>\n';
          }
          out += '</tr>\n';
        }
        out += '</tbody>';
      }
      return out + '</table>\n';
    }
    default:
      return '';
  }
}

// A task-list marker at the start of text: returns {checked, rest} or null.
function taskMarker(text) {
  if (text.startsWith('[ ] ')) return { checked: false, rest: text.slice(4) };
  if (text.startsWith('[x] ') || text.startsWith('[X] ')) return { checked: true, rest: text.slice(4) };
  if (text === '[ ]') return { checked: false, rest: '' };
  if (text === '[x]' || text === '[X]') return { checked: true, rest: '' };
  if (text.startsWith('[ ]\t')) return { checked: false, rest: text.slice(4) };
  if (text.startsWith('[x]\t') || text.startsWith('[X]\t')) return { checked: true, rest: text.slice(4) };
  return null;
}

function renderItem(item, tight, refs) {
  let out = '<li>';
  const kids = item.children;
  // task list: first child is a paragraph starting with [ ] / [x]
  let task = null;
  let firstText = null;
  if (kids.length > 0 && kids[0].t === 'para') {
    task = taskMarker(kids[0].text);
    if (task) firstText = task.rest;
  }
  for (let i = 0; i < kids.length; i++) {
    const k = kids[i];
    if (i === 0 && task) {
      // the checkbox replaces the marker in the first paragraph
      const box = task.checked
        ? '<input checked="" disabled="" type="checkbox">'
        : '<input disabled="" type="checkbox">';
      if (tight) {
        out += box;
        if (firstText !== '') out += ' ' + parseInline(firstText, refs);
      } else {
        out += '<p>' + box;
        if (firstText !== '') out += ' ' + parseInline(firstText, refs);
        out += '</p>\n';
      }
      continue;
    }
    // in a tight list every paragraph renders as inline content (no <p>)
    if (k.t === 'para' && tight) {
      out += parseInline(k.text, refs);
    } else {
      out += renderBlock(k, refs);
    }
  }
  return out + '</li>\n';
}

// ---------------------------------------------------------------- entry point

export function parse(markdown) {
  if (markdown === '') return '';
  const src = markdown.replace(/\r\n?/g, '\n');
  const refs = new Map();
  const lines = src.split('\n');
  // A final \n produces a trailing empty string that is not a real line:
  // treating it as a blank line wrongly strips an HTML block's trailing
  // newline and adds a spurious \n to type 1-5 HTML / code blocks at EOF.
  if (src.endsWith('\n') && lines.length > 0 && lines[lines.length - 1] === '') lines.pop();
  const blocks = parseBlocks(lines, refs);
  return renderBlocks(blocks, refs);
}
