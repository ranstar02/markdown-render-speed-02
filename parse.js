// Fast, dependency-free Markdown renderer.
//
// Returns byte-identical HTML to marked 18.1.3 with its defaults
// (gfm on, breaks off, pedantic off, async off). Written from scratch:
// a block lexer that turns the source into a small token tree, an inline
// lexer that fills in the inline tokens, and a renderer that walks the
// tree. No state is kept between parse() calls.

const ESC = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };
const ESC_ALL = /[&<>"']/g;
const ESC_NO_ENCODE = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;
const ESC_NO_ENCODE_TEST = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/;

// Escape HTML characters. With encodeAll every & is escaped; otherwise an
// & that starts a valid entity or character reference is left alone.
function esc(s, encodeAll) {
  return encodeAll ? s.replace(ESC_ALL, (m) => ESC[m]) : s.replace(ESC_NO_ENCODE, (m) => ESC[m]);
}

const NUM_REF = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));/;
const NUM_REF_ALL = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;

// Decode numeric character references in inline text. A bare & that is not
// part of any reference becomes &amp;; a reference to & itself also becomes
// the literal string "&amp;" so it survives the later escaping pass.
function decodeRefs(s) {
  if (!s.includes('&#')) return s;
  return s.replace(NUM_REF_ALL, (m, dec, hex) => {
    if (dec === undefined && hex === undefined) return '&amp;';
    const n = dec === undefined ? parseInt(hex, 16) : parseInt(dec, 10);
    if (n === 0 || n > 0x10ffff || (n >= 0xd800 && n <= 0xdfff)) return '\uFFFD';
    if (n === 38) return '&amp;';
    return String.fromCodePoint(n);
  });
}

function cleanUrl(href) {
  try { return encodeURI(href).replace(/%25/g, '%'); } catch { return null; }
}

const ANY_PUNCT = /\\([\p{P}\p{S}])/gu;
// Turn backslash-escaped punctuation into the punctuation itself.
function unescapePunct(s) {
  return s.replace(ANY_PUNCT, '$1');
}

// Normalize a link label for lookup: trim, collapse inner whitespace,
// case-fold the way marked does.
function normLabel(s) {
  return s.trim().replace(/\s+/g, ' ').toLowerCase().toUpperCase().toLowerCase();
}

// Remove a run of trailing characters ch from the end of s.
function stripTail(s, ch) {
  let n = s.length;
  while (n > 0 && s.charAt(n - 1) === ch) n--;
  return s.slice(0, n);
}

// Drop trailing blank lines, keeping at most one blank line at the end.
function trimBlankLines(s) {
  const lines = s.split('\n');
  let t = lines.length - 1;
  while (t >= 0 && /^[ \t]*$/.test(lines[t])) t--;
  return lines.length - t <= 2 ? s : lines.slice(0, t + 1).join('\n');
}

// Expand tabs to spaces, counting columns from col.
function expandTabs(s, col) {
  let out = '';
  let c = col;
  for (const ch of s) {
    if (ch === '\t') { const w = 4 - (c % 4); out += ' '.repeat(w); c += w; }
    else { out += ch; c++; }
  }
  return out;
}

// Find the index of the closing delimiter that balances the opening one
// at the start, skipping backslash escapes. Returns -1 when balanced
// without a closer, -2 when a closer appears while still nested.
function findBalanced(s, open, close) {
  if (s.indexOf(open) === -1 && s.indexOf(close) === -1) return -1;
  let depth = 0;
  for (let i = 0; i < s.length; i++) {
    if (s[i] === '\\') { i++; continue; }
    if (s[i] === open) depth++;
    else if (s[i] === close) { depth--; if (depth < 0) return i; }
  }
  return depth > 0 ? -2 : -1;
}

// Split a table row on unescaped pipes, trimming cells and dropping the
// empty cells produced by leading/trailing pipes.
function splitRow(s, count) {
  const withMarks = s.replace(/\|/g, (m, off) => {
    let escaped = false;
    for (let p = off - 1; p >= 0 && s[p] === '\\'; p--) escaped = !escaped;
    return escaped ? '|' : ' |';
  });
  const cells = withMarks.split(' |');
  let start = 0;
  if (!cells[0].trim()) start = 1;
  let end = cells.length;
  if (end > start && !cells[end - 1].trim()) end--;
  const out = [];
  for (let i = start; i < end; i++) out.push(cells[i].trim().replace(/\\\|/g, '|'));
  if (count !== undefined) {
    if (out.length > count) out.length = count;
    while (out.length < count) out.push('');
  }
  return out;
}

// ---- block-level patterns -------------------------------------------------

const BLOCK_TAGS = 'address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul';

const RE = {
  newline: /^(?:[ \t]*(?:\n|$))+/,
  indentedCode: /^((?: {4}| {0,3}\t)[^\n]+(?:\n(?:[ \t]*(?:\n|$))*)?)+/,
  hr: /^ {0,3}((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)/,
  atx: /^ {0,3}(#{1,6})(?=\s|$)(.*)(?:\n+|$)/,
  // Link reference definition: [label]: <href|href> "title"
  def: new RegExp(
    '^ {0,3}\\[' +
    '(?!\\s*\\])((?:\\\\[\\s\\S]|[^\\[\\]\\\\\\n]|\\n(?![ \\t]*\\n))+)' +
    '\\]: *(?:\\n[ \\t]*)?(<[^\\s][^\\s]*>|[^<\\s][^\\s]*|<.*?>)' +
    '(?:(?: +(?:\\n[ \\t]*)?| *\\n[ \\t]*)' +
    '("(?:\\\\[\\s\\S]|[^"\\\\])*"|\'(?:\\\\[\\s\\S]|[^\'\\\\\\n]|\\n(?!\\n))*\'|\\((?:\\\\[\\s\\S]|[^()\\\\])*\\))' +
    ')? *(?:\\n+|$)'
  ),
  htmlComment: /<!--(?:-?>|[\s\S]*?(?:-->|$))/,
};

// HTML block (types 1-7), built from the CommonMark list of block tags.
const HTML_BLOCK = new RegExp(
  '^ {0,3}(?:' +
  '<(script|pre|style|textarea)[\\s>][\\s\\S]*?(?:</\\1>[^\\n]*\\n*|$)' +
  '|<!--(?:-?>|[\\s\\S]*?(?:-->|$))[^\\n]*(?:\\n+|$)' +
  '|<\\?[\\s\\S]*?(?:\\?>[^\\n]*\\n*|$)' +
  '|<![A-Z][\\s\\S]*?(?:>[^\\n]*\\n*|$)' +
  '|<!\\[CDATA\\[[\\s\\S]*?(?:\\]\\]>[^\\n]*\\n*|$)' +
  '|</?(?:' + BLOCK_TAGS + ')(?:[ \\t]+|\\n|/?>|$)[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$)' +
  '|<(?!script|pre|style|textarea)(?:[a-z][a-z0-9-]*)(?: +[a-zA-Z:_][\\w.:-]*(?: *= *"[^"\\n]*"| *= *\'[^\'\\n]*\'| *= *[^\\s"\'=<>`]+)?)* *\\/?>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$)' +
  '|</[a-z][a-z0-9-]*\\s*>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$)' +
  ')', 'i'
);

// A line that can start an HTML block (type 1-7 start conditions).
function htmlStartRe(indent) {
  return new RegExp(
    '^ {0,' + indent + '}(?:</?(?:' + BLOCK_TAGS + ')(?: +|$|/?>)' +
    '|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)' +
    '|<\\?|<![A-Za-z]|<!\\[CDATA\\[)', 'i'
  );
}

// Paragraph: text lines that stop before a blank line or before a line
// that starts another block. The list pattern decides which list markers
// can interrupt a paragraph (only "1."/"1)" ordered markers, any bullet).
function paragraphRe(listPat, withTable) {
  const tablePat = withTable ? '| {0,3}\\|?(?:[:\\- ]*\\|)+[\\:\\- ]*\\n' : '';
  return new RegExp(
    '^([^\\n]+(?:\\n(?!' +
    ' {0,3}(?:(?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)' +
    '| {0,3}#{1,6}(?:\\s|$)' +
    '| {0,3}>' +
    '| {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)' +
    '|' + listPat +
    '| {0,3}(?:</?(?:' + BLOCK_TAGS + ')(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)' +
    tablePat +
    '|[ \\t]+\\n' +
    ')[^\\n]+)*)'
  );
}

// Setext heading: paragraph text followed by a === or --- underline.
function lheadingRe(listPat, withTable) {
  const tablePat = withTable ? '| {0,3}\\|?(?:[:\\- ]*\\|)+[\\:\\- ]*\\n' : '';
  return new RegExp(
    '^(?!' + listPat + ' |(?: {4}| {0,3}\\t)| {0,3}(?:`{3,}|~{3,})| {0,3}>| {0,3}#{1,6}(?:\\s|$)| {0,3}(?:(?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)| {0,3}<[^\\n>]+>\\n' + tablePat + ')' +
    '((?:.|\\n(?!\\s*?\\n|' + listPat + ' | {0,3}(?:`{3,}|~{3,})| {0,3}>| {0,3}#{1,6}(?:\\s|$)| {0,3}(?:(?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)| {0,3}<[^\\n>]+>\\n' + tablePat + '))+?)' +
    '\\n {0,3}(=+|-+)[ \\t]*(?:\\n+|$)'
  );
}

const BULLET = ' {0,3}(?:[*+-]|\\d{1,9}[.)])';
const PARA_LIST = ' {0,3}(?:[*+-]|1[.)])[ \\t]+[^ \\t\\n]';
const BQ_PARA_LIST = ' {0,3}(?:[*+-]|\\d{1,9}[.)])(?:[ \\t]|\\n|$)';

const PARA_GFM = paragraphRe(PARA_LIST, true);
const PARA_BQ = paragraphRe(BQ_PARA_LIST, true);
const LHEAD_GFM = lheadingRe(BULLET, true);

// Table: header line, delimiter line, then body rows.
const TABLE_RE = new RegExp(
  '^ *([^\\n ].*)\\n {0,3}((?:\\| *)?:?-+:? *(?:\\| *:?-+:? *)*(?:\\| *)?)' +
  '(?:\\n((?:(?! *\\n' +
  '| {0,3}(?:(?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)' +
  '| {0,3}#{1,6}(?:\\s|$)' +
  '| {0,3}>' +
  '|(?: {4}| {0,3}\\t)[^\\n]' +
  '| {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)' +
  '| {0,3}(?:[*+-]|1[.)])[ \\t]' +
  '| {0,3}(?:</?(?:' + BLOCK_TAGS + ')(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)' +
  ').*(?:\\n|$))*)\\n*|$)'
);

// Blockquote: one or more lines, each starting with an optional marker;
// the first line may open a paragraph that swallows lazy continuation lines.
const BLOCKQUOTE_RE = new RegExp(
  '^( {0,3}> ?(?:(?![ \\t]*(?:\\n|$))(' + PARA_BQ.source.slice(1) + ')|[^\\n]*)(?:\\n|$))+'
);

const TEXT_RE = /^[^\n]+/;

// ---- block lexer ----------------------------------------------------------
// Turns source text into a token tree. Inline token arrays are queued and
// filled in later, once every link reference definition in the document
// has been seen (a definition at the end of the document still applies to
// a paragraph at the top).

const LIST_ITEM_RE = (bullet) =>
  new RegExp(`^( {0,3}${bullet})((?:[ \t][^\\n]*)?(?:\\n|$))`);
const NEXT_BULLET_RE = (indent) =>
  new RegExp(`^ {0,${indent}}(?:[*+-]|\\d{1,9}[.)])((?:[ \t][^\\n]*)?(?:\\n|$))`);
const HR_RE = (indent) =>
  new RegExp(`^ {0,${indent}}((?:-[ \t]*){3,}|(?:_[ \t]*){3,}|(?:\\*[ \t]*){3,})(?:\\n+|$)`);
const FENCE_START_RE = (indent) =>
  new RegExp(`^ {0,${indent}}(?:\`\`\`|~~~)`);
const ATX_START_RE = (indent) =>
  new RegExp(`^ {0,${indent}}#{1,6}(?:\\s|$)`);
const BQ_START_RE = (indent) => new RegExp(`^ {0,${indent}}>`);

// The continuation-line interrupt regexes depend only on the capped
// indent (0..3); compile each set once and reuse it for every list item.
const listInterruptRes = new Map();
function listInterruptRe(capped) {
  let r = listInterruptRes.get(capped);
  if (!r) {
    r = {
      nextBullet: NEXT_BULLET_RE(capped),
      hr: HR_RE(capped),
      fence: FENCE_START_RE(capped),
      atx: ATX_START_RE(capped),
      html: htmlStartRe(capped),
      bq: BQ_START_RE(capped),
    };
    listInterruptRes.set(capped, r);
  }
  return r;
}

// Index of the first character that is not a space, or -1 when the string
// is all spaces (mirrors String.search(/[^ ]/)).
function firstNonSpace(s) {
  for (let i = 0; i < s.length; i++) if (s.charCodeAt(i) !== 32) return i;
  return -1;
}
// True when the string holds only spaces and tabs (a blank line).
function isBlankLine(s) {
  for (let i = 0; i < s.length; i++) {
    const c = s.charCodeAt(i);
    if (c !== 32 && c !== 9) return false;
  }
  return true;
}

// True when a line can be a table delimiter row: only '|', '-', ':', space
// and tab characters, with at least one '-' and at least one '|' or ':'
// (the table tokenizer itself requires ':' or '|' in the delimiter).
function isTableDelimRow(line) {
  let hasDash = false;
  let hasPipeOrColon = false;
  for (let i = 0; i < line.length; i++) {
    const c = line.charCodeAt(i);
    if (c === 45) hasDash = true;
    else if (c === 124 || c === 58) hasPipeOrColon = true;
    else if (c !== 32 && c !== 9) return false;
  }
  return hasDash && hasPipeOrColon;
}

// True when a line is a setext underline: up to three spaces, then a run of
// '=' or a run of '-', then only spaces/tabs.
function isSetextUnderline(line) {
  let i = 0;
  while (i < line.length && line.charCodeAt(i) === 32 && i < 3) i++;
  if (i >= line.length) return false;
  const c = line.charCodeAt(i);
  if (c !== 61 && c !== 45) return false;
  while (i < line.length && line.charCodeAt(i) === c) i++;
  while (i < line.length && (line.charCodeAt(i) === 32 || line.charCodeAt(i) === 9)) i++;
  return i === line.length;
}

// Whether any line after the first (up to the next blank line) is a setext
// underline. Setext text cannot span a blank line, so if none is found
// before one, the setext tokenizer cannot match and can be skipped.
function hasSetextUnderline(src, from) {
  let i = from;
  const n = src.length;
  while (i < n) {
    let j = src.indexOf('\n', i);
    if (j === -1) j = n;
    const line = src.slice(i, j);
    if (isBlankLine(line)) return false;
    if (isSetextUnderline(line)) return true;
    i = j + 1;
  }
  return false;
}

// First line of a string (without the trailing newline), without allocating
// an array the way split('\n', 1) would.
function firstLineOf(s) {
  const nl = s.indexOf('\n');
  return nl === -1 ? s : s.slice(0, nl);
}

class BlockLexer {
  constructor() {
    this.links = Object.create(null);
    this.hasLinks = false;
    this.queue = []; // {src, tokens} pairs whose tokens are filled in later
    this.top = true;
    this.inLink = false;
    this.inRawBlock = false;
    this.linkEmitted = false;
    this.linkParenPossible = true;
  }

  inline(src) {
    const tokens = [];
    this.queue.push({ src, tokens });
    return tokens;
  }

  lex(src) {
    src = src.replace(/\r\n|\r/g, '\n');
    const tokens = [];
    this.blockTokens(src, tokens);
    for (const job of this.queue) {
      this.inRawBlock = false;
      lexInline(this, job.src, job.tokens);
    }
    this.queue.length = 0;
    return tokens;
  }

  blockTokens(src, tokens, inQuote = false) {
    let smallest = Infinity;
    while (src) {
      if (src.length < smallest) smallest = src.length;
      else break; // no progress: something is wrong, bail out
      // Peek at the first line so tokenizers that cannot match are never
      // tried: each block type can only start with a few specific
      // characters (after up to three spaces of indent). The order below
      // is the same as marked's; a skipped tokenizer would have returned
      // undefined, so the result is identical.
      const nl = src.indexOf('\n');
      const first = nl === -1 ? src : src.slice(0, nl);
      let lead = 0;
      while (lead < first.length && first.charCodeAt(lead) === 32) lead++;
      const fc = lead < first.length ? first.charCodeAt(lead) : -1;
      const blank = fc === -1 || (fc === 9 && isBlankLine(first));
      const indentedCodeShape = lead >= 4 || (lead <= 3 && fc === 9);
      let tok;
      if (blank && (tok = this.space(src))) { src = src.slice(tok.raw.length); const last = tokens.at(-1); if (tok.raw.length === 1 && last) last.raw += '\n'; else tokens.push(tok); continue; }
      if (indentedCodeShape && (tok = this.indentedCode(src))) { src = src.slice(tok.raw.length); const last = tokens.at(-1); if (last && (last.type === 'paragraph' || last.type === 'text')) { last.raw += (last.raw.endsWith('\n') ? '' : '\n') + tok.raw; last.text += '\n' + tok.text; this.queue.at(-1).src = last.text; } else tokens.push(tok); continue; }
      if (lead <= 3 && (fc === 96 || fc === 126) && (tok = this.fences(src))) { src = src.slice(tok.raw.length); tokens.push(tok); continue; }
      if (lead <= 3 && fc === 35 && (tok = this.atx(src))) { src = src.slice(tok.raw.length); tokens.push(tok); continue; }
      if (lead <= 3 && (fc === 45 || fc === 95 || fc === 42) && (tok = this.hr(src))) { src = src.slice(tok.raw.length); tokens.push(tok); continue; }
      if (lead <= 3 && fc === 62 && (tok = this.blockquote(src))) { src = src.slice(tok.raw.length); tokens.push(tok); continue; }
      if (lead <= 3 && (fc === 45 || fc === 42 || fc === 43 || (fc >= 48 && fc <= 57)) && (tok = this.list(src))) { src = src.slice(tok.raw.length); tokens.push(tok); continue; }
      if (lead <= 3 && fc === 60 && (tok = this.htmlBlock(src))) { src = src.slice(tok.raw.length); tokens.push(tok); continue; }
      if (lead <= 3 && fc === 91 && (tok = this.def(src))) {
        src = src.slice(tok.raw.length);
        const last = tokens.at(-1);
        if (last && (last.type === 'paragraph' || last.type === 'text')) {
          last.raw += (last.raw.endsWith('\n') ? '' : '\n') + tok.raw;
          last.text += '\n' + tok.raw;
          this.queue.at(-1).src = last.text;
        } else {
          if (!this.links[tok.tag]) { this.links[tok.tag] = { href: tok.href, title: tok.title }; this.hasLinks = true; }
          tokens.push(tok);
        }
        continue;
      }
      // A table needs a delimiter row as the second line; a setext heading
      // needs an underline line before the next blank line. Both are cheap
      // to check, and skipping the big regexes when they cannot match is
      // a large saving on plain paragraphs.
      const nl2 = nl === -1 ? -1 : src.indexOf('\n', nl + 1);
      const second = nl === -1 ? '' : src.slice(nl + 1, nl2 === -1 ? src.length : nl2);
      if (nl !== -1 && isTableDelimRow(second) && (tok = this.table(src))) { src = src.slice(tok.raw.length); tokens.push(tok); continue; }
      if (nl !== -1 && hasSetextUnderline(src, nl + 1) && (tok = this.setext(src))) { src = src.slice(tok.raw.length); tokens.push(tok); continue; }
      if (this.top && (tok = this.paragraph(src))) {
        const last = tokens.at(-1);
        if (inQuote && last && last.type === 'paragraph') {
          last.raw += (last.raw.endsWith('\n') ? '' : '\n') + tok.raw;
          last.text += '\n' + tok.text;
          this.queue.pop();
          this.queue.at(-1).src = last.text;
        } else tokens.push(tok);
        if (tok.raw.length !== src.length) inQuote = true;
        src = src.slice(tok.raw.length);
        continue;
      }
      if ((tok = this.text(src))) {
        src = src.slice(tok.raw.length);
        const last = tokens.at(-1);
        if (last && last.type === 'text') {
          last.raw += (last.raw.endsWith('\n') ? '' : '\n') + tok.raw;
          last.text += '\n' + tok.text;
          this.queue.pop();
          this.queue.at(-1).src = last.text;
        } else tokens.push(tok);
        continue;
      }
      break; // unreachable in practice
    }
    this.top = true;
    return tokens;
  }

  space(src) {
    const m = RE.newline.exec(src);
    return m && m[0].length > 0 ? { type: 'space', raw: m[0] } : undefined;
  }

  indentedCode(src) {
    const m = RE.indentedCode.exec(src);
    if (!m) return undefined;
    const raw = trimBlankLines(m[0]);
    const text = raw.replace(/^(?: {0,3}\t| {1,4})/gm, '');
    return { type: 'code', raw, codeBlockStyle: 'indented', text };
  }

  fences(src) {
    const open = /^ {0,3}(`{3,}|~{3,})([^\n]*)(?:\n|$)/.exec(src);
    if (!open) return undefined;
    const fence = open[1];
    const ch = fence[0];
    // A backtick fence's info string may not contain a backtick.
    if (ch === '`' && open[2].includes('`')) return undefined;
    let rest = src.slice(open[0].length);
    let closeAt = -1;
    let closeLen = 0;
    const closeRe = new RegExp(`^ {0,3}(${ch}{${fence.length},})[ \\t]*(?=\\n|$)`, 'm');
    const cm = closeRe.exec(rest);
    if (cm) { closeAt = cm.index; closeLen = cm[0].length; }
    let content;
    let raw;
    if (closeAt === -1) { content = rest; raw = src; }
    else {
      // The newline right before the closing fence is not part of the
      // content, and the closing fence's own newline stays outside the raw.
      content = rest.slice(0, closeAt);
      if (content.endsWith('\n')) content = content.slice(0, -1);
      raw = src.slice(0, open[0].length + closeAt + closeLen);
    }
    // When the closing fence is indented, that indent is stripped from
    // every content line (the fence's own leading whitespace).
    const indentMatch = /^(\s+)(?:```)/.exec(raw);
    if (indentMatch) {
      const n = indentMatch[1].length;
      content = content.split('\n').map((line) => {
        const lead = /^\s+/.exec(line);
        if (!lead) return line;
        return line.slice(Math.min(lead[0].length, n));
      }).join('\n');
    }
    const lang = open[2] ? open[2].trim().replace(/\\([\p{P}\p{S}])/gu, '$1') : open[2];
    return { type: 'code', raw, lang, text: content };
  }

  atx(src) {
    const m = RE.atx.exec(src);
    if (!m) return undefined;
    let text = m[2].trim();
    if (/#$/.test(text)) {
      const stripped = stripTail(text, '#');
      if (!stripped || /[ \t]$/.test(stripped)) text = stripped.trim();
    }
    return { type: 'heading', raw: stripTail(m[0], '\n'), depth: m[1].length, text, tokens: this.inline(text) };
  }

  hr(src) {
    const m = RE.hr.exec(src);
    return m ? { type: 'hr', raw: stripTail(m[0], '\n') } : undefined;
  }

  blockquote(src) {
    const m = BLOCKQUOTE_RE.exec(src);
    if (!m) return undefined;
    let lines = stripTail(m[0], '\n').split('\n');
    let raw = '';
    let text = '';
    const tokens = [];
    while (lines.length > 0) {
      let i = 0;
      const chunk = [];
      let seenMarker = false;
      for (; i < lines.length; i++) {
        if (/^ {0,3}>/.test(lines[i])) { chunk.push(lines[i]); seenMarker = true; }
        else if (!seenMarker) chunk.push(lines[i]);
        else break;
      }
      lines = lines.slice(i);
      const joined = chunk.join('\n');
      // Indent setext underlines so they cannot turn the quoted paragraph
      // into a setext heading while the quote is re-lexed.
      const stripped = joined
        .replace(/^( {0,3}>)([ \t]+)/gm, (g, mark, ws) => mark + expandTabs(ws, mark.length))
        .replace(/\n {0,3}((?:=+|-+)[ \t]*)(?=\n|$)/g, '\n    $1')
        .replace(/^ {0,3}>[ \t]?/gm, '');
      raw = raw ? raw + '\n' + joined : joined;
      text = text ? text + '\n' + stripped : stripped;
      const wasTop = this.top;
      this.top = true;
      this.blockTokens(stripped, tokens, true);
      this.top = wasTop;
      if (lines.length === 0) break;
      const last = tokens.at(-1);
      if (!last) break;
      if (last.type === 'code' || last.type === 'heading' || last.type === 'hr' || last.type === 'html' || last.type === 'table') break;
      if (last.type === 'blockquote') {
        const rest = lines.join('\n');
        const mergedSrc = last.raw + '\n' + rest.replace(/^ {0,3}>[ \t]?/gm, '');
        const inner = this.blockquote(mergedSrc);
        tokens[tokens.length - 1] = inner;
        const tail = mergedSrc.slice(inner.raw.length).replace(/^\n/, '');
        const tailLines = tail ? tail.split('\n').length : 0;
        const consumed = tailLines ? lines.slice(0, -tailLines) : lines;
        if (consumed.length > 0) {
          raw += '\n' + consumed.join('\n');
          text = text.slice(0, text.length - last.text.length) + inner.text;
        }
        lines = lines.slice(consumed.length);
        if (lines.length > 0 && /^ {0,3}>/.test(lines[0])) continue;
        break;
      }
      if (last.type === 'list') {
        const rest = lines.join('\n');
        const merged = this.list(last.raw + '\n' + rest);
        tokens[tokens.length - 1] = merged;
        const extra = merged.raw.length > last.raw.length
          ? rest.slice(last.raw.length + 1, merged.raw.length).split('\n').length : 0;
        if (extra > 0) raw += '\n' + lines.slice(0, extra).join('\n');
        lines = lines.slice(extra);
        continue;
      }
    }
    return { type: 'blockquote', raw, tokens, text };
  }

  list(src) {
    const m = /^ {0,3}([*+-]|\d{1,9}[.)])((?:[ \t][^\n]*)?(?:\n|$))/.exec(src);
    if (!m) return undefined;
    const bullet = m[1].trim();
    const ordered = bullet.length > 1;
    const list = { type: 'list', raw: '', ordered, start: ordered ? +bullet.slice(0, -1) : '', loose: false, items: [] };
    const bulletPat = ordered ? `\\d{1,9}\\${bullet.slice(-1)}` : `\\${bullet}`;
    const itemRe = LIST_ITEM_RE(bulletPat);
    let rest = src;
    let anyBlank = false;
    while (rest) {
      const it = itemRe.exec(rest);
      if (!it || RE.hr.test(rest)) break;
      const startOff = src.length - rest.length;
      rest = rest.slice(it[0].length);
      const firstLine = firstLineOf(it[2]);
      const markerLen = it[1].length;
      const content = firstLine.includes('\t')
        ? firstLine.replace(/^[ \t]+/, (w) => expandTabs(w, markerLen)) : firstLine;
      const nextLine = firstLineOf(rest);
      const empty = isBlankLine(content);
      let indent;
      let itemText;
      let skipContinuation = false;
      if (empty && /^[ \t]*$/.test(nextLine)) { rest = rest.slice(nextLine.length + 1); itemText = ''; indent = markerLen + 1; skipContinuation = true; }
      else if (empty) { indent = markerLen + 1; itemText = ''; }
      else {
        indent = firstNonSpace(content);
        if (indent > 4) indent = 1;
        itemText = content.slice(indent);
        indent += markerLen;
      }
      // Consume continuation lines belonging to this item. The block
      // starters that can interrupt an item are checked with the indent
      // capped at (indent - 1): a marker sitting exactly at the item's
      // content column belongs to the item, not to the outside.
      let chunk = itemText;
      let blank = empty;
      let prev = content;
      const capped = Math.max(0, Math.min(3, indent - 1));
      const { nextBullet, hr: hrRe, fence: fenceRe, atx: atxRe, html: htmlRe, bq: bqRe } = listInterruptRe(capped);
      while (!skipContinuation && rest) {
        const line = firstLineOf(rest);
        const expanded = line.includes('\t')
          ? line.replace(/^[ \t]+/, (w) => expandTabs(w, 0)) : line;
        if (fenceRe.test(line) || atxRe.test(line) || htmlRe.test(line) || bqRe.test(line) || nextBullet.test(line) || hrRe.test(line)) break;
        if (firstNonSpace(expanded) >= indent || isBlankLine(line)) {
          chunk += '\n' + expanded.slice(indent);
        } else {
          // A lazy continuation line cannot follow a fence, ATX heading,
          // HTML block or thematic break line: the item ends there.
          const prevExp = prev.includes('\t') ? prev.replace(/\t/g, '    ') : prev;
          if (blank || firstNonSpace(prevExp) >= 4 || fenceRe.test(prev) || atxRe.test(prev) || htmlRe.test(prev) || hrRe.test(prev)) break;
          const setextLine = /^ {0,3}(?:=+|-+) *$/.test(line) && LHEAD_GFM.test(prev + '\n' + line);
          chunk += '\n' + (setextLine ? '    ' + expanded.replace(/^ {0,3}/, '') : line);
        }
        blank = isBlankLine(line);
        prev = expanded.slice(indent);
        rest = rest.slice(line.length + 1);
      }
      const raw = src.slice(startOff, src.length - rest.length);
      if (anyBlank) list.loose = true;
      if (/\n[ \t]*\n[ \t]*$/.test(raw)) anyBlank = true;
      list.items.push({ type: 'list_item', raw, task: false, loose: false, text: chunk, tokens: [] });
      if (!rest) break;
    }
    const lastItem = list.items.at(-1);
    if (!lastItem) return undefined;
    lastItem.raw = lastItem.raw.trimEnd();
    lastItem.text = lastItem.text.trimEnd();
    list.raw = src.slice(0, src.length - rest.length).trimEnd();
    for (const item of list.items) {
      const wasTop = this.top;
      this.top = false;
      item.tokens = this.blockTokens(item.text, []);
      this.top = wasTop;
      if (!list.loose) {
        const spaces = item.tokens.filter((t) => t.type === 'space');
        if (spaces.length > 0 && spaces.some((t) => /\n.*\n/.test(t.raw))) list.loose = true;
      }
    }
    for (const item of list.items) {
      const first = item.tokens[0];
      if (/^\[[ xX]\][ \t]+\S/.test(item.text) && (first?.type === 'text' || first?.type === 'paragraph')) {
        item.task = true;
        item.text = item.text.replace(/^\[[ xX]\][ \t]+/, '');
        first.raw = first.raw.replace(/^\[[ xX]\][ \t]+/, '');
        first.text = first.text.replace(/^\[[ xX]\][ \t]+/, '');
        for (let q = this.queue.length - 1; q >= 0; q--) {
          if (/^\[[ xX]\][ \t]+\S/.test(this.queue[q].src)) {
            this.queue[q].src = this.queue[q].src.replace(/^\[[ xX]\][ \t]+/, '');
            break;
          }
        }
        const cb = /\[[ xX]\]/.exec(item.raw);
        if (cb) {
          const box = { type: 'checkbox', raw: cb[0] + ' ', checked: cb[0] !== '[ ]' };
          item.checked = box.checked;
          if (list.loose && first && (first.type === 'paragraph' || first.type === 'text') && first.tokens) {
            first.raw = box.raw + first.raw;
            first.text = box.raw + first.text;
            first.tokens.unshift(box);
          } else if (list.loose) {
            item.tokens.unshift({ type: 'paragraph', raw: box.raw, text: box.raw, tokens: [box] });
          } else item.tokens.unshift(box);
        }
      } else if (/^\[[ xX]\][ \t]+\S/.test(item.text)) item.task = false;
    }
    if (list.loose) {
      for (const item of list.items) {
        item.loose = true;
        for (const t of item.tokens) if (t.type === 'text') t.type = 'paragraph';
      }
    }
    return list;
  }

  htmlBlock(src) {
    const m = HTML_BLOCK.exec(src);
    if (!m) return undefined;
    const raw = trimBlankLines(m[0]);
    return { type: 'html', block: true, raw, pre: m[1] === 'pre' || m[1] === 'script' || m[1] === 'style', text: raw };
  }

  def(src) {
    const m = RE.def.exec(src);
    if (!m) return undefined;
    if (!/^</.test(m[2]) && findBalanced(m[2], '(', ')') !== -1) return undefined;
    const tag = normLabel(m[1]);
    const href = m[2] ? m[2].replace(/^<(.*)>$/, '$1').replace(/\\([\p{P}\p{S}])/gu, '$1') : '';
    const title = m[3] ? m[3].substring(1, m[3].length - 1).replace(/\\([\p{P}\p{S}])/gu, '$1') : m[3];
    return { type: 'def', tag, raw: stripTail(m[0], '\n'), href, title };
  }

  table(src) {
    const m = TABLE_RE.exec(src);
    if (!m || !/[:|]/.test(m[2])) return undefined;
    const header = splitRow(m[1]);
    const delim = m[2].replace(/^\||\| *$/g, '').split('|');
    if (header.length !== delim.length) return undefined;
    const align = delim.map((d) =>
      /^ *-+: *$/.test(d) ? 'right' : /^ *:-+: *$/.test(d) ? 'center' : /^ *:-+ *$/.test(d) ? 'left' : null);
    const rows = m[3] && m[3].trim() ? m[3].replace(/\n[ \t]*$/, '').split('\n') : [];
    const out = { type: 'table', raw: stripTail(m[0], '\n'), header: [], align, rows: [] };
    for (let i = 0; i < header.length; i++) {
      out.header.push({ text: header[i], tokens: this.inline(header[i]), header: true, align: align[i] });
    }
    for (const row of rows) {
      out.rows.push(splitRow(row, header.length).map((cell, i) => ({ text: cell, tokens: this.inline(cell), header: false, align: align[i] })));
    }
    return out;
  }

  setext(src) {
    const m = LHEAD_GFM.exec(src);
    if (!m) return undefined;
    const text = m[1].trim();
    return { type: 'heading', raw: stripTail(m[0], '\n'), depth: m[2].charAt(0) === '=' ? 1 : 2, text, tokens: this.inline(text) };
  }

  paragraph(src) {
    const m = PARA_GFM.exec(src);
    if (!m) return undefined;
    let text = m[1];
    if (text.charAt(text.length - 1) === '\n') text = text.slice(0, -1);
    return { type: 'paragraph', raw: m[0], text, tokens: this.inline(text) };
  }

  text(src) {
    const m = TEXT_RE.exec(src);
    if (!m) return undefined;
    return { type: 'text', raw: m[0], text: m[0], tokens: this.inline(m[0]) };
  }
}

// ---- inline lexer ---------------------------------------------------------

const PUNCT = /[\p{P}\p{S}]/u;
const PUNCT_NOT_TILDE = /(?!~)[\p{P}\p{S}]/u;
const ALNUM = /[\p{L}\p{N}]/u;
// "Is punctuation" the way marked's inline punctuation rule means it:
// whitespace counts, and * / _ do not.
const IS_PUNCT = /^((?![*_])[\s\p{P}\p{S}])/u;

const INLINE = {
  escape: /^\\([!"#$%&'()*+,\-./:;<=>?@\[\]\\^_`{|}~])/,
  code: /^(`+)([^`]|[^`][\s\S]*?[^`])\1(?!`)/,
  br: /^( {2,}|\\)\n(?!\s*$)[ \t]*/,
  tag: /^<!--(?:-?>|[\s\S]*?-->)|^<\/[a-zA-Z][a-zA-Z0-9-]*\s*>|^<[a-zA-Z][a-zA-Z0-9-]*(?:\s+[a-zA-Z:_][\w.:-]*(?:\s*=\s*"[^"]*"|\s*=\s*'[^']*'|\s*=\s*[^\s"'=<>`]+)?)*\s*\/?>|^<\?[\s\S]*?\?>|^<![a-zA-Z]+\s[\s\S]*?>|^<!\[CDATA\[[\s\S]*?\]\]>/,
  autolink: /^<([a-zA-Z][a-zA-Z0-9+.-]{1,31}:[^\s\x00-\x1f<>]*|[a-zA-Z0-9.!#$%&'*+/=?^_`{|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_]))>/,
  url: /^(?:(?:mailto|xmpp):[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])(?:\/[A-Za-z0-9@.]+)?|((?:[hH][tT][tT][pP][sS]?|[fF][tT][pP]):\/\/|www\.)(?:[a-zA-Z0-9\-]+\.?)+[^\s<]*|[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-]))/,
  backpedal: /(?:[^?!.,:;*_'"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'"~)]+(?!$))+/,
  // Left delimiter of an emphasis run.
  emLDelim: new RegExp(
    '^(?:\\*+(?:((?!\\*)(?!~)[\\p{P}\\p{S}])|([^\\s*]))?)' +
    '|^_+(?:((?!_)(?!~)[\\p{P}\\p{S}])|([^\\s_]))?', 'u'
  ),
  // Right delimiters for * runs (GFM: ~ is not punctuation here).
  emRDelimAst: new RegExp(
    '^[^_*]*?__[^_*]*?\\*[^_*]*?(?=__)|[^*]+(?=[^*])' +
    '|(?!\\*)(?!~)[\\p{P}\\p{S}](\\*+)(?=[\\s]|$)' +
    '|(?:[^\\s\\p{P}\\p{S}]|~)(\\*+)(?!\\*)(?=(?!~)[\\s\\p{P}\\p{S}]|$)' +
    '|(?!\\*)(?!~)[\\s\\p{P}\\p{S}](\\*+)(?=(?:[^\\s\\p{P}\\p{S}]|~))' +
    '|[\\s](\\*+)(?!\\*)(?=(?!~)[\\p{P}\\p{S}])' +
    '|(?!\\*)(?!~)[\\p{P}\\p{S}](\\*+)(?!\\*)(?=(?!~)[\\p{P}\\p{S}])' +
    '|(?:[^\\s\\p{P}\\p{S}]|~)(\\*+)(?=(?:[^\\s\\p{P}\\p{S}]|~))', 'gu'
  ),
  // Right delimiters for _ runs. Unlike *, _ has no "inside a word"
  // closer alternative: a _ run between two word characters cannot close.
  emRDelimUnd: new RegExp(
    '^[^_*]*?\\*\\*[^_*]*?_[^_*]*?(?=\\*\\*)|[^_]+(?=[^_])' +
    '|(?!_)[\\p{P}\\p{S}](_+)(?=[\\s]|$)' +
    '|[^\\s\\p{P}\\p{S}](_+)(?!_)(?=[\\s\\p{P}\\p{S}]|$)' +
    '|(?!_)[\\s\\p{P}\\p{S}](_+)(?=[^\\s\\p{P}\\p{S}])' +
    '|[\\s](_+)(?!_)(?=[\\p{P}\\p{S}])' +
    '|(?!_)[\\p{P}\\p{S}](_+)(?!_)(?=[\\p{P}\\p{S}])', 'gu'
  ),
  delLDelim: /^(~~?)(?:((?!~)[\p{P}\p{S}])|[^\s~])/u,
  delRDelim: new RegExp(
    '^[^~]+(?=[^~])' +
    '|(?!~)[\\p{P}\\p{S}](~~?)(?=[\\s]|$)' +
    '|[^\\s\\p{P}\\p{S}](~~?)(?!~)(?=[\\s\\p{P}\\p{S}]|$)' +
    '|(?!~)[\\s\\p{P}\\p{S}](~~?)(?=[^\\s\\p{P}\\p{S}])' +
    '|[\\s](~~?)(?!~)(?=[\\p{P}\\p{S}])' +
    '|(?!~)[\\p{P}\\p{S}](~~?)(?!~)(?=[\\p{P}\\p{S}])' +
    '|[^\\s\\p{P}\\p{S}](~~?)(?=[^\\s\\p{P}\\p{S}])', 'gu'
  ),
  text: new RegExp(
    '^(?:[^a-zA-Z0-9](?=(?:mailto|xmpp):)' +
    '|(`+|~+|[^`~])(?:(?=[`~])|(?= {2,}\\n)|(?=[a-zA-Z0-9.!#$%&\'*+\\/=?_`{|}~-]+@)' +
    '|[\\s\\S]*?(?:(?=[\\\\<!\\[`*~_]|\\b_|[hH][tT][tT][pP][sS]?|[fF][tT][pP]:\\/\\/|(?<![^\\s*_~(])www\\.|$)' +
    '|[^ ](?= {2,}\\n)|[^a-zA-Z0-9](?=(?:mailto|xmpp):)' +
    '|[^a-zA-Z0-9.!#$%&\'*+\\/=?_`{|}~-](?=[a-zA-Z0-9.!#$%&\'*+\\/=?_`{|}~-]+@))))'
  ),
};

// A bracket pair with no nesting inside it.
const LE_INNER = '(?:\\\\[\\s\\S]|[^\\[\\]\\\\])*';
const LE = '\\[(?:' + LE_INNER + ')\\]';
// Label inside [ ... ] for inline links (may contain one level of nested
// brackets and code spans, but no unescaped ] outside them).
const LABEL_INNER = '(?:\\[(?:' + LE + '|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\\])|[^\\[\\]\\\\`])*?';
const LABEL_REF = '(?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\\\n]|\\n(?![ \\t]*\\n))+';
const LINK_RE = new RegExp(
  '^!?\\[(' + LABEL_INNER + ')\\]\\([ \\t\\n]*' +
  '(<(?:\\\\.|[^\\n<>\\\\])+>|[^ \\t\\n\\x00-\\x1f]+|(?=\\)))' +
  '(?:(?:[ \\t]+(?:\\n[ \\t]*)?|\\n[ \\t]*)' +
  '("(?:\\\\[\\s\\S]|[^"\\\\])*"|\'(?:\\\\[\\s\\S]|[^\'\\\\])*\'|\\((?:\\\\[\\s\\S]|[^)\\\\])*\\)))?[ \\t\\n]*\\)'
);
const REFLINK_RE = new RegExp('^!?\\[(' + LABEL_INNER + ')\\]\\[(' + LABEL_REF + ')\\]');
const NOLINK_RE = new RegExp('^!?\\[(' + LABEL_REF + ')\\](?:\\[\\])?');
// Used to find link-like text when masking emphasis input.
const REFLINK_SEARCH_RE = new RegExp(
  '(?:!?\\[(' + '(?:[^\\[\\]\\\\`]*(?:\\[(?:\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\\]))){0,999}?[^\\[\\]\\\\`]*?' + ')\\]\\[(' + '(?:\\\\[\\s\\S]|[^\\[\\]\\\\]){1,999}' + ')\\]' +
  '|(?:!?\\[(' + '(?:\\\\[\\s\\S]|[^\\[\\]\\\\]){1,999}' + ')\\](?:\\[\\])?))', 'g'
);
const BLOCKSKIP_RE = new RegExp(
  '\\[(?:[^\\[\\]`]|(?<a>`+)[^`]+\\k<a>(?!`))*?\\]\\((?:\\\\[\\s\\S]|[^\\\\\\(\\)]|\\((?:\\\\[\\s\\S]|[^\\\\\\(\\)])*\\))*\\)' +
  '|(?<!`)(?<b>`+)[^`]+\\k<b>(?!`)' +
  '|<(?! )[^<>]*?>', 'g'
);
const MASK_PUNCT_RE = /(`+)(?:[^`]|[^`][\s\S]*?[^`])\1(?!`)|`+|\\([\p{P}\p{S}])/gu;

// Does the link text contain an HTML tag or autolink that runs past the
// end of the text? Such a link is not a link at all.
function linkTextHasTag(full, text, offset, lx) {
  if (!text.includes('<')) return false;
  for (let i = 0; i < text.length; i++) {
    if (text[i] === '\\') { i++; continue; }
    if (text[i] === '`') {
      const m = INLINE.code.exec(text.slice(i));
      if (m) { i += m[0].length - 1; continue; }
    }
    if (text[i] !== '<') continue;
    const rest = full.slice(offset + i);
    const m = INLINE.tag.exec(rest) || INLINE.autolink.exec(rest);
    if (m) {
      if (m[0].length > text.length - i) return true;
      i += m[0].length - 1;
    }
  }
  return false;
}

function linkInText(src, links) {
  if (!src.includes('[')) return false;
  for (const m of src.matchAll(BLOCKSKIP_RE)) {
    if (LINK_RE.test(m[0]) && src.charAt(m.index - 1) !== '!') return true;
  }
  for (const m of src.matchAll(REFLINK_SEARCH_RE)) {
    const s = m[0];
    const r = s.lastIndexOf('[');
    if (!(s.charAt(0) === '!' || !Object.hasOwn(links, normLabel(s.slice(r + 1, -1)))) &&
        !(r > 1 && linkInText(s.slice(1, r - 1), links))) return true;
  }
  return false;
}

// Mask code spans, backslash escapes and link-like text in a copy of the
// inline source so the emphasis closer search cannot see delimiters that
// live inside them. Length is preserved, so indices still line up.
function maskForEm(src, links, hasLinks) {
  let t = src;
  if (hasLinks && src.includes('[') && src.includes(']')) {
    t = t.replace(REFLINK_SEARCH_RE, (m) => {
      const o = m.lastIndexOf('[');
      if (!Object.hasOwn(links, normLabel(m.slice(o + 1, -1)))) return m;
      if (o > 1 && m.charAt(0) !== '!') {
        const inner = m.slice(1, o - 1);
        if (linkInText(inner, links)) {
          return '[' + inner.replace(REFLINK_SEARCH_RE, (x) => {
            const p = x.lastIndexOf('[');
            return Object.hasOwn(links, normLabel(x.slice(p + 1, -1))) ? '[' + 'a'.repeat(x.length - 2) + ']' : x;
          }) + '][' + 'a'.repeat(m.length - o - 2) + ']';
        }
      }
      return '[' + 'a'.repeat(m.length - 2) + ']';
    });
  }
  if (src.includes('`') || src.includes('\\')) {
    t = t.replace(MASK_PUNCT_RE, (m, ticks, punct) => {
      if (punct) return '+'.repeat(m.length);
      if (ticks) return ticks + m.slice(ticks.length, -ticks.length).replace(/`/g, '+') + ticks;
      return m;
    });
  }
  if (src.includes('[') || src.includes('`') || src.includes('<')) {
    t = t.replace(BLOCKSKIP_RE, (m) => '[' + 'a'.repeat(m.length - 2) + ']');
  }
  return t;
}

function inlineTokensOf(lx, src) {
  const tokens = [];
  lexInline(lx, src, tokens);
  return tokens;
}

// Build a link or image token, lexing its text inline. Returns undefined
// when a link's text itself contains a link (the inner link wins).
function makeLink(m, ref, raw, lx) {
  const text = m[1].replace(/\\([\[\]])/g, '$1');
  const isImage = m[0].charAt(0) === '!';
  const saveInLink = lx.inLink, saveEmitted = lx.linkEmitted, saveRaw = lx.inRawBlock;
  lx.inLink = true;
  lx.linkEmitted = false;
  const tokens = inlineTokensOf(lx, text);
  const emittedInside = lx.linkEmitted;
  lx.linkEmitted = saveEmitted;
  lx.inLink = saveInLink;
  if (!isImage) {
    if (emittedInside) { lx.inRawBlock = saveRaw; return undefined; }
    lx.linkEmitted = true;
  }
  return { type: isImage ? 'image' : 'link', raw, href: ref.href, title: ref.title || null, text, tokens };
}

function lexInline(lx, src, tokens) {
  const saveParen = lx.linkParenPossible;
  lx.linkParenPossible = saveParen && src.includes(')');
  try {
    tokenizeInline(lx, src, tokens);
  } finally {
    lx.linkParenPossible = saveParen;
  }
}

function tokenizeInline(lx, src, tokens) {
  // The emphasis closer search needs a masked copy of the source, but only
  // when the text both contains an emphasis delimiter and contains something
  // worth masking (a code span, a link, a tag or an escape).
  const masked = (src.includes('*') || src.includes('_') || src.includes('~'))
    && (src.includes('`') || src.includes('[') || src.includes('<') || src.includes('\\'))
    ? maskForEm(src, lx.links, lx.hasLinks) : src;
  let prevChar = '';
  let prevWasText = false;
  let guard = Infinity;
  while (src) {
    if (src.length < guard) guard = src.length;
    else break;
    if (!prevWasText) prevChar = '';
    prevWasText = false;
    const c0 = src.charCodeAt(0);
    let tok;
    // Dispatch on the first character: most tokenizers can only match at
    // one specific opening character, so trying all of them on every chunk
    // is wasted work. The order below mirrors marked's tokenizer order.
    if (c0 === 92) { // backslash: escape, then hard break (\\\n), then text
      if ((tok = inlineEscape(src))) { src = src.slice(tok.raw.length); tokens.push(tok); continue; }
      if ((tok = inlineBr(src))) { src = src.slice(tok.raw.length); tokens.push(tok); continue; }
    } else if (c0 === 60) { // '<': tag, then autolink
      if ((tok = inlineTag(src, lx))) { src = src.slice(tok.raw.length); tokens.push(tok); continue; }
      if ((tok = inlineAutolink(src))) { src = src.slice(tok.raw.length); tokens.push(tok); continue; }
    } else if (c0 === 91 || (c0 === 33 && src.charCodeAt(1) === 91)) { // '[' or '![': link, then reflink
      if ((tok = inlineLink(src, lx))) { src = src.slice(tok.raw.length); tokens.push(tok); continue; }
      if ((tok = inlineReflink(src, lx))) {
        src = src.slice(tok.raw.length);
        const last = tokens.at(-1);
        if (tok.type === 'text' && last?.type === 'text') { last.raw += tok.raw; last.text += tok.text; }
        else tokens.push(tok);
        continue;
      }
    } else if (c0 === 42 || c0 === 95) { // '*' or '_': emphasis
      if ((tok = emStrong(src, masked, prevChar, lx))) { src = src.slice(tok.raw.length); tokens.push(tok); continue; }
    } else if (c0 === 96) { // '`': code span
      if ((tok = inlineCodespan(src))) { src = src.slice(tok.raw.length); tokens.push(tok); continue; }
    } else if (c0 === 126) { // '~': strikethrough
      if ((tok = inlineDel(src, masked, prevChar, lx))) { src = src.slice(tok.raw.length); tokens.push(tok); continue; }
    } else if (c0 === 32) { // space: hard break (two or more spaces + newline)
      if ((tok = inlineBr(src))) { src = src.slice(tok.raw.length); tokens.push(tok); continue; }
    } else if (!lx.inLink && mayBeUrl(src, c0)) {
      if ((tok = inlineUrl(src))) { src = src.slice(tok.raw.length); tokens.push(tok); continue; }
    }
    if ((tok = inlineText(src, lx))) {
      src = src.slice(tok.raw.length);
      if (tok.raw.slice(-1) !== '_') prevChar = tok.raw.slice(-1);
      prevWasText = true;
      const last = tokens.at(-1);
      if (last?.type === 'text') { last.raw += tok.raw; last.text += tok.text; }
      else tokens.push(tok);
      continue;
    }
    break; // unreachable in practice
  }
}

// Plain-text scanner: finds how far the inline text token extends, without
// a regex. It reproduces marked's text-token stop positions exactly:
//  - a run of backticks or tildes at the start is the first chunk, and the
//    token ends right after it when another backtick/tilde, two spaces plus
//    a newline, or an email-shaped word follows;
//  - the body stops before any character another tokenizer can claim
//    (\ < ! [ ` * ~ _), before a URL protocol or a www. start (with the
//    lookbehind marked requires), and before a hard break;
//  - a character that precedes an email word or a mailto:/xmpp: scheme is
//    included, then the token ends (so the URL tokenizer gets its turn).
// The URL and email checks use the same case rules as marked's URL regex:
// 'www.' and 'mailto:'/'xmpp:' are lowercase-only, protocols carry '://'.
const TEXT_STOP = new Uint8Array(128);
for (const c of [92, 60, 33, 91, 96, 42, 126, 95]) TEXT_STOP[c] = 1;
const EMAIL_CHARS = new Uint8Array(128);
for (const c of [46, 33, 35, 36, 37, 38, 39, 42, 43, 47, 61, 63, 95, 96, 123, 124, 125, 126, 45]) EMAIL_CHARS[c] = 1;

function isAlnumChar(c) {
  return (c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122);
}
function isEmailChar(c) {
  return (c < 128 && EMAIL_CHARS[c] === 1) || isAlnumChar(c);
}
// True when the substring at i is a run of email characters followed by
// '@' (the email-word lookahead of the text regex).
function emailWordAt(src, i) {
  let j = i;
  while (j < src.length && isEmailChar(src.charCodeAt(j))) j++;
  return j > i && src.charCodeAt(j) === 64;
}
// True when the substring at i is two or more spaces followed by '\n'.
function spacesNewlineAt(src, i) {
  let j = i;
  while (src.charCodeAt(j) === 32) j++;
  return j - i >= 2 && src.charCodeAt(j) === 10;
}
// True when a URL protocol (http(s):// or ftp://, any case) starts at i.
function protocolAt(src, i) {
  const c = src.charCodeAt(i);
  if (c === 104 || c === 72) {
    if (!ciAt(src, i + 1, 'ttp')) return false;
    let j = i + 4;
    if (src.charCodeAt(j) === 115 || src.charCodeAt(j) === 83) j++;
    return src.charCodeAt(j) === 58 && src.charCodeAt(j + 1) === 47 && src.charCodeAt(j + 2) === 47;
  }
  if (c === 102 || c === 70) {
    if (!ciAt(src, i + 1, 'tp')) return false;
    const j = i + 3;
    return src.charCodeAt(j) === 58 && src.charCodeAt(j + 1) === 47 && src.charCodeAt(j + 2) === 47;
  }
  return false;
}
// Case-insensitive match of a lowercase pattern at src[i].
function ciAt(src, i, pat) {
  for (let k = 0; k < pat.length; k++) {
    const c = src.charCodeAt(i + k);
    if (c !== pat.charCodeAt(k) && c !== pat.charCodeAt(k) - 32) return false;
  }
  return true;
}

function scanTextLen(src) {
  const n = src.length;
  if (n === 0) return 0;
  const c0 = src.charCodeAt(0);
  // A non-alphanumeric character immediately before mailto:/xmpp: is a
  // one-character token on its own.
  if (!isAlnumChar(c0) && (src.startsWith('mailto:', 1) || src.startsWith('xmpp:', 1))) return 1;
  // First chunk: a run of backticks, a run of tildes, or one other char.
  let p;
  if (c0 === 96 || c0 === 126) {
    p = 1;
    while (p < n && src.charCodeAt(p) === c0) p++;
  } else {
    p = 1;
  }
  // Whether any email can start in this string at all: without '@' the
  // email lookaheads can never fire, so skip all of them.
  const hasAt = src.includes('@');
  // Stops right after the first chunk.
  if (p < n) {
    const cp = src.charCodeAt(p);
    if (cp === 96 || cp === 126) return p;
    if (spacesNewlineAt(src, p)) return p;
    if (hasAt && emailWordAt(src, p)) return p;
  }
  // Body. The checks are split by character class so the common cases
  // (letters, digits, spaces) do the least work: a stop can only fire at
  // a character of the right class.
  while (p < n) {
    const c = src.charCodeAt(p);
    if ((c >= 97 && c <= 122) || (c >= 65 && c <= 90) || (c >= 48 && c <= 57)) {
      // Alphanumeric: only a protocol, a www. start or a hard break can
      // stop the token here.
      if ((c === 104 || c === 72 || c === 102 || c === 70)
        && (src.charCodeAt(p + 1) === 116 || src.charCodeAt(p + 1) === 84)) {
        if (protocolAt(src, p)) return p;
      } else if (c === 119 && src.startsWith('www.', p) && /[\s*_~(]/.test(src[p - 1])) {
        return p;
      }
      if (src.charCodeAt(p + 1) === 32 && src.charCodeAt(p + 2) === 32 && spacesNewlineAt(src, p + 1)) return p + 1;
      p++;
      continue;
    }
    if (c === 32) {
      // Space: only a following mailto: scheme or email word can stop it.
      if (hasAt && emailWordAt(src, p + 1)) return p + 1;
      const n1 = src.charCodeAt(p + 1);
      if ((n1 === 109 || n1 === 120) && (src.startsWith('mailto:', p + 1) || src.startsWith('xmpp:', p + 1))) return p + 1;
      p++;
      continue;
    }
    if (c < 128 && TEXT_STOP[c] === 1) return p;
    if (src.charCodeAt(p + 1) === 32 && src.charCodeAt(p + 2) === 32 && spacesNewlineAt(src, p + 1)) return p + 1;
    if (!isAlnumChar(c)) {
      const n1 = src.charCodeAt(p + 1);
      if ((n1 === 109 || n1 === 120) && (src.startsWith('mailto:', p + 1) || src.startsWith('xmpp:', p + 1))) return p + 1;
      if (hasAt && !isEmailChar(c) && emailWordAt(src, p + 1)) return p + 1;
    }
    p++;
  }
  return n;
}

function inlineText(src, lx) {
  const len = scanTextLen(src);
  if (len === 0) return undefined;
  const raw = src.slice(0, len);
  const inRaw = lx.inRawBlock;
  return { type: 'text', raw, text: inRaw ? raw : decodeRefs(raw), escaped: inRaw };
}

// Cheap pre-check for the extended-autolink tokenizer: a URL or email can
// only start with www. / http / ftp / mailto / xmpp, or with a word that
// contains '@' before any space, '<' or newline.
function mayBeUrl(src, c0) {
  if (c0 === 119 || c0 === 87 || c0 === 104 || c0 === 72 || c0 === 102 || c0 === 70
    || c0 === 109 || c0 === 77 || c0 === 120 || c0 === 88) return true;
  let i = 0;
  while (i < src.length) {
    const ch = src.charCodeAt(i);
    if (ch === 64) return true; // '@'
    if (ch === 32 || ch === 10 || ch === 60 || ch === 9) return false;
    i++;
  }
  return false;
}

function inlineEscape(src) {
  const m = INLINE.escape.exec(src);
  return m ? { type: 'escape', raw: m[0], text: m[1] } : undefined;
}

function inlineTag(src, lx) {
  const m = INLINE.tag.exec(src);
  if (!m) return undefined;
  if (!lx.inLink && /^<a /i.test(m[0])) lx.inLink = true;
  else if (lx.inLink && /^<\/a>/i.test(m[0])) lx.inLink = false;
  if (!lx.inRawBlock && /^<(pre|code|kbd|script)(\s|>)/i.test(m[0])) lx.inRawBlock = true;
  else if (lx.inRawBlock && /^<\/(pre|code|kbd|script)(\s|>)/i.test(m[0])) lx.inRawBlock = false;
  return { type: 'html', raw: m[0], inLink: lx.inLink, inRawBlock: lx.inRawBlock, block: false, text: m[0] };
}

function inlineLink(src, lx) {
  if (lx.linkParenPossible === false) return undefined;
  const m = LINK_RE.exec(src);
  if (!m) return undefined;
  const bang = m[0].charAt(0) === '!' ? 2 : 1;
  if (linkTextHasTag(src, m[1], bang, lx)) return undefined;
  let href = m[2].trim();
  if (href.charAt(0) === '<') {
    if (href.charAt(href.length - 1) !== '>') return undefined;
    const stripped = stripTail(href.slice(0, -1), '\\');
    if ((href.length - stripped.length) % 2 === 0) return undefined;
  } else {
    const bal = findBalanced(m[2], '(', ')');
    if (bal === -2) return undefined;
    if (bal > -1) {
      const cut = (m[0].charAt(0) === '!' ? 5 : 4) + m[1].length + bal;
      m[2] = m[2].substring(0, bal);
      m[0] = m[0].substring(0, cut).trim();
      m[3] = '';
      href = m[2].trim();
    }
  }
  const tail = stripTail(m[0].slice(0, -1), '\\');
  if ((m[0].length - tail.length) % 2 === 0) return undefined;
  let title = m[3] ? m[3].slice(1, -1) : '';
  href = href.trim();
  if (href.charAt(0) === '<') href = href.slice(1, -1);
  return makeLink(m, { href: href && unescapePunct(href), title: title && unescapePunct(title) }, m[0], lx);
}

function inlineReflink(src, lx) {
  let m = REFLINK_RE.exec(src) || NOLINK_RE.exec(src);
  if (!m) return undefined;
  const bang = m[0].charAt(0) === '!' ? 2 : 1;
  if (linkTextHasTag(src, m[1], bang, lx)) return undefined;
  const ref = lx.links[normLabel(m[2] || m[1])];
  if (!ref) return { type: 'text', raw: m[0].charAt(0), text: m[0].charAt(0) };
  return makeLink(m, ref, m[0], lx);
}

function emStrong(src, masked, prev, lx) {
  const m = INLINE.emLDelim.exec(src);
  if (!m || (!m[1] && !m[2] && !m[3] && !m[4])) return undefined;
  const delim = m[0][0];
  const sameDelim = prev === delim;
  const cur = masked.length - src.length;
  let runStart = cur;
  while (runStart > 0 && masked[runStart - 1] === delim) runStart--;
  const beforeRun = runStart > 0 ? masked[runStart - 1] : '';
  const beforeIsPunct = beforeRun === '*' || beforeRun === '_' || IS_PUNCT.test(beforeRun);
  let prevCh = prev;
  if (runStart < cur) prevCh = beforeRun;
  const prevIsPunct = runStart < cur ? beforeIsPunct : IS_PUNCT.test(prevCh);
  if (m[4] && ALNUM.test(prevCh)) return undefined;
  const afterPunct = m[1] || m[3] || '';
  if (!afterPunct || !prevCh || prevIsPunct) {
    const k = [...m[0]].length - 1;
    let remaining = k;
    let extra = 0;
    const total = cur - runStart + k;
    const canOpenAsCloser = !!beforeRun.trim() && (!!afterPunct || (delim === '*' && !beforeIsPunct));
    if (delim !== '*' && delim !== '_') return undefined;
    const rdelim = delim === '*' ? INLINE.emRDelimAst : INLINE.emRDelimUnd;
    // No closer delimiter at all in the rest of the string: the regex
    // search below would scan to the end and fail, so skip it.
    if (masked.indexOf(delim, cur + k) === -1) return undefined;
    const hay = masked.slice(cur + k);
    rdelim.lastIndex = 0;
    let match;
    while ((match = rdelim.exec(hay)) !== null) {
      const g = match[1] || match[2] || match[3] || match[4] || match[5] || match[6];
      if (!g) continue;
      const b = [...g].length;
      if (match[3] || match[4]) { remaining += b; continue; }
      else if (match[5] || match[6] || canOpenAsCloser) {
        if (sameDelim && (match[5] || match[6])) break;
        if (total % 3 && !((total + b) % 3)) { extra += b; continue; }
      }
      remaining -= b;
      if (remaining > 0) continue;
      const take = Math.min(b, b + remaining + extra);
      const firstLen = [...match[0]][0].length;
      const raw = src.slice(0, k + match.index + firstLen + take);
      if (Math.min(k, take) % 2) {
        const inner = raw.slice(1, -1);
        return { type: 'em', raw, text: inner, tokens: inlineTokensOf(lx, inner) };
      }
      const inner = raw.slice(2, -2);
      return { type: 'strong', raw, text: inner, tokens: inlineTokensOf(lx, inner) };
    }
  }
  return undefined;
}

function inlineCodespan(src) {
  const m = INLINE.code.exec(src);
  if (!m) return undefined;
  let text = m[2].replace(/\n/g, ' ');
  const hasNonSpace = /[^ ]/.test(text);
  const wrapped = text.charAt(0) === ' ' && text.charAt(text.length - 1) === ' ';
  if (hasNonSpace && wrapped) text = text.substring(1, text.length - 1);
  return { type: 'codespan', raw: m[0], text };
}

function inlineBr(src) {
  const m = INLINE.br.exec(src);
  return m ? { type: 'br', raw: m[0] } : undefined;
}

function inlineDel(src, masked, prev, lx) {
  const m = INLINE.delLDelim.exec(src);
  if (!m) return undefined;
  if (!m[2] && prev && !IS_PUNCT.test(prev)) return undefined;
  const runLen = [...m[1]].length;
  let remaining = runLen;
  const cur = masked.length - src.length;
  // No '~' at all in the rest of the string: no closer can exist.
  if (masked.indexOf('~', cur + runLen) === -1) return undefined;
  const hay = masked.slice(cur + runLen);
  const rdelim = INLINE.delRDelim;
  rdelim.lastIndex = 0;
  let match;
  while ((match = rdelim.exec(hay)) !== null) {
    const g = match[1] || match[2] || match[3] || match[4] || match[5] || match[6];
    if (!g) continue;
    const b = [...g].length;
    if (b !== runLen) continue;
    if (match[3] || match[4]) { remaining += b; continue; }
    remaining -= b;
    if (remaining > 0) continue;
    const take = Math.min(b, b + remaining);
    const firstLen = [...match[0]][0].length;
    const raw = src.slice(0, runLen + match.index + firstLen + take);
    const inner = raw.slice(runLen, -runLen);
    return { type: 'del', raw, text: inner, tokens: inlineTokensOf(lx, inner) };
  }
  return undefined;
}

function inlineAutolink(src) {
  const m = INLINE.autolink.exec(src);
  if (!m) return undefined;
  let text, href;
  if (m[2] === '@') { text = m[1]; href = 'mailto:' + text; }
  else { text = m[1]; href = text; }
  return { type: 'link', raw: m[0], text, href, autolink: true, tokens: [{ type: 'text', raw: text, text }] };
}

function inlineUrl(src) {
  const m = INLINE.url.exec(src);
  if (!m) return undefined;
  let text, href;
  if (m[2] === '@') { text = m[0]; href = 'mailto:' + text; }
  else {
    let raw = m[0];
    let prev;
    do { prev = raw; raw = INLINE.backpedal.exec(raw)?.[0] ?? ''; } while (raw !== prev);
    text = raw;
    href = m[1] === 'www.' ? 'http://' + raw : raw;
  }
  return { type: 'link', raw: text, text, href, autolink: true, tokens: [{ type: 'text', raw: text, text }] };
}

// ---- renderer -------------------------------------------------------------
// Walks the token tree and builds the HTML string.

function renderTokens(lx, tokens) {
  let out = '';
  for (const tok of tokens) out += renderToken(lx, tok);
  return out;
}

function renderToken(lx, tok) {
  switch (tok.type) {
    case 'space': return '';
    case 'hr': return '<hr>\n';
    case 'heading': return `<h${tok.depth}>${renderInline(lx, tok.tokens)}</h${tok.depth}>\n`;
    case 'code': {
      const lang = (tok.lang || '').match(/^\S*/)?.[0] || '';
      const text = tok.text ? tok.text.replace(/\n$/, '') + '\n' : '';
      const body = esc(text, true);
      return lang
        ? `<pre><code class="language-${esc(lang)}">${body}</code></pre>\n`
        : `<pre><code>${body}</code></pre>\n`;
    }
    case 'table': {
      let head = '';
      for (const cell of tok.header) head += renderTableCell(lx, cell);
      let out = `<table>\n<thead>\n<tr>\n${head}</tr>\n</thead>\n`;
      if (tok.rows.length > 0) {
        let body = '';
        for (const row of tok.rows) {
          let cells = '';
          for (const cell of row) cells += renderTableCell(lx, cell);
          body += `<tr>\n${cells}</tr>\n`;
        }
        out += `<tbody>${body}</tbody>`;
      }
      return out + '</table>\n';
    }
    case 'blockquote': return `<blockquote>\n${renderTokens(lx, tok.tokens)}</blockquote>\n`;
    case 'list': {
      let items = '';
      for (const item of tok.items) items += renderListItem(lx, item);
      const tag = tok.ordered ? 'ol' : 'ul';
      const start = tok.ordered && tok.start !== 1 ? ` start="${tok.start}"` : '';
      return `<${tag}${start}>\n${items}</${tag}>\n`;
    }
    case 'checkbox': return `<input ${tok.checked ? 'checked="" ' : ''}disabled="" type="checkbox"> `;
    case 'html': return tok.text;
    case 'def': return '';
    case 'paragraph': return `<p>${renderInline(lx, tok.tokens)}</p>\n`;
    case 'text': return renderInline(lx, tok.tokens);
    default: return '';
  }
}

function renderListItem(lx, item) {
  return `<li>${renderTokens(lx, item.tokens)}</li>\n`;
}

function renderTableCell(lx, cell) {
  const tag = cell.header ? 'th' : 'td';
  const align = cell.align ? ` align="${cell.align}"` : '';
  return `<${tag}${align}>${renderInline(lx, cell.tokens)}</${tag}>\n`;
}

function renderInline(lx, tokens, textOnly) {
  let out = '';
  for (const tok of tokens) out += renderInlineToken(lx, tok, textOnly);
  return out;
}

function renderInlineToken(lx, tok, textOnly) {
  switch (tok.type) {
    case 'escape': return textOnly ? tok.text : esc(tok.text);
    case 'html': return tok.text;
    case 'link': {
      if (textOnly) return renderInline(lx, tok.tokens, true);
      const inner = tok.autolink ? esc(tok.text, true) : renderInline(lx, tok.tokens);
      const href = cleanUrl(tok.href);
      if (href === null) return inner;
      let out = `<a href="${esc(href, tok.autolink)}"`;
      if (tok.title) out += ` title="${esc(tok.title)}"`;
      return out + `>${inner}</a>`;
    }
    case 'image': {
      if (textOnly) return renderInline(lx, tok.tokens, true);
      const alt = renderInline(lx, tok.tokens, true);
      const href = cleanUrl(tok.href);
      if (href === null) return esc(alt);
      let out = `<img src="${esc(href)}" alt="${esc(alt)}"`;
      if (tok.title) out += ` title="${esc(tok.title)}"`;
      return out + '>';
    }
    case 'checkbox': return `<input ${tok.checked ? 'checked="" ' : ''}disabled="" type="checkbox"> `;
    case 'strong': return textOnly ? renderInline(lx, tok.tokens, true) : `<strong>${renderInline(lx, tok.tokens)}</strong>`;
    case 'em': return textOnly ? renderInline(lx, tok.tokens, true) : `<em>${renderInline(lx, tok.tokens)}</em>`;
    case 'codespan': return textOnly ? tok.text : `<code>${esc(tok.text, true)}</code>`;
    case 'br': return textOnly ? '' : '<br>';
    case 'del': return textOnly ? renderInline(lx, tok.tokens, true) : `<del>${renderInline(lx, tok.tokens)}</del>`;
    case 'text':
      if (textOnly) return tok.text;
      if ('tokens' in tok && tok.tokens) return renderInline(lx, tok.tokens);
      return tok.escaped ? tok.text : esc(tok.text);
    default: return '';
  }
}

// ---- entry point ----------------------------------------------------------

export function parse(markdown) {
  const lx = new BlockLexer();
  const tokens = lx.lex(markdown);
  return renderTokens(lx, tokens);
}
