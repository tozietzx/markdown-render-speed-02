// parse.js — a fast drop-in for marked 18.1.3 (GFM, default options).
//
// parse(markdown) returns exactly the HTML that marked 18.1.3's
// marked.parse(markdown) returns with its defaults (gfm true, breaks false,
// pedantic false, async false), for every string.
//
// The matching rules are marked's own: the block and inline patterns are the
// ones marked 18.1.3 compiles for its GFM rule set (see the RB / RI tables
// below), and the tokenizing order and state machine follow marked's Lexer
// and Tokenizer. Credit: marked (https://github.com/markedjs/marked, MIT);
// the matching patterns and the algorithm they drive are derived from it.
// This file is a fresh implementation, not a copy of marked's source: it
// restructures the work for speed instead of carrying marked's token trees.
//
// Where the speed comes from, without changing any output:
//   - The block lexer dispatches on the first characters of the remaining
//     source, so a paragraph never pays for the fences / heading / hr /
//     blockquote / list / html / definition regexes that cannot match it.
//   - Inline content is rendered straight to HTML during the render phase
//     instead of being built into token objects and walked a second time.
//     Link reference definitions are still collected first (two phases, as
//     in marked), so a reference defined later in the document still works.
//   - The emphasis mask (the masked copy of an inline source that marked
//     builds eagerly for every inline run containing * _ or ~) is built
//     lazily, only when an emphasis or strikethrough match is attempted.
//   - No per-call allocation of a Lexer / Tokenizer / Parser object graph:
//     one small state object per parse() call, plain objects for blocks.
//
// No input is ever recognised by table or hash: every output is computed
// from the markdown given. No caching across calls; parse() keeps nothing
// from an earlier call.

/* ---------- "other" patterns: the small shared regexes ---------- */
const codeRemoveIndent = /^(?: {0,3}\t| {1,4})/gm;
const outputLinkReplace = /\\([\[\]])/g;
const indentCodeCompensation = /^(\s+)(?:```)/;
const beginningSpace = /^\s+/;
const endingHash = /#$/;
const startingSpaceChar = /^ /;
const endingSpaceChar = / $/;
const endingSpaceTabChar = /[ \t]$/;
const nonSpaceChar = /[^ ]/;
const newLineCharGlobal = /\n/g;
const tabCharGlobal = /\t/g;
const leadingSpaceTab = /^[ \t]+/;
const multipleSpaceGlobal = /\s+/g;
const blankLine = /^[ \t]*$/;
const doubleBlankLine = /\n[ \t]*\n[ \t]*$/;
const blockquoteStart = /^ {0,3}>/;
const blockquoteSetextReplace = /\n {0,3}((?:=+|-+)[ \t]*)(?=\n|$)/g;
const blockquoteSetextReplace2 = /^ {0,3}>[ \t]?/gm;
const blockquoteMarkerWhitespace = /^( {0,3}>)([ \t]+)/gm;
const listReplaceNesting = /^ {1,4}(?=( {4})*[^ ])/g;
const listIsTask = /^\[[ xX]\][ \t]+\S/;
const listReplaceTask = /^\[[ xX]\][ \t]+/;
const listTaskCheckbox = /\[[ xX]\]/;
const anyLine = /\n.*\n/;
const hrefBrackets = /^<(.*)>$/;
const tableDelimiter = /[:|]/;
const tableAlignChars = /^\||\| *$/g;
const tableRowBlankLine = /\n[ \t]*$/;
const tableAlignRight = /^ *-+: *$/;
const tableAlignCenter = /^ *:-+: *$/;
const tableAlignLeft = /^ *:-+ *$/;
const startATag = /^<a /i;
const endATag = /^<\/a>/i;
const startPreScriptTag = /^<(pre|code|kbd|script)(\s|>)/i;
const endPreScriptTag = /^<\/(pre|code|kbd|script)(\s|>)/i;
const startAngleBracket = /^</;
const endAngleBracket = />$/;
const unicodeAlphaNumeric = /[\p{L}\p{N}]/u;
const numericCharacterReference = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));/;
const numericCharacterReferenceOrAmpersand = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;
const escapeTest = /[&<>"']/;
const escapeReplace = /[&<>"']/g;
const escapeTestNoEncode = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/;
const escapeReplaceNoEncode = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;
const percentDecode = /%25/g;
const findPipe = /\|/g;
const splitPipe = / \|/;
const slashPipe = /\\\|/g;
const carriageReturn = /\r\n|\r/g;
const spaceLine = /^ +$/gm;
const notSpaceStart = /^\S*/;
const endingNewline = /\n$/;

const BLOCK_TAGS = 'address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul';

/** Memoised builders for the indent-dependent block patterns (indent clamped to 0..3). */
function memoRegex(build) {
  const cache = [];
  return (indent) => {
    const n = Math.max(0, Math.min(3, indent - 1));
    return cache[n] || (cache[n] = build(n));
  };
}
const listItemRegex = (indent) => new RegExp(`^( {0,3}${indent})((?:[ \t][^\n]*)?(?:\n|$))`);
const nextBulletRegex = memoRegex((n) => new RegExp(`^ {0,${n}}(?:[*+-]|\\d{1,9}[.)])((?:[ \t][^\n]*)?(?:\\n|$))`));
const hrRegex = memoRegex((n) => new RegExp(`^ {0,${n}}((?:-[ \t]*){3,}|(?:_[ \t]*){3,}|(?:\\*[ \t]*){3,})(?:\\n+|$)`));
const fencesBeginRegex = memoRegex((n) => new RegExp(`^ {0,${n}}(?:\`\`\`|~~~)`));
const headingBeginRegex = memoRegex((n) => new RegExp(`^ {0,${n}}#{1,6}(?:\\s|$)`));
const htmlBeginRegex = memoRegex((n) => new RegExp(`^ {0,${n}}(?:</?(?:${BLOCK_TAGS})(?: +|$|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)`, 'i'));
const blockquoteBeginRegex = memoRegex((n) => new RegExp(`^ {0,${n}}>`));

/* ---------- small helpers ---------- */
const ESCAPES = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };
const escapeChar = (c) => ESCAPES[c];
/** marked's escape: with encode=true every & < > " ' is encoded; otherwise a & that already starts a valid entity or numeric reference is left alone. */
function esc(s, encode) {
  if (encode) {
    if (escapeTest.test(s)) return s.replace(escapeReplace, escapeChar);
  } else if (escapeTestNoEncode.test(s)) {
    return s.replace(escapeReplaceNoEncode, escapeChar);
  }
  return s;
}
/** Decode numeric character references (and leave a bare & alone as &amp;). */
function unescapeEntities(s) {
  if (!numericCharacterReference.test(s)) return s;
  return s.replace(numericCharacterReferenceOrAmpersand, (whole, dec, hex) => {
    if (dec === undefined && hex === undefined) return '&amp;';
    const code = dec === undefined ? parseInt(hex, 16) : parseInt(dec, 10);
    if (code === 0 || code > 1114111 || (code >= 55296 && code <= 57343)) return '\uFFFD';
    if (code === 38) return '&amp;';
    return String.fromCodePoint(code);
  });
}
/** encodeURI a link href, keeping %25 as %; null when it cannot be encoded. */
function encodeHref(href) {
  try {
    const e = encodeURI(href);
    return e.includes('%25') ? e.replace(percentDecode, '%') : e;
  } catch {
    return null;
  }
}
/** Split a table row on unescaped pipes, trimming cells and honouring the column count. */
function splitTableRow(row, count) {
  const cells = row.replace(findPipe, (m, off, str) => {
    let escaped = false;
    for (let p = off - 1; p >= 0 && str[p] === '\\'; p--) escaped = !escaped;
    return escaped ? '|' : ' |';
  }).split(splitPipe);
  let i = 0;
  if (cells[0].trim() || cells.shift(), cells.length > 0 && !cells.at(-1)?.trim()) cells.pop();
  if (count) {
    if (cells.length > count) cells.splice(count);
    else while (cells.length < count) cells.push('');
  }
  for (; i < cells.length; i++) cells[i] = cells[i].trim().replace(slashPipe, '|');
  return cells;
}
/** Trim trailing copies of ch from s (or, with invert, trailing chars that are not ch). */
function trimEndChar(s, ch, invert) {
  const n = s.length;
  if (n === 0) return '';
  let cut = 0;
  for (; cut < n;) {
    const c = s.charAt(n - cut - 1);
    if (c === ch && !invert) cut++;
    else if (c !== ch && invert) cut++;
    else break;
  }
  return s.slice(0, n - cut);
}
/** Drop trailing blank lines when there are more than two of them. */
function trimTrailingBlanks(s) {
  const lines = s.split('\n');
  let t = lines.length - 1;
  for (; t >= 0 && blankLine.test(lines[t]);) t--;
  return lines.length - t <= 2 ? s : lines.slice(0, t + 1).join('\n');
}
/** Normalise a link reference label for lookup. */
function normalizeLabel(label) {
  return label.trim().replace(multipleSpaceGlobal, ' ').toLowerCase().toUpperCase().toLowerCase();
}
/** Find the index of the unmatched closing paren in s (parens are the two chars of pair); -2 when an opening paren is never closed, -1 when there are no parens at all. */
function findParenClose(s, pair) {
  if (s.indexOf(pair[0]) === -1 && s.indexOf(pair[1]) === -1) return -1;
  let depth = 0;
  for (let i = 0; i < s.length; i++) {
    if (s[i] === '\\') { i++; continue; }
    if (s[i] === pair[0]) depth++;
    else if (s[i] === pair[1] && (--depth, depth < 0)) return i;
  }
  return depth > 0 ? -2 : -1;
}
/** Expand tabs to spaces, to the next multiple of 4 columns from column offset. */
function expandTabs(s, offset = 0) {
  let col = offset;
  let out = '';
  for (const ch of s) {
    if (ch === '\t') {
      const n = 4 - (col % 4);
      out += ' '.repeat(n);
      col += n;
    } else {
      out += ch;
      col++;
    }
  }
  return out;
}
/** Remove the fence's opening-line indent from each line of fenced code. */
function fenceIndentComp(raw, code) {
  const m = raw.match(indentCodeCompensation);
  if (m === null) return code;
  const indent = m[1];
  return code.split('\n').map((line) => {
    const lead = line.match(beginningSpace);
    if (lead === null) return line;
    return line.slice(Math.min(lead[0].length, indent.length));
  }).join('\n');
}
/** Scan a masked inline source for the last emphasis / strikethrough closer positions. */
function scanMask(src) {
  const em = { '*': -1, _: -1 };
  let del = -1;
  const n = src.length;
  for (let i = 0; i < n; i++) {
    const ch = src[i];
    if (ch !== '*' && ch !== '_' && ch !== '~') continue;
    const prev = i === 0 ? '\n' : src[i - 1];
    let j = i + 1;
    for (; j < n && src[j] === ch;) j++;
    if (prev !== ' ' && prev !== '\t' && prev !== '\n' && prev !== '\r' && prev !== '\f') {
      if (ch === '~') del = i;
      else em[ch] = i;
    }
    i = j - 1;
  }
  return { maskedSrc: src, lastPossibleEmStrongCloserIndex: em, lastPossibleDelCloserIndex: del };
}
// Block and inline patterns, exactly as marked 18.1.3 compiles them for its GFM
// rule set (dumped from the vendored marked.esm.js via its exported Lexer.rules).
const RB = {
  newline: new RegExp("^(?:[ \\t]*(?:\\n|$))+", ""),
  code: new RegExp("^((?: {4}| {0,3}\\t)[^\\n]+(?:\\n(?:[ \\t]*(?:\\n|$))*)?)+", ""),
  fences: new RegExp("^ {0,3}(`{3,}(?=[^`\\n]*(?:\\n|$))|~{3,})([^\\n]*)(?:\\n|$)(?:|([\\s\\S]*?)(?:\\n|$))(?: {0,3}(?:(?=`)\\1`*|(?=~)\\1~*) *(?=\\n|$)|$)", ""),
  hr: new RegExp("^ {0,3}((?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)", ""),
  heading: new RegExp("^ {0,3}(#{1,6})(?=\\s|$)(.*)(?:\\n+|$)", ""),
  html: new RegExp("^ {0,3}(?:<(script|pre|style|textarea)[\\s>][\\s\\S]*?(?:<\\/\\1>[^\\n]*\\n*|$)|<!--(?:-?>|[\\s\\S]*?(?:-->|$))[^\\n]*(\\n+|$)|<\\?[\\s\\S]*?(?:\\?>[^\\n]*\\n*|$)|<![A-Z][\\s\\S]*?(?:>[^\\n]*\\n*|$)|<!\\[CDATA\\[[\\s\\S]*?(?:\\]\\]>[^\\n]*\\n*|$)|<\\/?(address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?:[ \\t]+|\\n|\\/?>|$)[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$)|<(?!(?:script|pre|style|textarea)(?![a-z0-9-]))([a-z][a-z0-9-]*)(?: +[a-zA-Z:_][\\w.:-]*(?: *= *\"[^\"\\n]*\"| *= *'[^'\\n]*'| *= *[^\\s\"'=<>`]+)?)*? *\\/?>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$)|<\\/[a-z][a-z0-9-]*\\s*>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$))", "i"),
  def: new RegExp("^ {0,3}\\[((?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\\\n]|\\n(?![ \\t]*\\n))+)\\]: *(?:\\n[ \\t]*)?([^<\\s][^\\s]*|<.*?>)(?:(?: +(?:\\n[ \\t]*)?| *\\n[ \\t]*)((?:\"(?:\\\\[\\s\\S]|[^\"\\\\])*\"|'(?:\\\\[\\s\\S]|[^'\\\\\\n]|\\n(?!\\n))*'|\\((?:\\\\[\\s\\S]|[^()\\\\])*\\))))? *(?:\\n+|$)", ""),
  table: new RegExp("^ *([^\\n ].*)\\n {0,3}((?:\\| *)?:?-+:? *(?:\\| *:?-+:? *)*(?:\\| *)?)(?:\\n((?:(?! *\\n| {0,3}((?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)| {0,3}#{1,6}(?:\\s|$)| {0,3}>|(?: {4}| {0,3}\t)[^\\n]| {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)| {0,3}(?:[*+-]|1[.)])[ \\t]| {0,3}(?:<\\/?(?:address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?: +|\\n|\\/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)).*(?:\\n|$))*)\\n*|$)", ""),
  lheading: new RegExp("^(?! {0,3}(?:[*+-]|\\d{1,9}[.)]) |(?: {4}| {0,3}\\t)| {0,3}(?:`{3,}|~{3,})| {0,3}>| {0,3}#{1,6}(?:\\s|$)| {0,3}<[^\\n>]+>\\n| {0,3}\\|?(?:[:\\- ]*\\|)+[\\:\\- ]*\\n)((?:.|\\n(?!\\s*?\\n| {0,3}(?:[*+-]|\\d{1,9}[.)]) | {0,3}(?:`{3,}|~{3,})| {0,3}>| {0,3}#{1,6}(?:\\s|$)| {0,3}(?:(?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)| {0,3}<[^\\n>]+>\\n| {0,3}\\|?(?:[:\\- ]*\\|)+[\\:\\- ]*\\n))+?)\\n {0,3}(=+|-+)[ \\t]*(?:\\n+|$)", ""),
  list: new RegExp("^( {0,3}(?:[*+-]|\\d{1,9}[.)]))([ \\t][^\\n]*?)?(?:\\n|$)", ""),
  paragraph: new RegExp("^([^\\n]+(?:\\n(?! {0,3}((?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)| {0,3}#{1,6}(?:\\s|$)| {0,3}>| {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)| {0,3}(?:[*+-]|1[.)])[ \\t]+[^ \\t\\n]| {0,3}(?:<\\/?(?:address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?: +|\\n|\\/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)| *([^\\n ].*)\\n {0,3}((?:\\| *)?:?-+:? *(?:\\| *:?-+:? *)*(?:\\| *)?)(?:\\n((?:(?! *\\n| {0,3}((?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)| {0,3}#{1,6}(?:\\s|$)| {0,3}>|(?: {4}| {0,3}\t)[^\\n]| {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)| {0,3}(?:[*+-]|1[.)])[ \\t]| {0,3}(?:<\\/?(?:address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?: +|\\n|\\/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)).*(?:\\n|$))*)\\n*|$)|[ \\t]+\\n)[^\\n]+)*)", ""),
  text: new RegExp("^[^\\n]+", ""),
  blockquote: new RegExp("^( {0,3}> ?(?:(?![ \\t]*(?:\\n|$))(([^\\n]+(?:\\n(?! {0,3}((?:-[\\t ]*){3,}|(?:_[ \\t]*){3,}|(?:\\*[ \\t]*){3,})(?:\\n+|$)| {0,3}#{1,6}(?:\\s|$)| {0,3}>| {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)| {0,3}(?:[*+-]|\\d{1,9}[.)])(?:[ \\t]|\\n|$)| {0,3}(?:<\\/?(?:address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul)(?: +|\\n|\\/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)|[ \\t]+\\n)[^\\n]+)*))|[^\\n]*)(?:\\n|$))+", ""),
};
const RI = {
  escape: new RegExp("^\\\\([!\"#$%&'()*+,\\-./:;<=>?@\\[\\]\\\\^_`{|}~])", ""),
  code: new RegExp("^(`+)([^`]|[^`][\\s\\S]*?[^`])\\1(?!`)", ""),
  br: new RegExp("^( {2,}|\\\\)\\n(?!\\s*$)[ \\t]*", ""),
  text: new RegExp("^(?:[^a-zA-Z0-9](?=(?:mailto|xmpp):)|(`+|~+|[^`~])(?:(?=[`~])|(?= {2,}\\n)|(?=[a-zA-Z0-9.!#$%&'*+\\/=?_`{\\|}~-]+@)|[\\s\\S]*?(?:(?=[\\\\<!\\[`*~_]|\\b_|[hH][tT][tT][pP][sS]?|[fF][tT][pP]:\\/\\/|(?<![^\\s*_~(])www\\.|$)|[^ ](?= {2,}\\n)|[^a-zA-Z0-9](?=(?:mailto|xmpp):)|[^a-zA-Z0-9.!#$%&'*+\\/=?_`{\\|}~-](?=[a-zA-Z0-9.!#$%&'*+\\/=?_`{\\|}~-]+@))))", ""),
  emStrongLDelim: new RegExp("^(?:\\*+(?:((?!\\*)(?!~)[\\p{P}\\p{S}])|([^\\s*]))?)|^_+(?:((?!_)(?!~)[\\p{P}\\p{S}])|([^\\s_]))?", "u"),
  emStrongRDelimAst: new RegExp("^[^_*]*?__[^_*]*?\\*[^_*]*?(?=__)|[^*]+(?=[^*])|(?!\\*)(?!~)[\\p{P}\\p{S}](\\*+)(?=[\\s]|$)|(?:[^\\s\\p{P}\\p{S}]|~)(\\*+)(?!\\*)(?=(?!~)[\\s\\p{P}\\p{S}]|$)|(?!\\*)(?!~)[\\s\\p{P}\\p{S}](\\*+)(?=(?:[^\\s\\p{P}\\p{S}]|~))|[\\s](\\*+)(?!\\*)(?=(?!~)[\\p{P}\\p{S}])|(?!\\*)(?!~)[\\p{P}\\p{S}](\\*+)(?!\\*)(?=(?!~)[\\p{P}\\p{S}])|(?:[^\\s\\p{P}\\p{S}]|~)(\\*+)(?=(?:[^\\s\\p{P}\\p{S}]|~))", "gu"),
  emStrongRDelimUnd: new RegExp("^[^_*]*?\\*\\*[^_*]*?_[^_*]*?(?=\\*\\*)|[^_]+(?=[^_])|(?!_)[\\p{P}\\p{S}](_+)(?=[\\s]|$)|[^\\s\\p{P}\\p{S}](_+)(?!_)(?=[\\s\\p{P}\\p{S}]|$)|(?!_)[\\s\\p{P}\\p{S}](_+)(?=[^\\s\\p{P}\\p{S}])|[\\s](_+)(?!_)(?=[\\p{P}\\p{S}])|(?!_)[\\p{P}\\p{S}](_+)(?!_)(?=[\\p{P}\\p{S}])", "gu"),
  delLDelim: new RegExp("^~~?(?:((?!~)[\\p{P}\\p{S}])|[^\\s~])", "u"),
  delRDelim: new RegExp("^[^~]+(?=[^~])|(?!~)[\\p{P}\\p{S}](~~?)(?=[\\s]|$)|[^\\s\\p{P}\\p{S}](~~?)(?!~)(?=[\\s\\p{P}\\p{S}]|$)|(?!~)[\\s\\p{P}\\p{S}](~~?)(?=[^\\s\\p{P}\\p{S}])|[\\s](~~?)(?!~)(?=[\\p{P}\\p{S}])|(?!~)[\\p{P}\\p{S}](~~?)(?!~)(?=[\\p{P}\\p{S}])|[^\\s\\p{P}\\p{S}](~~?)(?=[^\\s\\p{P}\\p{S}])", "gu"),
  del: new RegExp("^(~~?)(?=[^\\s~])((?:\\\\[\\s\\S]|[^\\\\])*?(?:\\\\[\\s\\S]|[^\\s~\\\\]))\\1(?=[^~]|$)", ""),
  autolink: new RegExp("^<([a-zA-Z][a-zA-Z0-9+.-]{1,31}:[^\\s\\x00-\\x1f<>]*|[a-zA-Z0-9.!#$%&'*+/=?_`{|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_]))>", ""),
  tag: new RegExp("^<!--(?:-?>|[\\s\\S]*?-->)|^<\\/[a-zA-Z][a-zA-Z0-9-]*\\s*>|^<[a-zA-Z][a-zA-Z0-9-]*(?:\\s+[a-zA-Z:_][\\w.:-]*(?:\\s*=\\s*\"[^\"]*\"|\\s*=\\s*'[^']*'|\\s*=\\s*[^\\s\"'=<>`]+)?)*?\\s*\\/?>|^<\\?[\\s\\S]*?\\?>|^<![a-zA-Z]+\\s[\\s\\S]*?>|^<!\\[CDATA\\[[\\s\\S]*?\\]\\]>", ""),
  link: new RegExp("^!?\\[((?:\\[(?:\\[(?:\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\\])|[^\\[\\]\\\\`])*?)\\]\\([ \\t\\n]*(<(?:\\\\.|[^\\n<>\\\\])+>|[^ \\t\\n\\x00-\\x1f]+|(?=\\)))(?:(?:[ \\t]+(?:\\n[ \\t]*)?|\\n[ \\t]*)(\"(?:\\\\[\\s\\S]|[^\"\\\\])*\"|'(?:\\\\[\\s\\S]|[^'\\\\])*'|\\((?:\\\\[\\s\\S]|[^)\\\\])*\\)))?[ \\t\\n]*\\)", ""),
  reflink: new RegExp("^!?\\[((?:\\[(?:\\[(?:\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\\])|[^\\[\\]\\\\`])*?)\\]\\[((?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\\\n]|\\n(?![ \\t]*\\n))+)\\]", ""),
  nolink: new RegExp("^!?\\[((?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\\\n]|\\n(?![ \\t]*\\n))+)\\](?:\\[\\])?", ""),
  reflinkSearch: new RegExp("!?\\[((?:[^\\[\\]\\\\`]*(?:\\[(?:\\[(?:\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|[^\\[\\]\\\\])*\\]|\\\\[\\s\\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\\]))){0,999}?[^\\[\\]\\\\`]*?)\\]\\[((?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\]){1,999})\\]|!?\\[((?!\\s*\\])(?:\\\\[\\s\\S]|[^\\[\\]\\\\]){1,999})\\](?:\\[\\])?(?!\\()", "g"),
  url: new RegExp("^(?:mailto:[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])|xmpp:[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])(?:\\/[A-Za-z0-9@.]+)?)|^((?:[hH][tT][tT][pP][sS]?|[fF][tT][pP]):\\/\\/|www\\.)(?:[a-zA-Z0-9\\-]+\\.?)+[^\\s<]*|^[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\\w-])", ""),
  _backpedal: new RegExp("(?:[^?!.,:;*_'\"~()&]+|\\([^)]*\\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'\"~)]+(?!$))+", ""),
  punctuation: new RegExp("^((?![*_])[\\s\\p{P}\\p{S}])", "u"),
  anyPunctuation: new RegExp("\\\\([\\p{P}\\p{S}])", "gu"),
  anyPunctuationOutsideCode: new RegExp("(`+)(?:[^`]|[^`][\\s\\S]*?[^`])\\1(?!`)|`+|\\\\([\\p{P}\\p{S}])", "gu"),
  blockSkip: new RegExp("\\[(?:[^\\[\\]`]|(?<a>`+)[^`]+\\k<a>(?!`))*?\\]\\((?:\\\\[\\s\\S]|[^\\\\\\(\\)]|\\((?:\\\\[\\s\\S]|[^\\\\\\(\\)])*\\))*\\)|(?<!`)()(?<b>`+)[^`]+\\k<b>(?!`)|<(?! )[^<>]*?>", "g"),
};

/** Count code points (not code units) in s; spreading a long match just to count them is wasteful. */
function cpLen(s) {
  let n = 0;
  for (let i = 0; i < s.length; i++) {
    if (s.charCodeAt(i) >= 0xD800 && s.charCodeAt(i) <= 0xDBFF) i++;
    n++;
  }
  return n;
}
/** Length in code units of the first code point of s. */
function firstCpLen(s) {
  const c = s.charCodeAt(0);
  return c >= 0xD800 && c <= 0xDBFF ? 2 : 1;
}
/** Does s end with a blank line (the /\n[ \t]*\n[ \t]*$/ test, done from the end)? */
function hasDoubleBlank(s) {
  let i = s.length - 1;
  while (i >= 0 && (s[i] === ' ' || s[i] === '\t')) i--;
  if (i < 0 || s[i] !== '\n') return false;
  i--;
  while (i >= 0 && (s[i] === ' ' || s[i] === '\t')) i--;
  return i >= 0 && s[i] === '\n';
}
/** Index of the first char of s that is not a space, or -1. */
function firstNonSpace(s) {
  for (let i = 0; i < s.length; i++) if (s[i] !== ' ') return i;
  return -1;
}
/** Width of s's leading whitespace, counting a tab as 4 (as replacing each tab by four spaces would); -1 when s is all whitespace. */
function leadingWidth(s) {
  let w = 0;
  for (let i = 0; i < s.length; i++) {
    if (s[i] === ' ') w++;
    else if (s[i] === '\t') w += 4;
    else return w;
  }
  return -1;
}
/** Expand tabs in a line's leading whitespace (tab-stop expansion); the line itself when it has no leading tab. */
function expandLeadingTabs(line) {
  let i = 0;
  let hasTab = false;
  while (i < line.length && (line[i] === ' ' || line[i] === '\t')) {
    if (line[i] === '\t') hasTab = true;
    i++;
  }
  if (!hasTab) return line;
  let out = '';
  let col = 0;
  for (let j = 0; j < i; j++) {
    if (line[j] === '\t') {
      const n = 4 - (col % 4);
      out += ' '.repeat(n);
      col += n;
    } else {
      out += ' ';
      col++;
    }
  }
  return out + line.slice(i);
}

/* ---------- block lexer ----------
   Block tokens are plain objects. Inline content stays as raw source text on
   the token (its `text`, or a table cell's `text`); it is rendered in the
   render phase, after every link reference definition has been collected.
   A token may also carry `checkbox` (a task-list item's checkbox), which the
   renderer emits before the token's inline content. */

function trySpace(src) {
  const t = RB.newline.exec(src);
  if (t && t[0].length > 0) return { type: 'space', raw: t[0] };
}
function tryCode(src) {
  const t = RB.code.exec(src);
  if (t) {
    const raw = trimTrailingBlanks(t[0]);
    return { type: 'code', raw, codeBlockStyle: 'indented', text: raw.replace(codeRemoveIndent, '') };
  }
}
function tryFences(src) {
  const t = RB.fences.exec(src);
  if (t) {
    return {
      type: 'code', raw: t[0],
      lang: t[2] ? t[2].trim().replace(RI.anyPunctuation, '$1') : t[2],
      text: fenceIndentComp(t[0], t[3] || ''),
    };
  }
}
function tryHeading(src) {
  const t = RB.heading.exec(src);
  if (t) {
    let text = t[2].trim();
    if (endingHash.test(text)) {
      const s = trimEndChar(text, '#');
      if (!s || endingSpaceTabChar.test(s)) text = s.trim();
    }
    return { type: 'heading', raw: trimEndChar(t[0], '\n'), depth: t[1].length, text };
  }
}
function tryHr(src) {
  const t = RB.hr.exec(src);
  if (t) return { type: 'hr', raw: trimEndChar(t[0], '\n') };
}
function tryBlockquote(src, lx) {
  const t = RB.blockquote.exec(src);
  if (!t) return;
  const lines = trimEndChar(t[0], '\n').split('\n');
  let raw = '', text = '';
  const tokens = [];
  while (lines.length > 0) {
    let seen = false;
    const chunk = [];
    let p;
    for (p = 0; p < lines.length; p++) {
      if (blockquoteStart.test(lines[p])) { chunk.push(lines[p]); seen = true; }
      else if (!seen) chunk.push(lines[p]);
      else break;
    }
    lines.splice(0, p);
    const joined = chunk.join('\n');
    const stripped = joined
      .replace(blockquoteMarkerWhitespace, (g, marker, ws) => marker + expandTabs(ws, marker.length))
      .replace(blockquoteSetextReplace, '\n    $1')
      .replace(blockquoteSetextReplace2, '');
    raw = raw ? raw + '\n' + joined : joined;
    text = text ? text + '\n' + stripped : stripped;
    const savedTop = lx.state.top;
    lx.state.top = true;
    blockTokens(stripped, tokens, true, lx);
    lx.state.top = savedTop;
    if (lines.length === 0) break;
    const last = tokens.at(-1);
    if (last?.type === 'code' || last?.type === 'heading' || last?.type === 'hr' || last?.type === 'html' || last?.type === 'table') break;
    if (last?.type === 'blockquote') {
      const inner = last;
      const rest = lines.join('\n');
      const combined = inner.raw + '\n' + rest.replace(blockquoteSetextReplace2, '');
      const reparsed = tryBlockquote(combined, lx);
      tokens[tokens.length - 1] = reparsed;
      const leftover = combined.substring(reparsed.raw.length).replace(/^\n/, '');
      const leftoverLines = leftover ? leftover.split('\n').length : 0;
      const consumed = leftoverLines ? lines.slice(0, -leftoverLines) : lines;
      if (consumed.length > 0) raw = raw + '\n' + consumed.join('\n');
      text = text.substring(0, text.length - inner.text.length) + reparsed.text;
      lines.splice(0, consumed.length);
      if (lines.length > 0 && blockquoteStart.test(lines[0])) continue;
      break;
    } else if (last?.type === 'list') {
      const inner = last;
      const combined = inner.raw + '\n' + lines.join('\n');
      const reparsed = tryList(combined, lx);
      tokens[tokens.length - 1] = reparsed;
      const extra = reparsed.raw.length > inner.raw.length
        ? combined.slice(inner.raw.length + 1, reparsed.raw.length).split('\n').length : 0;
      if (extra > 0) {
        const y = lines.slice(0, extra).join('\n');
        raw = raw + '\n' + y;
        text = text + '\n' + y;
      }
      lines.splice(0, extra);
      continue;
    }
  }
  return { type: 'blockquote', raw, tokens, text };
}
/** First char of line that lies within maxSpaces leading spaces (undefined when the line is shorter or the next char is a space beyond the limit). */
function firstCharWithin(line, maxSpaces) {
  let i = 0;
  while (i < maxSpaces && line[i] === ' ') i++;
  return line[i];
}

function tryList(src, lx) {
  const head = RB.list.exec(src);
  if (!head) return;
  const original = src;
  let rest = src;
  const bullet = head[1].trim();
  const ordered = bullet.length > 1;
  const list = {
    type: 'list', raw: '', ordered,
    start: ordered ? +bullet.slice(0, -1) : '', loose: false, items: [],
  };
  const bulletPattern = ordered ? `\\d{1,9}\\${bullet.slice(-1)}` : `\\${bullet}`;
  const itemRe = listItemRegex(bulletPattern);
  let sawDoubleBlank = false;
  while (rest) {
    let skipContent = false;
    let itemText = '';
    const itemMatch = itemRe.exec(rest);
    if (!itemMatch || RB.hr.test(rest)) break;
    const k = original.length - rest.length;
    rest = rest.substring(itemMatch[0].length);
    const nl1 = itemMatch[2].indexOf('\n');
    const firstLine = nl1 === -1 ? itemMatch[2] : itemMatch[2].slice(0, nl1);
    const bulletLen = itemMatch[1].length;
    // m is the previous line's content after the item indent, for the checks below.
    let m = firstLine.replace(leadingSpaceTab, (v) => expandTabs(v, bulletLen));
    const nl2 = rest.indexOf('\n');
    const nextLine = nl2 === -1 ? rest : rest.slice(0, nl2);
    const isEmpty = blankLine.test(m);
    let indent = 0;
    if (isEmpty) indent = bulletLen + 1;
    else {
      indent = firstNonSpace(m);
      if (indent > 4) indent = 1;
      itemText = m.slice(indent);
      indent += bulletLen;
    }
    if (isEmpty && blankLine.test(nextLine)) {
      rest = nl2 === -1 ? '' : rest.substring(nl2 + 1);
      skipContent = true;
    }
    if (!skipContent) {
      const nextBullet = nextBulletRegex(indent);
      const hrRe = hrRegex(indent);
      const fencesRe = fencesBeginRegex(indent);
      const headingRe = headingBeginRegex(indent);
      const htmlRe = htmlBeginRegex(indent);
      const quoteRe = blockquoteBeginRegex(indent);
      let prevBlank = isEmpty;
      while (rest) {
        const nl = rest.indexOf('\n');
        const line = nl === -1 ? rest : rest.slice(0, nl);
        const expanded = expandLeadingTabs(line);
        // Break test: each candidate regex is anchored and can only match when the line's first char (within indent spaces) is its own trigger char.
        const fc = firstCharWithin(line, indent);
        let breaks = false;
        if (fc === '`' || fc === '~') breaks = fencesRe.test(line);
        else if (fc === '#') breaks = headingRe.test(line);
        else if (fc === '<') breaks = htmlRe.test(line);
        else if (fc === '>') breaks = quoteRe.test(line);
        else if (fc === '*') breaks = nextBullet.test(line) || hrRe.test(line);
        else if (fc === '+') breaks = nextBullet.test(line);
        else if (fc === '-') breaks = nextBullet.test(line) || hrRe.test(line);
        else if (fc >= '0' && fc <= '9') breaks = nextBullet.test(line);
        else if (fc === '_') breaks = hrRe.test(line);
        if (breaks) break;
        if (firstNonSpace(expanded) >= indent || blankLine.test(line)) {
          itemText += '\n' + expanded.slice(indent);
        } else {
          if (prevBlank || leadingWidth(m) >= 4) break;
          const mc = firstCharWithin(m, indent);
          if (mc === '`' || mc === '~') { if (fencesRe.test(m)) break; }
          else if (mc === '#') { if (headingRe.test(m)) break; }
          else if (mc === '<') { if (htmlRe.test(m)) break; }
          else if (mc === '-' || mc === '_' || mc === '*') { if (hrRe.test(m)) break; }
          const setext = /^ {0,3}(?:=+|-+) *$/.test(line) && RB.lheading.test(m + '\n' + line)
            ? '    ' + expanded.replace(/^ {0,3}/, '') : line;
          itemText += '\n' + setext;
        }
        prevBlank = blankLine.test(line);
        rest = nl === -1 ? '' : rest.substring(nl + 1);
        m = expanded.slice(indent);
      }
    }
    const itemRaw = original.slice(k, original.length - rest.length);
    if (!list.loose) {
      if (sawDoubleBlank) list.loose = true;
      else if (hasDoubleBlank(itemRaw)) sawDoubleBlank = true;
    }
    list.items.push({
      type: 'list_item', raw: itemRaw,
      task: listIsTask.test(itemText), loose: false, text: itemText, tokens: [],
    });
  }
  const lastItem = list.items.at(-1);
  if (!lastItem) return;
  lastItem.raw = lastItem.raw.trimEnd();
  lastItem.text = lastItem.text.trimEnd();
  list.raw = original.slice(0, original.length - rest.length).trimEnd();
  for (const item of list.items) {
    lx.state.top = false;
    item.tokens = blockTokens(item.text, [], false, lx);
    if (!list.loose) {
      const spaces = item.tokens.filter((g) => g.type === 'space');
      if (spaces.length > 0 && spaces.some((g) => anyLine.test(g.raw))) list.loose = true;
    }
  }
  for (const item of list.items) {
    const first = item.tokens[0];
    if (item.task && (first?.type === 'text' || first?.type === 'paragraph')) {
      item.text = item.text.replace(listReplaceTask, '');
      first.raw = first.raw.replace(listReplaceTask, '');
      first.text = first.text.replace(listReplaceTask, '');
      const found = listTaskCheckbox.exec(item.raw);
      if (found) {
        const box = { type: 'checkbox', raw: found[0] + ' ', checked: found[0] !== '[ ]' };
        item.checked = box.checked;
        if (list.loose) {
          first.checkbox = box;
        } else {
          item.tokens.unshift(box);
        }
      }
    } else if (item.task) {
      item.task = false;
    }
  }
  if (list.loose) {
    for (const item of list.items) {
      item.loose = true;
      for (const tok of item.tokens) if (tok.type === 'text') tok.type = 'paragraph';
    }
  }
  return list;
}
function tryHtml(src) {
  const t = RB.html.exec(src);
  if (t) {
    const raw = trimTrailingBlanks(t[0]);
    return { type: 'html', block: true, raw, pre: t[1] === 'pre' || t[1] === 'script' || t[1] === 'style', text: raw };
  }
}
function tryDef(src) {
  const t = RB.def.exec(src);
  if (t) {
    if (!startAngleBracket.test(t[2]) && findParenClose(t[2], '()') !== -1) return;
    const tag = normalizeLabel(t[1]);
    const href = t[2] ? t[2].replace(hrefBrackets, '$1').replace(RI.anyPunctuation, '$1') : '';
    const title = t[3] ? t[3].substring(1, t[3].length - 1).replace(RI.anyPunctuation, '$1') : t[3];
    return { type: 'def', tag, raw: trimEndChar(t[0], '\n'), href, title };
  }
}
function tryTable(src) {
  const t = RB.table.exec(src);
  if (!t || !tableDelimiter.test(t[2])) return;
  const headerCells = splitTableRow(t[1]);
  const alignParts = t[2].replace(tableAlignChars, '').split('|');
  const rowLines = t[3]?.trim() ? t[3].replace(tableRowBlankLine, '').split('\n') : [];
  const table = { type: 'table', raw: trimEndChar(t[0], '\n'), header: [], align: [], rows: [] };
  if (headerCells.length !== alignParts.length) return;
  for (const part of alignParts) {
    if (tableAlignRight.test(part)) table.align.push('right');
    else if (tableAlignCenter.test(part)) table.align.push('center');
    else if (tableAlignLeft.test(part)) table.align.push('left');
    else table.align.push(null);
  }
  for (let i = 0; i < headerCells.length; i++) {
    table.header.push({ text: headerCells[i], header: true, align: table.align[i] });
  }
  for (const line of rowLines) {
    table.rows.push(splitTableRow(line, table.header.length).map((cell, i) => ({ text: cell, header: false, align: table.align[i] })));
  }
  return table;
}
function tryLheading(src) {
  const t = RB.lheading.exec(src);
  if (t) {
    return { type: 'heading', raw: trimEndChar(t[0], '\n'), depth: t[2].charAt(0) === '=' ? 1 : 2, text: t[1].trim() };
  }
}
function tryParagraph(src) {
  const t = RB.paragraph.exec(src);
  if (t) {
    const text = t[1].charAt(t[1].length - 1) === '\n' ? t[1].slice(0, -1) : t[1];
    return { type: 'paragraph', raw: t[0], text };
  }
}
function tryText(src) {
  const t = RB.text.exec(src);
  if (t) return { type: 'text', raw: t[0], text: t[0] };
}

/** A table can only match when the second line is a delimiter line (it holds a dash) and the first line holds text. */
function tableMayMatch(src) {
  const nl = src.indexOf('\n');
  if (nl === -1) return false;
  let i = 0;
  while (i < nl && src[i] === ' ') i++;
  if (i >= nl) return false;
  const nl2 = src.indexOf('\n', nl + 1);
  const line2 = nl2 === -1 ? src.slice(nl + 1) : src.slice(nl + 1, nl2);
  return line2.includes('-');
}
/** A setext heading can only match when a line starting with = or - (after at most 3 spaces) appears before the next blank line. */
function lheadingMayMatch(src) {
  const blank = src.indexOf('\n\n');
  const end = blank === -1 ? src.length : blank;
  let i = src.indexOf('\n');
  while (i !== -1 && i < end) {
    let j = i + 1;
    let sp = 0;
    while (sp < 3 && src[j] === ' ') { j++; sp++; }
    if (j < end && (src[j] === '=' || src[j] === '-')) return true;
    i = src.indexOf('\n', i + 1);
  }
  return false;
}

/** Lex block tokens from src into tokens. `nested` is true inside a blockquote (a paragraph there may merge into a preceding one). Returns the tokens array. */
function blockTokens(src, tokens, nested, lx) {
  let guard = Infinity;
  while (src) {
    if (src.length < guard) guard = src.length;
    else throw new Error('Infinite loop on byte: ' + src.charCodeAt(0));
    let tok;
    // First-character dispatch: every block pattern is anchored, so a pattern
    // whose first required character cannot appear is skipped outright.
    let sp = 0;
    while (sp < 3 && src[sp] === ' ') sp++;
    const c = src[sp];
    const c0 = src[0];
    if ((c0 === ' ' || c0 === '\t' || c0 === '\n') && (tok = trySpace(src))) {
      src = src.substring(tok.raw.length);
      const prev = tokens.at(-1);
      if (tok.raw.length === 1 && prev !== undefined) prev.raw += '\n';
      else tokens.push(tok);
      continue;
    }
    if ((c0 === '\t' || src.startsWith('    ') || (sp >= 1 && src[sp] === '\t')) && (tok = tryCode(src))) {
      src = src.substring(tok.raw.length);
      const prev = tokens.at(-1);
      if (prev?.type === 'paragraph' || prev?.type === 'text') {
        prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + tok.raw;
        prev.text += '\n' + tok.text;
      } else tokens.push(tok);
      continue;
    }
    if ((c === '`' || c === '~') && (tok = tryFences(src))) { src = src.substring(tok.raw.length); tokens.push(tok); continue; }
    if (c === '#' && (tok = tryHeading(src))) { src = src.substring(tok.raw.length); tokens.push(tok); continue; }
    if ((c === '-' || c === '_' || c === '*') && (tok = tryHr(src))) { src = src.substring(tok.raw.length); tokens.push(tok); continue; }
    if (c === '>' && (tok = tryBlockquote(src, lx))) { src = src.substring(tok.raw.length); tokens.push(tok); continue; }
    if ((c === '*' || c === '+' || c === '-' || (c >= '0' && c <= '9')) && (tok = tryList(src, lx))) { src = src.substring(tok.raw.length); tokens.push(tok); continue; }
    if (c === '<' && (tok = tryHtml(src))) { src = src.substring(tok.raw.length); tokens.push(tok); continue; }
    if (c === '[' && (tok = tryDef(src))) {
      src = src.substring(tok.raw.length);
      const prev = tokens.at(-1);
      if (prev?.type === 'paragraph' || prev?.type === 'text') {
        prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + tok.raw;
        prev.text += '\n' + tok.raw;
      } else {
        if (!lx.links[tok.tag]) lx.links[tok.tag] = { href: tok.href, title: tok.title };
        tokens.push(tok);
      }
      continue;
    }
    if (tableMayMatch(src) && (tok = tryTable(src))) { src = src.substring(tok.raw.length); tokens.push(tok); continue; }
    if (lheadingMayMatch(src) && (tok = tryLheading(src))) { src = src.substring(tok.raw.length); tokens.push(tok); continue; }
    if (lx.state.top && (tok = tryParagraph(src))) {
      const prev = tokens.at(-1);
      if (nested && prev?.type === 'paragraph') {
        prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + tok.raw;
        prev.text += '\n' + tok.text;
      } else tokens.push(tok);
      nested = false;
      src = src.substring(tok.raw.length);
      continue;
    }
    if (tok = tryText(src)) {
      src = src.substring(tok.raw.length);
      const prev = tokens.at(-1);
      if (prev?.type === 'text') {
        prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + tok.raw;
        prev.text += '\n' + tok.text;
      } else tokens.push(tok);
      continue;
    }
    throw new Error('Infinite loop on byte: ' + src.charCodeAt(0));
  }
  lx.state.top = true;
  return tokens;
}

/* ---------- inline rendering ----------
   Renders an inline source straight to HTML (or, with plain=true, to the
   plain text the text renderer would produce for an image's alt text).
   No inline token objects are built: each construct is recognised and its
   output appended at once. The state machine (inLink, inRawBlock,
   linkEmitted, linkParenPossible) and the emphasis mask follow marked's
   inline lexer exactly; the mask is built lazily, only when an emphasis or
   strikethrough match is attempted. */

function maskSource(src, lx) {
  let t = src;
  if (lx.links && src.includes('[')) {
    const re = RI.reflinkSearch;
    const maskRef = (r) => {
      const o = r.lastIndexOf('[');
      if (!Object.hasOwn(lx.links, normalizeLabel(r.slice(o + 1, -1)))) return r;
      if (o > 1 && r.charAt(0) !== '!') {
        const inner = r.slice(1, o - 1);
        if (linkInTextMask(inner, lx)) return '[' + inner.replace(re, maskRef) + '][' + 'a'.repeat(r.length - o - 2) + ']';
      }
      return '[' + 'a'.repeat(r.length - 2) + ']';
    };
    t = t.replace(re, maskRef);
  }
  // Both replaces below can only match when a backtick, backslash, '[' or '<' is present; skip the full scan otherwise.
  if (t.includes('`') || t.includes('\\')) {
    t = t.replace(RI.anyPunctuationOutsideCode, (n, s, r) => r ? '+'.repeat(n.length) : s ? s + n.slice(s.length, -s.length).replace(/`/g, '+') + s : n);
  }
  if (t.includes('[') || t.includes('<') || t.includes('`')) {
    t = t.replace(RI.blockSkip, (n, s, r) => {
      const o = r ? r.length : 0;
      return n.slice(0, o) + '[' + 'a'.repeat(n.length - o - 2) + ']';
    });
  }
  return t;
}
function linkInTextMask(src, lx) {
  if (!src.includes('[')) return false;
  for (const m of src.matchAll(RI.blockSkip)) {
    if (RI.link.test(m[0]) && src.charAt(m.index - 1) !== '!') return true;
  }
  for (const m of src.matchAll(RI.reflinkSearch)) {
    const s = m[0];
    const r = s.lastIndexOf('[');
    if (!(s.charAt(0) === '!' || !Object.hasOwn(lx.links, normalizeLabel(s.slice(r + 1, -1)))) && !(r > 1 && linkInTextMask(s.slice(1, r - 1), lx))) return true;
  }
  return false;
}
/** The masked copy of the current inline source (built lazily). */
function currentMask(lx) {
  const top = lx.maskStack[lx.maskStack.length - 1];
  if (top.masked === null) top.masked = maskSource(top.src, lx);
  return top.masked;
}
/** The closer scan of the current inline source (built lazily). */
function currentScan(lx) {
  const top = lx.maskStack[lx.maskStack.length - 1];
  if (top.scan === null) top.scan = scanMask(currentMask(lx));
  return top.scan;
}
/** Does the link label text hold an HTML tag or autolink that runs past the label's end? */
function linkInText(src, label, offset) {
  if (!label.includes('<')) return false;
  for (let i = 0; i < label.length; i++) {
    if (label[i] === '\\') { i++; continue; }
    if (label[i] === '`') {
      const code = RI.code.exec(label.slice(i));
      if (code) { i += code[0].length - 1; continue; }
    }
    if (label[i] !== '<') continue;
    const rest = src.slice(offset + i);
    const tag = RI.tag.exec(rest) || RI.autolink.exec(rest);
    if (tag) {
      if (tag[0].length > label.length - i) return true;
      i += tag[0].length - 1;
    }
  }
  return false;
}
/** Build a link or image from a matched label and a resolved reference. Returns null when the link must be dropped (a link inside a link). */
function makeLink(match, ref, raw, lx, plain) {
  const isImage = match[0].charAt(0) === '!';
  const label = match[1].replace(outputLinkReplace, '$1');
  const savedInLink = lx.state.inLink;
  const savedEmitted = lx.state.linkEmitted;
  const savedRawBlock = lx.state.inRawBlock;
  lx.state.inLink = true;
  lx.state.linkEmitted = false;
  const inner = renderInline(label, lx, plain || isImage);
  const emittedInside = lx.state.linkEmitted;
  lx.state.linkEmitted = savedEmitted;
  lx.state.inLink = savedInLink;
  if (!isImage) {
    if (emittedInside) { lx.state.inRawBlock = savedRawBlock; return null; }
    lx.state.linkEmitted = true;
  }
  // In plain mode a link and an image both render as their inner plain text.
  if (plain) return { s: inner, len: raw.length };
  if (isImage) {
    const alt = inner;
    const encoded = encodeHref(ref.href);
    if (encoded === null) return { s: esc(alt), len: raw.length };
    let out = '<img src="' + esc(encoded) + '" alt="' + esc(alt) + '"';
    if (ref.title) out += ' title="' + esc(ref.title) + '"';
    return { s: out + '>', len: raw.length };
  }
  const encoded = encodeHref(ref.href);
  if (encoded === null) return { s: inner, len: raw.length };
  let out = '<a href="' + esc(encoded) + '"';
  if (ref.title) out += ' title="' + esc(ref.title) + '"';
  return { s: out + '>' + inner + '</a>', len: raw.length };
}
function inlineEscape(src, plain) {
  const t = RI.escape.exec(src);
  if (!t) return null;
  return { s: plain ? t[1] : esc(t[1]), len: t[0].length };
}
function inlineTag(src, lx) {
  const t = RI.tag.exec(src);
  if (!t) return null;
  if (!lx.state.inLink && startATag.test(t[0])) lx.state.inLink = true;
  else if (lx.state.inLink && endATag.test(t[0])) lx.state.inLink = false;
  if (!lx.state.inRawBlock && startPreScriptTag.test(t[0])) lx.state.inRawBlock = true;
  else if (lx.state.inRawBlock && endPreScriptTag.test(t[0])) lx.state.inRawBlock = false;
  return { s: t[0], len: t[0].length };
}
function inlineLink(src, lx, plain) {
  if (lx.state.linkParenPossible === false) return null;
  const t = RI.link.exec(src);
  if (!t) return null;
  const bang = t[0].charAt(0) === '!' ? 2 : 1;
  if (linkInText(src, t[1], bang)) return null;
  const s = t[2].trim();
  if (startAngleBracket.test(s)) {
    if (!endAngleBracket.test(s)) return null;
    const l = trimEndChar(s.slice(0, -1), '\\');
    if ((s.length - l.length) % 2 === 0) return null;
  } else {
    const l = findParenClose(t[2], '()');
    if (l === -2) return null;
    if (l > -1) {
      const h = (t[0].indexOf('!') === 0 ? 5 : 4) + t[1].length + l;
      t[2] = t[2].substring(0, l);
      t[0] = t[0].substring(0, h).trim();
      t[3] = '';
    }
  }
  const r = trimEndChar(t[0].slice(0, -1), '\\');
  if ((t[0].length - r.length) % 2 === 0) return null;
  let href = t[2];
  const title = t[3] ? t[3].slice(1, -1) : '';
  href = href.trim();
  if (startAngleBracket.test(href)) href = href.slice(1, -1);
  return makeLink(t, { href: href && href.replace(RI.anyPunctuation, '$1'), title: title && title.replace(RI.anyPunctuation, '$1') }, t[0], lx, plain);
}
function inlineReflink(src, lx, plain) {
  const m = RI.reflink.exec(src) || RI.nolink.exec(src);
  if (!m) return null;
  const bang = m[0].charAt(0) === '!' ? 2 : 1;
  if (linkInText(src, m[1], bang)) return null;
  const ref = lx.links[normalizeLabel(m[2] || m[1])];
  if (!ref) {
    const ch = m[0].charAt(0);
    return { s: plain ? ch : esc(ch), len: 1 };
  }
  return makeLink(m, ref, m[0], lx, plain);
}
function inlineEmStrong(src, lx, prevChar, plain) {
  const m = RI.emStrongLDelim.exec(src);
  if (!m || (!m[1] && !m[2] && !m[3] && !m[4])) return null;
  const ch = m[0][0];
  const sameAsPrev = prevChar === ch;
  const masked = currentMask(lx);
  const i = masked.length - src.length;
  let l = i;
  while (l > 0 && masked[l - 1] === ch) l--;
  const p = [...masked.slice(Math.max(0, l - 2), l)].at(-1) ?? '';
  const h = p === '*' || p === '_' || !!RI.punctuation.exec(p);
  if (l < i) prevChar = p;
  const u = l < i ? h : !!RI.punctuation.exec(prevChar);
  if (m[4] && prevChar.match(unicodeAlphaNumeric)) return null;
  const d = m[1] || m[3] || '';
  if (!d || !prevChar || u) {
    const k = cpLen(m[0]) - 1;
    let g, b, openers = k, unusable = 0;
    const y = i - l + k;
    const R = !!p.trim() && (!!d || (ch === '*' && !h));
    if (ch !== '*' && ch !== '_') return null;
    const delimRe = ch === '*' ? RI.emStrongRDelimAst : RI.emStrongRDelimUnd;
    const v = currentScan(lx).lastPossibleEmStrongCloserIndex[ch];
    const Q = masked.length - src.length + k;
    if (v < Q) return null;
    const t = masked.slice(-src.length + k);
    const limit = v - Q;
    delimRe.lastIndex = 0;
    let s;
    while ((s = delimRe.exec(t)) !== null && !(s.index > limit)) {
      g = s[1] || s[2] || s[3] || s[4] || s[5] || s[6];
      if (!g) continue;
      b = cpLen(g);
      if (s[3] || s[4]) { openers += b; continue; }
      if (s[5] || s[6] || R) {
        if (sameAsPrev && (s[5] || s[6])) break;
        if (y % 3 && !((y + b) % 3)) { unusable += b; continue; }
      }
      if (openers -= b, openers > 0) continue;
      b = Math.min(b, b + openers + unusable);
      const te = firstCpLen(s[0]);
      const M = src.slice(0, k + s.index + te + b);
      if (Math.min(k, b) % 2) {
        const inner = M.slice(1, -1);
        const html = renderInline(inner, lx, plain);
        return { s: plain ? html : '<em>' + html + '</em>', len: M.length };
      }
      const inner = M.slice(2, -2);
      const html = renderInline(inner, lx, plain);
      return { s: plain ? html : '<strong>' + html + '</strong>', len: M.length };
    }
  }
  return null;
}
function inlineCodespan(src, plain) {
  const t = RI.code.exec(src);
  if (!t) return null;
  let text = t[2].replace(newLineCharGlobal, ' ');
  const hasNonSpace = nonSpaceChar.test(text);
  const padded = startingSpaceChar.test(text) && endingSpaceChar.test(text);
  if (hasNonSpace && padded) text = text.substring(1, text.length - 1);
  return { s: plain ? text : '<code>' + esc(text, true) + '</code>', len: t[0].length };
}
function inlineBr(src, plain) {
  const t = RI.br.exec(src);
  if (!t) return null;
  return { s: plain ? '' : '<br>', len: t[0].length };
}
function inlineDel(src, lx, prevChar, plain) {
  const m = RI.delLDelim.exec(src);
  if (!m) return null;
  if (!((m[1] || '') || !prevChar || RI.punctuation.exec(prevChar))) return null;
  const o = cpLen(m[0]) - 1;
  let i, l, openers = o;
  const masked = currentMask(lx);
  const u = currentScan(lx).lastPossibleDelCloserIndex;
  const d = masked.length - src.length + o;
  if (u < d) return null;
  const t = masked.slice(-src.length + o);
  const limit = u - d;
  const delimRe = RI.delRDelim;
  delimRe.lastIndex = 0;
  let s;
  while ((s = delimRe.exec(t)) !== null && !(s.index > limit)) {
    i = s[1] || s[2] || s[3] || s[4] || s[5] || s[6];
    if (!i || (l = cpLen(i), l !== o)) continue;
    if (s[3] || s[4]) { openers += l; continue; }
    if (openers -= l, openers > 0) continue;
    l = Math.min(l, l + openers);
    const g = firstCpLen(s[0]);
    const raw = src.slice(0, o + s.index + g + l);
    const inner = raw.slice(o, -o);
    const html = renderInline(inner, lx, plain);
    return { s: plain ? html : '<del>' + html + '</del>', len: raw.length };
  }
  return null;
}
function inlineAutolink(src, plain) {
  const t = RI.autolink.exec(src);
  if (!t) return null;
  let text, href;
  if (t[2] === '@') { text = t[1]; href = 'mailto:' + text; }
  else { text = t[1]; href = text; }
  if (plain) return { s: text, len: t[0].length };
  const encoded = encodeHref(href);
  if (encoded === null) return { s: esc(text, true), len: t[0].length };
  return { s: '<a href="' + esc(encoded, true) + '">' + esc(text, true) + '</a>', len: t[0].length };
}
/** Cheap superset check: true whenever RI.url could match at the start of rest (a protocol/www/mailto prefix, or a word run holding '@' with a '.' after it). */
function maybeUrl(rest) {
  const c0 = rest[0];
  if (c0 === 'w' && rest.startsWith('www.')) return true;
  if (c0 === 'm' && rest.startsWith('mailto:')) return true;
  if (c0 === 'x' && rest.startsWith('xmpp:')) return true;
  if (c0 === 'h' || c0 === 'H' || c0 === 'f' || c0 === 'F') {
    const s = rest.slice(0, 8).toLowerCase();
    if (s.startsWith('http://') || s.startsWith('https://') || s.startsWith('ftp://')) return true;
  }
  // Email: a local-part word run, '@', then a domain run holding a '.'.
  let i = 0;
  while (i < rest.length) {
    const c = rest.charCodeAt(i);
    if ((c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122) ||
        c === 46 || c === 95 || c === 43 || c === 45) { i++; continue; }
    break;
  }
  if (i === 0 || rest[i] !== '@') return false;
  let j = i + 1;
  while (j < rest.length) {
    const c = rest.charCodeAt(j);
    if ((c >= 48 && c <= 57) || (c >= 65 && c <= 90) || (c >= 97 && c <= 122) ||
        c === 46 || c === 95 || c === 45) {
      if (c === 46) return true;
      j++;
      continue;
    }
    break;
  }
  return false;
}

function inlineUrl(src, plain) {
  const t = RI.url.exec(src);
  if (!t) return null;
  let text, href;
  if (t[2] === '@') { text = t[0]; href = 'mailto:' + text; }
  else {
    let cur;
    do {
      cur = t[0];
      t[0] = RI._backpedal.exec(t[0])?.[0] ?? '';
    } while (cur !== t[0]);
    text = t[0];
    href = t[1] === 'www.' ? 'http://' + t[0] : t[0];
  }
  if (plain) return { s: text, len: t[0].length };
  const encoded = encodeHref(href);
  if (encoded === null) return { s: esc(text, true), len: t[0].length };
  return { s: '<a href="' + esc(encoded, true) + '">' + esc(text, true) + '</a>', len: t[0].length };
}
function inlineText(src, lx, plain) {
  const t = RI.text.exec(src);
  if (!t) return null;
  const inRawBlock = lx.state.inRawBlock;
  const html = inRawBlock ? t[0] : plain ? unescapeEntities(t[0]) : esc(unescapeEntities(t[0]));
  return { s: html, len: t[0].length, raw: t[0] };
}
/** Render one inline source to HTML (plain=true: to the plain text an image's alt text uses). */
function renderInline(src, lx, plain) {
  const savedParen = lx.state.linkParenPossible;
  lx.state.linkParenPossible = savedParen && src.includes(')');
  lx.maskStack.push({ src, masked: null, scan: null });
  let out = '';
  let prevChar = '';
  let afterText = false;
  let guard = Infinity;
  try {
    let rest = src;
    while (rest) {
      if (rest.length < guard) guard = rest.length;
      else throw new Error('Infinite loop on byte: ' + rest.charCodeAt(0));
      if (!afterText) prevChar = '';
      afterText = false;
      const ch = rest[0];
      let res = null;
      if (ch === '\\') res = inlineEscape(rest, plain) || inlineBr(rest, plain);
      else if (ch === '<') res = inlineTag(rest, lx) || inlineAutolink(rest, plain);
      else if (ch === '[' || ch === '!') res = inlineLink(rest, lx, plain) || inlineReflink(rest, lx, plain);
      else if (ch === '*' || ch === '_') res = inlineEmStrong(rest, lx, prevChar, plain);
      else if (ch === '`') res = inlineCodespan(rest, plain);
      else if (ch === '~') res = inlineDel(rest, lx, prevChar, plain);
      else if (ch === ' ') res = inlineBr(rest, plain);
      else if ((ch >= 'a' && ch <= 'z') || (ch >= 'A' && ch <= 'Z') || (ch >= '0' && ch <= '9') || ch === '.' || ch === '_' || ch === '+' || ch === '-') {
        if (!lx.state.inLink && maybeUrl(rest)) res = inlineUrl(rest, plain);
      }
      if (res) {
        out += res.s;
        rest = rest.substring(res.len);
        continue;
      }
      const textRes = inlineText(rest, lx, plain);
      if (textRes) {
        out += textRes.s;
        if (textRes.raw.slice(-1) !== '_') prevChar = textRes.raw.slice(-1);
        afterText = true;
        rest = rest.substring(textRes.len);
        continue;
      }
      throw new Error('Infinite loop on byte: ' + rest.charCodeAt(0));
    }
  } finally {
    lx.maskStack.pop();
    lx.state.linkParenPossible = savedParen;
  }
  return out;
}

/* ---------- block rendering ---------- */
/** A paragraph or text token's inline content, with its task-list checkbox (if any) emitted first. */
function inlineWithCheckbox(tok, lx) {
  const box = tok.checkbox
    ? '<input ' + (tok.checkbox.checked ? 'checked="" ' : '') + 'disabled="" type="checkbox"> '
    : '';
  return box + renderInline(tok.text, lx, false);
}
function renderCode(tok) {
  const lang = (tok.lang || '').match(notSpaceStart)?.[0];
  const text = tok.text ? tok.text.replace(endingNewline, '') + '\n' : '';
  const body = esc(text, true);
  if (lang) return '<pre><code class="language-' + esc(lang) + '">' + body + '</code></pre>\n';
  return '<pre><code>' + body + '</code></pre>\n';
}
function renderTableCell(cell, lx) {
  const tag = cell.header ? 'th' : 'td';
  const align = cell.align ? ` align="${cell.align}"` : '';
  return `<${tag}${align}>` + renderInline(cell.text, lx, false) + `</${tag}>\n`;
}
function renderTable(tok, lx) {
  let head = '';
  for (const cell of tok.header) head += renderTableCell(cell, lx);
  let out = '<table>\n<thead>\n<tr>\n' + head + '</tr>\n</thead>\n';
  if (tok.rows.length > 0) {
    let body = '';
    for (const row of tok.rows) {
      let cells = '';
      for (const cell of row) cells += renderTableCell(cell, lx);
      body += '<tr>\n' + cells + '</tr>\n';
    }
    out += '<tbody>' + body + '</tbody>';
  }
  return out + '</table>\n';
}
function renderList(tok, lx) {
  const tag = tok.ordered ? 'ol' : 'ul';
  const start = tok.ordered && tok.start !== 1 ? ` start="${tok.start}"` : '';
  let items = '';
  for (const item of tok.items) items += '<li>' + renderBlocks(item.tokens, lx) + '</li>\n';
  return `<${tag}${start}>\n` + items + `</${tag}>\n`;
}
function renderBlocks(tokens, lx) {
  let out = '';
  for (const tok of tokens) {
    switch (tok.type) {
      case 'space': break;
      case 'hr': out += '<hr>\n'; break;
      case 'heading': out += `<h${tok.depth}>` + renderInline(tok.text, lx, false) + `</h${tok.depth}>\n`; break;
      case 'code': out += renderCode(tok); break;
      case 'table': out += renderTable(tok, lx); break;
      case 'blockquote': out += '<blockquote>\n' + renderBlocks(tok.tokens, lx) + '</blockquote>\n'; break;
      case 'list': out += renderList(tok, lx); break;
      case 'checkbox': out += '<input ' + (tok.checked ? 'checked="" ' : '') + 'disabled="" type="checkbox"> '; break;
      case 'html': out += tok.text; break;
      case 'def': break;
      case 'paragraph': out += '<p>' + inlineWithCheckbox(tok, lx) + '</p>\n'; break;
      case 'text': out += inlineWithCheckbox(tok, lx); break;
      default: throw new Error('Token with "' + tok.type + '" type was not found.');
    }
  }
  return out;
}

/** The HTML marked 18.1.3 renders for `markdown`, with marked's defaults. */
export function parse(markdown) {
  const lx = {
    links: Object.create(null),
    state: { inLink: false, inRawBlock: false, linkEmitted: false, linkParenPossible: true, top: true },
    maskStack: [],
  };
  const src = markdown.replace(carriageReturn, '\n');
  const tokens = blockTokens(src, [], false, lx);
  return renderBlocks(tokens, lx);
}
