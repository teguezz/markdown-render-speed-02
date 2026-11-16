// parse.js — a fast drop-in replacement for marked 18.1.3.
//
// parse(markdown) returns, for every string, exactly the HTML that
// marked.parse(markdown) returns with marked's default options
// (gfm: true, breaks: false, pedantic: false, async: false).
//
// This is a derivative work of marked (MIT, see LICENSE and NOTICE),
// re-implemented for speed:
//   - the block lexer dispatches on the first characters of a line and
//     only runs a grammar regex when a cheap gate says it can match;
//   - the inline lexer dispatches on the current character instead of
//     trying every inline rule at every position;
//   - block structure is collected line by line where marked re-scans;
//   - rendering is a single walk over the token tree, inlined here.
// The grammar itself — token boundaries, edge cases, output bytes — is
// marked's, and the grammar regexes below are marked's own patterns,
// kept wherever a regex is genuinely the clearest way to state a rule.

// ---------------------------------------------------------------------
// Small string helpers (same semantics as marked's internal helpers).
// ---------------------------------------------------------------------

// Remove a trailing run of `ch` (or, with toEnd, of not-`ch`) characters.
function trimRightChar(str, ch, toEnd) {
  const len = str.length;
  if (len === 0) return '';
  let count = 0;
  while (count < len) {
    const c = str.charAt(len - count - 1);
    if (c === ch && !toEnd) count++;
    else if (c !== ch && toEnd) count++;
    else break;
  }
  return str.slice(0, len - count);
}

const blankLineRe = /^[ \t]*$/;

// Drop trailing blank lines of a block, keeping the text untouched when
// at most one blank line (or none) trails.
function trimTrailingBlankLines(str) {
  const lines = str.split('\n');
  let last = lines.length - 1;
  while (last >= 0 && blankLineRe.test(lines[last])) last--;
  return lines.length - last <= 2 ? str : lines.slice(0, last + 1).join('\n');
}

// The key under which a link reference definition is stored: trimmed,
// whitespace runs folded to one space, case folded.
function normalizeLabel(str) {
  return str.trim().replace(/\s+/g, ' ').toLowerCase().toUpperCase().toLowerCase();
}

// Index of the bracket that closes the first opener, honouring backslash
// escapes; -1 when balanced or absent, -2 when an opener never closes.
function findClosingBracket(str, brackets) {
  if (str.indexOf(brackets[0]) === -1 && str.indexOf(brackets[1]) === -1) return -1;
  let level = 0;
  for (let i = 0; i < str.length; i++) {
    if (str[i] === '\\') i++;
    else if (str[i] === brackets[0]) level++;
    else if (str[i] === brackets[1] && (level--, level < 0)) return i;
  }
  return level > 0 ? -2 : -1;
}

// Expand tabs to spaces, tab stops every 4 columns from `startColumn`.
function expandTabs(str, startColumn = 0) {
  let col = startColumn;
  let out = '';
  for (const ch of str) {
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

// ---------------------------------------------------------------------
// HTML escaping and entity handling (marked's escape / unescape rules).
// ---------------------------------------------------------------------

const escapeReplacements = {
  '&': '&amp;',
  '<': '&lt;',
  '>': '&gt;',
  '"': '&quot;',
  "'": '&#39;',
};
const escapeTestRe = /[&<>"']/;
const escapeReplaceRe = /[&<>"']/g;
const escapeTestNoEncodeRe = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/;
const escapeReplaceNoEncodeRe = /[<>"']|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;

function escapeHtml(str, encode) {
  if (encode) {
    if (escapeTestRe.test(str)) return str.replace(escapeReplaceRe, (c) => escapeReplacements[c]);
  } else if (escapeTestNoEncodeRe.test(str)) {
    return str.replace(escapeReplaceNoEncodeRe, (c) => escapeReplacements[c]);
  }
  return str;
}

const numericRefRe = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));/;
const numericRefOrAmpRe = /&#(?:(\d{1,7})|[Xx]([A-Fa-f0-9]{1,6}));|&(?!(#\d{1,7}|#[Xx][a-fA-F0-9]{1,6}|\w+);)/g;

// Decode numeric character references in a text run; a bare ampersand
// that starts no reference becomes &amp;. Named references stay as-is.
function decodeEntities(str) {
  if (!numericRefRe.test(str)) return str;
  return str.replace(numericRefOrAmpRe, (match, dec, hex) => {
    if (dec === undefined && hex === undefined) return '&amp;';
    const code = dec === undefined ? Number.parseInt(hex, 16) : Number.parseInt(dec, 10);
    if (code === 0 || code > 0x10FFFF || (code >= 0xD800 && code <= 0xDFFF)) return '\uFFFD';
    if (code === 38) return '&amp;';
    return String.fromCodePoint(code);
  });
}

// encodeURI an href the way marked does; null when it cannot be encoded.
function cleanUrl(href) {
  try {
    return encodeURI(href).replace(/%25/g, '%');
  } catch {
    return null;
  }
}

// Split a table row into cells: unescaped pipes separate, \| is a pipe.
function splitCells(row, rowLength) {
  const swapped = row.replace(/\|/g, (match, offset, str) => {
    let escaped = false;
    let p = offset;
    while (--p >= 0 && str[p] === '\\') escaped = !escaped;
    return escaped ? '|' : ' |';
  });
  const cells = swapped.split(/ \|/);
  if (!cells[0].trim()) cells.shift();
  if (cells.length > 0 && !cells.at(-1)?.trim()) cells.pop();
  if (rowLength) {
    if (cells.length > rowLength) cells.splice(rowLength);
    else while (cells.length < rowLength) cells.push('');
  }
  for (let i = 0; i < cells.length; i++) {
    cells[i] = cells[i].trim().replace(/\\\|/g, '|');
  }
  return cells;
}

// ---------------------------------------------------------------------
// Regex composition, the way marked builds its grammar: start from a
// template and splice named sub-patterns into it, dropping the inner
// ^ anchors of the spliced pieces.
// ---------------------------------------------------------------------

const caretRe = /(^|[^\[])\^/g;

function compose(regex, flags = '') {
  let source = typeof regex === 'string' ? regex : regex.source;
  const api = {
    replace(name, val) {
      let v = typeof val === 'string' ? val : val.source;
      v = v.replace(caretRe, '$1');
      source = source.replace(name, v);
      return api;
    },
    getRegex() {
      return new RegExp(source, flags);
    },
  };
  return api;
}

const lookbehindWorks = (() => {
  try {
    return !!new RegExp('(?<=1)(?<!1)');
  } catch {
    return false;
  }
})();

// Indent-parameterised begin-of-construct patterns used by the list
// walker. marked caches four variants; the variant built for a content
// indent R is the one for clamp(R - 1, 0, 3).
function indentVariant(factory) {
  const cache = [];
  return (indent) => {
    const n = Math.max(0, Math.min(3, indent - 1));
    return cache[n] || (cache[n] = factory(n));
  };
}

// ---------------------------------------------------------------------
// The "other" rule table: small patterns shared by lexer and renderer.
// ---------------------------------------------------------------------

const tagNames = 'address|article|aside|base|basefont|blockquote|body|caption|center|col|colgroup|dd|details|dialog|dir|div|dl|dt|fieldset|figcaption|figure|footer|form|frame|frameset|h[1-6]|head|header|hr|html|iframe|legend|li|link|main|menu|menuitem|meta|nav|noframes|ol|optgroup|option|p|param|search|section|summary|table|tbody|td|tfoot|th|thead|title|tr|track|ul';

const other = {
  codeRemoveIndent: /^(?: {0,3}\t| {1,4})/gm,
  outputLinkReplace: /\\([\[\]])/g,
  indentCodeCompensation: /^(\s+)(?:```)/,
  beginningSpace: /^\s+/,
  endingHash: /#$/,
  startingSpaceChar: /^ /,
  endingSpaceChar: / $/,
  endingSpaceTabChar: /[ \t]$/,
  nonSpaceChar: /[^ ]/,
  newLineCharGlobal: /\n/g,
  tabCharGlobal: /\t/g,
  leadingSpaceTab: /^[ \t]+/,
  blankLine: /^[ \t]*$/,
  doubleBlankLine: /\n[ \t]*\n[ \t]*$/,
  blockquoteStart: /^ {0,3}>/,
  blockquoteSetextReplace: /\n {0,3}((?:=+|-+)[ \t]*)(?=\n|$)/g,
  blockquoteSetextReplace2: /^ {0,3}>[ \t]?/gm,
  blockquoteMarkerWhitespace: /^( {0,3}>)([ \t]+)/gm,
  listIsTask: /^\[[ xX]\][ \t]+\S/,
  listReplaceTask: /^\[[ xX]\][ \t]+/,
  listTaskCheckbox: /\[[ xX]\]/,
  anyLine: /\n.*\n/,
  hrefBrackets: /^<(.*)>$/,
  tableDelimiter: /[:|]/,
  tableAlignChars: /^\||\| *$/g,
  tableRowBlankLine: /\n[ \t]*$/,
  tableAlignRight: /^ *-+: *$/,
  tableAlignCenter: /^ *:-+: *$/,
  tableAlignLeft: /^ *:-+ *$/,
  startATag: /^<a /i,
  endATag: /^<\/a>/i,
  startPreScriptTag: /^<(pre|code|kbd|script)(\s|>)/i,
  endPreScriptTag: /^<\/(pre|code|kbd|script)(\s|>)/i,
  startAngleBracket: /^</,
  endAngleBracket: />$/,
  unicodeAlphaNumeric: /[\p{L}\p{N}]/u,
  listItemRegex: (bullet) => new RegExp(`^( {0,3}${bullet})((?:[\t ][^\\n]*)?(?:\\n|$))`),
  nextBulletRegex: indentVariant((a) => new RegExp(`^ {0,${a}}(?:[*+-]|\\d{1,9}[.)])((?:[ \t][^\\n]*)?(?:\\n|$))`)),
  hrRegex: indentVariant((a) => new RegExp(`^ {0,${a}}((?:-[ \t]*){3,}|(?:_[ \t]*){3,}|(?:\\*[ \t]*){3,})(?:\\n+|$)`)),
  fencesBeginRegex: indentVariant((a) => new RegExp(`^ {0,${a}}(?:\`\`\`|~~~)`)),
  headingBeginRegex: indentVariant((a) => new RegExp(`^ {0,${a}}#{1,6}(?:\\s|$)`)),
  htmlBeginRegex: indentVariant((a) => new RegExp(`^ {0,${a}}(?:</?(?:${tagNames})(?: +|$|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)`, 'i')),
  blockquoteBeginRegex: indentVariant((a) => new RegExp(`^ {0,${a}}>`)),
};

// ---------------------------------------------------------------------
// Block grammar (GFM variant, the one marked's defaults select).
// ---------------------------------------------------------------------

const blockNewline = /^(?:[ \t]*(?:\n|$))+/;
const blockCode = /^((?: {4}| {0,3}\t)[^\n]+(?:\n(?:[ \t]*(?:\n|$))*)?)+/;
const blockFences = /^ {0,3}(`{3,}(?=[^`\n]*(?:\n|$))|~{3,})([^\n]*)(?:\n|$)(?:|([\s\S]*?)(?:\n|$))(?: {0,3}(?:(?=`)\1`*|(?=~)\1~*) *(?=\n|$)|$)/;
const blockHeading = /^ {0,3}(#{1,6})(?=\s|$)(.*)(?:\n+|$)/;
const blockHr = /^ {0,3}((?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)/;

const bulletPattern = / {0,3}(?:[*+-]|\d{1,9}[.)])/;
const linkLabelPattern = /(?!\s*\])(?:\\[\s\S]|[^\[\]\\\n]|\n(?![ \t]*\n))+/;
const defTitlePattern = /(?:"(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\\n]|\n(?!\n))*'|\((?:\\[\s\S]|[^()\\])*\))/;

const blockDef = compose(/^ {0,3}\[(label)\]: *(?:\n[ \t]*)?([^<\s][^\s]*|<.*?>)(?:(?: +(?:\n[ \t]*)?| *\n[ \t]*)(title))? *(?:\n+|$)/)
  .replace('label', linkLabelPattern)
  .replace('title', defTitlePattern)
  .getRegex();

const blockList = compose(/^(bull)([ \t][^\n]*?)?(?:\n|$)/)
  .replace(/bull/g, bulletPattern)
  .getRegex();

const commentPattern = /<!--(?:-?>|[\s\S]*?(?:-->|$))/;
const blockHtml = compose('^ {0,3}(?:<(script|pre|style|textarea)[\\s>][\\s\\S]*?(?:</\\1>[^\\n]*\\n*|$)|comment[^\\n]*(\\n+|$)|<\\?[\\s\\S]*?(?:\\?>[^\\n]*\\n*|$)|<![A-Z][\\s\\S]*?(?:>[^\\n]*\\n*|$)|<!\\[CDATA\\[[\\s\\S]*?(?:\\]\\]>[^\\n]*\\n*|$)|</?(tag)(?:[ \\t]+|\\n|/?>|$)[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$)|<(?!(?:script|pre|style|textarea)(?![a-z0-9-]))([a-z][a-z0-9-]*)(?:attribute)*? */?>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$)|</[a-z][a-z0-9-]*\\s*>(?=[ \\t]*(?:\\n|$))[\\s\\S]*?(?:(?:\\n[ \t]*)+\\n|$))', 'i')
  .replace('comment', commentPattern)
  .replace('tag', tagNames)
  .replace('attribute', / +[a-zA-Z:_][\w.:-]*(?: *= *"[^"\n]*"| *= *'[^'\n]*'| *= *[^\s"'=<>`]+)?/)
  .getRegex();

// The paragraph template: a first line, then more lines as long as the
// next line opens none of the interrupting constructs.
const paragraphTemplate = /^([^\n]+(?:\n(?!hr|heading|lheading|blockquote|fences|list|html|table|[ \t]+\n)[^\n]+)*)/;

function paragraphWith(listPattern) {
  return compose(paragraphTemplate)
    .replace('hr', blockHr)
    .replace('heading', ' {0,3}#{1,6}(?:\\s|$)')
    .replace('|lheading', '')
    .replace('|table', '')
    .replace('blockquote', ' {0,3}>')
    .replace('fences', ' {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)')
    .replace('list', listPattern)
    .replace('html', ' {0,3}(?:</?(?:tag)(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)')
    .replace('tag', tagNames)
    .getRegex();
}

// Setext heading template: lazy text lines that may not cross a blank
// line or a line opening another construct, then the = / - underline.
const setextTemplate = /^(?!bull |blockCode|fences|blockquote|heading|html|table)((?:.|\n(?!\s*?\n|bull |fences|blockquote|heading|hr|html|table))+?)\n {0,3}(=+|-+)[ \t]*(?:\n+|$)/;

function setextWith(tablePattern) {
  let builder = compose(setextTemplate)
    .replace(/bull/g, bulletPattern)
    .replace(/blockCode/g, /(?: {4}| {0,3}\t)/)
    .replace(/fences/g, / {0,3}(?:`{3,}|~{3,})/)
    .replace(/blockquote/g, / {0,3}>/)
    .replace(/heading/g, / {0,3}#{1,6}(?:\s|$)/)
    .replace(/hr/g, / {0,3}(?:(?:-[\t ]*){3,}|(?:_[ \t]*){3,}|(?:\*[ \t]*){3,})(?:\n+|$)/)
    .replace(/html/g, / {0,3}<[^\n>]+>\n/);
  if (tablePattern !== null) builder = builder.replace(/table/g, tablePattern);
  return builder.getRegex();
}

const blockTable = compose('^ *([^\\n ].*)\\n {0,3}((?:\\| *)?:?-+:? *(?:\\| *:?-+:? *)*(?:\\| *)?)(?:\\n((?:(?! *\\n|hr|heading|blockquote|code|fences|list|html).*(?:\\n|$))*)\\n*|$)')
  .replace('hr', blockHr)
  .replace('heading', ' {0,3}#{1,6}(?:\\s|$)')
  .replace('blockquote', ' {0,3}>')
  .replace('code', '(?: {4}| {0,3}\t)[^\\n]')
  .replace('fences', ' {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)')
  .replace('list', ' {0,3}(?:[*+-]|1[.)])[ \\t]')
  .replace('html', ' {0,3}(?:</?(?:tag)(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)')
  .replace('tag', tagNames)
  .getRegex();

const blockParagraph = compose(paragraphTemplate)
  .replace('hr', blockHr)
  .replace('heading', ' {0,3}#{1,6}(?:\\s|$)')
  .replace('|lheading', '')
  .replace('table', blockTable)
  .replace('blockquote', ' {0,3}>')
  .replace('fences', ' {0,3}(?:`{3,}(?=[^`\\n]*(?:\\n|$))|~~~)[^\\n]*(?:\\n|$)')
  .replace('list', ' {0,3}(?:[*+-]|1[.)])[ \\t]+[^ \\t\\n]')
  .replace('html', ' {0,3}(?:</?(?:tag)(?: +|\\n|/?>)|<(?:(?:script|pre|style|textarea)(?:[\\s>]|$)|!--)|<\\?|<![A-Za-z]|<!\\[CDATA\\[)')
  .replace('tag', tagNames)
  .getRegex();

const blockLheading = setextWith(/ {0,3}\|?(?:[:\- ]*\|)+[\:\- ]*\n/);

const blockBlockquote = compose('^( {0,3}> ?(?:(?![ \t]*(?:\\n|$))(paragraph)|[^\\n]*)(?:\\n|$))+')
  .replace('paragraph', paragraphWith(/ {0,3}(?:[*+-]|\d{1,9}[.)])(?:[ \t]|\n|$)/))
  .getRegex();

const blockText = /^[^\n]+/;

const block = {
  newline: blockNewline,
  code: blockCode,
  fences: blockFences,
  heading: blockHeading,
  hr: blockHr,
  blockquote: blockBlockquote,
  def: blockDef,
  list: blockList,
  html: blockHtml,
  lheading: blockLheading,
  paragraph: blockParagraph,
  table: blockTable,
  text: blockText,
};

// ---------------------------------------------------------------------
// Inline grammar (GFM variant).
// ---------------------------------------------------------------------

const punctClass = /[\p{P}\p{S}]/u;
const notPunctSpaceClass = /[^\s\p{P}\p{S}]/u;
const punctSpaceClass = /[\s\p{P}\p{S}]/u;
const gfmPunctClass = /(?!~)[\p{P}\p{S}]/u;
const gfmNotPunctSpaceClass = /(?:[^\s\p{P}\p{S}]|~)/u;
const gfmPunctSpaceClass = /(?!~)[\s\p{P}\p{S}]/u;

const inlineEscape = /^\\([!"#$%&'()*+,\-./:;<=>?@\[\]\\^_`{|}~])/;
const inlineCode = /^(`+)([^`]|[^`][\s\S]*?[^`])\1(?!`)/;
const inlineBr = /^( {2,}|\\)\n(?!\s*$)[ \t]*/;

const inlineAutolink = compose(/^<(scheme:[^\s\x00-\x1f<>]*|email)>/)
  .replace('scheme', /[a-zA-Z][a-zA-Z0-9+.-]{1,31}/)
  .replace('email', /[a-zA-Z0-9.!#$%&'*+/=?^_`{|}~-]+(@)[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?(?:\.[a-zA-Z0-9](?:[a-zA-Z0-9-]{0,61}[a-zA-Z0-9])?)+(?![-_])/)
  .getRegex();

const closedCommentPattern = compose(commentPattern)
  .replace('(?:-->|$)', '-->')
  .getRegex();

const inlineTag = compose('^comment|^</[a-zA-Z][a-zA-Z0-9-]*\\s*>|^<[a-zA-Z][a-zA-Z0-9-]*(?:attribute)*?\\s*/?>|^<\\?[\\s\\S]*?\\?>|^<![a-zA-Z]+\\s[\\s\\S]*?>|^<!\\[CDATA\\[[\\s\\S]*?\\]\\]>')
  .replace('comment', closedCommentPattern)
  .replace('attribute', /\s+[a-zA-Z:_][\w.:-]*(?:\s*=\s*"[^"]*"|\s*=\s*'[^']*'|\s*=\s*[^\s"'=<>`]+)?/)
  .getRegex();

const bracketSpan = /\[(?:\\[\s\S]|[^\[\]\\])*\]/;
const linkLabelInline = compose(/(?:\[(?:brackets|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\])|[^\[\]\\`])*?/)
  .replace('brackets', bracketSpan)
  .getRegex();

const inlineLink = compose(/^!?\[(label)\]\([ \t\n]*(href)(?:(?:[ \t]+(?:\n[ \t]*)?|\n[ \t]*)(title))?[ \t\n]*\)/)
  .replace('label', linkLabelInline)
  .replace('href', /<(?:\\.|[^\n<>\\])+>|[^ \t\n\x00-\x1f]+|(?=\))/)
  .replace('title', /"(?:\\[\s\S]|[^"\\])*"|'(?:\\[\s\S]|[^'\\])*'|\((?:\\[\s\S]|[^)\\])*\)/)
  .getRegex();

const inlineReflink = compose(/^!?\[(label)\]\[(ref)\]/)
  .replace('label', linkLabelInline)
  .replace('ref', linkLabelPattern)
  .getRegex();

const inlineNolink = compose(/^!?\[(ref)\](?:\[\])?/)
  .replace('ref', linkLabelPattern)
  .getRegex();

const searchLabel = compose(/(?:[^\[\]\\`]*(?:\[(?:brackets|\\[\s\S]|[^\[\]\\])*\]|\\[\s\S]|`+(?!`)[^`]*?`+(?!`)|``+(?=\]))){0,999}?[^\[\]\\`]*?/)
  .replace('brackets', bracketSpan)
  .getRegex();
const searchRef = /(?!\s*\])(?:\\[\s\S]|[^\[\]\\]){1,999}/;

const inlineReflinkSearch = compose('reflink|nolink(?!\\()', 'g')
  .replace('reflink', compose(/^!?\[(label)\]\[(ref)\]/).replace('label', searchLabel).replace('ref', searchRef).getRegex())
  .replace('nolink', compose(/^!?\[(ref)\](?:\[\])?/).replace('ref', searchRef).getRegex())
  .getRegex();

const inlineBlockSkip = compose(/link|precode-code|html/, 'g')
  .replace('link', /\[(?:[^\[\]`]|(?<a>`+)[^`]+\k<a>(?!`))*?\]\((?:\\[\s\S]|[^\\\(\)]|\((?:\\[\s\S]|[^\\\(\)])*\))*\)/)
  .replace('precode-', lookbehindWorks ? '(?<!`)()' : '(^^|[^`])')
  .replace('code', /(?<b>`+)[^`]+\k<b>(?!`)/)
  .replace('html', /<(?! )[^<>]*?>/)
  .getRegex();

const emStrongLDelimTemplate = /^(?:\*+(?:((?!\*)punct)|([^\s*]))?)|^_+(?:((?!_)punct)|([^\s_]))?/;
const inlineEmStrongLDelim = compose(emStrongLDelimTemplate, 'u')
  .replace(/punct/g, gfmPunctClass)
  .getRegex();

const rDelimAstTemplate = '^[^_*]*?__[^_*]*?\\*[^_*]*?(?=__)|[^*]+(?=[^*])|(?!\\*)punct(\\*+)(?=[\\s]|$)|notPunctSpace(\\*+)(?!\\*)(?=punctSpace|$)|(?!\\*)punctSpace(\\*+)(?=notPunctSpace)|[\\s](\\*+)(?!\\*)(?=punct)|(?!\\*)punct(\\*+)(?!\\*)(?=punct)|notPunctSpace(\\*+)(?=notPunctSpace)';
const inlineEmStrongRDelimAst = compose(rDelimAstTemplate, 'gu')
  .replace(/notPunctSpace/g, gfmNotPunctSpaceClass)
  .replace(/punctSpace/g, gfmPunctSpaceClass)
  .replace(/punct/g, gfmPunctClass)
  .getRegex();

const rDelimUndTemplate = '^[^_*]*?\\*\\*[^_*]*?_[^_*]*?(?=\\*\\*)|[^_]+(?=[^_])|(?!_)punct(_+)(?=[\\s]|$)|notPunctSpace(_+)(?!_)(?=punctSpace|$)|(?!_)punctSpace(_+)(?=notPunctSpace)|[\\s](_+)(?!_)(?=punct)|(?!_)punct(_+)(?!_)(?=punct)';
const inlineEmStrongRDelimUnd = compose(rDelimUndTemplate, 'gu')
  .replace(/notPunctSpace/g, notPunctSpaceClass)
  .replace(/punctSpace/g, punctSpaceClass)
  .replace(/punct/g, punctClass)
  .getRegex();

const inlineDelLDelim = compose(/^~~?(?:((?!~)punct)|[^\s~])/, 'u')
  .replace(/punct/g, punctClass)
  .getRegex();

const rDelimDelTemplate = '^[^~]+(?=[^~])|(?!~)punct(~~?)(?=[\\s]|$)|notPunctSpace(~~?)(?!~)(?=punctSpace|$)|(?!~)punctSpace(~~?)(?=notPunctSpace)|[\\s](~~?)(?!~)(?=punct)|(?!~)punct(~~?)(?!~)(?=punct)|notPunctSpace(~~?)(?=notPunctSpace)';
const inlineDelRDelim = compose(rDelimDelTemplate, 'gu')
  .replace(/notPunctSpace/g, notPunctSpaceClass)
  .replace(/punctSpace/g, punctSpaceClass)
  .replace(/punct/g, punctClass)
  .getRegex();

const protocolPattern = /[hH][tT][tT][pP][sS]?|[fF][tT][pP]/;
const emailCorePattern = /[A-Za-z0-9._+-]+@[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])/;
const emailProtocolPattern = compose(/(?:mailto:email|xmpp:email(?:\/[A-Za-z0-9@.]+)?)/)
  .replace(/email/g, emailCorePattern)
  .getRegex();

const inlineUrl = compose(/^emailProtocol|^((?:protocol):\/\/|www\.)(?:[a-zA-Z0-9\-]+\.?)+[^\s<]*|^email/)
  .replace('emailProtocol', emailProtocolPattern)
  .replace('protocol', protocolPattern)
  .replace('email', /[A-Za-z0-9._+-]+(@)[a-zA-Z0-9-_]+(?:\.[a-zA-Z0-9-_]*[a-zA-Z0-9])+(?![\w-])/)
  .getRegex();

const inlineBackpedal = /(?:[^?!.,:;*_'"~()&]+|\([^)]*\)|&(?![a-zA-Z0-9]+;$)|[?!.,:;*_'"~)]+(?!$))+/;

const inlineText = compose(/^(?:[^a-zA-Z0-9](?=emailProtocol)|(`+|~+|[^`~])(?:(?=[`~])|(?= {2,}\n)|(?=[a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-]+@)|[\s\S]*?(?:(?=[\\<!\[`*~_]|\b_|protocol:\/\/|wwwStart|$)|[^ ](?= {2,}\n)|[^a-zA-Z0-9](?=emailProtocol)|[^a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-](?=[a-zA-Z0-9.!#$%&'*+\/=?_`{\|}~-]+@))))/)
  .replace('protocol', protocolPattern)
  .replace(/emailProtocol/g, /(?:mailto|xmpp):/)
  .replace('wwwStart', lookbehindWorks ? '(?<![^\\s*_~(])www\\.' : 'www\\.')
  .getRegex();

const inlinePunctuation = compose(/^((?![*_])punctSpace)/, 'u')
  .replace(/punctSpace/g, punctSpaceClass)
  .getRegex();

const inlineAnyPunctuation = compose(/\\(punct)/, 'gu')
  .replace(/punct/g, punctClass)
  .getRegex();

const inlineAnyPunctuationOutsideCode = compose(/(`+)(?:[^`]|[^`][\s\S]*?[^`])\1(?!`)|`+|\\(punct)/, 'gu')
  .replace(/punct/g, punctClass)
  .getRegex();

const inline = {
  escape: inlineEscape,
  code: inlineCode,
  br: inlineBr,
  autolink: inlineAutolink,
  tag: inlineTag,
  link: inlineLink,
  reflink: inlineReflink,
  nolink: inlineNolink,
  reflinkSearch: inlineReflinkSearch,
  blockSkip: inlineBlockSkip,
  emStrongLDelim: inlineEmStrongLDelim,
  emStrongRDelimAst: inlineEmStrongRDelimAst,
  emStrongRDelimUnd: inlineEmStrongRDelimUnd,
  delLDelim: inlineDelLDelim,
  delRDelim: inlineDelRDelim,
  url: inlineUrl,
  _backpedal: inlineBackpedal,
  text: inlineText,
  punctuation: inlinePunctuation,
  anyPunctuation: inlineAnyPunctuation,
  anyPunctuationOutsideCode: inlineAnyPunctuationOutsideCode,
};

// ---------------------------------------------------------------------
// Lexer state. One instance per parse() call: nothing is kept between
// calls, so parse stays stateless per case.
// ---------------------------------------------------------------------

function createLexer() {
  return {
    links: Object.create(null),
    queue: [], // {src, tokens} inline work queued by block tokens
    maskStack: [], // delimiter-scan masks of enclosing inline passes
    state: {
      inLink: false,
      inRawBlock: false,
      linkEmitted: false,
      linkParenPossible: true,
      top: true,
    },
  };
}

// Queue a block token's inner text for the inline pass; returns the
// (still empty) token array the inline pass will fill in place.
function queueInline(lex, src, tokens) {
  lex.queue.push({ src, tokens });
  return tokens;
}

// ---------------------------------------------------------------------
// Block tokenizers. Each returns a token or undefined, like marked's.
// ---------------------------------------------------------------------

function tokSpace(lex, src) {
  const cap = block.newline.exec(src);
  if (cap && cap[0].length > 0) return { type: 'space', raw: cap[0] };
}

function tokCode(lex, src) {
  const cap = block.code.exec(src);
  if (!cap) return;
  const raw = trimTrailingBlankLines(cap[0]);
  return {
    type: 'code',
    raw,
    codeBlockStyle: 'indented',
    text: raw.replace(other.codeRemoveIndent, ''),
  };
}

function tokFences(lex, src) {
  const cap = block.fences.exec(src);
  if (!cap) return;
  const raw = cap[0];
  let text = cap[3] || '';
  const indent = raw.match(other.indentCodeCompensation);
  if (indent !== null) {
    const width = indent[1].length;
    text = text
      .split('\n')
      .map((line) => {
        const lead = line.match(other.beginningSpace);
        if (lead === null) return line;
        return line.slice(Math.min(lead[0].length, width));
      })
      .join('\n');
  }
  return {
    type: 'code',
    raw,
    lang: cap[2] ? cap[2].trim().replace(inline.anyPunctuation, '$1') : cap[2],
    text,
  };
}

function tokHeading(lex, src) {
  const cap = block.heading.exec(src);
  if (!cap) return;
  let text = cap[2].trim();
  if (other.endingHash.test(text)) {
    const stripped = trimRightChar(text, '#');
    if (!stripped || other.endingSpaceTabChar.test(stripped)) text = stripped.trim();
  }
  const tokens = [];
  queueInline(lex, text, tokens);
  return {
    type: 'heading',
    raw: trimRightChar(cap[0], '\n'),
    depth: cap[1].length,
    text,
    tokens,
  };
}

function tokHr(lex, src) {
  const cap = block.hr.exec(src);
  if (cap) return { type: 'hr', raw: trimRightChar(cap[0], '\n') };
}

function tokBlockquote(lex, src) {
  const cap = block.blockquote.exec(src);
  if (!cap) return;
  let lines = trimRightChar(cap[0], '\n').split('\n');
  let rawAll = '';
  let textAll = '';
  const tokens = [];
  while (lines.length > 0) {
    let hasMarker = false;
    const passLines = [];
    let p;
    for (p = 0; p < lines.length; p++) {
      if (other.blockquoteStart.test(lines[p])) {
        passLines.push(lines[p]);
        hasMarker = true;
      } else if (!hasMarker) {
        passLines.push(lines[p]);
      } else break;
    }
    lines = lines.slice(p);
    const joined = passLines.join('\n');
    const stripped = joined
      .replace(other.blockquoteMarkerWhitespace, (m, marker, ws) => marker + expandTabs(ws, marker.length))
      .replace(other.blockquoteSetextReplace, '\n    $1')
      .replace(other.blockquoteSetextReplace2, '');
    rawAll = rawAll ? rawAll + '\n' + joined : joined;
    textAll = textAll ? textAll + '\n' + stripped : stripped;
    const savedTop = lex.state.top;
    lex.state.top = true;
    blockTokens(lex, stripped, tokens, true);
    lex.state.top = savedTop;
    if (lines.length === 0) break;
    const last = tokens.at(-1);
    if (
      last?.type === 'code' ||
      last?.type === 'heading' ||
      last?.type === 'hr' ||
      last?.type === 'html' ||
      last?.type === 'table'
    ) {
      break;
    }
    if (last?.type === 'blockquote') {
      const rest0 = lines.join('\n');
      const mergedSrc = last.raw + '\n' + rest0.replace(other.blockquoteSetextReplace2, '');
      const merged = tokBlockquote(lex, mergedSrc);
      tokens[tokens.length - 1] = merged;
      const rest = mergedSrc.substring(merged.raw.length).replace(/^\n/, '');
      const restLines = rest ? rest.split('\n').length : 0;
      const consumed = restLines ? lines.slice(0, -restLines) : lines;
      if (consumed.length > 0) rawAll += '\n' + consumed.join('\n');
      textAll = textAll.substring(0, textAll.length - last.text.length) + merged.text;
      lines = lines.slice(consumed.length);
      if (lines.length > 0 && other.blockquoteStart.test(lines[0])) continue;
      break;
    } else if (last?.type === 'list') {
      const mergedSrc = last.raw + '\n' + lines.join('\n');
      const merged = tokList(lex, mergedSrc);
      tokens[tokens.length - 1] = merged;
      const extra =
        merged.raw.length > last.raw.length
          ? mergedSrc.slice(last.raw.length + 1, merged.raw.length).split('\n').length
          : 0;
      if (extra > 0) {
        const taken = lines.slice(0, extra).join('\n');
        rawAll += '\n' + taken;
        textAll += '\n' + taken;
      }
      lines = lines.slice(extra);
      continue;
    }
  }
  return { type: 'blockquote', raw: rawAll, tokens, text: textAll };
}

function tokList(lex, src) {
  let cap = block.list.exec(src);
  if (!cap) return;
  const origin = src;
  const consumed = () => origin.length - src.length;
  const bull = cap[1].trim();
  const ordered = bull.length > 1;
  const list = {
    type: 'list',
    raw: '',
    ordered,
    start: ordered ? +bull.slice(0, -1) : '',
    loose: false,
    items: [],
  };
  const bulletRe = ordered ? `\\d{1,9}\\${bull.slice(-1)}` : `\\${bull}`;
  const itemRe = other.listItemRegex(bulletRe);
  let blankSeen = false;
  while (src) {
    let itemEnded = false;
    const itemParts = [];
    cap = itemRe.exec(src);
    if (!cap || block.hr.test(src)) break;
    const itemStart = consumed();
    src = src.substring(cap[0].length);
    const cap2Nl = cap[2].indexOf('\n');
    const firstLine = cap2Nl === -1 ? cap[2] : cap[2].slice(0, cap2Nl);
    const bulletLen = cap[1].length;
    const fl0 = firstLine.charCodeAt(0);
    let content =
      fl0 === 32 || fl0 === 9
        ? firstLine.replace(other.leadingSpaceTab, (m) => expandTabs(m, bulletLen))
        : firstLine;
    const srcNl = src.indexOf('\n');
    let nextLine = srcNl === -1 ? src : src.slice(0, srcNl);
    let firstBlank = !content.trim();
    let indent = 0;
    if (firstBlank) {
      indent = bulletLen + 1;
      itemParts.push('');
    } else {
      indent = content.search(other.nonSpaceChar);
      if (indent > 4) indent = 1;
      itemParts.push(content.slice(indent));
      indent += bulletLen;
    }
    if (firstBlank && other.blankLine.test(nextLine)) {
      src = src.substring(nextLine.length + 1);
      itemEnded = true;
    }
    if (!itemEnded) {
      const nextBullet = other.nextBulletRegex(indent);
      const hrBegin = other.hrRegex(indent);
      const fencesBegin = other.fencesBeginRegex(indent);
      const headingBegin = other.headingBeginRegex(indent);
      const htmlBegin = other.htmlBeginRegex(indent);
      const quoteBegin = other.blockquoteBeginRegex(indent);
      // Every begin pattern is `^ {0,R}` plus one construct character, so
      // a line whose first non-space character (within R spaces) is not a
      // construct character cannot match any of them: gate the regexes.
      const maxSp = Math.max(0, Math.min(3, indent - 1));
      const startsConstruct = (s) => {
        let p = 0;
        while (p <= maxSp && s[p] === ' ') p++;
        if (p > maxSp) return false;
        const c = s[p];
        if (c === '`' || c === '~') return fencesBegin.test(s);
        if (c === '#') return headingBegin.test(s);
        if (c === '<') return htmlBegin.test(s);
        if (c === '>') return quoteBegin.test(s);
        if (c === '*' || c === '-') return nextBullet.test(s) || hrBegin.test(s);
        if (c === '+') return nextBullet.test(s);
        if (c === '_') return hrBegin.test(s);
        if (c >= '0' && c <= '9') return nextBullet.test(s);
        return false;
      };
      const startsLazyBreak = (s) => {
        let p = 0;
        while (p <= maxSp && s[p] === ' ') p++;
        if (p > maxSp) return false;
        const c = s[p];
        if (c === '`' || c === '~') return fencesBegin.test(s);
        if (c === '#') return headingBegin.test(s);
        if (c === '<') return htmlBegin.test(s);
        if (c === '*' || c === '-' || c === '_') return hrBegin.test(s);
        return false;
      };
      while (src) {
        const nl = src.indexOf('\n');
        const line = nl === -1 ? src : src.slice(0, nl);
        nextLine = line;
        const c0 = line.charCodeAt(0);
        const expanded =
          c0 === 32 || c0 === 9 ? line.replace(other.leadingSpaceTab, (m) => expandTabs(m)) : line;
        if (startsConstruct(line)) {
          break;
        }
        const blank = !line.trim();
        const sliced = expanded.slice(indent);
        if (expanded.search(other.nonSpaceChar) >= indent || blank) {
          itemParts.push(sliced);
        } else {
          if (
            firstBlank ||
            content.replace(other.tabCharGlobal, '    ').search(other.nonSpaceChar) >= 4 ||
            startsLazyBreak(content)
          ) {
            break;
          }
          const lazy =
            /^ {0,3}(?:=+|-+) *$/.test(line) && block.lheading.test(`${content}\n${line}`)
              ? '    ' + expanded.replace(/^ {0,3}/, '')
              : line;
          itemParts.push(lazy);
        }
        firstBlank = blank;
        src = nl === -1 ? '' : src.substring(nl + 1);
        content = sliced;
      }
    }
    const itemText = itemParts.join('\n');
    const itemRaw = origin.slice(itemStart, consumed());
    if (!list.loose) {
      if (blankSeen) list.loose = true;
      else if (other.doubleBlankLine.test(itemRaw)) blankSeen = true;
    }
    list.items.push({
      type: 'list_item',
      raw: itemRaw,
      task: other.listIsTask.test(itemText),
      loose: false,
      text: itemText,
      tokens: [],
    });
  }
  const lastItem = list.items.at(-1);
  if (lastItem) {
    lastItem.raw = lastItem.raw.trimEnd();
    lastItem.text = lastItem.text.trimEnd();
  } else return;
  list.raw = origin.slice(0, consumed()).trimEnd();
  for (const item of list.items) {
    lex.state.top = false;
    item.tokens = blockTokens(lex, item.text, [], false);
    if (!list.loose) {
      const spaces = item.tokens.filter((t) => t.type === 'space');
      list.loose = spaces.length > 0 && spaces.some((t) => other.anyLine.test(t.raw));
    }
  }
  for (const item of list.items) {
    const first = item.tokens[0];
    if (item.task && (first?.type === 'text' || first?.type === 'paragraph')) {
      item.text = item.text.replace(other.listReplaceTask, '');
      first.raw = first.raw.replace(other.listReplaceTask, '');
      first.text = first.text.replace(other.listReplaceTask, '');
      for (let g = lex.queue.length - 1; g >= 0; g--) {
        if (other.listIsTask.test(lex.queue[g].src)) {
          lex.queue[g].src = lex.queue[g].src.replace(other.listReplaceTask, '');
          break;
        }
      }
      const checkboxMatch = other.listTaskCheckbox.exec(item.raw);
      if (checkboxMatch) {
        const checkbox = {
          type: 'checkbox',
          raw: checkboxMatch[0] + ' ',
          checked: checkboxMatch[0] !== '[ ]',
        };
        item.checked = checkbox.checked;
        if (list.loose) {
          const head = item.tokens[0];
          if (
            head &&
            (head.type === 'paragraph' || head.type === 'text') &&
            'tokens' in head &&
            head.tokens
          ) {
            head.raw = checkbox.raw + head.raw;
            head.text = checkbox.raw + head.text;
            head.tokens.unshift(checkbox);
          } else {
            item.tokens.unshift({ type: 'paragraph', raw: checkbox.raw, text: checkbox.raw, tokens: [checkbox] });
          }
        } else {
          item.tokens.unshift(checkbox);
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

function tokHtml(lex, src) {
  const cap = block.html.exec(src);
  if (!cap) return;
  const raw = trimTrailingBlankLines(cap[0]);
  return {
    type: 'html',
    block: true,
    raw,
    pre: cap[1] === 'pre' || cap[1] === 'script' || cap[1] === 'style',
    text: raw,
  };
}

function tokDef(lex, src) {
  const cap = block.def.exec(src);
  if (!cap) return;
  if (!other.startAngleBracket.test(cap[2]) && findClosingBracket(cap[2], '()') !== -1) return;
  return {
    type: 'def',
    tag: normalizeLabel(cap[1]),
    raw: trimRightChar(cap[0], '\n'),
    href: cap[2]
      ? cap[2].replace(other.hrefBrackets, '$1').replace(inline.anyPunctuation, '$1')
      : '',
    title: cap[3]
      ? cap[3].substring(1, cap[3].length - 1).replace(inline.anyPunctuation, '$1')
      : cap[3],
  };
}

function tokTable(lex, src) {
  const cap = block.table.exec(src);
  if (!cap || !other.tableDelimiter.test(cap[2])) return;
  const headerCells = splitCells(cap[1]);
  const alignRow = cap[2].replace(other.tableAlignChars, '').split('|');
  const bodyRows = cap[3]?.trim()
    ? cap[3].replace(other.tableRowBlankLine, '').split('\n')
    : [];
  if (headerCells.length !== alignRow.length) return;
  const table = {
    type: 'table',
    raw: trimRightChar(cap[0], '\n'),
    header: [],
    align: [],
    rows: [],
  };
  for (const cell of alignRow) {
    if (other.tableAlignRight.test(cell)) table.align.push('right');
    else if (other.tableAlignCenter.test(cell)) table.align.push('center');
    else if (other.tableAlignLeft.test(cell)) table.align.push('left');
    else table.align.push(null);
  }
  for (let i = 0; i < headerCells.length; i++) {
    const tokens = [];
    queueInline(lex, headerCells[i], tokens);
    table.header.push({ text: headerCells[i], tokens, header: true, align: table.align[i] });
  }
  for (const row of bodyRows) {
    table.rows.push(
      splitCells(row, table.header.length).map((cell, j) => {
        const tokens = [];
        queueInline(lex, cell, tokens);
        return { text: cell, tokens, header: false, align: table.align[j] };
      }),
    );
  }
  return table;
}

function tokLheading(lex, src) {
  const cap = block.lheading.exec(src);
  if (!cap) return;
  const text = cap[1].trim();
  const tokens = [];
  queueInline(lex, text, tokens);
  return {
    type: 'heading',
    raw: trimRightChar(cap[0], '\n'),
    depth: cap[2].charAt(0) === '=' ? 1 : 2,
    text,
    tokens,
  };
}

// Paragraph collection, line by line. The composed paragraph regex
// accepts a first line, then more lines while the next line opens none
// of the interrupting constructs; these checks mirror its lookahead
// alternatives one for one, gated on the line's first characters.
const paraDelimRe = /^ {0,3}(?:\| *)?:?-+:? *(?:\| *:?-+:? *)*(?:\| *)?$/;
const paraListRe = /^ {0,3}(?:[*+-]|1[.)])[ \t]+[^ \t\n]/;
const paraFencesRe = /^ {0,3}(?:`{3,}[^`]*$|~{3,})/;
const paraBlankRe = /^[ \t]+$/;

function paragraphLineStops(line, nextLine, hasTrailingNl) {
  if (hasTrailingNl && paraBlankRe.test(line)) return true;
  let p = 0;
  while (p <= 3 && line[p] === ' ') p++;
  if (p <= 3) {
    const c = line[p];
    if (c === '#') {
      if (other.headingBeginRegex(4).test(line)) return true;
    } else if (c === '>') {
      return true;
    } else if (c === '`' || c === '~') {
      if (paraFencesRe.test(line)) return true;
    } else if (c === '<') {
      if (other.htmlBeginRegex(4).test(line)) return true;
    } else if (c === '*' || c === '+' || c === '-') {
      if (other.hrRegex(4).test(line) || paraListRe.test(line)) return true;
    } else if (c === '_') {
      if (other.hrRegex(4).test(line)) return true;
    } else if (c === '1') {
      if (paraListRe.test(line)) return true;
    }
  }
  // A table interrupts when this line is a header (some non-space
  // character) and the next line is a delimiter row.
  if (nextLine !== null && /[^ ]/.test(line) && paraDelimRe.test(nextLine)) return true;
  return false;
}

function tokParagraph(lex, src) {
  const firstNl = src.indexOf('\n');
  const firstEnd = firstNl === -1 ? src.length : firstNl;
  if (firstEnd === 0) return;
  let pos = firstEnd;
  while (pos < src.length) {
    const lineStart = pos + 1;
    if (lineStart >= src.length) break;
    let lineEnd = src.indexOf('\n', lineStart);
    if (lineEnd === -1) lineEnd = src.length;
    if (lineEnd === lineStart) break; // an empty line ends the paragraph
    const line = src.slice(lineStart, lineEnd);
    let nextLine = null;
    if (lineEnd < src.length) {
      const nStart = lineEnd + 1;
      let nEnd = src.indexOf('\n', nStart);
      if (nEnd === -1) nEnd = src.length;
      nextLine = src.slice(nStart, nEnd);
    }
    if (paragraphLineStops(line, nextLine, lineEnd < src.length)) break;
    pos = lineEnd;
  }
  const raw = src.slice(0, pos);
  const tokens = [];
  queueInline(lex, raw, tokens);
  return { type: 'paragraph', raw, text: raw, tokens };
}

function tokText(lex, src) {
  const cap = block.text.exec(src);
  if (!cap) return;
  const tokens = [];
  queueInline(lex, cap[0], tokens);
  return { type: 'text', raw: cap[0], text: cap[0], tokens };
}

// ---------------------------------------------------------------------
// The block pass. marked tries every block rule at every position; here
// a cheap scan of the first line gates the rules whose pattern cannot
// match, and the rest run in marked's own order, so the first matching
// rule is the same one marked would pick.
// ---------------------------------------------------------------------

function firstLineInfo(src) {
  const nl = src.indexOf('\n');
  const line = nl === -1 ? src : src.slice(0, nl);
  let spaces = 0;
  while (spaces < line.length && line[spaces] === ' ') spaces++;
  let blank = true;
  for (let i = 0; i < line.length; i++) {
    const c = line[i];
    if (c !== ' ' && c !== '\t') {
      blank = false;
      break;
    }
  }
  return { line, spaces, blank, ch: spaces <= 3 ? line[spaces] : undefined };
}

// Could a setext underline sit under the text starting here? Scans the
// run of non-blank lines for an underline line; the setext pattern can
// never cross a blank line, so if none shows up it cannot match.
function setextPossible(src) {
  let pos = src.indexOf('\n');
  if (pos === -1) return false;
  pos++;
  while (pos < src.length) {
    let end = src.indexOf('\n', pos);
    if (end === -1) end = src.length;
    const line = src.slice(pos, end);
    if (/^ {0,3}(=+|-+)[ \t]*$/.test(line)) return true;
    if (!/[^ \t]/.test(line)) return false;
    if (end === src.length) return false;
    pos = end + 1;
  }
  return false;
}

function tablePossible(info, src) {
  if (info.blank) return false;
  const firstNl = src.indexOf('\n');
  if (firstNl === -1) return false;
  let end = src.indexOf('\n', firstNl + 1);
  if (end === -1) end = src.length;
  const second = src.slice(firstNl + 1, end);
  return /^ {0,3}[|: -]*$/.test(second) && second.includes('-');
}

function listPossible(info) {
  const { line, spaces } = info;
  if (spaces > 3) return false;
  const c = line[spaces];
  if (c === '*' || c === '+' || c === '-') {
    const next = line[spaces + 1];
    return next === undefined || next === ' ' || next === '\t';
  }
  if (c >= '0' && c <= '9') {
    let i = spaces;
    let digits = 0;
    while (i < line.length && line[i] >= '0' && line[i] <= '9') {
      i++;
      digits++;
    }
    if (digits > 9) return false;
    if (line[i] !== '.' && line[i] !== ')') return false;
    const next = line[i + 1];
    return next === undefined || next === ' ' || next === '\t';
  }
  return false;
}

function blockTokens(lex, src, tokens, inQuote) {
  let lastLen = Infinity;
  while (src) {
    if (src.length < lastLen) lastLen = src.length;
    else break; // nothing consumed last round: bail out like marked does
    const info = firstLineInfo(src);
    const ch = info.ch;
    let tok;

    if (info.blank && (tok = tokSpace(lex, src))) {
      src = src.substring(tok.raw.length);
      const prev = tokens.at(-1);
      if (tok.raw.length === 1 && prev !== undefined) prev.raw += '\n';
      else tokens.push(tok);
      continue;
    }
    if (
      !info.blank &&
      (info.spaces >= 4 || src[0] === '\t' || (info.spaces >= 1 && src[info.spaces] === '\t')) &&
      (tok = tokCode(lex, src))
    ) {
      src = src.substring(tok.raw.length);
      const prev = tokens.at(-1);
      if (prev?.type === 'paragraph' || prev?.type === 'text') {
        prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + tok.raw;
        prev.text += '\n' + tok.text;
        lex.queue.at(-1).src = prev.text;
      } else tokens.push(tok);
      continue;
    }
    if (
      info.spaces <= 3 &&
      (ch === '`' || ch === '~') &&
      src[info.spaces + 1] === ch &&
      src[info.spaces + 2] === ch &&
      (tok = tokFences(lex, src))
    ) {
      src = src.substring(tok.raw.length);
      tokens.push(tok);
      continue;
    }
    if (info.spaces <= 3 && ch === '#' && (tok = tokHeading(lex, src))) {
      src = src.substring(tok.raw.length);
      tokens.push(tok);
      continue;
    }
    if (
      info.spaces <= 3 &&
      (ch === '-' || ch === '_' || ch === '*') &&
      (tok = tokHr(lex, src))
    ) {
      src = src.substring(tok.raw.length);
      tokens.push(tok);
      continue;
    }
    if (info.spaces <= 3 && ch === '>' && (tok = tokBlockquote(lex, src))) {
      src = src.substring(tok.raw.length);
      tokens.push(tok);
      continue;
    }
    if (listPossible(info) && (tok = tokList(lex, src))) {
      src = src.substring(tok.raw.length);
      tokens.push(tok);
      continue;
    }
    if (info.spaces <= 3 && ch === '<' && (tok = tokHtml(lex, src))) {
      src = src.substring(tok.raw.length);
      tokens.push(tok);
      continue;
    }
    if (info.spaces <= 3 && ch === '[' && (tok = tokDef(lex, src))) {
      src = src.substring(tok.raw.length);
      const prev = tokens.at(-1);
      if (prev?.type === 'paragraph' || prev?.type === 'text') {
        prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + tok.raw;
        prev.text += '\n' + tok.raw;
        lex.queue.at(-1).src = prev.text;
      } else {
        if (!lex.links[tok.tag]) lex.links[tok.tag] = { href: tok.href, title: tok.title };
        tokens.push(tok);
      }
      continue;
    }
    if (tablePossible(info, src) && (tok = tokTable(lex, src))) {
      src = src.substring(tok.raw.length);
      tokens.push(tok);
      continue;
    }
    if (setextPossible(src) && (tok = tokLheading(lex, src))) {
      src = src.substring(tok.raw.length);
      tokens.push(tok);
      continue;
    }
    if (lex.state.top && (tok = tokParagraph(lex, src))) {
      const prev = tokens.at(-1);
      if (inQuote && prev?.type === 'paragraph') {
        prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + tok.raw;
        prev.text += '\n' + tok.text;
        lex.queue.pop();
        lex.queue.at(-1).src = prev.text;
      } else tokens.push(tok);
      src = src.substring(tok.raw.length);
      continue;
    }
    if ((tok = tokText(lex, src))) {
      src = src.substring(tok.raw.length);
      const prev = tokens.at(-1);
      if (prev?.type === 'text') {
        prev.raw += (prev.raw.endsWith('\n') ? '' : '\n') + tok.raw;
        prev.text += '\n' + tok.text;
        lex.queue.pop();
        lex.queue.at(-1).src = prev.text;
      } else tokens.push(tok);
      continue;
    }
    if (src) break;
  }
  lex.state.top = true;
  return tokens;
}

// ---------------------------------------------------------------------
// Inline tokenizers.
// ---------------------------------------------------------------------

function tokEscape(lex, src) {
  const cap = inline.escape.exec(src);
  if (cap) return { type: 'escape', raw: cap[0], text: cap[1] };
}

function tokTag(lex, src) {
  const cap = inline.tag.exec(src);
  if (!cap) return;
  if (!lex.state.inLink && other.startATag.test(cap[0])) lex.state.inLink = true;
  else if (lex.state.inLink && other.endATag.test(cap[0])) lex.state.inLink = false;
  if (!lex.state.inRawBlock && other.startPreScriptTag.test(cap[0])) lex.state.inRawBlock = true;
  else if (lex.state.inRawBlock && other.endPreScriptTag.test(cap[0])) lex.state.inRawBlock = false;
  return {
    type: 'html',
    raw: cap[0],
    inLink: lex.state.inLink,
    inRawBlock: lex.state.inRawBlock,
    block: false,
    text: cap[0],
  };
}

// True when a tag inside a would-be link label reaches past the label:
// the label's ] would be swallowed, so the link does not count.
function labelSwallowsTag(src, label, offset) {
  if (!label.includes('<')) return false;
  for (let s = 0; s < label.length; s++) {
    if (label[s] === '\\') {
      s++;
      continue;
    }
    if (label[s] === '`') {
      const code = inline.code.exec(label.slice(s));
      if (code) {
        s += code[0].length - 1;
        continue;
      }
    }
    if (label[s] !== '<') continue;
    const rest = src.slice(offset + s);
    const m = inline.tag.exec(rest) || inline.autolink.exec(rest);
    if (m) {
      if (m[0].length > label.length - s) return true;
      s += m[0].length - 1;
    }
  }
  return false;
}

function outputLink(lex, cap, href, title, raw) {
  const text = cap[1].replace(other.outputLinkReplace, '$1');
  const isImage = cap[0].charAt(0) === '!';
  const prevInLink = lex.state.inLink;
  const prevEmitted = lex.state.linkEmitted;
  const prevRawBlock = lex.state.inRawBlock;
  lex.state.inLink = true;
  lex.state.linkEmitted = false;
  const tokens = inlineTokens(lex, text, []);
  const emitted = lex.state.linkEmitted;
  lex.state.linkEmitted = prevEmitted;
  lex.state.inLink = prevInLink;
  if (!isImage) {
    if (emitted) {
      lex.state.inRawBlock = prevRawBlock;
      return undefined;
    }
    lex.state.linkEmitted = true;
  }
  return { type: isImage ? 'image' : 'link', raw, href, title: title || null, text, tokens };
}

function tokLink(lex, src) {
  if (lex.state.linkParenPossible === false) return;
  const cap = inline.link.exec(src);
  if (!cap) return;
  const offset = cap[0].charAt(0) === '!' ? 2 : 1;
  if (labelSwallowsTag(src, cap[1], offset)) return;
  const hrefTrim = cap[2].trim();
  if (other.startAngleBracket.test(hrefTrim)) {
    if (!other.endAngleBracket.test(hrefTrim)) return;
    const stripped = trimRightChar(hrefTrim.slice(0, -1), '\\');
    if ((hrefTrim.length - stripped.length) % 2 === 0) return;
  } else {
    const bracket = findClosingBracket(cap[2], '()');
    if (bracket === -2) return;
    if (bracket > -1) {
      const idx = (cap[0].indexOf('!') === 0 ? 5 : 4) + cap[1].length + bracket;
      cap[2] = cap[2].substring(0, bracket);
      cap[0] = cap[0].substring(0, idx).trim();
      cap[3] = '';
    }
  }
  const beforeParen = trimRightChar(cap[0].slice(0, -1), '\\');
  if ((cap[0].length - beforeParen.length) % 2 === 0) return;
  let href = cap[2].trim();
  const title = cap[3] ? cap[3].slice(1, -1) : '';
  if (other.startAngleBracket.test(href)) href = href.slice(1, -1);
  return outputLink(
    lex,
    cap,
    href && href.replace(inline.anyPunctuation, '$1'),
    title && title.replace(inline.anyPunctuation, '$1'),
    cap[0],
  );
}

function tokReflink(lex, src) {
  const cap = inline.reflink.exec(src) || inline.nolink.exec(src);
  if (!cap) return;
  const offset = cap[0].charAt(0) === '!' ? 2 : 1;
  if (labelSwallowsTag(src, cap[1], offset)) return;
  const link = lex.links[normalizeLabel(cap[2] || cap[1])];
  if (!link) {
    const firstChar = cap[0].charAt(0);
    return { type: 'text', raw: firstChar, text: firstChar };
  }
  return outputLink(lex, cap, link.href, link.title, cap[0]);
}

// The last index at which a run of `delim` that could close an emphasis
// span starts in `masked` (a run whose preceding char is not blank).
function scanClosers(masked) {
  const emStrong = { '*': -1, _: -1 };
  let del = -1;
  const n = masked.length;
  for (let s = 0; s < n; s++) {
    const r = masked[s];
    if (r !== '*' && r !== '_' && r !== '~') continue;
    const prev = s === 0 ? '\n' : masked[s - 1];
    let i = s + 1;
    while (i < n && masked[i] === r) i++;
    if (prev !== ' ' && prev !== '\t' && prev !== '\n' && prev !== '\r' && prev !== '\f') {
      if (r === '~') del = s;
      else emStrong[r] = s;
    }
    s = i - 1;
  }
  return { maskedSrc: masked, emStrong, del };
}

// The closer scan of a masked run is computed on first use: many runs
// contain a delimiter character whose opener checks fail before any
// closer is ever consulted.
function closersFor(lex, masked) {
  const top = lex.maskStack.at(-1);
  if (top && top.maskedSrc === masked) {
    if (!top.done) {
      const scanned = scanClosers(masked);
      top.emStrong = scanned.emStrong;
      top.del = scanned.del;
      top.done = true;
    }
    return top;
  }
  return scanClosers(masked);
}

function possibleCloser(lex, masked, delim) {
  return closersFor(lex, masked).emStrong[delim];
}

function possibleDelCloser(lex, masked) {
  return closersFor(lex, masked).del;
}

function tokEmStrong(lex, src, masked, lastChar) {
  const cap = inline.emStrongLDelim.exec(src);
  if (!cap || (!cap[1] && !cap[2] && !cap[3] && !cap[4])) return;
  const delim = cap[0][0];
  const nested = lastChar === delim;
  const offset = masked.length - src.length;
  let runStart = offset;
  while (runStart > 0 && masked[runStart - 1] === delim) runStart--;
  const prevChar = [...masked.slice(Math.max(0, runStart - 2), runStart)].at(-1) ?? '';
  const prevIsDelimOrPunct =
    prevChar === '*' || prevChar === '_' || !!inline.punctuation.exec(prevChar);
  if (runStart < offset) lastChar = prevChar;
  const prevIsPunct = runStart < offset ? prevIsDelimOrPunct : !!inline.punctuation.exec(lastChar);
  if (cap[4] && other.unicodeAlphaNumeric.test(lastChar)) return;
  const afterPunct = cap[1] || cap[3] || '';
  if (!afterPunct || !lastChar || prevIsPunct) {
    const opener = [...cap[0]].length - 1;
    let balance = opener;
    let skipped = 0;
    const triple = offset - runStart + opener;
    const keepDelims = !!prevChar.trim() && (!!afterPunct || (delim === '*' && !prevIsDelimOrPunct));
    if (delim !== '*' && delim !== '_') return;
    const rDelim = delim === '*' ? inline.emStrongRDelimAst : inline.emStrongRDelimUnd;
    const closerAt = possibleCloser(lex, masked, delim);
    const base = masked.length - src.length + opener;
    if (closerAt < base) return;
    const rest = masked.slice(-src.length + opener);
    const maxIndex = closerAt - base;
    rDelim.lastIndex = 0;
    let match;
    while ((match = rDelim.exec(rest)) !== null && !(match.index > maxIndex)) {
      const run = match[1] || match[2] || match[3] || match[4] || match[5] || match[6];
      if (!run) continue;
      let runLen = [...run].length;
      if (match[3] || match[4]) {
        balance += runLen;
        continue;
      } else if (match[5] || match[6] || keepDelims) {
        if (nested && (match[5] || match[6])) break;
        if (triple % 3 && !((triple + runLen) % 3)) {
          skipped += runLen;
          continue;
        }
      }
      balance -= runLen;
      if (balance > 0) continue;
      runLen = Math.min(runLen, runLen + balance + skipped);
      const firstCharLen = [...match[0]][0].length;
      const raw = src.slice(0, opener + match.index + firstCharLen + runLen);
      if (Math.min(opener, runLen) % 2) {
        const text = raw.slice(1, -1);
        return { type: 'em', raw, text, tokens: inlineTokens(lex, text, []) };
      }
      const text = raw.slice(2, -2);
      return { type: 'strong', raw, text, tokens: inlineTokens(lex, text, []) };
    }
  }
}

function tokCodespan(lex, src) {
  const cap = inline.code.exec(src);
  if (!cap) return;
  let text = cap[2].replace(other.newLineCharGlobal, ' ');
  const hasNonSpace = other.nonSpaceChar.test(text);
  const padded = other.startingSpaceChar.test(text) && other.endingSpaceChar.test(text);
  if (hasNonSpace && padded) text = text.substring(1, text.length - 1);
  return { type: 'codespan', raw: cap[0], text };
}

function tokBr(lex, src) {
  const cap = inline.br.exec(src);
  if (cap) return { type: 'br', raw: cap[0] };
}

function tokDel(lex, src, masked, lastChar) {
  const cap = inline.delLDelim.exec(src);
  if (!cap) return;
  if (!(cap[1] || '') || !lastChar || inline.punctuation.exec(lastChar)) {
    const opener = [...cap[0]].length - 1;
    let balance = opener;
    const rDelim = inline.delRDelim;
    const closerAt = possibleDelCloser(lex, masked);
    const base = masked.length - src.length + opener;
    if (closerAt < base) return;
    const rest = masked.slice(-src.length + opener);
    const maxIndex = closerAt - base;
    rDelim.lastIndex = 0;
    let match;
    while ((match = rDelim.exec(rest)) !== null && !(match.index > maxIndex)) {
      const run = match[1] || match[2] || match[3] || match[4] || match[5] || match[6];
      if (!run) continue;
      let runLen = [...run].length;
      if (runLen !== opener) continue;
      if (match[3] || match[4]) {
        balance += runLen;
        continue;
      }
      balance -= runLen;
      if (balance > 0) continue;
      runLen = Math.min(runLen, runLen + balance);
      const firstCharLen = [...match[0]][0].length;
      const raw = src.slice(0, opener + match.index + firstCharLen + runLen);
      const text = raw.slice(opener, -opener);
      return { type: 'del', raw, text, tokens: inlineTokens(lex, text, []) };
    }
  }
}

function tokAutolink(lex, src) {
  const cap = inline.autolink.exec(src);
  if (!cap) return;
  let text, href;
  if (cap[2] === '@') {
    text = cap[1];
    href = 'mailto:' + text;
  } else {
    text = cap[1];
    href = text;
  }
  return {
    type: 'link',
    raw: cap[0],
    text,
    href,
    autolink: true,
    tokens: [{ type: 'text', raw: text, text }],
  };
}

function tokUrl(lex, src) {
  const cap = inline.url.exec(src);
  if (!cap) return;
  let text, href;
  if (cap[2] === '@') {
    text = cap[0];
    href = 'mailto:' + cap[0];
  } else {
    let prev;
    do {
      prev = cap[0];
      cap[0] = inline._backpedal.exec(cap[0])?.[0] ?? '';
    } while (prev !== cap[0]);
    text = cap[0];
    href = cap[1] === 'www.' ? 'http://' + cap[0] : cap[0];
  }
  return {
    type: 'link',
    raw: cap[0],
    text,
    href,
    autolink: true,
    tokens: [{ type: 'text', raw: text, text }],
  };
}

function tokInlineText(lex, src) {
  const cap = inline.text.exec(src);
  if (!cap) return;
  const inRaw = lex.state.inRawBlock;
  return {
    type: 'text',
    raw: cap[0],
    text: inRaw ? cap[0] : decodeEntities(cap[0]),
    escaped: inRaw,
  };
}

// ---------------------------------------------------------------------
// The em/strong mask: a same-length copy of the inline source in which
// link destinations, code spans and escaped punctuation are blanked to
// filler letters, so delimiter scans are not confused by them.
// ---------------------------------------------------------------------

function linkInText(lex, text) {
  if (!text.includes('[')) return false;
  const linkRe = inline.link;
  for (const m of text.matchAll(inline.blockSkip)) {
    if (linkRe.test(m[0]) && text.charAt(m.index - 1) !== '!') return true;
  }
  for (const m of text.matchAll(inline.reflinkSearch)) {
    const s = m[0];
    const r = s.lastIndexOf('[');
    if (
      !(s.charAt(0) === '!' || !Object.hasOwn(lex.links, normalizeLabel(s.slice(r + 1, -1)))) &&
      !(r > 1 && linkInText(lex, s.slice(1, r - 1)))
    ) {
      return true;
    }
  }
  return false;
}

function maskReflink(lex, match) {
  const open = match.lastIndexOf('[');
  if (!Object.hasOwn(lex.links, normalizeLabel(match.slice(open + 1, -1)))) return match;
  if (open > 1 && match.charAt(0) !== '!') {
    const inner = match.slice(1, open - 1);
    if (linkInText(lex, inner)) {
      return (
        '[' +
        inner.replace(inline.reflinkSearch, (m) => maskReflink(lex, m)) +
        '][' +
        'a'.repeat(match.length - open - 2) +
        ']'
      );
    }
  }
  return '[' + 'a'.repeat(match.length - 2) + ']';
}

function maskSource(lex, src) {
  let out = src;
  if (lex.hasLinks && src.includes('[')) {
    out = out.replace(inline.reflinkSearch, (m) => maskReflink(lex, m));
  }
  // The punctuation pass can only match a code span, a bare backtick
  // run, or an escaped punctuation mark; with neither a backtick nor a
  // backslash in the string it is the identity.
  if (out.includes('`') || out.includes('\\')) {
    out = out.replace(inline.anyPunctuationOutsideCode, (match, codeRun, punct) =>
      punct
        ? '+'.repeat(match.length)
        : codeRun
          ? codeRun + match.slice(codeRun.length, -codeRun.length).replace(/`/g, '+') + codeRun
          : match,
    );
  }
  // The block-skip pass can only match a link-shaped span, a code
  // span, or a tag; with none of '[', '`', '<' present it is the identity.
  if (out.includes('[') || out.includes('`') || out.includes('<')) {
    out = out.replace(inline.blockSkip, (match, g1, pre) => {
      const off = pre ? pre.length : 0;
      return match.slice(0, off) + '[' + 'a'.repeat(match.length - off - 2) + ']';
    });
  }
  return out;
}

// ---------------------------------------------------------------------
// The inline pass. marked attempts every inline rule at every position;
// here the first character picks the only rules that can match there,
// in marked's order, and plain text runs fall through to the text rule.
// ---------------------------------------------------------------------

const emailLocalChars = new Set(
  "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789.!#$%&'*+/=?^_`{|}~-",
);

// Could the extended-autolink rule match here? Cheap necessary tests:
// a mailto:/xmpp: prefix, a protocol:// prefix, a www. prefix, or an
// email-shaped run (local-part characters, then @, then a domain char).
function urlPossible(src) {
  if (src.startsWith('www.') || src.startsWith('mailto:') || src.startsWith('xmpp:')) return true;
  const c0 = src[0];
  if (
    (c0 === 'h' || c0 === 'H' || c0 === 'f' || c0 === 'F') &&
    /^(?:[hH][tT][tT][pP][sS]?|[fF][tT][pP]):\/\//.test(src)
  ) {
    return true;
  }
  let i = 0;
  while (i < src.length && emailLocalChars.has(src[i])) i++;
  return i > 0 && src[i] === '@' && i + 1 < src.length && /[A-Za-z0-9]/.test(src[i + 1]);
}

// A run matching none of these can only ever lex as plain text: no
// escape, tag, link, emphasis, code-span or strikethrough characters,
// no '&' (entities), no '@' (email autolinks), no hard break, no
// '://' (protocol autolinks), and none of the lowercase autolink
// prefixes (www., mailto:, xmpp:).
const plainInlineRe = /[\\`*_~\[<!&@]| {2,}\n|:\/\/|www\.|mailto:|xmpp:/;

function inlineTokens(lex, src, tokens) {
  if (src && !plainInlineRe.test(src)) {
    // One text token, exactly what the full pipeline would produce:
    // with no '&' in the run, entity decoding is the identity.
    tokens.push({ type: 'text', raw: src, text: src, escaped: lex.state.inRawBlock });
    return tokens;
  }
  const savedParen = lex.state.linkParenPossible;
  lex.state.linkParenPossible = savedParen && src.includes(')');
  try {
    const needsMask = src.includes('*') || src.includes('_') || src.includes('~');
    const masked = needsMask ? maskSource(lex, src) : src;
    lex.maskStack.push({ maskedSrc: masked, emStrong: null, del: null, done: false });
    try {
      return tokenizeInline(lex, src, masked, tokens);
    } finally {
      lex.maskStack.pop();
    }
  } finally {
    lex.state.linkParenPossible = savedParen;
  }
}

function tokenizeInline(lex, src, masked, tokens) {
  let keepLastChar = false;
  let lastChar = '';
  let lastLen = Infinity;
  while (src) {
    if (src.length < lastLen) lastLen = src.length;
    else break;
    if (!keepLastChar) lastChar = '';
    keepLastChar = false;
    let tok;
    const c = src[0];

    if (c === '\\') {
      if ((tok = tokEscape(lex, src))) {
        src = src.substring(tok.raw.length);
        tokens.push(tok);
        continue;
      }
      if (src[1] === '\n' && (tok = tokBr(lex, src))) {
        src = src.substring(tok.raw.length);
        tokens.push(tok);
        continue;
      }
    } else if (c === '<') {
      if ((tok = tokTag(lex, src))) {
        src = src.substring(tok.raw.length);
        tokens.push(tok);
        continue;
      }
      if ((tok = tokAutolink(lex, src))) {
        src = src.substring(tok.raw.length);
        tokens.push(tok);
        continue;
      }
    } else if (c === '[' || (c === '!' && src[1] === '[')) {
      if ((tok = tokLink(lex, src))) {
        src = src.substring(tok.raw.length);
        tokens.push(tok);
        continue;
      }
      if ((tok = tokReflink(lex, src))) {
        src = src.substring(tok.raw.length);
        const prev = tokens.at(-1);
        if (tok.type === 'text' && prev?.type === 'text') {
          prev.raw += tok.raw;
          prev.text += tok.text;
        } else tokens.push(tok);
        continue;
      }
    } else if (c === '*' || c === '_') {
      if ((tok = tokEmStrong(lex, src, masked, lastChar))) {
        src = src.substring(tok.raw.length);
        tokens.push(tok);
        continue;
      }
    } else if (c === '`') {
      if ((tok = tokCodespan(lex, src))) {
        src = src.substring(tok.raw.length);
        tokens.push(tok);
        continue;
      }
    } else if (c === ' ') {
      if (src[1] === ' ' && (tok = tokBr(lex, src))) {
        src = src.substring(tok.raw.length);
        tokens.push(tok);
        continue;
      }
    } else if (c === '~') {
      if ((tok = tokDel(lex, src, masked, lastChar))) {
        src = src.substring(tok.raw.length);
        tokens.push(tok);
        continue;
      }
    }

    if (!lex.state.inLink && urlPossible(src) && (tok = tokUrl(lex, src))) {
      src = src.substring(tok.raw.length);
      tokens.push(tok);
      continue;
    }

    if ((tok = tokInlineText(lex, src))) {
      src = src.substring(tok.raw.length);
      if (tok.raw.slice(-1) !== '_') lastChar = tok.raw.slice(-1);
      keepLastChar = true;
      const prev = tokens.at(-1);
      if (prev?.type === 'text') {
        prev.raw += tok.raw;
        prev.text += tok.text;
      } else tokens.push(tok);
      continue;
    }
    if (src) break;
  }
  return tokens;
}

// ---------------------------------------------------------------------
// Rendering: one walk over the token tree, emitting marked's HTML.
// ---------------------------------------------------------------------

function renderTextToken(tok) {
  if (tok.tokens) return renderInline(tok.tokens, false);
  if (tok.escaped) return tok.text;
  return escapeHtml(tok.text, false);
}

// The plain-text renderer used for image alt text: tags contribute
// their text, emphasis its contents, nothing is escaped.
function renderPlain(tokens) {
  let out = '';
  for (const tok of tokens) {
    switch (tok.type) {
      case 'strong':
      case 'em':
      case 'del':
      case 'link':
      case 'image':
        out += tok.tokens ? renderPlain(tok.tokens) : tok.text;
        break;
      case 'codespan':
      case 'html':
      case 'text':
        out += tok.text;
        break;
      case 'br':
        break;
      case 'checkbox':
        out += tok.raw;
        break;
      default:
        out += tok.text ?? '';
    }
  }
  return out;
}

function renderInline(tokens, plain) {
  if (plain) return renderPlain(tokens);
  let out = '';
  for (const tok of tokens) {
    switch (tok.type) {
      case 'escape':
        out += renderTextToken(tok);
        break;
      case 'html':
        out += tok.text;
        break;
      case 'link': {
        const inner = tok.autolink ? escapeHtml(tok.text, true) : renderInline(tok.tokens, false);
        const cleaned = cleanUrl(tok.href);
        if (cleaned === null) {
          out += inner;
          break;
        }
        let tag = '<a href="' + escapeHtml(cleaned, tok.autolink) + '"';
        if (tok.title) tag += ' title="' + escapeHtml(tok.title, false) + '"';
        out += tag + '>' + inner + '</a>';
        break;
      }
      case 'image': {
        const alt = tok.tokens ? renderInline(tok.tokens, true) : tok.text;
        const cleaned = cleanUrl(tok.href);
        if (cleaned === null) {
          out += escapeHtml(alt, false);
          break;
        }
        let tag = '<img src="' + escapeHtml(cleaned, false) + '" alt="' + escapeHtml(alt, false) + '"';
        if (tok.title) tag += ' title="' + escapeHtml(tok.title, false) + '"';
        out += tag + '>';
        break;
      }
      case 'checkbox':
        out += '<input ' + (tok.checked ? 'checked="" ' : '') + 'disabled="" type="checkbox"> ';
        break;
      case 'strong':
        out += '<strong>' + renderInline(tok.tokens, false) + '</strong>';
        break;
      case 'em':
        out += '<em>' + renderInline(tok.tokens, false) + '</em>';
        break;
      case 'codespan':
        out += '<code>' + escapeHtml(tok.text, true) + '</code>';
        break;
      case 'br':
        out += '<br>';
        break;
      case 'del':
        out += '<del>' + renderInline(tok.tokens, false) + '</del>';
        break;
      case 'text':
        out += renderTextToken(tok);
        break;
      default:
        break;
    }
  }
  return out;
}

function renderTable(table) {
  let headCells = '';
  for (const cell of table.header) headCells += renderTableCell(cell);
  let out = '<table>\n<thead>\n' + '<tr>\n' + headCells + '</tr>\n' + '</thead>\n';
  let body = '';
  for (const row of table.rows) {
    let cells = '';
    for (const cell of row) cells += renderTableCell(cell);
    body += '<tr>\n' + cells + '</tr>\n';
  }
  if (body) out += '<tbody>' + body + '</tbody>';
  return out + '</table>\n';
}

function renderTableCell(cell) {
  const tag = cell.header ? 'th' : 'td';
  const open = cell.align ? `<${tag} align="${cell.align}">` : `<${tag}>`;
  return open + renderInline(cell.tokens, false) + `</${tag}>\n`;
}

function renderBlocks(tokens) {
  let out = '';
  for (const tok of tokens) {
    switch (tok.type) {
      case 'space':
        break;
      case 'hr':
        out += '<hr>\n';
        break;
      case 'heading':
        out += `<h${tok.depth}>` + renderInline(tok.tokens, false) + `</h${tok.depth}>\n`;
        break;
      case 'code': {
        const lang = (tok.lang || '').match(/^\S*/)?.[0];
        const body = tok.text ? escapeHtml(tok.text.replace(/\n$/, '') + '\n', true) : '';
        out += lang
          ? '<pre><code class="language-' + escapeHtml(lang, false) + '">' + body + '</code></pre>\n'
          : '<pre><code>' + body + '</code></pre>\n';
        break;
      }
      case 'table':
        out += renderTable(tok);
        break;
      case 'blockquote':
        out += '<blockquote>\n' + renderBlocks(tok.tokens) + '</blockquote>\n';
        break;
      case 'list': {
        let items = '';
        for (const item of tok.items) items += '<li>' + renderBlocks(item.tokens) + '</li>\n';
        const tag = tok.ordered ? 'ol' : 'ul';
        const start = tok.ordered && tok.start !== 1 ? ' start="' + tok.start + '"' : '';
        out += '<' + tag + start + '>\n' + items + '</' + tag + '>\n';
        break;
      }
      case 'checkbox':
        out += '<input ' + (tok.checked ? 'checked="" ' : '') + 'disabled="" type="checkbox"> ';
        break;
      case 'html':
        out += tok.text;
        break;
      case 'def':
        break;
      case 'paragraph':
        out += '<p>' + renderInline(tok.tokens, false) + '</p>\n';
        break;
      case 'text':
        out += renderTextToken(tok);
        break;
      default:
        break;
    }
  }
  return out;
}

// ---------------------------------------------------------------------
// The entry point: same contract as marked.parse with default options.
// ---------------------------------------------------------------------

export function parse(markdown) {
  const lex = createLexer();
  const src = markdown.replace(/\r\n|\r/g, '\n');
  const tokens = blockTokens(lex, src, [], false);
  // All link definitions are known once the block pass is done; the
  // inline mask only needs its reflink pass when any exist.
  lex.hasLinks = Object.keys(lex.links).length > 0;
  for (let i = 0; i < lex.queue.length; i++) {
    const entry = lex.queue[i];
    lex.state.inRawBlock = false;
    inlineTokens(lex, entry.src, entry.tokens);
  }
  return renderBlocks(tokens);
}
