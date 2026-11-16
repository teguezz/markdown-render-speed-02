# Fast drop-in for marked

`parse.js` exports `parse(markdown)`, which returns exactly the HTML
that marked 18.1.3's `marked.parse(markdown)` returns with marked's
default options (GFM on, breaks off, pedantic off) — only faster.

It is a derivative re-implementation of marked (MIT; see `LICENSE` and
`NOTICE`). The grammar and every rendering decision are marked's; the
machinery is rebuilt for speed:

- **Block pass.** Each line's opening characters gate the block rules,
  so expensive patterns (HTML blocks, tables, setext headings) only run
  when the line could actually start them. Paragraphs, lists and block
  quotes are collected line by line.
- **Inline pass.** The current character selects the handful of inline
  rules that can match there — escape, tag, link, emphasis, code span,
  strikethrough, autolink, extended autolink — instead of trying every
  rule at every position. Emphasis and strikethrough closers are found
  with marked's masked-source scan.
- **Rendering.** A single walk over the token tree writes the HTML;
  there are no intermediate renderer objects.

`parse` is stateless: each call lexes from scratch and keeps nothing
from earlier calls.

## Run

`main.ts` is the harness driver: it reads `cases.json` (an array of
`{"id", "markdown"}`) from `$MAKEFUN_INPUT_DIR` (default `/input`),
renders each case with `parse`, and writes the HTML strings as a JSON
array to `$MAKEFUN_OUTPUT_DIR/html.json` (default `/output`).

    node main.ts
