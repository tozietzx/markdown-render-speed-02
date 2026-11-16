# Make Markdown rendering faster

A fast drop-in for marked 18.1.3 (GFM, default options). `parse(markdown)`
returns exactly the HTML `marked.parse(markdown)` returns with its defaults,
for every string — and does it faster.

## How

The matching rules are marked's own (the block and inline patterns are the
ones marked 18.1.3 compiles for its GFM rule set, and the tokenizing order
and state machine follow marked's Lexer and Tokenizer), reimplemented from
scratch for speed instead of carrying marked's token trees:

- The block lexer dispatches on the first characters of the remaining
  source, so a paragraph never pays for the fences / heading / hr /
  blockquote / list / html / definition regexes that cannot match it.
- Inline content is rendered straight to HTML during the render phase
  instead of being built into token objects and walked a second time.
  Link reference definitions are still collected first (two phases, as in
  marked), so a reference defined later in the document still works.
- The emphasis mask (the masked copy of an inline source that marked
  builds eagerly for every inline run containing `*` `_` or `~`) is built
  lazily, only when an emphasis or strikethrough match is attempted.
- No per-call allocation of a Lexer / Tokenizer / Parser object graph:
  one small state object per `parse()` call, plain objects for blocks.

No input is recognised by table or hash: every output is computed from the
markdown given. No caching across calls; `parse()` keeps nothing from an
earlier call.

## Layout

- `parse.js` — the parser (dependency-free ES module, exports `parse`).
- `main.ts` — the driver the harness runs: reads `/input/cases.json`,
  renders each case with `parse`, writes `/output/html.json`.

## Credit

marked (https://github.com/markedjs/marked, MIT). The matching patterns
and the algorithm they drive are derived from marked 18.1.3; see NOTICE.
