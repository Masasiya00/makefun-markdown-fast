# makefun-markdown-fast

A fast drop-in for marked 18.1.3 — make.fun markdown-render-speed-02.

`parse.js` exports `parse(markdown)` returning exactly the HTML that
marked 18.1.3 renders with its default options (GFM on). `main.ts` reads
`/input/cases.json` and writes `/output/html.json`.

## How the parser works

`parse.js` is a single dependency-free ES module, written from scratch
against the CommonMark 0.31.2 spec and the GFM extensions (tables,
strikethrough, task lists, extended autolinks).

- **Block layer.** The input is split into lines and walked by a
  container stack (document, blockquote, list, list item). Each line
  first tries to match the open containers (lazy paragraph continuation
  included), then is consumed as a new block: ATX/setext headings,
  fenced or indented code, HTML blocks (types 1–7), thematic breaks,
  blockquotes, lists, or plain paragraphs. Link reference definitions
  are stripped out of paragraphs as they are finalised (first
  definition wins) and a paragraph whose header line is followed by a
  valid delimiter row becomes a GFM table.
- **Inline layer.** A single scan tokenises backslash escapes, code
  spans, autolinks, raw HTML, image/link brackets and `*`/`_`/`~`
  delimiter runs, then a delimiter-stack pass resolves emphasis,
  strong, strikethrough and links with the spec's rule-of-three and
  flanking rules. Text escapes `"` and `'` too; named entities are
  never decoded, numeric character references are (decimal 1–7 digits,
  hex 1–6, out-of-range becomes U+FFFD).
- **Fast paths.** A paragraph made of plain text with no special
  characters short-circuits straight to escaping, and a paragraph with
  no inline markers skips the delimiter stack. The 40 long generated
  documents dominate the input, so most of the time is spent in the
  tight line scan and the plain-text escape, not in allocation.

## Local test loop

From the build directory, with the kit at `../markdown-render-speed-02-kit/markdown-render-speed-02-kit`:

```sh
mkdir -p /tmp/mdt-out /tmp/mdt-scores
MAKEFUN_INPUT_DIR=../markdown-render-speed-02-kit/markdown-render-speed-02-kit/practice/input \
  MAKEFUN_OUTPUT_DIR=/tmp/mdt-out node main.ts
MAKEFUN_OUTPUT_DIR=/tmp/mdt-out \
  MAKEFUN_REFERENCE_DIR=../markdown-render-speed-02-kit/markdown-render-speed-02-kit/practice/reference \
  MAKEFUN_SCORES_DIR=/tmp/mdt-scores \
  node ../markdown-render-speed-02-kit/markdown-render-speed-02-kit/program/scorer/main.ts
cat /tmp/mdt-scores/scores.json
```

A single case can be diffed against the expected output and the marked
oracle with `/tmp/one.mjs <case-id>` (e.g. `node /tmp/one.mjs cm-042`).

## Status

In progress — block parser, link reference definitions, tables and the
`parse()` entry point are written; correctness is being driven to
720/720 on the local scorer before speed tuning.

## License

MIT. See LICENSE.
