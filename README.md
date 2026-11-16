# makefun-markdown-fast

A fast drop-in for marked 18.1.3 — make.fun markdown-render-speed-02.

`parse.js` exports `parse(markdown)` returning exactly the HTML that
marked 18.1.3 renders with its default options (GFM on). `main.ts` reads
`/input/cases.json` and writes `/output/html.json`.

## License

MIT. See LICENSE.
