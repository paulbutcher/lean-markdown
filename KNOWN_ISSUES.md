<!--
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-->

# Known Issues

## 1. Footnotes aren't implemented

`GFMarkdown` doesn't implement cmark-gfm's footnotes extension at all: `[^label]` reference syntax and `[^label]: text` definition syntax both pass through as ordinary text (a literal `[^label]`, or a link-reference-definition-shaped paragraph) rather than becoming a footnote reference and a rendered `<section class="footnotes">` block. Exercised by `extensions.json` examples 23-27 and every `regression.txt` example tagged (wholly or partly) `footnotes`; both are excluded from the generated guard suites (`test/GfmGuards.lean`, `test/GfmRegressionGuards.lean`) rather than left in to fail.

## 2. Extended autolinks have a few simplifications

`GFMarkdown/Autolink.lean`'s `http://`/`https://`/`ftp://`/`www.`/email autolinking diverges from cmark-gfm's `extensions/autolink.c` in three small ways, none exercised by the vendored example suite:

- `checkDomainGo` skips the source's escaped-character handling inside a domain.
- `matchScheme` tests directly at each position rather than literally rewinding through already-tokenized inline nodes; this can only differ from `url_match` for a scheme spanning more than one resolved node, e.g. straddling a backslash escape.
- A rejected email-autolink attempt just moves on to the next `@` rather than replicating the source's exact "skip past the whole failed span" offset arithmetic.

## 3. `Document.sanitize`'s URI scheme allowlist is deliberately small

`CommonMark.allowedUriSchemes` is `http`, `https`, `mailto`. Other schemes some sites treat as safe for links (`tel:`, `sms:`, `xmpp:`, ...) are cleared along with genuinely dangerous ones (`javascript:`, `data:`), since the allowlist errs toward rejecting anything not positively known to be safe. Not exercised by the vendored example suite (neither spec has a notion of "safe rendering"); see `test/SanitizeExamples.lean`.

## 4. Math and emphasis that cross resolve differently from md4c

The LaTeX math extension (`Options.math`) follows md4c's dialect, and matches it on every case in `test/vendor/md4c/` except one shape: a math span and an emphasis span that *cross*. md4c analyses `$` in the same left-to-right mark pass as `*`/`_`, so the span whose closing delimiter comes first wins, and `md_disable_marks` retroactively un-resolves whatever the winner swallowed. This library resolves a math span at tokenize time instead, the way it already resolves a code span, so math always wins:

| input | md4c | here |
| --- | --- | --- |
| `*a $b* c$` | `<em>a $b</em> c$` | math containing `b* c` |
| `$$a *b$$ c*` | display math `a *b` | same |
| `$a *b* c$` | math containing `a *b*` | same |

Only the first shape differs; nesting and the reverse crossing agree. Matching md4c exactly would mean rebuilding `resolveEmphasis` as a mark array with retroactive disabling, on the code the 652 CommonMark guards depend on, for inputs where md4c itself emits unmatched delimiters. Pinned in `test/MathDivergenceGuards.lean`.

## Non-goals

- **Smart punctuation** (cmark's `--smart` option: curly quotes, em/en dashes, ellipses) is not implemented in either variant. It's a separate cmark-core rendering option, not a GFM syntax extension (see `test/vendor/README.md`'s note on `smart_punct.txt`).
