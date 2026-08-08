# Known Issues

## 1. Case folding for reference-label matching is incomplete

`labelFoldChar` (`CommonMark/Parser/Inline.lean`), used to compare link reference
labels, uses `Unicode.getLowerChar` (from the `UnicodeBasic` library) for Unicode's
*simple* case mapping, which covers every script's ordinary lowercase mapping. The
spec calls for *full* Unicode case fold, though, which differs from simple mapping
for a handful of code points whose fold expands to more than one character; only the
ẞ (U+1E9E) -> "ss" case is handled, via `expandSharpS`. Other full-fold-only
exceptions (there are only a few dozen in `CaseFolding.txt`, none exercised by the
vendored example suite) aren't.

## 2. Footnotes aren't implemented

`GFMarkdown` doesn't implement cmark-gfm's footnotes extension at all: `[^label]`
reference syntax and `[^label]: text` definition syntax both pass through as ordinary
text (a literal `[^label]`, or a link-reference-definition-shaped paragraph) rather
than becoming a footnote reference and a rendered `<section class="footnotes">` block.
Exercised by `extensions.json` examples 23-27 and every `regression.txt` example tagged
(wholly or partly) `footnotes`; both are excluded from the generated guard suites
(`test/GfmGuards.lean`, `test/GfmRegressionGuards.lean`) rather than left in to fail.

## 3. Extended autolinks have a few simplifications

`GFMarkdown/Autolink.lean`'s `http://`/`https://`/`ftp://`/`www.`/email autolinking
diverges from cmark-gfm's `extensions/autolink.c` in three small ways, none
exercised by the vendored example suite:

- `checkDomainGo` skips the source's escaped-character handling inside a domain.
- `matchScheme` tests directly at each position rather than literally rewinding through
  already-tokenized inline nodes; this can only differ from `url_match` for a scheme
  spanning more than one resolved node, e.g. straddling a backslash escape.
- A rejected email-autolink attempt just moves on to the next `@` rather than
  replicating the source's exact "skip past the whole failed span" offset arithmetic.

## 4. `Document.sanitize`'s URI scheme allowlist is deliberately small

`CommonMark.allowedUriSchemes` is `http`, `https`, `mailto`. Other schemes some sites
treat as safe for links (`tel:`, `sms:`, `xmpp:`, ...) are cleared along with genuinely
dangerous ones (`javascript:`, `data:`), since the allowlist errs toward rejecting
anything not positively known to be safe. Not exercised by the vendored example suite
(neither spec has a notion of "safe rendering"); see `test/SanitizeExamples.lean`.

## Non-goals

- **Smart punctuation** (cmark's `--smart` option: curly quotes, em/en dashes,
  ellipses) is not implemented in either variant. It's a separate cmark-core rendering
  option, not a GFM syntax extension (see `test/vendor/README.md`'s note on 
  `smart_punct.txt`).
