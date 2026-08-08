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

## 2. Numeric character references for lone surrogates don't produce U+FFFD

`codepointToStr` (`CommonMark/Parser/Inline.lean`) is supposed to replace any
invalid Unicode code point with the REPLACEMENT CHARACTER (U+FFFD), per the spec's
"Invalid Unicode code points will be replaced by the REPLACEMENT CHARACTER
(U+FFFD)". Its guard only checks `cp == 0 || cp > 0x10FFFF`, which misses the
surrogate range 0xD800-0xDFFF (e.g. input `&#xD800;`). For a surrogate value,
`Char.ofNat` silently substitutes `'\0'` instead of raising or signalling failure
(this is documented Lean core behavior: "If the `Nat` does not encode a valid
Unicode scalar value, `'\0'` is returned instead"), so those references currently
render as NUL rather than U+FFFD..

## 3. Footnotes aren't implemented

`GFMarkdown` doesn't implement cmark-gfm's footnotes extension at all: `[^label]`
reference syntax and `[^label]: text` definition syntax both pass through as ordinary
text (a literal `[^label]`, or a link-reference-definition-shaped paragraph) rather
than becoming a footnote reference and a rendered `<section class="footnotes">` block.
Exercised by `extensions.json` examples 23-27 and every `regression.txt` example tagged
(wholly or partly) `footnotes`; both are excluded from the generated guard suites
(`test/GfmGuards.lean`, `test/GfmRegressionGuards.lean`) rather than left in to fail.

## 4. Extended autolinks have a few simplifications

`GFMarkdown/Autolink.lean`'s `http://`/`https://`/`ftp://`/`www.`/email autolinking
diverges from cmark-gfm's `extensions/autolink.c` in three small ways, none
exercised by the vendored example suite:

- `checkDomainGo` skips the source's escaped-character handling inside a domain.
- `matchScheme` tests directly at each position rather than literally rewinding through
  already-tokenized inline nodes; this can only differ from `url_match` for a scheme
  spanning more than one resolved node, e.g. straddling a backslash escape.
- A rejected email-autolink attempt just moves on to the next `@` rather than
  replicating the source's exact "skip past the whole failed span" offset arithmetic.

## 5. `Document.sanitize`'s URI scheme allowlist is deliberately small

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
