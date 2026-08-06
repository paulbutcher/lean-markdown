# Known Issues

Places where the implementation passes the full official CommonMark 0.31.2 example
suite (652/652, including the `native_decide` conformance theorem in
`test/Conformance.lean`) but does not fully match the letter of the spec, because the
spec examples don't happen to exercise the gap.

## 1. Unicode punctuation/symbol classification is a hand-picked subset

`isUnicodePunctOrSymbol` (`CommonMark/Parser/Inline.lean`), used for emphasis flanking
rules, is supposed to match any character in Unicode general categories P* or S*. It
only covers ASCII punctuation, the Latin-1 Supplement block (0xA1-0xBF), and the
Currency Symbols block (0x20A0-0x20CF). Punctuation/symbol characters outside those
ranges (e.g. CJK punctuation, most of the General Punctuation block, mathematical
operators, emoji) are misclassified as non-punctuation for flanking purposes.

Fix would mean generating a full P*/S* range table from `UnicodeData.txt` and
switching the lookup from a linear list scan to binary search over sorted ranges
(a linear scan isn't viable at the resulting range count, a few thousand).

## 2. Unicode whitespace classification for flanking is ASCII + NBSP only

`isFlankingWhitespace` (`CommonMark/Parser/Inline.lean`) is supposed to match the
Unicode `White_Space` property. It only recognizes ASCII whitespace plus U+00A0
(NBSP). Other Unicode whitespace code points (U+2000-200A, U+2028, U+2029, U+202F,
U+205F, U+3000, etc.) aren't recognized, so flanking computed around them can be
wrong.

Same fix shape as #1: generate the range table from `PropList.txt` (much smaller,
on the order of two dozen ranges).

## 3. Case folding for reference-label matching is a hand-picked subset

`labelFoldChar`/`expandSharpS` (`CommonMark/Parser/Inline.lean`), used to compare
link reference labels, are supposed to apply full Unicode case folding. They only
cover ASCII, the Latin-1 Supplement, Greek, and the ẞ -> "ss" special case. Two
labels differing only by case in other scripts (Cyrillic, Armenian, Georgian, etc.)
won't be recognized as equal when the spec says they should be.

Fix would mean generating the fold table from `CaseFolding.txt`. Most entries are
simple 1:1 folds (mechanical, same shape as the existing tables); a minority are
1:many (like the existing ẞ -> "ss" case), which the label-comparison logic already
has to handle, so the pattern doesn't need to change, just the table size.

## 4. Numeric character references for lone surrogates don't produce U+FFFD

`codepointToStr` (`CommonMark/Parser/Inline.lean`) is supposed to replace any
invalid Unicode code point with the REPLACEMENT CHARACTER (U+FFFD), per the spec's
"Invalid Unicode code points will be replaced by the REPLACEMENT CHARACTER
(U+FFFD)". Its guard only checks `cp == 0 || cp > 0x10FFFF`, which misses the
surrogate range 0xD800-0xDFFF (e.g. input `&#xD800;`). For a surrogate value,
`Char.ofNat` silently substitutes `'\0'` instead of raising or signalling failure
(this is documented Lean core behavior: "If the `Nat` does not encode a valid
Unicode scalar value, `'\0'` is returned instead"), so those references currently
render as NUL rather than U+FFFD.

Unlike #1-#3, this isn't a data-completeness gap, it's a one-line guard fix: also
reject `0xD800 <= cp && cp <= 0xDFFF` in `codepointToStr`.

## Notes

- None of the above are exercised by the official example suite, which is why they
  survived Phase 5 despite 100% conformance against it.
- Items #1-#3 all follow the same shape: the spec formally depends on Unicode
  Character Database tables, and the implementation currently substitutes a
  hand-picked subset of ranges sized to what the example suite needed rather than
  the full tables.
