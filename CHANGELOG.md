# Changelog

## [0.8.0] - 2026-10-06

* Lean v4.34.1
* lean-html v0.10.0, under which `a` and `del` take the category of their context
* UnicodeBasic is pinned to its v2.0.4 release rather than a commit

## [0.7.1] - 2026-08-30

* Every theorem now documents what it establishes and how its proposition says it
* The fuel a raw-HTML reading is given is proved sufficient, where before it was only argued in a comment

## [0.7.0] - 2026-08-29

* `renderHtmlSafe`'s output is now proved well-formed for every input, with no no-embedded-raw-HTML side condition
* `Document.sanitize` is proved idempotent
* URI scheme allowlisting is proved case-insensitive, so no capitalization of a non-allowlisted scheme is accepted
* The build treats warnings as errors, in both the library and the test package

## [0.6.0] - 2026-08-29

* Optional LaTeX math (`Options.math`), following md4c's dialect and emitting pandoc's `math inline`/`math display` spans
* Delimiter flanking after an entity reference now uses the source `;` rather than the decoded character, so `&#65;_foo_` emphasizes

## [0.5.0] - 2026-08-21

Move to Lean's module system.

## [0.4.0] - 2026-08-16

Tidying up and restructuring.

## [0.3.1] - 2026-08-12

Utilise the new UnicodeBasic case folding support.

## [0.3.0] - 2026-08-08

* Unicode-aware punctuation, whitespace, and case-fold classification via `UnicodeBasic`
* Fix numeric character references for lone surrogates

## [0.2.0] - 2026-08-08

Safety and well formedness for untrusted input.

## [0.1.0] - 2026-08-07

Initial release.
