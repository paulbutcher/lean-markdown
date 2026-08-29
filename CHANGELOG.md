<!--
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-->

# Changelog

## [Unreleased]

* The build treats warnings as errors, in both the library and the test package
* `renderHtmlSafe`'s output is now proved well-formed for every input, with no no-embedded-raw-HTML side condition
* `Document.sanitize` is proved idempotent
* URI scheme allowlisting is proved case-insensitive, so no capitalization of a non-allowlisted scheme is accepted

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
