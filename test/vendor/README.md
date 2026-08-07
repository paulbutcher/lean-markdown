# Vendored CommonMark / GFM specs

Split by which variant each suite applies to: `CommonMark/` for the base CommonMark
spec, `GFM/` for cmark-gfm's extension suites.

## `CommonMark/`

- `spec.txt` is the CommonMark 0.31.2 specification, fetched verbatim from
  https://github.com/commonmark/commonmark-spec/blob/0.31.2/spec.txt.
- `spec.json` is the embedded example suite (652 markdown/HTML pairs) extracted
  from `spec.txt` by `scripts/extract_spec.pl`, reproducing the schema that
  upstream's `test/spec_tests.py --dump-tests` produces.
- `test/SpecGuards.lean` is generated from `spec.json` by
  `scripts/generate_guards.pl`; it holds one `#guard` per example, checked by
  `lake test`. Re-run both scripts, in order, after vendoring a newer
  `spec.txt`:
  ```
  scripts/extract_spec.pl test/vendor/CommonMark/spec.txt > test/vendor/CommonMark/spec.json
  scripts/generate_guards.pl test/vendor/CommonMark/spec.json > test/SpecGuards.lean
  ```

## `GFM/`

- `extensions.txt` is cmark-gfm's GFM-extensions example suite (30
  markdown/HTML pairs, covering tables, strikethrough, task lists, extended
  autolinks, footnotes, and the raw-HTML tag filter), fetched verbatim from
  https://github.com/github/cmark-gfm/blob/0.29.0.gfm.13/test/extensions.txt
  (the latest tagged release). It uses the same embedded-example format as
  `spec.txt` (same 32-backtick example fence), with a YAML front-matter block
  that `scripts/extract_spec.pl` skips harmlessly since it only reacts to the
  example-fence and `#`-heading patterns; `extract_spec.pl` works on it
  unmodified.
- `regression.txt` (26 examples: assorted historical bug-regression cases) and
  `smart_punct.txt` (16 examples: smart quote/dash/ellipsis substitution) are
  cmark-gfm's other two example suites, fetched verbatim from the same
  `0.29.0.gfm.13` tag
  (https://github.com/github/cmark-gfm/blob/0.29.0.gfm.13/test/regression.txt,
  https://github.com/github/cmark-gfm/blob/0.29.0.gfm.13/test/smart_punct.txt).
  Same fence convention, no front matter; `extract_spec.pl` works on both
  unmodified.
- None of the three GFM suites are wired into a generated guards file yet; see
  `GFM_PLAN.md` Phase 6.

## License

`spec.txt` (prose and embedded examples) is Copyright (c) 2014-16 John
MacFarlane, released under CC-BY-SA 4.0
(https://creativecommons.org/licenses/by-sa/4.0/). `extensions.txt` (prose and
embedded examples) is Copyright (c) 2016 Yuki Izumi, released under the same
CC-BY-SA 4.0 license per its own front matter. `regression.txt` and
`smart_punct.txt` carry no separate license header of their own and are
covered by cmark-gfm's project-wide `COPYING` (BSD-2-Clause-style, Copyright
(c) 2014 John MacFarlane). `spec.json` is a mechanical extraction of the
example pairs embedded in `spec.txt` and carries the same license as that
file. None of these files contain source code from commonmark.js or
cmark(-gfm).
