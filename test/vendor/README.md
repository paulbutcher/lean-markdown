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
  unmodified. `extensions.json` is its extracted example suite, same schema
  as `spec.json`:
  ```
  scripts/extract_spec.pl test/vendor/GFM/extensions.txt > test/vendor/GFM/extensions.json
  ```
- `regression.txt` (26 examples: assorted historical bug-regression cases) and
  `smart_punct.txt` (16 examples: smart quote/dash/ellipsis substitution) are
  cmark-gfm's other two example suites, fetched verbatim from the same
  `0.29.0.gfm.13` tag
  (https://github.com/github/cmark-gfm/blob/0.29.0.gfm.13/test/regression.txt,
  https://github.com/github/cmark-gfm/blob/0.29.0.gfm.13/test/smart_punct.txt).
  Same fence convention, no front matter; `extract_spec.pl` works on both
  unmodified.
- `test/GfmGuards.lean` is generated from `extensions.json`, filtered to whichever examples
  cover the sections implemented so far (currently 1-19, 21, 22, 28-30: Tables through the
  HTML tag filter, plus Task lists), via `scripts/generate_guards.pl`'s optional
  checker/import arguments. Re-run and widen the selection as later phases land:
  ```
  jq '[.[] | select((.example >= 1 and .example <= 19) or .example == 21 or .example == 22
    or (.example >= 28 and .example <= 30))]' test/vendor/GFM/extensions.json \
    | scripts/generate_guards.pl /dev/stdin checkExampleGfm CheckExampleGfm > test/GfmGuards.lean
  ```
  Example 20 is excluded from the selection above and instead hand-appended to the generated
  file afterward: its expected output is cmark-gfm's own "<IGNORE>" marker (a "just don't crash
  on this" case, not a real HTML fixture), which `checkExampleGfm`'s exact-string check can't
  express. Examples 23-27 (footnotes) aren't implemented yet; wiring all of `extensions.txt`
  (and `regression.txt`/`smart_punct.txt`) into one generated suite, expecting many failures
  until later phases land, is `GFM_PLAN.md` Phase 6 -- at which point this file's
  incremental-selection approach is superseded by that fuller suite.

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
