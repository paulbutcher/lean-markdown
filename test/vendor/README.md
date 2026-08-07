# Vendored CommonMark spec

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
  scripts/extract_spec.pl test/vendor/spec.txt > test/vendor/spec.json
  scripts/generate_guards.pl test/vendor/spec.json > test/SpecGuards.lean
  ```

## License

`spec.txt` (prose and embedded examples) is Copyright (c) 2014-16 John
MacFarlane, released under CC-BY-SA 4.0
(https://creativecommons.org/licenses/by-sa/4.0/). `spec.json` is a mechanical
extraction of the example pairs embedded in that file and carries the same
license. Neither file contains source code from commonmark.js or cmark.
