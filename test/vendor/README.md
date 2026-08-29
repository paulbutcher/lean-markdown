<!--
Copyright (c) 2026 Paul Butcher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-->

# Vendored CommonMark / GFM / md4c specs

Split by which variant each suite applies to: `CommonMark/` for the base CommonMark spec, `GFM/` for cmark-gfm's extension suites, `md4c/` for the LaTeX math extension.

## `CommonMark/`

- `spec.txt` is the CommonMark 0.31.2 specification, fetched verbatim from https://github.com/commonmark/commonmark-spec/blob/0.31.2/spec.txt.
- `spec.json` is the embedded example suite (652 markdown/HTML pairs) extracted from `spec.txt` by `scripts/extract_spec.pl`, reproducing the schema that upstream's `test/spec_tests.py --dump-tests` produces.
- `test/SpecGuards.lean` is generated from `spec.json` by `scripts/generate_guards.pl`; it holds one `#guard` per example, checked by `lake test`. Re-run both scripts, in order, after vendoring a newer `spec.txt`:
  ```
  scripts/extract_spec.pl test/vendor/CommonMark/spec.txt > test/vendor/CommonMark/spec.json
  scripts/generate_guards.pl test/vendor/CommonMark/spec.json > test/SpecGuards.lean
  ```

## `GFM/`

- `extensions.txt` is cmark-gfm's GFM-extensions example suite (30 markdown/HTML pairs, covering tables, strikethrough, task lists, extended autolinks, footnotes, and the raw-HTML tag filter), fetched verbatim from https://github.com/github/cmark-gfm/blob/0.29.0.gfm.13/test/extensions.txt (the latest tagged release). It uses the same embedded-example format as `spec.txt` (same 32-backtick example fence), with a YAML front-matter block that `scripts/extract_spec.pl` skips harmlessly since it only reacts to the example-fence and `#`-heading patterns; `extract_spec.pl` works on it unmodified. `extensions.json` is its extracted example suite, same schema as `spec.json`:
  ```
  scripts/extract_spec.pl test/vendor/GFM/extensions.txt > test/vendor/GFM/extensions.json
  ```
- `regression.txt` (26 examples: assorted historical bug-regression cases) and `smart_punct.txt` (16 examples: smart quote/dash/ellipsis substitution) are cmark-gfm's other two example suites, fetched verbatim from the same `0.29.0.gfm.13` tag (https://github.com/github/cmark-gfm/blob/0.29.0.gfm.13/test/regression.txt, https://github.com/github/cmark-gfm/blob/0.29.0.gfm.13/test/smart_punct.txt). Same fence convention as `spec.txt`/`extensions.txt`, no YAML front matter; but `regression.txt` mixes plain-CommonMark and GFM-extension regression cases in one file, so some of its example fences carry extra words after `example` (e.g. `` ```` example strikethrough `` or `` ```` example footnotes autolink strikethrough table ``), naming which extension(s) that specific example needs. `extract_spec.pl` records this as each example's `extensions` JSON field (space-separated, `""` when absent); it's what `regression.json`'s guard generation below dispatches on. `extensions.txt`/`spec.txt`/`smart_punct.txt` never use this tag (the first two are always run with every extension of their kind enabled; the third is untagged for a different reason, see below).
- `test/GfmGuards.lean` is generated from `extensions.json`, filtered to whichever examples cover the sections implemented so far (currently 1-19, 21, 22, 28-30: Tables through the HTML tag filter, plus Task lists), via `scripts/generate_guards.pl`'s optional checker/import arguments. Re-run and widen the selection as later phases land:
  ```
  jq '[.[] | select((.example >= 1 and .example <= 19) or .example == 21 or .example == 22
    or (.example >= 28 and .example <= 30))]' test/vendor/GFM/extensions.json \
    | scripts/generate_guards.pl /dev/stdin checkExampleGfm CheckExampleGfm > test/GfmGuards.lean
  ```
  Example 20 is excluded from the selection above and instead hand-appended to the generated file afterward: its expected output is cmark-gfm's own "<IGNORE>" marker (a "just don't crash on this" case, not a real HTML fixture), which `checkExampleGfm`'s exact-string check can't express. Examples 23-27 (footnotes) aren't implemented yet, and are excluded the same way as example 20's neighbors below.
- `test/GfmRegressionGuards.lean` is generated from `regression.json`, dispatched per example against either `checkExample` (plain CommonMark, for examples with an empty `extensions` tag) or `checkExampleGfm` (GFM, for examples tagged with only implemented extensions), then merged in example-number order under one set of imports:
  ```
  jq '[.[] | select(.extensions == "")]' test/vendor/GFM/regression.json > /tmp/regression_plain.json
  jq '[.[] | select(.extensions != "" and (.extensions | test("footnotes") | not))]' \
    test/vendor/GFM/regression.json > /tmp/regression_gfm.json
  scripts/generate_guards.pl /tmp/regression_plain.json checkExample CheckExample | tail -n +6 > /tmp/plain_body.lean
  scripts/generate_guards.pl /tmp/regression_gfm.json checkExampleGfm CheckExampleGfm | tail -n +6 > /tmp/gfm_body.lean
  cat /tmp/plain_body.lean /tmp/gfm_body.lean | grep -v '^$' | sort -t' ' -k3 -n
  ```
  then hand-assembled into `test/GfmRegressionGuards.lean` with a shared header importing both `CheckExample` and `CheckExampleGfm`. Examples tagged (wholly or partly) `footnotes` (13, 20-25) are excluded, same reason as `extensions.json` 23-27; each gap is marked with a comment rather than silently skipped.
- `smart_punct.txt` is entirely excluded from the generated guard suites: every example there tests cmark's `--smart` typographic-substitution option (curly quotes, em/en dashes, ellipses), which is a separate cmark-core rendering option, not a GFM syntax extension. This is also why its fences carry no per-example `extensions` tag: the whole file is meant to be run with `--smart` turned on globally, an axis this port doesn't model at all (there's no smart-punctuation pass in either `CommonMark` or `GFMarkdown`).

## `md4c/`

The LaTeX math extension follows md4c's dialect (`$...$`, `$$...$$`), so md4c is the reference implementation for it, as cmark is for `CommonMark/` and cmark-gfm for `GFM/`.

- `spec-latex-math.txt` is md4c's own example suite for the extension (6 examples), fetched verbatim from https://github.com/mity/md4c/blob/release-0.5.3/test/spec-latex-math.txt.
- `interactions.txt` (56 examples) is *authored here*, not vendored: md4c's own suite covers none of the flanking corners, run-length matching, opener-stack behaviour, or interaction with the constructs md4c resolves before `$`. Its expected output was captured from `md2html --flatex-math` at the same tag.

md4c's extension suites end each example with a third section holding the `md2html` flags it needs, where the CommonMark and cmark-gfm suites have only two, so extraction needs `--flags-section`. Guard generation needs `--math-output`, which rewrites md2html's placeholder `<x-equation>` tag into the pandoc-style `<span class="math inline">\(...\)</span>` this library emits. Doing that translation in the generator is what lets both `.txt` files keep md4c's own output verbatim: what differs from upstream is a script you can read rather than expectations somebody retyped.

```
scripts/extract_spec.pl --flags-section test/vendor/md4c/spec-latex-math.txt > test/vendor/md4c/spec-latex-math.json
scripts/extract_spec.pl --flags-section test/vendor/md4c/interactions.txt > test/vendor/md4c/interactions.json
scripts/generate_guards.pl --math-output test/vendor/md4c/spec-latex-math.json checkExampleMath CheckExampleMath > test/MathGuards.lean
scripts/generate_guards.pl --math-output test/vendor/md4c/interactions.json checkExampleMath CheckExampleMath > test/MathInteractionGuards.lean
```

Both `.json` files are re-checked against md4c itself by `scripts/verify_md4c.pl`, which CI runs after building the oracle with `scripts/build_md4c.sh` (that script pins the md4c tag). Since `lake test` checks this library against the same recordings, the two together are what pin the extension to md4c's behaviour. The inputs where the two deliberately differ are deliberately absent from these files; they live in `test/MathDivergenceGuards.lean`, with `KNOWN_ISSUES.md` 4 for the reason.

## License

`spec.txt` (prose and embedded examples) is Copyright (c) 2014-16 John MacFarlane, released under CC-BY-SA 4.0 (https://creativecommons.org/licenses/by-sa/4.0/). `extensions.txt` (prose and embedded examples) is Copyright (c) 2016 Yuki Izumi, released under the same CC-BY-SA 4.0 license per its own front matter. `regression.txt` and `smart_punct.txt` carry no separate license header of their own and are covered by cmark-gfm's project-wide `COPYING` (BSD-2-Clause-style, Copyright (c) 2014 John MacFarlane). `spec.json` is a mechanical extraction of the example pairs embedded in `spec.txt` and carries the same license as that file. `spec-latex-math.txt` carries no license header of its own and is covered by md4c's project-wide `LICENSE.md` (MIT, Copyright (c) 2016-2024 Martin Mitáš); `interactions.txt` is original to this project and carries the project's own license. None of these files contain source code from commonmark.js, cmark(-gfm), or md4c.

