# lean-markdown

A Markdown parser and HTML renderer for Lean 4. Supports both
[CommonMark 0.31.2](https://spec.commonmark.org/0.31.2/) and 
[GitHub Flavored Markdown (GFM)](https://github.com/github/cmark-gfm/).

## Guarantees

- **Conformant**: passes every test in the official CommonMark and cmark-gfm suites.
- **Total**: never panics or loops on any input, including adversarial input.
- **Safe**: proved to never let an AST leaf's string content produce unescaped HTML 
  markup, or break out of an attribute.
- **Well-formed**: for input with no embedded raw HTML, output is proved well-formed
  HTML.

See [KNOWN_ISSUES.md](KNOWN_ISSUES.md).

## Usage

```lean
import CommonMark

open CommonMark

def main : IO Unit := do
  let doc := parseDocument "# Hello\n\nSome *emphasis* and a [link](https://example.com).\n"
  IO.println (renderHtml doc)
```

renders:

```html
<h1>Hello</h1>
<p>Some <em>emphasis</em> and a <a href="https://example.com">link</a>.</p>
```

For GFM use `GFMarkdown` instead:

```lean
import GFMarkdown

open GFMarkdown

def main : IO Unit := do
  let doc := parseDocument "- [x] Done\n- [ ] ~~Not~~ Still to do\n"
  IO.println (renderHtml doc)
```

renders:

```html
<ul>
<li><input type="checkbox" checked="" disabled="" /> Done</li>
<li><input type="checkbox" disabled="" /> <del>Not</del> Still to do</li>
</ul>
```

`Document.map`/`Document.fold` (`CommonMark.Ast`) cover whole-tree rewrites and
traversals. For localized, cursor-style edits, use the zipper
(`BlockZipper`/`InlineZipper` in `CommonMark.Zipper`) instead of walking
`Document`/`Block`/`Inline` by hand:

```lean
open CommonMark

-- Bolds the first paragraph of a document, leaving everything else untouched.
def boldFirstParagraph (doc : Document) : Document :=
  match BlockZipper.ofDocument doc with
  | some z =>
    match z.focus with
    | .paragraph content => (z.replace (.paragraph [.strong content])).toDocument
    | _ => doc
  | none => doc
```

## Installing

Add to your `lakefile.toml`:

```toml
[[require]]
name = "markdown"
git = "<repository URL>"
```

## Development

```
lake build   # build the library
lake test    # run the example-suite conformance test and other tests
```

## Formal verification

- `BlockZipper`/`InlineZipper` round-trip and navigation laws (`test/ZipperLaws.lean`):
  the correctness contract that cursor-style document editing relies on.
- Newline-normalization algebraic properties (`test/ParserLaws.lean`): output is always
  `\r`-free, and normalization is idempotent.
- HTML well-formedness (`test/HtmlWellFormedness.lean`,
  `test/GfmHtmlWellFormedness.lean`): for a `Document` with no embedded raw HTML,
  `renderHtml` produces well-formed HTML (balanced tags, no stray `<`/`>`), for both
  CommonMark and GFM.

## Conformance tests

- `test/SpecGuards.lean`: every example in the official CommonMark spec.
- `test/GfmGuards.lean`: GFM extension examples (tables, strikethrough, autolinks, HTML
  tag filter, task lists).
- `test/GfmRegressionGuards.lean`: regression cases from cmark-gfm.

All three are generated from the vendored cmark/cmark-gfm test suites by
`scripts/generate_guards.pl`; see [test/vendor/README.md](test/vendor/README.md).

## Property-based testing

`test/GfmNonEmissionProperties.lean` uses [Plausible](https://github.com/leanprover-community/plausible)
to fuzz two claims about parser fallback paths that aren't (yet) formally proven: that
randomly generated tables and strikethrough-shaped input never lose text in the
rendered output.

## License

Apache License 2.0; see [LICENSE](LICENSE).
