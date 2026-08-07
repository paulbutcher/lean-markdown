# lean-markdown

A [CommonMark 0.31.2](https://spec.commonmark.org/0.31.2/) parser and HTML renderer for
Lean 4 (the `CommonMark` namespace), with a GitHub Flavored Markdown (GFM) variant
(`GFMarkdown`) built on top of the same core: tables, strikethrough, task lists,
extended autolinks, and the raw-HTML tag filter, with footnotes the one extension not
yet implemented (see [KNOWN_ISSUES.md](KNOWN_ISSUES.md)).

## Guarantees

The first three guarantees hold for both `CommonMark` and `GFMarkdown`, since
`GFMarkdown` is built directly on `CommonMark`'s parser and shares the same `Html`
node-construction layer for rendering; the fourth is `CommonMark`-only.

- **Conformant**: `CommonMark.parseDocument` matches every example in the official
  CommonMark example suite; `GFMarkdown.parseDocument` matches cmark-gfm's own
  `extensions.txt`/`regression.txt` suites, except the examples requiring footnotes
  (unimplemented, see [KNOWN_ISSUES.md](KNOWN_ISSUES.md)). Both suites are
  automatically extracted from their respective upstream sources (see `test/vendor`).
- **Total**: `parseDocument` never panics or loops on any input, including adversarial
  input; no `partial` functions anywhere in the library, in either variant.
- **Safe**: `renderHtml` is proved to never let an AST leaf's string content produce
  unescaped HTML markup, or break out of an attribute, for the same reason in both
  variants: every rendered node is built through the shared `Html` library's typed
  constructors, never hand-built strings.
- **Well-formed** (`CommonMark` only): for input with no embedded raw HTML,
  `CommonMark.renderHtml`'s output is proved well-formed HTML: balanced tags, with no
  stray `<`/`>` outside of tag delimiters (`renderHtml_wellFormed` in
  `test/HtmlWellFormedness.lean`). `GFMarkdown.renderHtml` has no equivalent formal
  proof; its extra node kinds (tables, task-list checkboxes, `<del>`) are checked only
  by the conformance suite above, the same way the rest of its behavior is.

See [KNOWN_ISSUES.md](KNOWN_ISSUES.md) for the handful of places where the
implementation trades a small amount of spec-letter fidelity, mostly full-Unicode-table
completeness, for a smaller and more maintainable codebase; none of them affect the
official example suite.

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

For GFM (tables, strikethrough, task lists, extended autolinks, raw-HTML filtering),
use `GFMarkdown` instead:

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

See [KNOWN_ISSUES.md](KNOWN_ISSUES.md) for known spec-conformance gaps.

## License

Apache License 2.0; see [LICENSE](LICENSE).
