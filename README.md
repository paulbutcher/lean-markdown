# lean-commonmark

A [CommonMark 0.31.2](https://spec.commonmark.org/0.31.2/) parser and HTML renderer for
Lean 4.

## Guarantees

- **Conformant**: matches every example in the official CommonMark example suite,
  checked at build time as a machine-checked theorem (`commonmark_conformance` in
  `test/Conformance.lean`), not just an ordinary test run.
- **Total**: `parseDocument` never panics or loops on any input, including adversarial
  input; no `partial` functions anywhere in the library.
- **Safe**: `renderHtml` is proved to never let an AST leaf's string content produce
  unescaped HTML markup, or break out of an attribute.

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
name = "commonmark"
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
