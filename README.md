# lean-markdown

A Markdown parser and HTML renderer for Lean 4. Supports both [CommonMark 0.31.2](https://spec.commonmark.org/0.31.2/) and [GitHub Flavored Markdown (GFM)](https://github.com/github/cmark-gfm/).

See [A (somewhat) formally verified implementation of Markdown](https://paulbutcher.com/lean-markdown.html)

## Guarantees

- **Conformant**: passes every test in the official CommonMark and cmark-gfm suites, and every test in md4c's suite for the optional LaTeX math extension.
- **Total**: never panics or loops on any input, including adversarial input.
- **Safe**: proved to never let an AST leaf's string content produce unescaped HTML markup, or break out of an attribute.
- **Well-formed**: for input with no embedded raw HTML, output is proved well-formed: balanced tags, no stray `<`/`>`, and every attribute a quoted `name="value"` pair. Rendering is in the XHTML dialect, so that is well-formed XML.

Both CommonMark and GFM pass raw HTML through verbatim by design. For untrusted input use `renderHtmlSafe`, whose output is proved well-formed for *every* input, adversarial ones included, with no side condition.

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

LaTeX math is an optional extension, off by default and independent of GFM, so all four combinations are available through `parseDocumentWith`:

```lean
open CommonMark

#eval renderHtml (parseDocumentWith { math := true } "$x^2$ and $$e=mc^2$$\n")
-- <p><span class="math inline">\(x^2\)</span> and <span class="math display">\[e=mc^2\]</span></p>
```

It follows [md4c](https://github.com/mity/md4c)'s dialect; output is the pandoc-style `<span class="math inline">\(...\)</span>`. `GFMarkdown` has the same `parseDocumentWith`, with GFM's own extensions enabled.

For untrusted input, use `renderHtmlSafe` instead of `renderHtml`:

```lean
open CommonMark

#eval renderHtmlSafe (parseDocument "<script>alert(1)</script>\n\n[x](javascript:alert(1))\n")
-- <p></p>
-- <p><a href="">x</a></p>
```

`Document.map`/`Document.fold` (`CommonMark.Ast`) cover whole-tree rewrites and traversals. For localized, cursor-style edits, use the zipper (`BlockZipper`/`InlineZipper` in `CommonMark.Zipper`) instead of walking `Document`/`Block`/`Inline` by hand:

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
git = "https://github.com/paulbutcher/lean-markdown"
```

## Development

```
lake build   # build the library
lake test    # run the example-suite conformance test and other tests
```

## Formal verification

- `BlockZipper`/`InlineZipper` round-trip, navigation, and edit laws (`test/ZipperLaws.lean`): navigation steps invert one another, and `replace`/`insertLeft`/`insertRight` change the reconstructed document only at the focus.
- Newline-normalization algebraic properties (`test/ParserLaws.lean`): output is always `\r`-free, and normalization is idempotent.
- HTML well-formedness (`test/HtmlWellFormedness.lean`, `test/GfmHtmlWellFormedness.lean`): for a `Document` with no embedded raw HTML, `renderHtml` produces well-formed HTML (balanced tags, no stray `<`/`>`, every attribute a quoted pair).
- `renderHtmlSafe` well-formedness (`test/RenderSafeWellFormedness.lean`, `test/GfmRenderSafeWellFormedness.lean`): the same conclusion for *every* `Document`, the hypothesis discharged by what `Document.sanitize` removes.
- `Document.sanitize` safety (`test/SanitizeSafety.lean`, `test/GfmSanitizeSafety.lean`): its output never contains a `.htmlInline`/`.htmlBlock` leaf, and every `link`/`image` destination in it has an allowlisted URI scheme (or none, i.e. a relative reference).
- `Document.sanitize` idempotence (`test/SanitizeIdempotence.lean`, `test/GfmSanitizeIdempotence.lean`): sanitizing twice is sanitizing once, so layered defensive calls cost nothing.
- URI scheme allowlisting is case-insensitive (`test/UriSchemeLaws.lean`): a scheme not on the allowlist is rejected however it is capitalized, `javascript:` included.
- Fuel laws for the `Block` traversals (`test/AstFuelLaws.lean`, `test/GfmAstFuelLaws.lean`): `Block.listCount` saturates `Block.mapF`/`Block.mapListF`, and sanitizing preserves it. These are what let the well-formedness and sanitize proofs, which pick their fuel independently, be composed.
- `normalizeMathContent` preserves length (`test/MathProperties.lean`), which is what makes wrongly copying `normalizeCodeSpanContent`'s space-stripping fail to compile.

## Conformance tests

- `test/SpecGuards.lean`: every example in the official CommonMark spec.
- `test/GfmGuards.lean`: GFM extension examples.
- `test/GfmRegressionGuards.lean`: regression cases from cmark-gfm.
- `test/MathGuards.lean`: md4c's own example suite for the LaTeX math extension.
- `test/MathInteractionGuards.lean`: the flanking, run-length, and construct-interaction cases that suite doesn't reach, authored here with expected output captured from md4c itself.

All five are generated from the suites under `test/vendor/`; see [test/vendor/README.md](test/vendor/README.md). `test/MathDivergenceGuards.lean` is hand-written instead: it pins the inputs where this library's math output deliberately differs from md4c's, so that "fixing" one fails there and forces [KNOWN_ISSUES.md](KNOWN_ISSUES.md) to be updated alongside.

## Property-based testing

`test/GfmNonEmissionProperties.lean` uses [Plausible](https://github.com/leanprover-community/plausible) to fuzz two claims about parser fallback paths that aren't (yet) formally proven: that randomly generated tables and strikethrough-shaped input never lose text in the rendered output. `test/MathProperties.lean` fuzzes three more whole-pipeline claims, these about the LaTeX math extension: that math-shaped input keeps every `$` while the extension is off (what makes the opt-in real), that switching it on yields a math span carrying the LaTeX source through intact, and that no `$` survives once the delimiters have been consumed. `test/SanitizeExamples.lean` holds hand-picked examples of `Document.sanitize` neutralizing specific known-dangerous input end-to-end, a behavioral check on top of the proofs that legitimate content is not needlessly lost either.

## License

Apache License 2.0; see [LICENSE](LICENSE).
