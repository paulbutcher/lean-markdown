-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import CommonMark.Ast
import CommonMark.Parser.Entities
import CommonMark.Parser.Block
import CommonMark.Parser.Inline
import CommonMark.Render.Html
import CommonMark.Zipper

/-! A CommonMark 0.31.2 parser and HTML renderer.

Main entry points: `CommonMark.parseDocument : String → Document` and
`CommonMark.renderHtml : Document → String`. `Document`/`Block`/`Inline`
(`CommonMark.Ast`) are the parsed AST; `BlockZipper`/`InlineZipper`
(`CommonMark.Zipper`) provide cursor-style navigation and editing over it.

`parseDocument` is total and matches the official example suite exactly (see the
`#guard` checks in `test/SpecGuards.lean`); `renderHtml` builds its output
through the `Html` library's typed constructors (github.com/paulbutcher/lean-html) rather
than hand-rolled string concatenation, so every AST leaf's string content is escaped by
construction: it reaches the output only through `Html.Node.text`/`Html.Node.textElement`
(`Html.escape_safe`, `Html.Node.render_text_safe`, `Html.Node.render_textElement_safe`) or
`Html.Attrs.render` (`Html.Attrs.render_safe`), all public facts of that library. -/
