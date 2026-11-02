-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import CommonMark.Ast
public import CommonMark.Parser.Entities
public import CommonMark.Parser.Block
public import CommonMark.Parser.Inline
public import CommonMark.Render.Html
public import CommonMark.Sanitize
public import CommonMark.Zipper

/-! A CommonMark 0.31.2 parser and HTML renderer.

Main entry points: `CommonMark.parseDocument : String → Document` and
`CommonMark.renderHtml : Document → String`. `Document`/`Block`/`Inline`
(`CommonMark.Ast`) are the parsed AST; `BlockZipper`/`InlineZipper`
(`CommonMark.Zipper`) provide cursor-style navigation and editing over it.

`parseDocument` is total and matches the official example suite exactly (see the
`#guard` checks in `test/SpecGuards.lean`). `renderHtml` renders the tree `htmlNodes` builds
(`CommonMark.Render.Nodes`), a lean-html-model tree generic over the element payload, so that a
consumer such as a virtual DOM can take the tree instead of the string; `htmlNodesSafe` gives one
with no raw HTML. Rendering is lean-html-renderer's, so every AST leaf's string content is
escaped by construction: it reaches the output only through `Html.escape` (`Html.escape_safe`)
or `Html.Attrs.render` (`Html.Attrs.render_safe`), both public facts of that library. -/
