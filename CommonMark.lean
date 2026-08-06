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

`parseDocument` is total and matches the official example suite exactly (see
`commonmark_conformance` in `test/Conformance.lean`); `renderHtml` is proved not to let
any AST leaf's string content produce unescaped HTML markup or break out of an
attribute (see the `*_safe` theorems in `CommonMark.Render.Html`). -/
