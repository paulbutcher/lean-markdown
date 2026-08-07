-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import GFMarkdown.Ast
import GFMarkdown.Parser

/-! A GitHub Flavored Markdown (GFM) parser and renderer, built on top of `CommonMark`.

`GFMarkdown.Block`/`GFMarkdown.Document` (`GFMarkdown.Ast`) are the GFM-aware AST, adding
`table` alongside CommonMark's block kinds. Work in progress: see `GFM_PLAN.md` for the
implementation plan and current status. -/
