-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import CommonMark.Parser.Block

namespace GFMarkdown

/-- Block-level content for the GFM variant. `blockQuote`/`list` recurse over `GFMarkdown.Block`
    rather than `CommonMark.Block`, so a table can appear at any nesting depth (inside a quote
    or list item), not just at the top level. `commonmark` is only ever constructed from
    CommonMark's non-recursive block kinds (paragraph, heading, codeBlock, thematicBreak,
    htmlBlock); a `blockQuote`/`list` is always represented via this type's own constructors
    instead, never wrapped inside `commonmark`. -/
inductive Block where
  | commonmark (b : CommonMark.Block)
  | blockQuote (content : List Block)
  | list       (kind : CommonMark.ListType) (tight : Bool) (items : List (List Block))
  | table      (header : List (List CommonMark.Inline))
               (alignments : List CommonMark.Parser.TableAlignment)
               (rows : List (List (List CommonMark.Inline)))
  deriving Repr, BEq

/-- A parsed GFM document: an ordered list of top-level blocks. -/
abbrev Document := List Block

end GFMarkdown
