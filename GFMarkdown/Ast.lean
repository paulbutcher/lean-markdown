-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import CommonMark.Parser.Block

namespace GFMarkdown

/-- Block-level content for the GFM variant: `CommonMark.Block`'s shape exactly (so
    `blockQuote`/`list` recurse over `GFMarkdown.Block`, and a table can appear at any nesting
    depth, not just at the top level), but with `CommonMark.Parser.RawInline` in place of
    `CommonMark.Inline` wherever inline content is held, so a `paragraph`/`heading`/table cell
    can contain a `strikethrough`, plus `table` itself. There's no `CommonMark.Block` wrapper
    for the non-recursive kinds (paragraph/heading/codeBlock/thematicBreak/htmlBlock): once
    `paragraph`/`heading` need their own `RawInline`-typed content, wrapping the rest bought
    nothing but an extra case to unwrap everywhere. -/
inductive Block where
  | paragraph  (content : List CommonMark.Parser.RawInline)
  | heading    (level : Fin 6) (content : List CommonMark.Parser.RawInline)
  | codeBlock  (info : Option String) (literal : String)
  | blockQuote (content : List Block)
  | list       (kind : CommonMark.ListType) (tight : Bool) (items : List (List Block))
  | thematicBreak
  | htmlBlock  (s : String)
  | table      (header : List (List CommonMark.Parser.RawInline))
               (alignments : List CommonMark.Parser.TableAlignment)
               (rows : List (List (List CommonMark.Parser.RawInline)))
  deriving Repr, BEq

/-- A parsed GFM document: an ordered list of top-level blocks. -/
abbrev Document := List Block

-- Total node count, used to size fuel for the renderer's recursion (mirrors
-- `CommonMark.Block.count`/`listCount`, for the same reason: the doubly-nested `list` items
-- make the structural relationship opaque to the termination checker).
mutual
def Block.count : Block → Nat
  | .blockQuote content => 1 + Block.listCount content
  | .list _ _ items => 1 + items.foldl (fun acc c => acc + Block.listCount c) 0
  | _ => 1

def Block.listCount : List Block → Nat
  | [] => 0
  | b :: rest => 1 + Block.count b + Block.listCount rest
end

end GFMarkdown
