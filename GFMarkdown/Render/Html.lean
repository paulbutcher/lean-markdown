-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import GFMarkdown.Ast
import CommonMark.Render.Html
import Html

namespace GFMarkdown

open CommonMark (Inline)
open CommonMark.Parser (TableAlignment)

-- A bare "\n" leaf, valid in any content-model category (`Html.Node`'s `Coe String` instance
-- is category-polymorphic): `nodes` interspersed with one before each element and a final one
-- at the end, matching cmark-gfm's own `cr()`-before-each-child rendering convention for
-- tables (and, for `blockQuote`/`list` below, the same convention `CommonMark.Render.Html`
-- already follows).
private def interleaveNewlines {cat : Html.Category} (nodes : List (Html.Node cat)) :
    List (Html.Node cat) :=
  nodes.foldr (fun n acc => ("\n" : Html.Node cat) :: n :: acc) [("\n" : Html.Node cat)]

private def tableCellAlignAttrs : TableAlignment → List (String × String)
  | .left => [("align", "left")]
  | .right => [("align", "right")]
  | .center => [("align", "center")]
  | .unset => []

private def tableCellNode (isHeader : Bool) (alignment : TableAlignment)
    (content : List Inline) : Html.Node .tableCell :=
  let children : List (Html.Node .flow) :=
    (CommonMark.inlineListNodes content).map (fun (n : Html.Node .phrasing) => (n : Html.Node .flow))
  let attrs := tableCellAlignAttrs alignment
  if isHeader then Html.th children {} attrs else Html.td children {} attrs

private def tableRowNode (isHeader : Bool) (alignments : List TableAlignment)
    (cells : List (List Inline)) : Html.Node .tableRow :=
  Html.tr (interleaveNewlines (List.zipWith (tableCellNode isHeader) alignments cells))

private def tableNode (header : List (List Inline)) (alignments : List TableAlignment)
    (rows : List (List (List Inline))) : Html.Node .flow :=
  let theadNode := Html.thead (interleaveNewlines [tableRowNode true alignments header])
  let sections : List (Html.Node .tableSection) :=
    if rows.isEmpty then [theadNode]
    else [theadNode, Html.tbody (interleaveNewlines (rows.map (tableRowNode false alignments)))]
  Html.table (interleaveNewlines sections)

private def isCommonmarkParagraph : Block → Bool
  | .commonmark (.paragraph _) => true
  | _ => false

-- Mirrors `CommonMark.Render.Html`'s `renderBlockNodesF`/`renderBlocksNodeF`/`itemNode`
-- (fuel-bounded for the same reason: the doubly-nested `list` items make the structural
-- relationship opaque to the termination checker). `commonmark` delegates to the base
-- renderer's single-node case (fuel `1`, always sufficient since every `commonmark`-wrapped
-- block is a leaf, never `blockQuote`/`list`); `blockQuote`/`list`/`table` render natively so
-- a table nested at any depth still renders as one.
mutual
def renderBlockNodesF (tight : Bool) : Nat → Block → List (Html.Node .flow)
  | 0, _ => []
  | _ + 1, .commonmark b => CommonMark.renderBlockNodesF tight 1 b
  | fuel + 1, .blockQuote content =>
    [Html.blockquote (("\n" : Html.Node .flow) :: renderBlocksNodeF false fuel content), "\n"]
  | fuel + 1, .list kind isTight items =>
    let itemNodes : List (Html.Node .listItem) :=
      ("\n" : Html.Node .listItem) ::
        items.foldl (fun acc content => acc ++ [itemNode isTight fuel content, "\n"]) []
    let listNode : Html.Node .flow := match kind with
      | .bullet _ => Html.ul itemNodes
      | .ordered start _ =>
        if start == 1 then Html.ol itemNodes else Html.ol itemNodes { start := toString start }
    [listNode, "\n"]
  | _ + 1, .table header alignments rows => [tableNode header alignments rows, "\n"]

def renderBlocksNodeF (tight : Bool) : Nat → List Block → List (Html.Node .flow)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, b :: rest =>
    let bNodes := renderBlockNodesF tight fuel b
    let restNodes := renderBlocksNodeF tight fuel rest
    -- As in the base renderer: a tight paragraph renders with no trailing newline of its
    -- own, so it's the only block kind needing an explicit separator before a next sibling.
    if tight && !rest.isEmpty && isCommonmarkParagraph b then
      bNodes ++ [("\n" : Html.Node .flow)] ++ restNodes
    else bNodes ++ restNodes

def itemPrefix (isTight : Bool) (content : List Block) : List (Html.Node .flow) :=
  match content with
  | [] => []
  | b :: _ => if isTight && isCommonmarkParagraph b then [] else ["\n"]

def itemNode (isTight : Bool) (fuel : Nat) (content : List Block) : Html.Node .listItem :=
  Html.li (itemPrefix isTight content ++ renderBlocksNodeF isTight fuel content)
end

def renderBlocks (tight : Bool) (blocks : List Block) : String :=
  (renderBlocksNodeF tight (Block.listCount blocks + 1) blocks).foldl
    (fun acc n => acc ++ n.render (selfClosingVoid := true)) ""

/-- Renders a `Document` to HTML. Shares `CommonMark.renderHtml`'s escaping/safety
    guarantees for every non-table block, and for table cell content (both go through the
    same `Html` node constructors); the new `<table>`/`<thead>`/`<tbody>` structure is built
    the same way. -/
def renderHtml (doc : Document) : String :=
  renderBlocks false doc

end GFMarkdown
