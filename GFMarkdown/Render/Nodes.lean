-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import GFMarkdown.Ast
public import CommonMark.Render.Nodes

@[expose] public section

namespace GFMarkdown

open HtmlModel CommonMark CommonMark.HtmlNode
open CommonMark.Parser (RawInline TableAlignment)

-- Mirrors `CommonMark.plainTextOf`/`plainTextOfInlines`, extended with `strikethrough`.
mutual
def plainTextOf : RawInline → String
  | .text s => s
  | .code s => s
  | .emph content => plainTextOfList content
  | .strong content => plainTextOfList content
  | .link _ _ content => plainTextOfList content
  | .image _ _ content => plainTextOfList content
  | .htmlInline _ => ""
  | .softBreak => "\n"
  | .lineBreak => "\n"
  | .strikethrough content => plainTextOfList content
  | .math _ s => s

def plainTextOfList (content : List RawInline) : String :=
  content.foldl (init := "") fun acc i => acc ++ plainTextOf i
end

variable {P : Type} [HtmlPayload P]

-- Mirrors `CommonMark.inlineNodes`/`inlineListNodes`, extended with `strikethrough` (rendered
-- via `<del>`, matching cmark-gfm's own HTML output).
mutual
def inlineNodes (i : RawInline) : List (HtmlNode P .phrasing) :=
  match i with
  | .text s => [text s]
  | .code s => [elem .code .phrasing .phrasing (payload []) [text s]]
  | .emph content => [elem .em .phrasing .phrasing (payload []) (inlineListNodes content)]
  | .strong content => [elem .strong .phrasing .phrasing (payload []) (inlineListNodes content)]
  | .link dest title content =>
    [elem .a .phrasing .phrasing
      (payload (("href", CommonMark.percentEncodeUri dest) :: titleAttr title))
      (inlineListNodes content)]
  | .image dest title content =>
    [Web.widen (void .img .image (payload
      ([("src", CommonMark.percentEncodeUri dest), ("alt", plainTextOfList content)] ++
        titleAttr title)))]
  | .htmlInline s => [.verbatim s]
  | .softBreak => [text "\n"]
  | .lineBreak => [void .br .phrasing (payload []), text "\n"]
  | .strikethrough content => [elem .del .phrasing .phrasing (payload []) (inlineListNodes content)]
  -- Identical to `CommonMark.inlineNodes`' `.math` case; see the comment there for why the
  -- `\(`/`\[` delimiters are re-emitted.
  | .math display s =>
    [elem .span .phrasing .phrasing
      (payload [("class", if display then "math display" else "math inline")])
      [text (if display then "\\[" ++ s ++ "\\]" else "\\(" ++ s ++ "\\)")]]

def inlineListNodes : List RawInline → List (HtmlNode P .phrasing)
  | [] => []
  | i :: rest => inlineNodes i ++ inlineListNodes rest
end

-- `nodes` interspersed with a newline before each element and a final one at the end, matching
-- cmark-gfm's own `cr()`-before-each-child rendering convention for tables.
def interleaveNewlines {cat : Html.Cat} [Web.Widens .ws (.html cat)]
    (nodes : List (HtmlNode P cat)) : List (HtmlNode P cat) :=
  nodes.foldr (fun n acc => newline :: n :: acc) [newline]

def tableCellAlignAttrs : TableAlignment → List (String × String)
  | .left => [("align", "left")]
  | .right => [("align", "right")]
  | .center => [("align", "center")]
  | .unset => []

def tableCellNode (isHeader : Bool) (alignment : TableAlignment)
    (content : List RawInline) : HtmlNode P .tableCell :=
  let children : List (HtmlNode P .flow) := (inlineListNodes content).map Web.widen
  let attrs := payload (tableCellAlignAttrs alignment)
  if isHeader then elem .th .tableCell .flow attrs children
  else elem .td .tableCell .flow attrs children

def tableRowNode (isHeader : Bool) (alignments : List TableAlignment)
    (cells : List (List RawInline)) : HtmlNode P .tableRow :=
  elem .tr .tableRow .tableCellOrScript (payload [])
    (interleaveNewlines (List.zipWith (fun a c => Web.widen (tableCellNode isHeader a c))
      alignments cells))

-- The newline after `<table>` goes in the column-group slot, the only whitespace-admitting one
-- ahead of the head.
def tableNode (header : List (List RawInline)) (alignments : List TableAlignment)
    (rows : List (List (List RawInline))) : HtmlNode P .flow :=
  let theadNode : HtmlNode P .tableHead :=
    elem .thead .tableHead .tableRowOrScript (payload [])
      (interleaveNewlines [Web.widen (tableRowNode true alignments header)])
  let body : List (HtmlNode P .tableBodyOrScript) :=
    if rows.isEmpty then [newline]
    else interleaveNewlines [Web.widen (elem .tbody .tableBody .tableRowOrScript (payload [])
      (interleaveNewlines (rows.map fun r => Web.widen (tableRowNode false alignments r))))]
  Web.elem (.html .table) (.html .flow) (payload [])
    segs![.many (Nodes.ofList [(newline : HtmlNode P .tableColumnGroupOrScript)]), .one theadNode,
      .many (Nodes.ofList body)]

-- Mirrors `CommonMark.renderBlockNodesF`/`renderBlocksNodeF`/`itemNode` structurally
-- (fuel-bounded for the same reason: the doubly-nested `list` items make the structural
-- relationship opaque to the termination checker), since `GFMarkdown.Block` mirrors
-- `CommonMark.Block`'s shape directly rather than wrapping it.
mutual
def renderBlockNodesF (tight : Bool) : Nat → Block → List (HtmlNode P .flow)
  | 0, _ => []
  | _ + 1, .paragraph content =>
    if tight then (inlineListNodes content).map Web.widen
    else [Web.widen (elem .p .paragraph .phrasing (payload []) (inlineListNodes content)), text "\n"]
  | _ + 1, .heading level content => [headingNode level (inlineListNodes content), text "\n"]
  | _ + 1, .codeBlock info literal =>
    [elem .pre .flow .phrasing (payload [])
      [elem .code .phrasing .phrasing (payload (codeClassAttr info)) [text literal]], text "\n"]
  | _ + 1, .thematicBreak => [void .hr .flow (payload []), text "\n"]
  | _ + 1, .htmlBlock s => [.verbatim (if s.endsWith "\n" then s else s ++ "\n")]
  | fuel + 1, .blockQuote content =>
    [elem .blockquote .flow .flow (payload []) (text "\n" :: renderBlocksNodeF false fuel content),
      text "\n"]
  | fuel + 1, .list kind isTight items =>
    let itemNodes : List (HtmlNode P .listItemOrScript) :=
      newline :: items.foldl (fun acc (checked, content) =>
        acc ++ [Web.widen (itemNode isTight fuel checked content), newline]) []
    [listNode kind itemNodes, text "\n"]
  | _ + 1, .table header alignments rows => [tableNode header alignments rows, text "\n"]

-- `checked = some _` prefixes the item with GFM's disabled checkbox, taking the place of the
-- `[ ] `/`[x] ` text `GFMarkdown.Parser.taskListChecked` stripped from its first paragraph.
-- `disabled`/`checked` carry explicit empty values rather than being flags: a flag renders as
-- `disabled="disabled"` under `.xhtml`, but cmark-gfm's own output (and this library's
-- conformance target) uses `disabled=""`/`checked=""`, checked before disabled.
def checkboxNodes (checked : Option Bool) : List (HtmlNode P .flow) :=
  match checked with
  | none => []
  | some isChecked =>
    let stateAttrs := if isChecked then [("checked", ""), ("disabled", "")] else [("disabled", "")]
    [Web.widen (void .input .phrasing (payload (("type", "checkbox") :: stateAttrs))), text " "]

def renderBlocksNodeF (tight : Bool) : Nat → List Block → List (HtmlNode P .flow)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, b :: rest =>
    let bNodes := renderBlockNodesF tight fuel b
    let restNodes := renderBlocksNodeF tight fuel rest
    -- As in the base renderer: a tight paragraph renders with no trailing newline of its
    -- own, so it's the only block kind needing an explicit separator before a next sibling.
    if tight && !rest.isEmpty && (match b with | .paragraph _ => true | _ => false) then
      bNodes ++ [text "\n"] ++ restNodes
    else bNodes ++ restNodes

def itemPrefix (isTight : Bool) (content : List Block) : List (HtmlNode P .flow) :=
  match content with
  | [] => []
  | .paragraph _ :: _ => if isTight then [] else [text "\n"]
  | _ => [text "\n"]

def itemNode (isTight : Bool) (fuel : Nat) (checked : Option Bool) (content : List Block) :
    HtmlNode P .listItem :=
  elem .li .listItem .flow (payload [])
    (checkboxNodes checked ++ itemPrefix isTight content ++ renderBlocksNodeF isTight fuel content)
end

def blocksNodes (tight : Bool) (blocks : List Block) : List (HtmlNode P .flow) :=
  renderBlocksNodeF tight (Block.listCount blocks + 1) blocks

/-- The tree `renderHtml` renders. See `CommonMark.htmlNodes`. -/
def htmlNodes (doc : Document) : List (HtmlNode P .flow) :=
  blocksNodes false doc

end GFMarkdown
