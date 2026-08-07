-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import GFMarkdown.Ast
import CommonMark.Render.Html
import Html

namespace GFMarkdown

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

def plainTextOfList (content : List RawInline) : String :=
  content.foldl (init := "") fun acc i => acc ++ plainTextOf i
end

-- Mirrors `CommonMark.inlineNodes`/`inlineListNodes`, extended with `strikethrough` (rendered
-- via `<del>`, matching cmark-gfm's own HTML output).
mutual
def inlineNodes (i : RawInline) : List (Html.Node .phrasing) :=
  match i with
  | .text s => [(s : Html.Node .phrasing)]
  | .code s => [Html.code [(s : Html.Node .phrasing)]]
  | .emph content => [Html.em (inlineListNodes content)]
  | .strong content => [Html.strong (inlineListNodes content)]
  | .link dest title content =>
    [Html.a { href := CommonMark.percentEncodeUri dest, title := title } (inlineListNodes content)]
  | .image dest title content =>
    [Html.img { src := CommonMark.percentEncodeUri dest, alt := plainTextOfList content, title := title }]
  | .htmlInline s => [Html.Node.unsafeRaw s]
  | .softBreak => [("\n" : Html.Node .phrasing)]
  | .lineBreak => [Html.br {}, ("\n" : Html.Node .phrasing)]
  | .strikethrough content => [Html.del (inlineListNodes content)]

def inlineListNodes : List RawInline → List (Html.Node .phrasing)
  | [] => []
  | i :: rest => inlineNodes i ++ inlineListNodes rest
end

def headingNode (level : Fin 6) (children : List (Html.Node .phrasing)) : Html.Node .flow :=
  match level.val with
  | 0 => Html.h1 children
  | 1 => Html.h2 children
  | 2 => Html.h3 children
  | 3 => Html.h4 children
  | 4 => Html.h5 children
  | _ => Html.h6 children

-- A bare "\n" leaf, valid in any content-model category (`Html.Node`'s `Coe String` instance
-- is category-polymorphic): `nodes` interspersed with one before each element and a final one
-- at the end, matching cmark-gfm's own `cr()`-before-each-child rendering convention for
-- tables.
def interleaveNewlines {cat : Html.Category} (nodes : List (Html.Node cat)) :
    List (Html.Node cat) :=
  nodes.foldr (fun n acc => ("\n" : Html.Node cat) :: n :: acc) [("\n" : Html.Node cat)]

private def tableCellAlignAttrs : TableAlignment → List (String × String)
  | .left => [("align", "left")]
  | .right => [("align", "right")]
  | .center => [("align", "center")]
  | .unset => []

def tableCellNode (isHeader : Bool) (alignment : TableAlignment)
    (content : List RawInline) : Html.Node .tableCell :=
  let children : List (Html.Node .flow) :=
    (inlineListNodes content).map (fun (n : Html.Node .phrasing) => (n : Html.Node .flow))
  let attrs := tableCellAlignAttrs alignment
  if isHeader then Html.th children {} attrs else Html.td children {} attrs

def tableRowNode (isHeader : Bool) (alignments : List TableAlignment)
    (cells : List (List RawInline)) : Html.Node .tableRow :=
  Html.tr (interleaveNewlines (List.zipWith (tableCellNode isHeader) alignments cells))

def tableNode (header : List (List RawInline)) (alignments : List TableAlignment)
    (rows : List (List (List RawInline))) : Html.Node .flow :=
  let theadNode := Html.thead (interleaveNewlines [tableRowNode true alignments header])
  let sections : List (Html.Node .tableSection) :=
    if rows.isEmpty then [theadNode]
    else [theadNode, Html.tbody (interleaveNewlines (rows.map (tableRowNode false alignments)))]
  Html.table (interleaveNewlines sections)

-- Mirrors `CommonMark.Render.Html`'s `renderBlockNodesF`/`renderBlocksNodeF`/`itemNode`
-- structurally (fuel-bounded for the same reason: the doubly-nested `list` items make the
-- structural relationship opaque to the termination checker), since `GFMarkdown.Block` now
-- mirrors `CommonMark.Block`'s shape directly rather than wrapping it.
mutual
def renderBlockNodesF (tight : Bool) : Nat → Block → List (Html.Node .flow)
  | 0, _ => []
  | _ + 1, .paragraph content =>
    if tight then (inlineListNodes content).map (fun (n : Html.Node .phrasing) => (n : Html.Node .flow))
    else [Html.p (inlineListNodes content), "\n"]
  | _ + 1, .heading level content => [headingNode level (inlineListNodes content), "\n"]
  | _ + 1, .codeBlock info literal =>
    let classAttrs : Html.HtmlAttrs := match info with
      | some i =>
        let lang := (i.splitOn " ").head?.getD i
        if lang.isEmpty then {} else { class_ := s!"language-{lang}" }
      | none => {}
    [Html.pre [Html.code [(literal : Html.Node .phrasing)] classAttrs], "\n"]
  | _ + 1, .thematicBreak => [Html.hr {}, "\n"]
  | _ + 1, .htmlBlock s => [Html.Node.unsafeRaw (if s.endsWith "\n" then s else s ++ "\n")]
  | fuel + 1, .blockQuote content =>
    [Html.blockquote (("\n" : Html.Node .flow) :: renderBlocksNodeF false fuel content), "\n"]
  | fuel + 1, .list kind isTight items =>
    let itemNodes : List (Html.Node .listItem) :=
      ("\n" : Html.Node .listItem) ::
        items.foldl (fun acc (checked, content) =>
          acc ++ [itemNode isTight fuel checked content, "\n"]) []
    let listNode : Html.Node .flow := match kind with
      | .bullet _ => Html.ul itemNodes
      | .ordered start _ =>
        if start == 1 then Html.ol itemNodes else Html.ol itemNodes { start := toString start }
    [listNode, "\n"]
  | _ + 1, .table header alignments rows => [tableNode header alignments rows, "\n"]

-- `checked = some _` prefixes the item with GFM's disabled checkbox, taking the place of the
-- `[ ] `/`[x] ` text `GFMarkdown.Parser.taskListChecked` stripped from its first paragraph.
-- `disabled`/`checked` are built via `rawAttrs`, not `InputAttrs`'s own boolean fields: those
-- render as bare HTML5-minimized flags (`disabled`), but cmark-gfm's own output (and this
-- library's conformance target) uses explicit `disabled=""`/`checked=""`, checked before
-- disabled.
def checkboxNodes (checked : Option Bool) : List (Html.Node .flow) :=
  match checked with
  | none => []
  | some isChecked =>
    let stateAttrs := if isChecked then [("checked", ""), ("disabled", "")] else [("disabled", "")]
    [(Html.input { type := "checkbox" } stateAttrs : Html.Node .flow), " "]

def renderBlocksNodeF (tight : Bool) : Nat → List Block → List (Html.Node .flow)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, b :: rest =>
    let bNodes := renderBlockNodesF tight fuel b
    let restNodes := renderBlocksNodeF tight fuel rest
    -- As in the base renderer: a tight paragraph renders with no trailing newline of its
    -- own, so it's the only block kind needing an explicit separator before a next sibling.
    if tight && !rest.isEmpty && (match b with | .paragraph _ => true | _ => false) then
      bNodes ++ [("\n" : Html.Node .flow)] ++ restNodes
    else bNodes ++ restNodes

def itemPrefix (isTight : Bool) (content : List Block) : List (Html.Node .flow) :=
  match content with
  | [] => []
  | .paragraph _ :: _ => if isTight then [] else ["\n"]
  | _ => ["\n"]

def itemNode (isTight : Bool) (fuel : Nat) (checked : Option Bool) (content : List Block) :
    Html.Node .listItem :=
  Html.li (checkboxNodes checked ++ itemPrefix isTight content ++ renderBlocksNodeF isTight fuel content)
end

def renderBlocks (tight : Bool) (blocks : List Block) : String :=
  (renderBlocksNodeF tight (Block.listCount blocks + 1) blocks).foldl
    (fun acc n => acc ++ n.render (selfClosingVoid := true)) ""

/-- Renders a `Document` to HTML. Shares `CommonMark.renderHtml`'s escaping/safety guarantees
    (both go through the same `Html` node constructors); the new `<table>`/`<thead>`/`<tbody>`
    and `<del>` structure is built the same way. -/
def renderHtml (doc : Document) : String :=
  renderBlocks false doc

end GFMarkdown
