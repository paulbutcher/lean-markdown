-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import CommonMark.Ast
public import HtmlModel

@[expose] public section

namespace CommonMark

open HtmlModel

-- The tree is lean-html-model's, generic over the element payload, so that a consumer with a
-- payload of its own, such as a virtual DOM, can take it directly; `renderHtml` takes it at
-- lean-html-renderer's `Attrs`. Every element's children are checked against its content model
-- when the tree is built. `.verbatim` is used only for `.htmlInline`/`.htmlBlock` passthrough,
-- the one place literal, unescaped HTML from the Markdown source is meant to reach the output.

/-- An HTML node valid wherever category `cat` is, carrying payload `P` on each element. -/
abbrev HtmlNode (P : Type) (cat : Html.Cat) := Web.Node P (.html cat)

namespace HtmlNode

variable {P : Type}

def text {cat : Html.Cat} [h : Web.Widens .text (.html cat)] (s : String) : HtmlNode P cat :=
  Web.widen (.text s) h.widens

/-- A newline among children that aren't phrasing content, where text isn't allowed. -/
def newline {cat : Html.Cat} [h : Web.Widens .ws (.html cat)] : HtmlNode P cat :=
  Web.widen (Web.ws "\n") h.widens

def payload [HtmlPayload P] (attrs : List (String × String)) : P :=
  attrs.foldl (fun p (name, value) => HtmlPayload.attr name value p) HtmlPayload.empty

abbrev elem (e : Html.Elem) (cat content : Html.Cat) (p : P) (children : List (HtmlNode P content))
    (hc : Web.Cat.html cat ∈ Web.vocab.cats (.html e) := by decide +kernel)
    (ok : Web.vocab.Admits (.html e) (.html cat) [.many (.html content)] := by admits) :
    HtmlNode P cat :=
  Web.elem (.html e) (.html cat) p segs![.many (Nodes.ofList children)] hc ok

abbrev void (e : Html.Elem) (cat : Html.Cat) (p : P)
    (hc : Web.Cat.html cat ∈ Web.vocab.cats (.html e) := by decide +kernel)
    (ok : Web.vocab.Admits (.html e) (.html cat) [] := by admits) : HtmlNode P cat :=
  Web.elem (.html e) (.html cat) p segs![] hc ok

end HtmlNode

open HtmlNode

private def toHexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (n + '0'.toNat) else Char.ofNat (n - 10 + 'A'.toNat)

private def byteToPercent (b : Nat) : String :=
  "%" ++ (toHexDigit (b / 16)).toString ++ (toHexDigit (b % 16)).toString

-- The UTF-8 encoding of a Unicode scalar value, one byte per list element.
private def utf8Bytes (c : Char) : List Nat :=
  let cp := c.toNat
  if cp ≤ 0x7F then [cp]
  else if cp ≤ 0x7FF then [0xC0 ||| (cp >>> 6), 0x80 ||| (cp &&& 0x3F)]
  else if cp ≤ 0xFFFF then
    [0xE0 ||| (cp >>> 12), 0x80 ||| ((cp >>> 6) &&& 0x3F), 0x80 ||| (cp &&& 0x3F)]
  else
    [0xF0 ||| (cp >>> 18), 0x80 ||| ((cp >>> 12) &&& 0x3F),
     0x80 ||| ((cp >>> 6) &&& 0x3F), 0x80 ||| (cp &&& 0x3F)]

private def isHexDigitChar (c : Char) : Bool := c.isDigit || ('a' ≤ c.toLower && c.toLower ≤ 'f')

private def isUriSafeChar (c : Char) : Bool :=
  c.isAlphanum || "-_.!~*'();/?:@&=+$,#".toList.contains c

-- Matches the reference renderers' href/src encoding: percent-encode everything outside a
-- fixed safe set, but leave an existing well-formed %XX escape alone rather than
-- double-encoding it. This is CommonMark-specific (URI percent-encoding isn't something an
-- HTML library would do); the HTML-attribute escaping a URI also needs on top is the
-- renderer's, wherever the tree is rendered.
private def percentEncodeUriF : Nat → List Char → String
  | 0, _ => ""
  | _ + 1, [] => ""
  | fuel + 1, '%' :: h1 :: h2 :: rest =>
    if isHexDigitChar h1 && isHexDigitChar h2 then
      "%" ++ h1.toString ++ h2.toString ++ percentEncodeUriF fuel rest
    else "%25" ++ percentEncodeUriF fuel (h1 :: h2 :: rest)
  | fuel + 1, c :: rest =>
    if isUriSafeChar c then c.toString ++ percentEncodeUriF fuel rest
    else (utf8Bytes c).foldl (fun acc b => acc ++ byteToPercent b) "" ++ percentEncodeUriF fuel rest

@[no_expose]
def percentEncodeUri (s : String) : String :=
  percentEncodeUriF (s.length + 1) s.toList

/-- A `title` attribute when the link or image has one. -/
def titleAttr : Option String → List (String × String)
  | none => []
  | some t => [("title", t)]

-- Image alt text and link/heading plain-text needs are the un-escaped text content, with
-- inline markup stripped; safe to embed anywhere since whatever consumes it (an attribute
-- value, in every current use) is escaped by the renderer.
mutual
def plainTextOf (i : Inline) : String :=
  match i with
  | .text s => s
  | .code s => s
  | .emph content => plainTextOfInlines content
  | .strong content => plainTextOfInlines content
  | .link _ _ content => plainTextOfInlines content
  | .image _ _ content => plainTextOfInlines content
  | .htmlInline _ => ""
  | .softBreak => "\n"
  | .lineBreak => "\n"
  | .math _ s => s

def plainTextOfInlines (content : List Inline) : String :=
  content.foldl (init := "") fun acc i => acc ++ plainTextOf i
end

variable {P : Type} [HtmlPayload P]

-- A run of inline content is a list of phrasing-content fragments rather than one node
-- per `Inline`: every case is one fragment except `.lineBreak`, which is two (`<br />`
-- then the literal newline that follows it in the spec's output), so the natural shape is
-- `Inline → List (HtmlNode P .phrasing)`, flattened over a `List Inline` by `inlineListNodes`.
mutual
def inlineNodes (i : Inline) : List (HtmlNode P .phrasing) :=
  match i with
  | .text s => [text s]
  | .code s => [elem .code .phrasing .phrasing (payload []) [text s]]
  | .emph content => [elem .em .phrasing .phrasing (payload []) (inlineListNodes content)]
  | .strong content => [elem .strong .phrasing .phrasing (payload []) (inlineListNodes content)]
  | .link dest title content =>
    [elem .a .phrasing .phrasing (payload (("href", percentEncodeUri dest) :: titleAttr title))
      (inlineListNodes content)]
  | .image dest title content =>
    [Web.widen (void .img .image (payload
      ([("src", percentEncodeUri dest), ("alt", plainTextOfInlines content)] ++ titleAttr title)))]
  | .htmlInline s => [.verbatim s]
  | .softBreak => [text "\n"]
  | .lineBreak => [void .br .phrasing (payload []), text "\n"]
  -- The `\(`/`\[` delimiters are re-emitted around the LaTeX source rather than dropped with
  -- the `$`s: they are what a stock MathJax or KaTeX configuration scans for, so the output
  -- typesets with no further setup. The `math inline`/`math display` classes match what
  -- pandoc and commonmark-hs already emit.
  | .math display s =>
    [elem .span .phrasing .phrasing
      (payload [("class", if display then "math display" else "math inline")])
      [text (if display then "\\[" ++ s ++ "\\]" else "\\(" ++ s ++ "\\)")]]

def inlineListNodes : List Inline → List (HtmlNode P .phrasing)
  | [] => []
  | i :: rest => inlineNodes i ++ inlineListNodes rest
end

def headingNode (level : Fin 6) (children : List (HtmlNode P .phrasing)) : HtmlNode P .flow :=
  match level.val with
  | 0 => Web.widen (elem .h1 .heading .phrasing (payload []) children)
  | 1 => Web.widen (elem .h2 .heading .phrasing (payload []) children)
  | 2 => Web.widen (elem .h3 .heading .phrasing (payload []) children)
  | 3 => Web.widen (elem .h4 .heading .phrasing (payload []) children)
  | 4 => Web.widen (elem .h5 .heading .phrasing (payload []) children)
  | _ => Web.widen (elem .h6 .heading .phrasing (payload []) children)

def codeClassAttr : Option String → List (String × String)
  | some i =>
    let lang := (i.splitOn " ").head?.getD i
    if lang.isEmpty then [] else [("class", s!"language-{lang}")]
  | none => []

def listNode (kind : ListType) (items : List (HtmlNode P .listItemOrScript)) : HtmlNode P .flow :=
  match kind with
  | .bullet _ => elem .ul .flow .listItemOrScript (payload []) items
  | .ordered start _ =>
    elem .ol .flow .listItemOrScript (payload (if start == 1 then [] else [("start", toString start)]))
      items

-- Recursion is driven by an explicit fuel value (bounded by the total block count) rather
-- than structural recursion on Block/List Block, since the doubly-nested `list` items make
-- that relationship opaque to the termination checker; see the analogous parser code.
--
-- The spec's exact-byte-match output has whitespace conventions (a newline after every
-- non-tight-paragraph block, a tight paragraph suppressing its own leading/trailing
-- newline, `<li>` vs `<li>\n`, ...) with no room in a well-typed tree for an
-- "almost-Node"; they're represented as explicit newline leaves spliced into the
-- children lists alongside the real content: a `"\n"` text leaf among flow content, and
-- `HtmlNode.newline` between `<li>` elements, where text isn't allowed.
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
      newline :: items.foldl (fun acc content =>
        acc ++ [Web.widen (itemNode isTight fuel content), newline]) []
    [listNode kind itemNodes, text "\n"]

def renderBlocksNodeF (tight : Bool) : Nat → List Block → List (HtmlNode P .flow)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, b :: rest =>
    let bNodes := renderBlockNodesF tight fuel b
    let restNodes := renderBlocksNodeF tight fuel rest
    -- a tight paragraph renders with no trailing newline of its own; it's the only block
    -- kind that doesn't already end with one, so it's the only one needing a separator if
    -- another block follows within the same (tight) item.
    if tight && !rest.isEmpty && (match b with | .paragraph _ => true | _ => false) then
      bNodes ++ [text "\n"] ++ restNodes
    else bNodes ++ restNodes

-- Tightness only suppresses the paragraph wrapper (and its surrounding newlines); an item
-- whose first block is anything else is rendered exactly as in a loose list.
def itemPrefix (isTight : Bool) (content : List Block) : List (HtmlNode P .flow) :=
  match content with
  | [] => []
  | .paragraph _ :: _ => if isTight then [] else [text "\n"]
  | _ => [text "\n"]

def itemNode (isTight : Bool) (fuel : Nat) (content : List Block) : HtmlNode P .listItem :=
  elem .li .listItem .flow (payload []) (itemPrefix isTight content ++ renderBlocksNodeF isTight fuel content)
end

/-- The nodes `blocks` renders to. `tight` selects loose- vs. tight-list-style paragraph
    wrapping, matching the meaning of `Block.list`'s own field. Public so that an extension
    whose own block kinds contain ordinary `Block` content (e.g. a table cell containing a
    nested list) can build it the same way `htmlNodes` does. -/
def blocksNodes (tight : Bool) (blocks : List Block) : List (HtmlNode P .flow) :=
  renderBlocksNodeF tight (Block.listCount blocks + 1) blocks

/-- The tree `renderHtml` renders: the document as flow content, with every element's
    children checked against its content model. `.htmlInline`/`.htmlBlock` become verbatim
    leaves; `htmlNodesSafe` gives a tree with none. -/
def htmlNodes (doc : Document) : List (HtmlNode P .flow) :=
  blocksNodes false doc

end CommonMark
