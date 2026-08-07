-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import CommonMark.Ast
import Html

namespace CommonMark

-- HTML generation goes through `Html.Node`'s typed constructors (`Html/Tags.lean`,
-- `Html/Node.lean`) rather than hand-built strings: escaping, attribute quoting, and
-- balanced open/close tags all come from that library's own guarantees instead of being
-- re-derived here. `Html.Node.unsafeRaw` is used only for `.htmlInline`/`.htmlBlock`
-- passthrough, the one place literal, unescaped HTML from the Markdown source is meant to
-- reach the output verbatim.

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
-- HTML library would do); the HTML-attribute escaping a URI also needs on top happens
-- automatically wherever the result is used as an `Html` attribute value.
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

def percentEncodeUri (s : String) : String :=
  percentEncodeUriF (s.length + 1) s.toList

-- Image alt text and link/heading plain-text needs are the un-escaped text content, with
-- inline markup stripped; safe to embed anywhere since whatever consumes it (an `Html`
-- attribute value, in every current use) escapes on the way out.
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

def plainTextOfInlines (content : List Inline) : String :=
  content.foldl (init := "") fun acc i => acc ++ plainTextOf i
end

-- A run of inline content is a list of phrasing-content fragments rather than one node
-- per `Inline`: every case is one fragment except `.lineBreak`, which is two (`<br />`
-- then the literal newline that follows it in the spec's output), so the natural shape is
-- `Inline → List (Html.Node .phrasing)`, flattened over a `List Inline` by `inlineListNodes`.
mutual
def inlineNodes (i : Inline) : List (Html.Node .phrasing) :=
  match i with
  | .text s => [(s : Html.Node .phrasing)]
  | .code s => [Html.code [(s : Html.Node .phrasing)]]
  | .emph content => [Html.em (inlineListNodes content)]
  | .strong content => [Html.strong (inlineListNodes content)]
  | .link dest title content =>
    [Html.a { href := percentEncodeUri dest, title := title } (inlineListNodes content)]
  | .image dest title content =>
    [Html.img { src := percentEncodeUri dest, alt := plainTextOfInlines content, title := title }]
  | .htmlInline s => [Html.Node.unsafeRaw s]
  | .softBreak => [("\n" : Html.Node .phrasing)]
  | .lineBreak => [Html.br {}, ("\n" : Html.Node .phrasing)]

def inlineListNodes : List Inline → List (Html.Node .phrasing)
  | [] => []
  | i :: rest => inlineNodes i ++ inlineListNodes rest
end

-- Public alongside `plainTextOf`/`plainTextOfInlines`, for the same reason: a
-- Markdown-extension AST that embeds `List Inline` at its leaves (e.g. a table cell's
-- content) needs to render that embedded content identically to this renderer.
def renderInline (i : Inline) : String :=
  (inlineNodes i).foldl (fun acc n => acc ++ n.render (selfClosingVoid := true)) ""

def renderInlines (content : List Inline) : String :=
  (inlineListNodes content).foldl (fun acc n => acc ++ n.render (selfClosingVoid := true)) ""

def headingNode (level : Fin 6) (children : List (Html.Node .phrasing)) : Html.Node .flow :=
  match level.val with
  | 0 => Html.h1 children
  | 1 => Html.h2 children
  | 2 => Html.h3 children
  | 3 => Html.h4 children
  | 4 => Html.h5 children
  | _ => Html.h6 children

-- Recursion is driven by an explicit fuel value (bounded by the total block count) rather
-- than structural recursion on Block/List Block, since the doubly-nested `list` items make
-- that relationship opaque to the termination checker; see the analogous parser code.
--
-- The spec's exact-byte-match output has whitespace conventions (a newline after every
-- non-tight-paragraph block, a tight paragraph suppressing its own leading/trailing
-- newline, `<li>` vs `<li>\n`, ...) with no room in a well-typed `Node` tree for an
-- "almost-Node" -- they're represented as explicit `"\n"` leaves spliced into the
-- children lists alongside the real content. `Html.escape "\n" = "\n"` (no escapable
-- characters), and the library's `Coe String (Node cat)` instance is category-polymorphic,
-- so a bare `"\n"` is valid directly between `<li>` elements (`Node .listItem`), not just
-- inside flow/phrasing content.
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
        items.foldl (fun acc content => acc ++ [itemNode isTight fuel content, "\n"]) []
    let listNode : Html.Node .flow := match kind with
      | .bullet _ => Html.ul itemNodes
      | .ordered start _ =>
        if start == 1 then Html.ol itemNodes else Html.ol itemNodes { start := toString start }
    [listNode, "\n"]

def renderBlocksNodeF (tight : Bool) : Nat → List Block → List (Html.Node .flow)
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, b :: rest =>
    let bNodes := renderBlockNodesF tight fuel b
    let restNodes := renderBlocksNodeF tight fuel rest
    -- a tight paragraph renders with no trailing newline of its own; it's the only block
    -- kind that doesn't already end with one, so it's the only one needing a separator if
    -- another block follows within the same (tight) item.
    if tight && !rest.isEmpty && (match b with | .paragraph _ => true | _ => false) then
      bNodes ++ [("\n" : Html.Node .flow)] ++ restNodes
    else bNodes ++ restNodes

-- Tightness only suppresses the paragraph wrapper (and its surrounding newlines); an item
-- whose first block is anything else is rendered exactly as in a loose list.
def itemPrefix (isTight : Bool) (content : List Block) : List (Html.Node .flow) :=
  match content with
  | [] => []
  | .paragraph _ :: _ => if isTight then [] else ["\n"]
  | _ => ["\n"]

def itemNode (isTight : Bool) (fuel : Nat) (content : List Block) : Html.Node .listItem :=
  Html.li (itemPrefix isTight content ++ renderBlocksNodeF isTight fuel content)
end

-- Public for the same reason as the inline renderers above: an extension whose own block
-- kinds contain ordinary `Block` content (e.g. a table cell containing a nested list)
-- needs to render it the same way `renderHtml` does. `tight` selects loose- vs.
-- tight-list-style paragraph wrapping, matching the meaning of `Block.list`'s own field.
def renderBlocks (tight : Bool) (blocks : List Block) : String :=
  (renderBlocksNodeF tight (Block.listCount blocks + 1) blocks).foldl
    (fun acc n => acc ++ n.render (selfClosingVoid := true)) ""

/-- Renders a `Document` to HTML per the spec's exact escaping and formatting rules.
    No AST leaf's string content can produce unescaped `<`, `>`, `&`, or unescaped `"`
    inside an attribute in the output: every leaf reaches the output only through
    `Html.escape`/`Html.Attrs.render`, proved safe by `Html.escape_safe`/
    `Html.Attrs.render_safe` (github.com/paulbutcher/lean-html), or through
    `Html.Node.unsafeRaw` for `.htmlInline`/`.htmlBlock` passthrough, where verbatim
    HTML from the Markdown source is meant to reach the output unescaped. -/
def renderHtml (doc : Document) : String :=
  renderBlocks false doc

end CommonMark
