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
private def inlineNodes (i : Inline) : List (Html.Node .phrasing) :=
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

private def inlineListNodes : List Inline → List (Html.Node .phrasing)
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

private def headingNode (level : Fin 6) (children : List (Html.Node .phrasing)) : Html.Node .flow :=
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
-- `blockquote`/`ul`/`ol`/`li` wrapping stays hand-assembled string concatenation, unlike
-- the leaf-level tags above: their content recurses back through this same fuel-bounded
-- pair, which doesn't fit `Html.Node`'s children-are-already-built-`Node`s shape without
-- restructuring the whole recursion into tree-building. Their open/closing tags are fixed
-- literal strings (or, for `<ol start="N">`, a `Nat` rendered via `toString`, never
-- containing `<`/`>`/`"`), so this doesn't cost anything at the leaves, only at these four
-- wrapper tags.
mutual
private def renderBlockF (tight : Bool) : Nat → Block → String
  | 0, _ => ""
  | _ + 1, .paragraph content =>
    if tight then renderInlines content
    else (Html.p (inlineListNodes content)).render (selfClosingVoid := true) ++ "\n"
  | _ + 1, .heading level content =>
    (headingNode level (inlineListNodes content)).render (selfClosingVoid := true) ++ "\n"
  | _ + 1, .codeBlock info literal =>
    let classAttrs : Html.HtmlAttrs := match info with
      | some i =>
        let lang := (i.splitOn " ").head?.getD i
        if lang.isEmpty then {} else { class_ := s!"language-{lang}" }
      | none => {}
    (Html.pre [Html.code [(literal : Html.Node .phrasing)] classAttrs]).render
      (selfClosingVoid := true) ++ "\n"
  | _ + 1, .thematicBreak => (Html.hr {}).render (selfClosingVoid := true) ++ "\n"
  | _ + 1, .htmlBlock s => if s.endsWith "\n" then s else s ++ "\n"
  | fuel + 1, .blockQuote content =>
    "<blockquote>\n" ++ renderBlocksF false fuel content ++ "</blockquote>\n"
  | fuel + 1, .list kind isTight items =>
    let (openTag, closeTag) := match kind with
      | .bullet _ => ("<ul>", "</ul>")
      | .ordered start _ =>
        if start == 1 then ("<ol>", "</ol>") else (s!"<ol start=\"{start}\">", "</ol>")
    -- Tightness only suppresses the paragraph wrapper (and its surrounding newlines); an
    -- item whose first block is anything else is rendered exactly as in a loose list.
    let itemOpen (content : List Block) : String :=
      match content with
      | [] => "<li>"
      | .paragraph _ :: _ => if isTight then "<li>" else "<li>\n"
      | _ => "<li>\n"
    let itemsHtml := items.foldl
      (fun acc content => acc ++ itemOpen content ++ renderBlocksF isTight fuel content ++ "</li>\n") ""
    openTag ++ "\n" ++ itemsHtml ++ closeTag ++ "\n"

private def renderBlocksF (tight : Bool) : Nat → List Block → String
  | 0, _ => ""
  | _ + 1, [] => ""
  | fuel + 1, b :: rest =>
    let bStr := renderBlockF tight fuel b
    let restStr := renderBlocksF tight fuel rest
    -- a tight paragraph renders with no trailing newline of its own; if another block
    -- follows within the same (tight) item, a separator is still needed between them
    if tight && !rest.isEmpty && !bStr.endsWith "\n" then bStr ++ "\n" ++ restStr
    else bStr ++ restStr
end

-- Public for the same reason as the inline renderers above: an extension whose own block
-- kinds contain ordinary `Block` content (e.g. a table cell containing a nested list)
-- needs to render it the same way `renderHtml` does. `tight` selects loose- vs.
-- tight-list-style paragraph wrapping, matching the meaning of `Block.list`'s own field.
def renderBlocks (tight : Bool) (blocks : List Block) : String :=
  renderBlocksF tight (Block.listCount blocks + 1) blocks

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
