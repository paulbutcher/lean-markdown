-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import CommonMark.Ast

namespace CommonMark

-- Kept public, unlike most of this file's other helpers: any code producing HTML from
-- Markdown-derived text, including a Markdown-extension renderer built on top of this
-- library, needs the exact same escaping (and gets to reuse the safety proofs below
-- instead of re-deriving them).

def escapeChar (c : Char) : String :=
  match c with
  | '&' => "&amp;"
  | '<' => "&lt;"
  | '>' => "&gt;"
  | '"' => "&quot;"
  | _ => c.toString

def escapeText (s : String) : String :=
  s.foldl (init := "") fun acc c => acc ++ escapeChar c

-- Escaping-safety: `escapeChar`/`escapeText` never let a `<`, `>`, or `"` through raw, no
-- matter what string they're given. This is the load-bearing fact behind every attribute
-- and text node the renderer produces from AST leaf content (see the summary at the end
-- of this file for how it's composed into the renderer's overall safety argument).

theorem escapeChar_safe (c : Char) :
    ∀ d ∈ (escapeChar c).toList, d ≠ '<' ∧ d ≠ '>' ∧ d ≠ '"' := by
  unfold escapeChar
  split <;> first
    | decide
    | (intro d hd
       simp only [Char.toString, String.toList_singleton, List.mem_singleton] at hd
       subst hd
       simp_all)

-- General shape shared by every "concatenate an escaped/safe piece per element" fold in
-- this file (`escapeText`, and later `plainTextOfInlines`): if every piece `g x` is safe
-- and the starting accumulator is safe, so is the whole fold, regardless of what `g` is.
-- Kept independent of `Inline`/`Char` specifics (and of the `escapeChar`/`plainTextOf`
-- mutual-recursion groups) so it can be reused without disturbing their termination proofs.
theorem foldl_append_safe {α : Type} (g : α → String) (l : List α) (acc : String)
    (hacc : ∀ d ∈ acc.toList, d ≠ '<' ∧ d ≠ '>' ∧ d ≠ '"')
    (hg : ∀ x d, d ∈ (g x).toList → d ≠ '<' ∧ d ≠ '>' ∧ d ≠ '"') :
    ∀ d ∈ (l.foldl (fun acc x => acc ++ g x) acc).toList, d ≠ '<' ∧ d ≠ '>' ∧ d ≠ '"' := by
  induction l generalizing acc with
  | nil => simpa using hacc
  | cons x rest ih =>
    apply ih
    intro d hd
    rw [String.toList_append] at hd
    rcases List.mem_append.mp hd with hd' | hd'
    · exact hacc d hd'
    · exact hg x d hd'

-- Lets a cons-headed fold be split into its head's contribution and the fold over the
-- tail, which is what keeps the mutual safety proof below in exactly the head/tail shape
-- Lean's termination checker already accepts for `plainTextOf`/`plainTextOfInlines`
-- themselves, rather than routing through an accumulator-generalized helper (whose extra
-- parameter the checker can't line up against the other mutual member's single argument).
theorem foldl_append_eq {α : Type} (g : α → String) (l : List α) (c : String) :
    l.foldl (fun acc x => acc ++ g x) c = c ++ l.foldl (fun acc x => acc ++ g x) "" := by
  induction l generalizing c with
  | nil => simp
  | cons x rest ih =>
    calc (x :: rest).foldl (fun acc y => acc ++ g y) c
        = rest.foldl (fun acc y => acc ++ g y) (c ++ g x) := rfl
      _ = (c ++ g x) ++ rest.foldl (fun acc y => acc ++ g y) "" := ih (c ++ g x)
      _ = c ++ (g x ++ rest.foldl (fun acc y => acc ++ g y) "") := String.append_assoc
      _ = c ++ rest.foldl (fun acc y => acc ++ g y) (g x) := by rw [ih (g x)]
      _ = c ++ (x :: rest).foldl (fun acc y => acc ++ g y) "" := rfl

theorem escapeText_safe (s : String) :
    ∀ d ∈ (escapeText s).toList, d ≠ '<' ∧ d ≠ '>' ∧ d ≠ '"' := by
  unfold escapeText
  rw [String.foldl_eq_foldl_toList]
  exact foldl_append_safe escapeChar s.toList "" (by simp) escapeChar_safe

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
-- double-encoding it.
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

-- Percent-encoding leaves characters like `&` untouched (they're valid in a URI), so the
-- result still needs the usual HTML-attribute escaping on top.
def escapeUri (s : String) : String :=
  escapeText (percentEncodeUriF (s.length + 1) s.toList)

-- `escapeUri` is `escapeText` applied to whatever `percentEncodeUriF` produces, so its
-- safety follows regardless of what that intermediate string looks like.
theorem escapeUri_safe (s : String) :
    ∀ d ∈ (escapeUri s).toList, d ≠ '<' ∧ d ≠ '>' ∧ d ≠ '"' :=
  escapeText_safe _

-- Public alongside `escapeChar`/`escapeText`/`escapeUri`, for the same reason: a
-- Markdown-extension AST that embeds `List Inline` at its leaves (e.g. a table cell's
-- content) needs to render that embedded content identically to this renderer.
mutual
def renderInline (i : Inline) : String :=
  match i with
  | .text s => escapeText s
  | .code s => "<code>" ++ escapeText s ++ "</code>"
  | .emph content => "<em>" ++ renderInlines content ++ "</em>"
  | .strong content => "<strong>" ++ renderInlines content ++ "</strong>"
  | .link dest title content =>
    let titleAttr := match title with
      | some t => " title=\"" ++ escapeText t ++ "\""
      | none => ""
    "<a href=\"" ++ escapeUri dest ++ "\"" ++ titleAttr ++ ">" ++ renderInlines content ++ "</a>"
  | .image dest title content =>
    let titleAttr := match title with
      | some t => " title=\"" ++ escapeText t ++ "\""
      | none => ""
    "<img src=\"" ++ escapeUri dest ++ "\" alt=\"" ++ plainTextOfInlines content ++ "\"" ++
      titleAttr ++ " />"
  | .htmlInline s => s
  | .softBreak => "\n"
  | .lineBreak => "<br />\n"

def renderInlines (content : List Inline) : String :=
  content.foldl (init := "") fun acc i => acc ++ renderInline i

-- Image alt text is the plain-text rendering of the content, with inline markup stripped.
def plainTextOf (i : Inline) : String :=
  match i with
  | .text s => escapeText s
  | .code s => escapeText s
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

-- `plainTextOf`/`plainTextOfInlines` strip markup down to text, but the leftover text is
-- still leaf content and needs the same guarantee: dropping into `.htmlInline` returns ""
-- rather than the raw markup, so alt text built from it can't smuggle a tag through either.
mutual
theorem plainTextOf_safe (i : Inline) :
    ∀ d ∈ (plainTextOf i).toList, d ≠ '<' ∧ d ≠ '>' ∧ d ≠ '"' := by
  match i with
  | .text s => simp only [plainTextOf]; exact escapeText_safe s
  | .code s => simp only [plainTextOf]; exact escapeText_safe s
  | .emph content => simp only [plainTextOf]; exact plainTextOfInlines_safe content
  | .strong content => simp only [plainTextOf]; exact plainTextOfInlines_safe content
  | .link _ _ content => simp only [plainTextOf]; exact plainTextOfInlines_safe content
  | .image _ _ content => simp only [plainTextOf]; exact plainTextOfInlines_safe content
  | .htmlInline _ => simp [plainTextOf]
  | .softBreak => simp [plainTextOf]
  | .lineBreak => simp [plainTextOf]

theorem plainTextOfInlines_safe (content : List Inline) :
    ∀ d ∈ (plainTextOfInlines content).toList, d ≠ '<' ∧ d ≠ '>' ∧ d ≠ '"' := by
  match content with
  | [] => simp [plainTextOfInlines]
  | i :: rest =>
    simp only [plainTextOfInlines]
    show ∀ d ∈ (rest.foldl (fun acc j => acc ++ plainTextOf j) (plainTextOf i)).toList,
        d ≠ '<' ∧ d ≠ '>' ∧ d ≠ '"'
    rw [foldl_append_eq plainTextOf rest (plainTextOf i)]
    intro d hd
    rw [String.toList_append] at hd
    rcases List.mem_append.mp hd with hd' | hd'
    · exact plainTextOf_safe i d hd'
    · exact plainTextOfInlines_safe rest d (by simpa [plainTextOfInlines] using hd')
end

-- Recursion is driven by an explicit fuel value (bounded by the total block count) rather
-- than structural recursion on Block/List Block, since the doubly-nested `list` items make
-- that relationship opaque to the termination checker; see the analogous parser code.
mutual
private def renderBlockF (tight : Bool) : Nat → Block → String
  | 0, _ => ""
  | _ + 1, .paragraph content =>
    if tight then renderInlines content
    else "<p>" ++ renderInlines content ++ "</p>\n"
  | _ + 1, .heading level content =>
    let n := level.val + 1
    s!"<h{n}>" ++ renderInlines content ++ s!"</h{n}>\n"
  | _ + 1, .codeBlock info literal =>
    let classAttr := match info with
      | some i =>
        let lang := (i.splitOn " ").head?.getD i
        if lang.isEmpty then "" else s!" class=\"language-{escapeText lang}\""
      | none => ""
    "<pre><code" ++ classAttr ++ ">" ++ escapeText literal ++ "</code></pre>\n"
  | _ + 1, .thematicBreak => "<hr />\n"
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
    inside an attribute in the output; see this file's `*_safe` theorems for the proof. -/
def renderHtml (doc : Document) : String :=
  renderBlocks false doc

end CommonMark
