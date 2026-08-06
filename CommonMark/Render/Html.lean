-- Copyright (c) 2026 Paul Butcher. All rights reserved.
import CommonMark.Ast

namespace CommonMark

private def escapeChar (c : Char) : String :=
  match c with
  | '&' => "&amp;"
  | '<' => "&lt;"
  | '>' => "&gt;"
  | '"' => "&quot;"
  | _ => c.toString

private def escapeText (s : String) : String :=
  s.foldl (init := "") fun acc c => acc ++ escapeChar c

-- Href/src attribute values get the same HTML-attribute escaping as text; full URI
-- percent-encoding (as cmark does) is not yet implemented.
private def escapeUri (s : String) : String := escapeText s

mutual
private def renderInline (i : Inline) : String :=
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

private def renderInlines (content : List Inline) : String :=
  content.foldl (init := "") fun acc i => acc ++ renderInline i

-- Image alt text is the plain-text rendering of the content, with inline markup stripped.
private def plainTextOf (i : Inline) : String :=
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

private def plainTextOfInlines (content : List Inline) : String :=
  content.foldl (init := "") fun acc i => acc ++ plainTextOf i
end

mutual
private def blockCount : Block → Nat
  | .blockQuote content => 1 + blockListCount content
  | .list _ _ items => 1 + items.foldl (fun acc c => acc + blockListCount c) 0
  | _ => 1

private def blockListCount : List Block → Nat
  | [] => 0
  | b :: rest => 1 + blockCount b + blockListCount rest
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
        if lang.isEmpty then "" else s!" class=\"language-{lang}\""
      | none => ""
    "<pre><code" ++ classAttr ++ ">" ++ escapeText literal ++ "</code></pre>\n"
  | _ + 1, .thematicBreak => "<hr />\n"
  | _ + 1, .htmlBlock s => s
  | fuel + 1, .blockQuote content =>
    "<blockquote>\n" ++ renderBlocksF false fuel content ++ "</blockquote>\n"
  | fuel + 1, .list kind isTight items =>
    let (openTag, closeTag) := match kind with
      | .bullet _ => ("<ul>", "</ul>")
      | .ordered start _ =>
        if start == 1 then ("<ol>", "</ol>") else (s!"<ol start=\"{start}\">", "</ol>")
    let itemOpen := if isTight then "<li>" else "<li>\n"
    let itemsHtml := items.foldl
      (fun acc content => acc ++ itemOpen ++ renderBlocksF isTight fuel content ++ "</li>\n") ""
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

private def renderBlocks (tight : Bool) (blocks : List Block) : String :=
  renderBlocksF tight (blockListCount blocks + 1) blocks

def renderHtml (doc : Document) : String :=
  renderBlocks false doc

end CommonMark
