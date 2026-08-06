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

private def renderInline (i : Inline) : String :=
  match i with
  | .text s => escapeText s

private def renderInlines (content : List Inline) : String :=
  content.foldl (init := "") fun acc i => acc ++ renderInline i

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
    if tight then renderInlines content ++ "\n"
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
    let itemsHtml := items.foldl
      (fun acc content => acc ++ "<li>" ++ renderBlocksF isTight fuel content ++ "</li>\n") ""
    openTag ++ "\n" ++ itemsHtml ++ closeTag ++ "\n"

private def renderBlocksF (tight : Bool) : Nat → List Block → String
  | 0, _ => ""
  | _ + 1, [] => ""
  | fuel + 1, b :: rest => renderBlockF tight fuel b ++ renderBlocksF tight fuel rest
end

private def renderBlocks (tight : Bool) (blocks : List Block) : String :=
  renderBlocksF tight (blockListCount blocks + 1) blocks

def renderHtml (doc : Document) : String :=
  renderBlocks false doc

end CommonMark
