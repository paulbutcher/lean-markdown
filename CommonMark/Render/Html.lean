-- Copyright (c) 2026 Paul Butcher. All rights reserved.
import CommonMark.Ast

namespace CommonMark

private def escapeChar (c : Char) : String :=
  match c with
  | '&' => "&amp;"
  | '<' => "&lt;"
  | '>' => "&gt;"
  | _ => c.toString

private def escapeText (s : String) : String :=
  s.foldl (init := "") fun acc c => acc ++ escapeChar c

private def renderInline (i : Inline) : String :=
  match i with
  | .text s => escapeText s

private def renderInlines (content : List Inline) : String :=
  content.foldl (init := "") fun acc i => acc ++ renderInline i

private def renderBlock (b : Block) : String :=
  match b with
  | .paragraph content => "<p>" ++ renderInlines content ++ "</p>\n"

def renderHtml (doc : Document) : String :=
  doc.foldl (init := "") fun acc b => acc ++ renderBlock b

end CommonMark
