-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import GFMarkdown.Ast

-- GFM's raw-HTML "tag filter" extension: neuters a fixed list of tags (`title`, `textarea`,
-- `style`, `xmp`, `iframe`, `noembed`, `noframes`, `script`, `plaintext`) wherever they appear
-- in `.htmlInline`/`.htmlBlock` content, by escaping just the opening `<` to `&lt;` -- leaving
-- the tag name and its own `>` as literal text, so `<script>` renders as `&lt;script>`, not
-- `&lt;script&gt;` and not dropped entirely. Grounded in cmark-gfm's `extensions/tagfilter.c`
-- (`is_tag`/`filter`) and `src/html.c`'s `filter_html_block`/`CMARK_NODE_HTML_INLINE` case,
-- fetched and read directly: the "only the `<` changes, only when followed by a word boundary"
-- behavior isn't obvious from the example suite alone (e.g. why `<scripter>` must survive
-- unfiltered). Implemented as an AST-level pass (`tagFilterDocument`), same as `Autolink.lean`,
-- to stay composable with the rest of the pipeline rather than living in the renderer.
namespace GFMarkdown

open CommonMark.Parser (RawInline isUnicodeWhitespace)

def tagFilterBlacklist : List String :=
  ["title", "textarea", "style", "xmp", "iframe", "noembed", "noframes", "script", "plaintext"]

-- Does `chars` (already known to start with `<`) open or close exactly `tagName`
-- (case-insensitive), immediately followed by whitespace, `>`, or `/>`? The trailing-boundary
-- check is what stops `<scripter>` (a real, harmless tag name that merely starts with
-- "script") from being caught by the filter.
def isTagAt (chars : List Char) (tagName : String) : Bool :=
  match chars with
  | '<' :: rest =>
    let afterSlash := match rest with | '/' :: r => r | r => r
    let nameLen := tagName.length
    let namePrefix := afterSlash.take nameLen
    if namePrefix.length < nameLen then false
    else if String.ofList (namePrefix.map Char.toLower) ≠ tagName.toLower then false
    else
      match afterSlash.drop nameLen with
      | [] => false
      | c :: cs => isUnicodeWhitespace c || c == '>' || (c == '/' && cs.head? == some '>')
  | _ => false

def shouldFilterTagAt (chars : List Char) : Bool :=
  tagFilterBlacklist.any (isTagAt chars)

private def filterHtmlGo : Nat → List Char → List Char
  | 0, chars => chars
  | _ + 1, [] => []
  | fuel + 1, '<' :: rest =>
    (if shouldFilterTagAt ('<' :: rest) then "&lt;".toList else ['<']) ++ filterHtmlGo fuel rest
  | fuel + 1, c :: rest => c :: filterHtmlGo fuel rest

-- Mirrors cmark-gfm's `filter_html_block`/inline filtering: scans for every `<` in `s`, and
-- replaces just the ones that open/close a blacklisted tag.
def filterHtml (s : String) : String :=
  String.ofList (filterHtmlGo (s.length + 1) s.toList)

-- Recurses everywhere, including into an already-formed link's content (unlike
-- `Autolink.lean`'s walk): tag filtering has nothing to do with link nesting, so
-- `[<xmp>x</xmp>](url)` still needs its `<xmp>` filtered. No fuel needed here (unlike
-- `Autolink.lean`'s equivalent): each recursive call lands on a literal structural subterm of
-- its argument, the same pattern `narrowInline`/`narrowInlineList` already use without fuel.
mutual
def filterInline : RawInline → RawInline
  | .htmlInline s => .htmlInline (filterHtml s)
  | .emph content => .emph (filterInlineList content)
  | .strong content => .strong (filterInlineList content)
  | .strikethrough content => .strikethrough (filterInlineList content)
  | .link dest title content => .link dest title (filterInlineList content)
  | .image dest title content => .image dest title (filterInlineList content)
  | other => other

def filterInlineList : List RawInline → List RawInline
  | [] => []
  | i :: rest => filterInline i :: filterInlineList rest
end

-- Mirrors `autolinkBlockF`/`autolinkBlockListF`/`autolinkItemsF`'s fuel-bounded mutual
-- recursion (same reason: the doubly-nested `list` items hide the structural relationship
-- from the termination checker).
mutual
def filterBlockF : Nat → Block → Block
  | 0, b => b
  | _ + 1, .paragraph content => .paragraph (filterInlineList content)
  | _ + 1, .heading level content => .heading level (filterInlineList content)
  | _ + 1, .codeBlock info lit => .codeBlock info lit
  | fuel + 1, .blockQuote content => .blockQuote (filterBlockListF fuel content)
  | fuel + 1, .list kind tight items => .list kind tight (filterItemsF fuel items)
  | _ + 1, .thematicBreak => .thematicBreak
  | _ + 1, .htmlBlock s => .htmlBlock (filterHtml s)
  | _ + 1, .table header alignments rows =>
    .table (header.map filterInlineList) alignments (rows.map (List.map filterInlineList))

def filterBlockListF : Nat → List Block → List Block
  | 0, bs => bs
  | _ + 1, [] => []
  | fuel + 1, b :: rest => filterBlockF fuel b :: filterBlockListF fuel rest

def filterItemsF : Nat → List (Option Bool × List Block) → List (Option Bool × List Block)
  | 0, items => items
  | _ + 1, [] => []
  | fuel + 1, (checked, c) :: rest => (checked, filterBlockListF fuel c) :: filterItemsF fuel rest
end

/-- The raw-HTML tag filter, applied over a whole `Document`: escapes the opening `<` of any
    `title`/`textarea`/`style`/`xmp`/`iframe`/`noembed`/`noframes`/`script`/`plaintext` tag in
    raw HTML content, matching GFM's `tagfilter` extension. -/
def tagFilterDocument (doc : Document) : Document :=
  filterBlockListF (Block.listCount doc + 1) doc

end GFMarkdown
