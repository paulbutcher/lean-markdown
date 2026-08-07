-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import GFMarkdown.Ast

namespace GFMarkdown.Parser

open CommonMark.Parser (RawBlock LinkDefs parseInline takeSameKindItems rawBlockListCount
  rawBlockToBlockF)

-- Mirrors `CommonMark.Parser.rawBlockToBlockF`/`groupAndConvertF`'s mutual, fuel-bounded
-- recursion (see the comment there for why fuel is needed instead of structural recursion),
-- but recurses into `GFMarkdown.Block` for `blockQuote`/`listItem` rather than delegating to
-- the plain conversion, so a table nested inside either is still recognized as one.
mutual
def rawBlockToBlockGfmF (defs : LinkDefs) : Nat → RawBlock → GFMarkdown.Block
  | 0, _ => .commonmark (.paragraph [])
  | fuel + 1, .blockQuote content => .blockQuote (groupAndConvertGfmF defs fuel content)
  | fuel + 1, .listItem kind _ content => .list kind false [groupAndConvertGfmF defs fuel content]
  | _ + 1, .table header alignments rows =>
    .table (header.map (parseInline defs)) alignments (rows.map (List.map (parseInline defs)))
  -- Every remaining `RawBlock` constructor (paragraph/heading/codeBlock/thematicBreak/
  -- htmlBlock) has no nested-block content, so fuel can't matter to it; delegating to the
  -- plain single-node conversion with fuel `1` avoids restating its logic here.
  | _ + 1, b => .commonmark (rawBlockToBlockF defs 1 b)

def groupAndConvertGfmF (defs : LinkDefs) : Nat → List RawBlock → List GFMarkdown.Block
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, .listItem kind loose content :: rest =>
    let (siblings, rest') := takeSameKindItems kind rest
    let allItems := (kind, loose, content) :: siblings
    let looseOverall := allItems.any (fun (_, l, _) => l)
    let items := allItems.map (fun (_, _, c) => groupAndConvertGfmF defs fuel c)
    .list kind (!looseOverall) items :: groupAndConvertGfmF defs fuel rest'
  | fuel + 1, b :: rest => rawBlockToBlockGfmF defs fuel b :: groupAndConvertGfmF defs fuel rest
end

def groupAndConvertGfm (defs : LinkDefs) (blocks : List RawBlock) : List GFMarkdown.Block :=
  groupAndConvertGfmF defs (rawBlockListCount blocks + 1) blocks

end GFMarkdown.Parser
