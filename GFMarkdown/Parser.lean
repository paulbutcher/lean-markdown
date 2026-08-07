-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import GFMarkdown.Ast
import GFMarkdown.Autolink
import GFMarkdown.TagFilter

namespace GFMarkdown.Parser

open CommonMark.Parser (RawBlock LinkDefs parseInlineRaw takeSameKindItems rawBlockListCount
  headingLevelToFin)

-- GFM's task-list-item marker: `[ ]`/`[x]`/`[X]` followed by at least one space or tab,
-- recognized only as the very first three-plus characters of a list item's raw text (before
-- inline parsing ever sees it -- doing this after `parseInlineRaw` would be unreliable, since
-- `[`/`]` there would already have gone through bracket/link tokenization).
def matchTaskListPrefix (text : String) : Option (Bool × String) :=
  match text.toList with
  | '[' :: c :: ']' :: rest =>
    if c ≠ ' ' && c ≠ 'x' && c ≠ 'X' then none
    else
      match rest with
      | r :: _ =>
        if r == ' ' || r == '\t' then
          some (c ≠ ' ', String.ofList (rest.dropWhile (fun ch => ch == ' ' || ch == '\t')))
        else none
      | [] => none
  | _ => none

-- A task-list marker only ever applies to a list item's first block, and only when that
-- block is a paragraph (a nested list or code block right at the start can't carry one).
def taskListChecked (content : List RawBlock) : Option Bool × List RawBlock :=
  match content with
  | .paragraph text :: rest =>
    match matchTaskListPrefix text with
    | some (checked, text') => (some checked, .paragraph text' :: rest)
    | none => (none, content)
  | _ => (none, content)

-- Mirrors `CommonMark.Parser.rawBlockToBlockF`/`groupAndConvertF`'s mutual, fuel-bounded
-- recursion (see the comment there for why fuel is needed instead of structural recursion).
-- Fully independent from that conversion now (Phase 1 delegated the non-recursive cases to
-- it), rather than a partial mirror: once `paragraph`/`heading` need `RawInline`-typed
-- content of their own (to carry a `strikethrough`, which `CommonMark.Inline` never does),
-- there's nothing left to usefully delegate.
mutual
def rawBlockToBlockGfmF (defs : LinkDefs) : Nat → RawBlock → GFMarkdown.Block
  | 0, _ => .paragraph []
  | _ + 1, .paragraph text => .paragraph (parseInlineRaw true defs text)
  | _ + 1, .heading level text => .heading (headingLevelToFin level) (parseInlineRaw true defs text)
  | _ + 1, .codeBlock info lit => .codeBlock info lit
  | _ + 1, .thematicBreak => .thematicBreak
  | _ + 1, .htmlBlock s => .htmlBlock s
  | fuel + 1, .blockQuote content => .blockQuote (groupAndConvertGfmF defs fuel content)
  | fuel + 1, .listItem kind _ content =>
    .list kind false [(none, groupAndConvertGfmF defs fuel content)]
  | _ + 1, .table header alignments rows =>
    .table (header.map (parseInlineRaw true defs)) alignments
      (rows.map (List.map (parseInlineRaw true defs)))

def groupAndConvertGfmF (defs : LinkDefs) : Nat → List RawBlock → List GFMarkdown.Block
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, .listItem kind loose content :: rest =>
    let (siblings, rest') := takeSameKindItems kind rest
    let allItems := (kind, loose, content) :: siblings
    let looseOverall := allItems.any (fun (_, l, _) => l)
    let items := allItems.map (fun (_, _, c) =>
      let (checked, c') := taskListChecked c
      (checked, groupAndConvertGfmF defs fuel c'))
    .list kind (!looseOverall) items :: groupAndConvertGfmF defs fuel rest'
  | fuel + 1, b :: rest => rawBlockToBlockGfmF defs fuel b :: groupAndConvertGfmF defs fuel rest
end

def groupAndConvertGfm (defs : LinkDefs) (blocks : List RawBlock) : List GFMarkdown.Block :=
  groupAndConvertGfmF defs (rawBlockListCount blocks + 1) blocks

end GFMarkdown.Parser

namespace GFMarkdown

/-- Parses a GFM document into an AST. Total, for the same reason `CommonMark.parseDocument`
    is: every input string produces a `Document` rather than panicking or looping. Covers
    CommonMark's base syntax plus GFM tables, strikethrough, task lists, extended autolinks,
    and the raw-HTML tag filter. -/
def parseDocument (s : String) : Document :=
  let (blocks, defs) :=
    CommonMark.Parser.finalizeState (CommonMark.Parser.runLines true (CommonMark.Parser.splitLines s))
  tagFilterDocument (autolinkDocument (Parser.groupAndConvertGfm defs blocks))

end GFMarkdown
