-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import CommonMark.Ast

-- Document/Block/Inline is not a single homogeneous rose tree (Block has three different
-- shapes of children: List Block for block quotes, List (List Block) for list items,
-- List Inline for paragraphs/headings; Inline nests only in itself). A single generic
-- `Zipper α` therefore can't express "the" tree cursor; instead this file provides
-- `BlockZipper` and `InlineZipper`, one per node kind, connected at the one place the two
-- domains actually meet: `BlockZipper.down` on a paragraph/heading crosses into an
-- `InlineZipper`, and `InlineZipper.up` on its outermost frame crosses back.

namespace CommonMark

/-- What surrounds a `Block`-focused position. -/
inductive BlockCtx where
  | root
  | blockQuote (left right : List Block) (up : BlockCtx)
  | listItem (kind : ListType) (tight : Bool)
      (leftItems rightItems : List (List Block))
      (left right : List Block) (up : BlockCtx)
  deriving Repr, BEq

/-- A block-focused cursor. `leftSiblings`/`rightSiblings` hold the siblings of `focus`
    at this nesting level, closest first. -/
structure BlockZipper where
  focus : Block
  leftSiblings : List Block
  rightSiblings : List Block
  ctx : BlockCtx
  deriving Repr, BEq

/-- The block kind that hosts a run of inline content, kept separate from `Block` itself
    since a hosting block's other fields (e.g. heading level) don't change under
    inline-level editing. -/
inductive InlineHost where
  | paragraph
  | heading (level : Fin 6)
  deriving Repr, BEq

/-- What surrounds an `Inline`-focused position. Every chain of frames bottoms out at
    `blockRoot`, the paragraph or heading whose content this inline run belongs to. -/
inductive InlineCtx where
  | blockRoot (host : InlineHost) (left right : List Block) (up : BlockCtx)
  | emph   (left right : List Inline) (up : InlineCtx)
  | strong (left right : List Inline) (up : InlineCtx)
  | link   (dest : String) (title : Option String) (left right : List Inline) (up : InlineCtx)
  | image  (dest : String) (title : Option String) (left right : List Inline) (up : InlineCtx)
  deriving Repr, BEq

/-- An inline-focused cursor, the `Inline` counterpart to `BlockZipper`. -/
structure InlineZipper where
  focus : Inline
  leftSiblings : List Inline
  rightSiblings : List Inline
  ctx : InlineCtx
  deriving Repr, BEq

/-- Embeds a fully-closed content list at the level a `BlockCtx` frame was torn from,
    repeating outward until back at the document. -/
def BlockCtx.rebuild : BlockCtx → List Block → Document
  | .root, content => content
  | .blockQuote left right up, content =>
      up.rebuild (left.reverse ++ Block.blockQuote content :: right)
  | .listItem kind tight leftItems rightItems left right up, content =>
      let items := leftItems.reverse ++ content :: rightItems
      up.rebuild (left.reverse ++ Block.list kind tight items :: right)

/-- Embeds a fully-closed inline content list at the level an `InlineCtx` frame was torn
    from; unlike `BlockCtx.rebuild` this changes type partway through, since the
    outermost frame (`blockRoot`) hands off from `List Inline` back to `Document`. -/
def InlineCtx.rebuild : InlineCtx → List Inline → Document
  | .blockRoot host left right up, content =>
      let block := match host with
        | .paragraph => Block.paragraph content
        | .heading level => Block.heading level content
      up.rebuild (left.reverse ++ block :: right)
  | .emph left right up, content =>
      up.rebuild (left.reverse ++ Inline.emph content :: right)
  | .strong left right up, content =>
      up.rebuild (left.reverse ++ Inline.strong content :: right)
  | .link dest title left right up, content =>
      up.rebuild (left.reverse ++ Inline.link dest title content :: right)
  | .image dest title left right up, content =>
      up.rebuild (left.reverse ++ Inline.image dest title content :: right)

def BlockZipper.toDocument (z : BlockZipper) : Document :=
  z.ctx.rebuild (z.leftSiblings.reverse ++ z.focus :: z.rightSiblings)

def InlineZipper.toDocument (z : InlineZipper) : Document :=
  z.ctx.rebuild (z.leftSiblings.reverse ++ z.focus :: z.rightSiblings)

/-- Positions a zipper at the first block of a document; `none` for an empty document,
    which has no block to focus on. -/
def BlockZipper.ofDocument (doc : Document) : Option BlockZipper :=
  match doc with
  | [] => none
  | b :: rest => some { focus := b, leftSiblings := [], rightSiblings := rest, ctx := .root }

-- Sideways navigation: same nesting level, doesn't change focus type.

def BlockZipper.left (z : BlockZipper) : Option BlockZipper :=
  match z.leftSiblings with
  | [] => none
  | b :: rest =>
      some { z with focus := b, leftSiblings := rest, rightSiblings := z.focus :: z.rightSiblings }

def BlockZipper.right (z : BlockZipper) : Option BlockZipper :=
  match z.rightSiblings with
  | [] => none
  | b :: rest =>
      some { z with focus := b, leftSiblings := z.focus :: z.leftSiblings, rightSiblings := rest }

def InlineZipper.left (z : InlineZipper) : Option InlineZipper :=
  match z.leftSiblings with
  | [] => none
  | i :: rest =>
      some { z with focus := i, leftSiblings := rest, rightSiblings := z.focus :: z.rightSiblings }

def InlineZipper.right (z : InlineZipper) : Option InlineZipper :=
  match z.rightSiblings with
  | [] => none
  | i :: rest =>
      some { z with focus := i, leftSiblings := z.focus :: z.leftSiblings, rightSiblings := rest }

/-- `down` may land inside another block (block quote, list item) or cross into that
    block's inline content (paragraph, heading); leaves have no children. -/
inductive BlockDown where
  | toBlock  (z : BlockZipper)
  | toInline (z : InlineZipper)

def BlockZipper.down (z : BlockZipper) : Option BlockDown :=
  match z.focus with
  | .blockQuote content =>
      match content with
      | [] => none
      | b :: rest => some (.toBlock
          { focus := b, leftSiblings := [], rightSiblings := rest,
            ctx := .blockQuote z.leftSiblings z.rightSiblings z.ctx })
  | .list kind tight items =>
      match items with
      | [] => none
      | item :: restItems =>
          match item with
          | [] => none
          | b :: restBlocks => some (.toBlock
              { focus := b, leftSiblings := [], rightSiblings := restBlocks,
                ctx := .listItem kind tight [] restItems z.leftSiblings z.rightSiblings z.ctx })
  | .paragraph content =>
      match content with
      | [] => none
      | i :: rest => some (.toInline
          { focus := i, leftSiblings := [], rightSiblings := rest,
            ctx := .blockRoot .paragraph z.leftSiblings z.rightSiblings z.ctx })
  | .heading level content =>
      match content with
      | [] => none
      | i :: rest => some (.toInline
          { focus := i, leftSiblings := [], rightSiblings := rest,
            ctx := .blockRoot (.heading level) z.leftSiblings z.rightSiblings z.ctx })
  | .codeBlock .. | .thematicBreak | .htmlBlock .. => none

def BlockZipper.up (z : BlockZipper) : Option BlockZipper :=
  match z.ctx with
  | .root => none
  | .blockQuote left right up =>
      some
        { focus := .blockQuote (z.leftSiblings.reverse ++ z.focus :: z.rightSiblings),
          leftSiblings := left, rightSiblings := right, ctx := up }
  | .listItem kind tight leftItems rightItems left right up =>
      let item := z.leftSiblings.reverse ++ z.focus :: z.rightSiblings
      let items := leftItems.reverse ++ item :: rightItems
      some { focus := .list kind tight items, leftSiblings := left, rightSiblings := right, ctx := up }

def InlineZipper.down (z : InlineZipper) : Option InlineZipper :=
  match z.focus with
  | .emph content =>
      match content with
      | [] => none
      | i :: rest => some
          { focus := i, leftSiblings := [], rightSiblings := rest,
            ctx := .emph z.leftSiblings z.rightSiblings z.ctx }
  | .strong content =>
      match content with
      | [] => none
      | i :: rest => some
          { focus := i, leftSiblings := [], rightSiblings := rest,
            ctx := .strong z.leftSiblings z.rightSiblings z.ctx }
  | .link dest title content =>
      match content with
      | [] => none
      | i :: rest => some
          { focus := i, leftSiblings := [], rightSiblings := rest,
            ctx := .link dest title z.leftSiblings z.rightSiblings z.ctx }
  | .image dest title content =>
      match content with
      | [] => none
      | i :: rest => some
          { focus := i, leftSiblings := [], rightSiblings := rest,
            ctx := .image dest title z.leftSiblings z.rightSiblings z.ctx }
  | .text .. | .code .. | .htmlInline .. | .softBreak | .lineBreak => none

/-- `up` from an `InlineZipper` may stay inside inline content (emph, strong, link,
    image) or cross back to the hosting paragraph/heading. Unlike `BlockZipper.up`,
    this is total: every `InlineCtx` chain bottoms out at `blockRoot` by construction. -/
inductive InlineUp where
  | toInline (z : InlineZipper)
  | toBlock  (z : BlockZipper)

def InlineZipper.up (z : InlineZipper) : InlineUp :=
  match z.ctx with
  | .blockRoot host left right up =>
      let content := z.leftSiblings.reverse ++ z.focus :: z.rightSiblings
      let block := match host with
        | .paragraph => Block.paragraph content
        | .heading level => Block.heading level content
      .toBlock { focus := block, leftSiblings := left, rightSiblings := right, ctx := up }
  | .emph left right up =>
      .toInline
        { focus := .emph (z.leftSiblings.reverse ++ z.focus :: z.rightSiblings),
          leftSiblings := left, rightSiblings := right, ctx := up }
  | .strong left right up =>
      .toInline
        { focus := .strong (z.leftSiblings.reverse ++ z.focus :: z.rightSiblings),
          leftSiblings := left, rightSiblings := right, ctx := up }
  | .link dest title left right up =>
      .toInline
        { focus := .link dest title (z.leftSiblings.reverse ++ z.focus :: z.rightSiblings),
          leftSiblings := left, rightSiblings := right, ctx := up }
  | .image dest title left right up =>
      .toInline
        { focus := .image dest title (z.leftSiblings.reverse ++ z.focus :: z.rightSiblings),
          leftSiblings := left, rightSiblings := right, ctx := up }

-- List items are a second axis of siblinghood alongside ordinary block siblings (a list's
-- items are `List (List Block)`, not flattened into the block sibling chain), so moving
-- between items is a distinct operation from `left`/`right`.

def BlockZipper.nextItem (z : BlockZipper) : Option BlockZipper :=
  match z.ctx with
  | .listItem kind tight leftItems rightItems left right up =>
      match rightItems with
      | [] => none
      | nextContent :: restItems =>
          let item := z.leftSiblings.reverse ++ z.focus :: z.rightSiblings
          match nextContent with
          | [] => none
          | b :: restBlocks => some
              { focus := b, leftSiblings := [], rightSiblings := restBlocks,
                ctx := .listItem kind tight (item :: leftItems) restItems left right up }
  | _ => none

/-- Lands on the *last* block of the previous item, the natural place to continue from
    when moving backward. -/
def BlockZipper.prevItem (z : BlockZipper) : Option BlockZipper :=
  match z.ctx with
  | .listItem kind tight leftItems rightItems left right up =>
      match leftItems with
      | [] => none
      | prevContent :: restItems =>
          let item := z.leftSiblings.reverse ++ z.focus :: z.rightSiblings
          match prevContent.reverse with
          | [] => none
          | b :: restBlocksRev => some
              { focus := b, leftSiblings := restBlocksRev, rightSiblings := [],
                ctx := .listItem kind tight restItems (item :: rightItems) left right up }
  | _ => none

-- Edits at the cursor.

def BlockZipper.replace (z : BlockZipper) (b : Block) : BlockZipper := { z with focus := b }
def InlineZipper.replace (z : InlineZipper) (i : Inline) : InlineZipper := { z with focus := i }

def BlockZipper.insertLeft (z : BlockZipper) (b : Block) : BlockZipper :=
  { z with leftSiblings := b :: z.leftSiblings }
def BlockZipper.insertRight (z : BlockZipper) (b : Block) : BlockZipper :=
  { z with rightSiblings := b :: z.rightSiblings }

def InlineZipper.insertLeft (z : InlineZipper) (i : Inline) : InlineZipper :=
  { z with leftSiblings := i :: z.leftSiblings }
def InlineZipper.insertRight (z : InlineZipper) (i : Inline) : InlineZipper :=
  { z with rightSiblings := i :: z.rightSiblings }

/-- Deletes the focus, preferring the right sibling as the new focus, then the left, and
    finally collapsing to the (now childless) parent if this was the only node at this
    level. `none` only when deleting the last remaining block of the whole document. -/
def BlockZipper.delete (z : BlockZipper) : Option BlockZipper :=
  match z.rightSiblings with
  | b :: rest => some { z with focus := b, rightSiblings := rest }
  | [] =>
    match z.leftSiblings with
    | b :: rest => some { z with focus := b, leftSiblings := rest }
    | [] =>
      match z.ctx with
      | .root => none
      | .blockQuote left right up =>
          some { focus := .blockQuote [], leftSiblings := left, rightSiblings := right, ctx := up }
      | .listItem kind tight leftItems rightItems left right up =>
          let items := leftItems.reverse ++ [] :: rightItems
          some
            { focus := .list kind tight items, leftSiblings := left, rightSiblings := right, ctx := up }

/-- Deletes the focus, preferring the right sibling then the left, then collapsing to
    the (now childless) parent. `none` only when the parent context is a `blockRoot` and
    this was the only inline, which is instead handled by `BlockZipper.delete` (an empty
    paragraph/heading is meaningful, so the caller should decide via the block cursor). -/
def InlineZipper.delete (z : InlineZipper) : Option InlineZipper :=
  match z.rightSiblings with
  | i :: rest => some { z with focus := i, rightSiblings := rest }
  | [] =>
    match z.leftSiblings with
    | i :: rest => some { z with focus := i, leftSiblings := rest }
    | [] =>
      match z.ctx with
      | .blockRoot .. => none
      | .emph left right up =>
          some { focus := .emph [], leftSiblings := left, rightSiblings := right, ctx := up }
      | .strong left right up =>
          some { focus := .strong [], leftSiblings := left, rightSiblings := right, ctx := up }
      | .link dest title left right up =>
          some
            { focus := .link dest title [], leftSiblings := left, rightSiblings := right, ctx := up }
      | .image dest title left right up =>
          some
            { focus := .image dest title [], leftSiblings := left, rightSiblings := right, ctx := up }

-- Round-trip and navigation laws (`up (down z) = z`, `toDocument (ofDocument doc) = doc`,
-- etc.) are proven in test/ZipperLaws.lean rather than here: nothing in this file depends
-- on them, so they're the zipper's documented contract, not load-bearing implementation.

end CommonMark
