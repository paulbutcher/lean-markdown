-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import CommonMark

@[expose] public section

-- The documented contract of `BlockZipper`/`InlineZipper` (`CommonMark/Zipper.lean`):
-- round-trip and navigation laws that make cursor-style editing trustworthy. Proven here
-- rather than in the library itself since nothing in the library depends on them; they
-- exist purely to certify the guarantees the zipper's design relies on.

namespace CommonMark

/-- Opening a document at its first block and closing it again gives back the document
    unchanged: taking it apart loses nothing.

    The claim is an implication from `ofDocument doc = some z` rather than an equation about
    `ofDocument doc`, because there is no zipper for an empty document, nothing being there to
    focus on. That makes the statement vacuous at exactly the one input that has no round trip
    to describe, and an honest claim about every other. -/
theorem BlockZipper.ofDocument_toDocument {doc : Document} {z : BlockZipper} :
    BlockZipper.ofDocument doc = some z → z.toDocument = doc := by
  cases doc with
  | nil => intro h; cases h
  | cons b rest =>
    intro h
    simp only [ofDocument, Option.some.injEq] at h
    subst h
    rfl

/-- Descending into a block's content and going straight back up returns to the position left,
    not merely to somewhere that rebuilds the same document.

    The conclusion is `some z`, the very zipper descended from, so the sibling lists and the
    enclosing context are recovered too, which is what makes cursor-style editing safe across
    the move. The hypothesis matches only `down`'s `.toBlock` result; its `.toInline` result is
    the next theorem's business. The converse fails, `down` always landing on the first child
    whatever position `up` was reached from. -/
theorem BlockZipper.down_up {z z' : BlockZipper} :
    z.down = some (.toBlock z') → z'.up = some z := by
  obtain ⟨focus, ls, rs, ctx⟩ := z
  cases focus with
  | blockQuote content =>
      cases content with
      | nil => simp [BlockZipper.down]
      | cons b rest =>
          simp only [BlockZipper.down, Option.some.injEq, BlockDown.toBlock.injEq]
          rintro rfl
          simp [BlockZipper.up]
  | list kind tight items =>
      cases items with
      | nil => simp [BlockZipper.down]
      | cons item restItems =>
          cases item with
          | nil => simp [BlockZipper.down]
          | cons b restBlocks =>
              simp only [BlockZipper.down, Option.some.injEq, BlockDown.toBlock.injEq]
              rintro rfl
              simp [BlockZipper.up]
  | paragraph content => cases content <;> simp [BlockZipper.down]
  | heading level content => cases content <;> simp [BlockZipper.down]
  | codeBlock info lit => simp [BlockZipper.down]
  | thematicBreak => simp [BlockZipper.down]
  | htmlBlock s => simp [BlockZipper.down]

/-- Descending from a block into its inline content and going straight back up returns to the
    block position left.

    `InlineZipper.up` yields a `BlockDown` rather than a `BlockZipper` because inline content
    can sit inside other inline content, and it is total, no `Option`, because it always sits
    inside something. So the conclusion is `= .toBlock z`: up from here lands on the block
    half, and on exactly the zipper descended from. -/
theorem BlockZipper.down_up_inline {z : BlockZipper} {z' : InlineZipper} :
    z.down = some (.toInline z') → z'.up = .toBlock z := by
  obtain ⟨focus, ls, rs, ctx⟩ := z
  cases focus with
  | blockQuote content => cases content <;> simp [BlockZipper.down]
  | list kind tight items =>
      cases items with
      | nil => simp [BlockZipper.down]
      | cons item restItems => cases item <;> simp [BlockZipper.down]
  | paragraph content =>
      cases content with
      | nil => simp [BlockZipper.down]
      | cons i rest =>
          simp only [BlockZipper.down, Option.some.injEq, BlockDown.toInline.injEq]
          rintro rfl
          simp [InlineZipper.up]
  | heading level content =>
      cases content with
      | nil => simp [BlockZipper.down]
      | cons i rest =>
          simp only [BlockZipper.down, Option.some.injEq, BlockDown.toInline.injEq]
          rintro rfl
          simp [InlineZipper.up]
  | codeBlock info lit => simp [BlockZipper.down]
  | thematicBreak => simp [BlockZipper.down]
  | htmlBlock s => simp [BlockZipper.down]

/-- Stepping right to the next sibling block and back left returns to the position stepped
    from.

    Both moves are `Option`-valued, failing at the end of a sibling list; taking
    `z.right = some z'` as the hypothesis is what confines the claim to the case where the
    first move happened, and is why no separate condition on `z` is needed. -/
theorem BlockZipper.right_left {z z' : BlockZipper} :
    z.right = some z' → z'.left = some z := by
  obtain ⟨focus, ls, rs, ctx⟩ := z
  cases rs with
  | nil => simp [BlockZipper.right]
  | cons b rest =>
      simp only [BlockZipper.right, Option.some.injEq]
      rintro rfl
      simp [BlockZipper.left]

/-- Stepping left to the previous sibling block and back right returns to the position stepped
    from.

    The mirror image of the theorem above, and needed separately: sibling lists are stored one
    reversed and one not, so neither direction follows from the other by symmetry alone. -/
theorem BlockZipper.left_right {z z' : BlockZipper} :
    z.left = some z' → z'.right = some z := by
  obtain ⟨focus, ls, rs, ctx⟩ := z
  cases ls with
  | nil => simp [BlockZipper.left]
  | cons b rest =>
      simp only [BlockZipper.left, Option.some.injEq]
      rintro rfl
      simp [BlockZipper.right]

/-- Stepping right to the next sibling inline node and back left returns to the position
    stepped from.

    The block-level claim above says nothing about inline navigation, `InlineZipper` carrying
    its own `left`/`right` over its own sibling lists, so the law has to be stated again at
    this type. -/
theorem InlineZipper.right_left {z z' : InlineZipper} :
    z.right = some z' → z'.left = some z := by
  obtain ⟨focus, ls, rs, ctx⟩ := z
  cases rs with
  | nil => simp [InlineZipper.right]
  | cons i rest =>
      simp only [InlineZipper.right, Option.some.injEq]
      rintro rfl
      simp [InlineZipper.left]

/-- Stepping left to the previous sibling inline node and back right returns to the position
    stepped from.

    The mirror image of the theorem above, at the inline level; the four sideways laws together
    say a cursor can be moved either way along a run of siblings without drift. -/
theorem InlineZipper.left_right {z z' : InlineZipper} :
    z.left = some z' → z'.right = some z := by
  obtain ⟨focus, ls, rs, ctx⟩ := z
  cases ls with
  | nil => simp [InlineZipper.left]
  | cons i rest =>
      simp only [InlineZipper.left, Option.some.injEq]
      rintro rfl
      simp [InlineZipper.right]

/-- Replacing the focused block changes the reconstructed document at that one position and
    nowhere else: siblings and every enclosing level come back untouched.

    The right-hand side is `toDocument`'s own shape with `b` standing where `z.focus` stood, so
    the equation pins down what the document becomes rather than merely asserting that the rest
    is unaffected. `z.ctx.rebuild` is what carries the untouched enclosing levels, and it
    appears on the right unchanged. -/
theorem BlockZipper.replace_toDocument (z : BlockZipper) (b : Block) :
    (z.replace b).toDocument = z.ctx.rebuild (z.leftSiblings.reverse ++ b :: z.rightSiblings) := rfl

/-- Replacing the focused inline node changes the reconstructed document at that one position
    and nowhere else.

    The same shape as the block-level claim, though `InlineCtx.rebuild` hands off from
    `List Inline` back to `Document` at its outermost frame, so the enclosing block is part of
    what the right-hand side leaves untouched. -/
theorem InlineZipper.replace_toDocument (z : InlineZipper) (i : Inline) :
    (z.replace i).toDocument = z.ctx.rebuild (z.leftSiblings.reverse ++ i :: z.rightSiblings) := rfl

-- `insertRight` only touches `rightSiblings`, which `toDocument` doesn't reverse, so this
-- is `rfl` just like `replace_toDocument`. `insertLeft` touches `leftSiblings`, which
-- `toDocument` does reverse, so recovering the expected shape needs `List.reverse_cons`.

/-- Inserting a block to the right of the focus puts it immediately after the focus and leaves
    everything else where it was.

    The right-hand side spells out the whole reconstructed sibling run, `z.focus :: b :: rest`,
    which pins the new block's position exactly rather than saying only that it is somewhere
    among the right siblings. The focus itself still appears, insertion moving the cursor
    nowhere. -/
theorem BlockZipper.insertRight_toDocument (z : BlockZipper) (b : Block) :
    (z.insertRight b).toDocument =
      z.ctx.rebuild (z.leftSiblings.reverse ++ z.focus :: b :: z.rightSiblings) := rfl

/-- Inserting a block to the left of the focus puts it immediately before the focus and leaves
    everything else where it was.

    `leftSiblings` is stored nearest-first and reversed on rebuild, so a block consed onto it
    appears immediately before the focus in the document, which is what the right-hand side
    states; reading the field order alone would suggest the opposite. -/
theorem BlockZipper.insertLeft_toDocument (z : BlockZipper) (b : Block) :
    (z.insertLeft b).toDocument =
      z.ctx.rebuild (z.leftSiblings.reverse ++ b :: z.focus :: z.rightSiblings) := by
  simp [BlockZipper.insertLeft, BlockZipper.toDocument, List.reverse_cons]

/-- Inserting an inline node to the right of the focus puts it immediately after the focus and
    leaves everything else where it was.

    The inline-level counterpart of the block claim above, stated separately because the two
    zippers rebuild through different context types. -/
theorem InlineZipper.insertRight_toDocument (z : InlineZipper) (i : Inline) :
    (z.insertRight i).toDocument =
      z.ctx.rebuild (z.leftSiblings.reverse ++ z.focus :: i :: z.rightSiblings) := rfl

/-- Inserting an inline node to the left of the focus puts it immediately before the focus and
    leaves everything else where it was.

    As at block level, `leftSiblings` is stored reversed, so the right-hand side is what a
    reader would otherwise have to derive rather than what the field order suggests. -/
theorem InlineZipper.insertLeft_toDocument (z : InlineZipper) (i : Inline) :
    (z.insertLeft i).toDocument =
      z.ctx.rebuild (z.leftSiblings.reverse ++ i :: z.focus :: z.rightSiblings) := by
  simp [InlineZipper.insertLeft, InlineZipper.toDocument, List.reverse_cons]

-- `nextItem`/`prevItem` are not mutual inverses the way `left`/`right` are: each always
-- resets its own side to `[]` (first block of the next item; last block of the previous
-- one), rather than preserving the full sibling list the way `left`/`right` do. So
-- `prevItem (nextItem z) = some z` only when `z` was already at the end of its own item
-- (`z.rightSiblings = []`), i.e. exactly the position `prevItem` would itself produce;
-- otherwise `prevItem` lands on the true last block of that item, not literally `z`. This
-- mirrors why `down_up` holds unconditionally but `up_down` does not.

/-- Moving to the next list item and back returns to the position left, provided the cursor was
    on the last block of its own item.

    The hypothesis `z.rightSiblings = []` is not a proof artefact: `prevItem` always lands on
    the last block of the previous item, so it can return to `z` only when `z` was that block.
    Drop the hypothesis and the conclusion is false, not merely unproved. -/
theorem BlockZipper.nextItem_prevItem {z z' : BlockZipper} (hz : z.rightSiblings = []) :
    z.nextItem = some z' → z'.prevItem = some z := by
  obtain ⟨focus, ls, rs, ctx⟩ := z
  simp only at hz
  subst hz
  cases ctx with
  | root => simp [BlockZipper.nextItem]
  | blockQuote left right up => simp [BlockZipper.nextItem]
  | listItem kind tight leftItems rightItems left right up =>
    cases rightItems with
    | nil => simp [BlockZipper.nextItem]
    | cons nextContent restItems =>
      cases nextContent with
      | nil => simp [BlockZipper.nextItem]
      | cons b restBlocks =>
        simp only [BlockZipper.nextItem, Option.some.injEq]
        rintro rfl
        simp [BlockZipper.prevItem]

/-- Moving to the previous list item and back returns to the position left, provided the cursor
    was on the first block of its own item.

    `z.leftSiblings = []` is the mirror of the condition above, and needed for the mirror
    reason: `nextItem` always lands on the first block of the next item, so only a cursor
    already in that position can be returned to. -/
theorem BlockZipper.prevItem_nextItem {z z' : BlockZipper} (hz : z.leftSiblings = []) :
    z.prevItem = some z' → z'.nextItem = some z := by
  obtain ⟨focus, ls, rs, ctx⟩ := z
  simp only at hz
  subst hz
  cases ctx with
  | root => simp [BlockZipper.prevItem]
  | blockQuote left right up => simp [BlockZipper.prevItem]
  | listItem kind tight leftItems rightItems left right up =>
    cases leftItems with
    | nil => simp [BlockZipper.prevItem]
    | cons prevContent restItems =>
      cases hrev : prevContent.reverse with
      | nil => simp [BlockZipper.prevItem, hrev]
      | cons b restBlocksRev =>
        have hp : prevContent = restBlocksRev.reverse ++ [b] := by
          have h := congrArg List.reverse hrev
          simpa [List.reverse_cons] using h
        simp only [BlockZipper.prevItem, hrev, Option.some.injEq]
        rintro rfl
        simp [BlockZipper.nextItem, hp]

end CommonMark
