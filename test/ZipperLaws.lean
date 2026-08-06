-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import CommonMark

-- The documented contract of `BlockZipper`/`InlineZipper` (`CommonMark/Zipper.lean`):
-- round-trip and navigation laws that make cursor-style editing trustworthy. Proven here
-- rather than in the library itself since nothing in the library depends on them; they
-- exist purely to certify the guarantees the zipper's design relies on.

namespace CommonMark

theorem BlockZipper.ofDocument_toDocument {doc : Document} {z : BlockZipper} :
    BlockZipper.ofDocument doc = some z → z.toDocument = doc := by
  cases doc with
  | nil => intro h; cases h
  | cons b rest =>
    intro h
    simp only [ofDocument, Option.some.injEq] at h
    subst h
    rfl

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

theorem BlockZipper.right_left {z z' : BlockZipper} :
    z.right = some z' → z'.left = some z := by
  obtain ⟨focus, ls, rs, ctx⟩ := z
  cases rs with
  | nil => simp [BlockZipper.right]
  | cons b rest =>
      simp only [BlockZipper.right, Option.some.injEq]
      rintro rfl
      simp [BlockZipper.left]

theorem BlockZipper.left_right {z z' : BlockZipper} :
    z.left = some z' → z'.right = some z := by
  obtain ⟨focus, ls, rs, ctx⟩ := z
  cases ls with
  | nil => simp [BlockZipper.left]
  | cons b rest =>
      simp only [BlockZipper.left, Option.some.injEq]
      rintro rfl
      simp [BlockZipper.right]

theorem InlineZipper.right_left {z z' : InlineZipper} :
    z.right = some z' → z'.left = some z := by
  obtain ⟨focus, ls, rs, ctx⟩ := z
  cases rs with
  | nil => simp [InlineZipper.right]
  | cons i rest =>
      simp only [InlineZipper.right, Option.some.injEq]
      rintro rfl
      simp [InlineZipper.left]

theorem InlineZipper.left_right {z z' : InlineZipper} :
    z.left = some z' → z'.right = some z := by
  obtain ⟨focus, ls, rs, ctx⟩ := z
  cases ls with
  | nil => simp [InlineZipper.left]
  | cons i rest =>
      simp only [InlineZipper.left, Option.some.injEq]
      rintro rfl
      simp [InlineZipper.right]

/-- `replace` affects the reconstructed document only at the focus's own position. -/
theorem BlockZipper.replace_toDocument (z : BlockZipper) (b : Block) :
    (z.replace b).toDocument = z.ctx.rebuild (z.leftSiblings.reverse ++ b :: z.rightSiblings) := rfl

theorem InlineZipper.replace_toDocument (z : InlineZipper) (i : Inline) :
    (z.replace i).toDocument = z.ctx.rebuild (z.leftSiblings.reverse ++ i :: z.rightSiblings) := rfl

-- `insertRight` only touches `rightSiblings`, which `toDocument` doesn't reverse, so this
-- is `rfl` just like `replace_toDocument`. `insertLeft` touches `leftSiblings`, which
-- `toDocument` does reverse, so recovering the expected shape needs `List.reverse_cons`.

theorem BlockZipper.insertRight_toDocument (z : BlockZipper) (b : Block) :
    (z.insertRight b).toDocument =
      z.ctx.rebuild (z.leftSiblings.reverse ++ z.focus :: b :: z.rightSiblings) := rfl

theorem BlockZipper.insertLeft_toDocument (z : BlockZipper) (b : Block) :
    (z.insertLeft b).toDocument =
      z.ctx.rebuild (z.leftSiblings.reverse ++ b :: z.focus :: z.rightSiblings) := by
  simp [BlockZipper.insertLeft, BlockZipper.toDocument, List.reverse_cons]

theorem InlineZipper.insertRight_toDocument (z : InlineZipper) (i : Inline) :
    (z.insertRight i).toDocument =
      z.ctx.rebuild (z.leftSiblings.reverse ++ z.focus :: i :: z.rightSiblings) := rfl

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
