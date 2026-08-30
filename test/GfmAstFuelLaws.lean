-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import GFMarkdown

@[expose] public section

-- `AstFuelLaws.lean`'s count-preservation half, for `GFMarkdown.Document.sanitize`. No
-- saturation lemma is needed here: this variant's `Document.sanitize` already runs at
-- `Block.listCount doc + 1`, the same fuel `renderBlocks` picks, so establishing that
-- sanitizing leaves `Block.listCount` alone is enough to line the two up.

namespace GFMarkdown

mutual
/-- Sanitizing leaves a block's node count alone, so the fuel any later traversal computes from
    it is unchanged.

    Stated of `sanitizeBlockF` directly, where `AstFuelLaws.lean` states its counterpart of any
    count-preserving rewrite, because this variant's sanitizer is its own recursion rather than
    an instance of `Block.mapF`. `.htmlBlock` becoming `.paragraph []` is the case that could
    have failed; both count one. -/
theorem Block.count_sanitizeBlockF :
    (n : Nat) → (b : Block) → Block.count (sanitizeBlockF n b) = Block.count b
  | 0, _ => rfl
  | n + 1, b => by
    match b with
    | .paragraph _ => rfl
    | .heading .. => rfl
    | .codeBlock .. => rfl
    | .thematicBreak => rfl
    | .htmlBlock _ => simp [sanitizeBlockF, Block.count]
    | .table .. => rfl
    | .blockQuote content =>
      simp only [sanitizeBlockF, Block.count]
      rw [Block.listCount_sanitizeBlockListF n content]
    | .list kind tight items =>
      simp only [sanitizeBlockF, Block.count]
      rw [Block.itemsCount_sanitizeItems n items]

/-- The same of a list of blocks.

    `Block.listCount` sums the counts of the blocks in the list, so this follows from the claim
    above element by element, and it is the form a `Document` needs. -/
theorem Block.listCount_sanitizeBlockListF :
    (n : Nat) → (bs : List Block) →
      Block.listCount (sanitizeBlockListF n bs) = Block.listCount bs
  | 0, _ => rfl
  | n + 1, bs => by
    match bs with
    | [] => rfl
    | b :: rest =>
      simp only [sanitizeBlockListF, Block.listCount]
      rw [Block.count_sanitizeBlockF n b, Block.listCount_sanitizeBlockListF n rest]

/-- The same of a list's items, whose checkbox state the rewrite carries through untouched.

    An item is an `Option Bool` paired with its blocks, and `Block.itemsCount` counts only the
    blocks, so the proposition maps the sanitizer over the second component alone. That is
    exactly what `sanitizeBlockF` does to a `.list`, which is why the claim is stated in this
    shape rather than over a bare `List (List Block)`. -/
theorem Block.itemsCount_sanitizeItems :
    (n : Nat) → (items : List (Option Bool × List Block)) →
      Block.itemsCount (items.map (fun (checked, c) => (checked, sanitizeBlockListF n c)))
        = Block.itemsCount items
  | _, [] => rfl
  | n, (checked, c) :: rest => by
    simp only [List.map_cons, Block.itemsCount]
    rw [Block.listCount_sanitizeBlockListF n c, Block.itemsCount_sanitizeItems n rest]
end

/-- Sanitizing leaves a document's node count alone, so the fuel `renderBlocks` computes from
    the sanitized document is the fuel `Document.sanitize` itself ran at.

    `Block.listCount` is the quantity both fuels are derived from, so an equality between its
    value before and after sanitizing is the whole of the reconciliation here; unlike the
    CommonMark variant, no saturation lemma is needed, this sanitizer already running at the
    depth the renderer reads at. -/
theorem Document.listCount_sanitize (doc : Document) :
    Block.listCount (Document.sanitize doc) = Block.listCount doc :=
  Block.listCount_sanitizeBlockListF _ doc

end GFMarkdown
