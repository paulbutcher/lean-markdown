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

theorem Block.itemsCount_sanitizeItems :
    (n : Nat) → (items : List (Option Bool × List Block)) →
      Block.itemsCount (items.map (fun (checked, c) => (checked, sanitizeBlockListF n c)))
        = Block.itemsCount items
  | _, [] => rfl
  | n, (checked, c) :: rest => by
    simp only [List.map_cons, Block.itemsCount]
    rw [Block.listCount_sanitizeBlockListF n c, Block.itemsCount_sanitizeItems n rest]
end

/-- `Document.sanitize` leaves `Block.listCount` alone, so the fuel `renderBlocks` computes
    from the sanitized document is the fuel `Document.sanitize` itself ran at. -/
theorem Document.listCount_sanitize (doc : Document) :
    Block.listCount (Document.sanitize doc) = Block.listCount doc :=
  Block.listCount_sanitizeBlockListF _ doc

end GFMarkdown
