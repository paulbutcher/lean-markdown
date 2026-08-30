-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import GfmNoEmbeddedHtml

@[expose] public section

-- `AstFuelLaws.lean`'s count-preservation half, for `GFMarkdown.Document.sanitize`. Lining up
-- the sanitizer's fuel with the renderer's needs nothing more here: this variant's
-- `Document.sanitize` already runs at `Block.listCount doc + 1`, the same fuel `renderBlocks`
-- picks, so establishing that sanitizing leaves `Block.listCount` alone is enough.

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
    value before and after sanitizing is the whole of the reconciliation here; the CommonMark
    variant additionally needs `Block.mapListF_saturate` to bridge two different fuels, where
    this sanitizer already runs at the depth the renderer reads at. -/
theorem Document.listCount_sanitize (doc : Document) :
    Block.listCount (Document.sanitize doc) = Block.listCount doc :=
  Block.listCount_sanitizeBlockListF _ doc

-- `AstFuelLaws.lean`'s saturation half, for the reading `GfmNoEmbeddedHtml.lean` defines: the
-- modules that read a document at a fuel of their own choosing need to know the reading does
-- not depend on which sufficient fuel they chose. The helpers below are re-derived rather than
-- reused, `CommonMark`'s being `private` and about its own `Block`.

/-- Every block counts for at least one node.

    Strict positivity, not merely "not zero", is what the saturation proof below needs: its
    zero-fuel cases carry a hypothesis `Block.count b ≤ 0`, which this contradicts outright, so
    those cases close rather than having to be given a meaning. -/
private theorem count_pos (b : Block) : 0 < Block.count b := by
  match b with
  | .paragraph _ | .heading .. | .codeBlock .. | .thematicBreak | .htmlBlock _ | .table .. =>
    simp [Block.count]
  | .blockQuote _ => simp only [Block.count]; omega
  | .list .. => simp only [Block.count]; omega

/-- Two tests that agree on every element of a list agree on the whole list.

    The hypothesis is pointwise and only over the list's own elements, not over the type, which
    is what the `.list` case below can supply: the two readings agree at each item's fuel, and
    nowhere else need they agree at all. -/
private theorem all_congr {α : Type} {f g : α → Bool} :
    (l : List α) → (∀ a ∈ l, f a = g a) → l.all f = l.all g
  | [], _ => rfl
  | a :: rest, h => by
    simp only [List.all_cons, h a (List.mem_cons_self ..)]
    rw [all_congr rest (fun b hb => h b (List.mem_cons_of_mem _ hb))]

/-- No single item of a list block outweighs the total counted over all of them.

    An item is an `Option Bool` paired with its blocks and `Block.itemsCount` sums only the
    blocks, so the bound is stated of `p.2`; the checkbox contributes nothing to count and
    nothing to the bound. -/
private theorem listCount_le_itemsCount :
    (items : List (Option Bool × List Block)) →
      ∀ p ∈ items, Block.listCount p.2 ≤ Block.itemsCount items
  | [], _, hp => by simp at hp
  | (_, c) :: rest, p, hp => by
    simp only [Block.itemsCount]
    rcases List.mem_cons.mp hp with rfl | hp
    · exact Nat.le_add_right _ _
    · have := listCount_le_itemsCount rest p hp
      omega

/-- Fuel enough to enter a list block is fuel enough, less the step that entered it, for each
    of its items.

    The `n + 1` in the hypothesis against the `n` in the conclusion is exactly that one step:
    the reading spends a level on the `.list` node itself before handing what remains to the
    items, so this is the shape in which the recursive call's hypothesis arrives. -/
private theorem listCount_le_of_list {kind tight} {items : List (Option Bool × List Block)}
    {n : Nat} (h : Block.count (.list kind tight items) ≤ n + 1) :
    ∀ p ∈ items, Block.listCount p.2 ≤ n := by
  intro p hp
  simp only [Block.count] at h
  have := listCount_le_itemsCount items p hp
  omega

mutual
/-- Once the fuel is enough to reach every node, more fuel cannot change the verdict: a block
    read at any sufficient fuel gets the same answer as at any other.

    `n` and `m` are asked only to be sufficient, so the claim is that all sufficient fuels
    agree. What it rules out is a `.htmlBlock` or `.htmlInline` sitting deeper than the fuel
    reaches and going unnoticed, which is what would make a `= true` verdict worthless. -/
theorem Block.noEmbeddedHtmlF_saturate :
    (n m : Nat) → (b : Block) → Block.count b ≤ n → Block.count b ≤ m →
      Block.noEmbeddedHtmlF n b = Block.noEmbeddedHtmlF m b
  | 0, _, b, hn, _ => by have := count_pos b; omega
  | _ + 1, 0, b, _, hm => by have := count_pos b; omega
  | n + 1, m + 1, b, hn, hm => by
    match b with
    | .paragraph _ => rfl
    | .heading .. => rfl
    | .codeBlock .. => rfl
    | .thematicBreak => rfl
    | .htmlBlock _ => rfl
    | .table .. => rfl
    | .blockQuote content =>
      simp only [Block.count] at hn hm
      simp only [Block.noEmbeddedHtmlF]
      rw [Block.noEmbeddedHtmlListF_saturate n m content (by omega) (by omega)]
    | .list kind tight items =>
      simp only [Block.noEmbeddedHtmlF]
      refine all_congr items (fun p hp => ?_)
      obtain ⟨_, c⟩ := p
      exact Block.noEmbeddedHtmlListF_saturate n m c
        (listCount_le_of_list hn _ hp) (listCount_le_of_list hm _ hp)

/-- The same for a list of blocks, which is the shape a `Document` has and so the form the
    theorem below instantiates.

    `Block.listCount bs ≤ n` and `≤ m` say each fuel is enough for the whole list, which by the
    bound above is enough for every block within it. -/
theorem Block.noEmbeddedHtmlListF_saturate :
    (n m : Nat) → (bs : List Block) → Block.listCount bs ≤ n → Block.listCount bs ≤ m →
      Block.noEmbeddedHtmlListF n bs = Block.noEmbeddedHtmlListF m bs
  | 0, m, bs, hn, _ => by
    match bs with
    | [] => cases m <;> rfl
    | b :: rest =>
      simp only [Block.listCount] at hn
      have := count_pos b
      omega
  | n + 1, 0, bs, _, hm => by
    match bs with
    | [] => rfl
    | b :: rest =>
      simp only [Block.listCount] at hm
      have := count_pos b
      omega
  | n + 1, m + 1, bs, hn, hm => by
    match bs with
    | [] => rfl
    | b :: rest =>
      simp only [Block.listCount] at hn hm
      simp only [Block.noEmbeddedHtmlListF]
      rw [Block.noEmbeddedHtmlF_saturate n m b (by omega) (by omega),
        Block.noEmbeddedHtmlListF_saturate n m rest (by omega) (by omega)]
end

/-- Reading a document for embedded raw HTML at one more than its own node count settles the
    question: no larger fuel gives a different answer, so a `= true` verdict there cannot have
    been reached by stopping short of something.

    `Block.listCount doc` counts every block in `doc` and the reading spends one unit of fuel
    per level of nesting, so that fuel is already sufficient and the extra one this variant
    carries is spare. The proposition says every fuel at least that large agrees, which is what
    `Document.sanitize_noEmbeddedHtml` and `Document.hasEmbeddedHtml` both rest on, the two
    reading at the same depth. -/
theorem Document.noEmbeddedHtmlListF_saturate (doc : Document) (n : Nat)
    (h : Block.listCount doc + 1 ≤ n) :
    Block.noEmbeddedHtmlListF n doc
      = Block.noEmbeddedHtmlListF (Block.listCount doc + 1) doc :=
  Block.noEmbeddedHtmlListF_saturate n (Block.listCount doc + 1) doc
    (Nat.le_trans (Nat.le_succ _) h) (Nat.le_succ _)

end GFMarkdown
