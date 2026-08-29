-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import CommonMark

@[expose] public section

-- `Block.listCount` is exactly enough fuel for `Block.mapF`/`Block.mapListF` to reach every
-- node, so any larger value gives the same result. Modules that observe a mapped document
-- need this because they pick their own fuel independently of the one the map ran at:
-- `Document.sanitize` maps at `Block.listCount doc`, while `renderBlocks` renders at
-- `Block.listCount doc + 1`, and `RenderSafeWellFormedness.lean` has to put the two together.

namespace CommonMark

private theorem count_pos (b : Block) : 0 < Block.count b := by
  match b with
  | .paragraph _ | .heading .. | .codeBlock .. | .thematicBreak | .htmlBlock _ =>
    simp [Block.count]
  | .blockQuote _ => simp only [Block.count]; omega
  | .list .. => simp only [Block.count]; omega

private theorem mapListF_nil (fi : Inline → Inline) (fb : Block → Block) (n : Nat) :
    Block.mapListF fi fb n [] = [] := by
  match n with
  | 0 => rfl
  | _ + 1 => rfl

private theorem le_foldl_listCount (items : List (List Block)) (init : Nat) :
    init ≤ items.foldl (fun acc x => acc + Block.listCount x) init := by
  induction items generalizing init with
  | nil => simp
  | cons x rest ih =>
    exact Nat.le_trans (Nat.le_add_right init (Block.listCount x))
      (ih (init + Block.listCount x))

private theorem listCount_le_foldl (items : List (List Block)) (init : Nat) :
    ∀ c ∈ items, Block.listCount c ≤ items.foldl (fun acc x => acc + Block.listCount x) init := by
  induction items generalizing init with
  | nil => intro c hc; simp at hc
  | cons x rest ih =>
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact Nat.le_trans (Nat.le_add_left _ init)
        (le_foldl_listCount rest (init + Block.listCount c))
    · exact ih (init + Block.listCount x) c hc

private theorem listCount_le_of_list {kind tight} {items : List (List Block)} {n : Nat}
    (h : Block.count (.list kind tight items) ≤ n + 1) :
    ∀ c ∈ items, Block.listCount c ≤ n := by
  intro c hc
  simp only [Block.count] at h
  exact Nat.le_trans (listCount_le_foldl items 0 c hc) (by omega)

mutual
theorem Block.mapF_saturate (fi : Inline → Inline) (fb : Block → Block) :
    (n m : Nat) → (b : Block) → Block.count b ≤ n → Block.count b ≤ m →
      Block.mapF fi fb n b = Block.mapF fi fb m b
  | 0, _, b, hn, _ => by have := count_pos b; omega
  | _ + 1, 0, b, _, hm => by have := count_pos b; omega
  | n + 1, m + 1, b, hn, hm => by
    match b with
    | .paragraph _ => rfl
    | .heading .. => rfl
    | .codeBlock .. => rfl
    | .thematicBreak => rfl
    | .htmlBlock _ => rfl
    | .blockQuote content =>
      simp only [Block.count] at hn hm
      simp only [Block.mapF]
      rw [Block.mapListF_saturate fi fb n m content (by omega) (by omega)]
    | .list kind tight items =>
      simp only [Block.mapF]
      congr 2
      refine List.map_congr_left ?_
      intro c hc
      exact Block.mapListF_saturate fi fb n m c
        (listCount_le_of_list hn c hc) (listCount_le_of_list hm c hc)

theorem Block.mapListF_saturate (fi : Inline → Inline) (fb : Block → Block) :
    (n m : Nat) → (bs : List Block) → Block.listCount bs ≤ n → Block.listCount bs ≤ m →
      Block.mapListF fi fb n bs = Block.mapListF fi fb m bs
  | 0, m, bs, hn, _ => by
    match bs with
    | [] => rw [mapListF_nil, mapListF_nil]
    | b :: rest =>
      simp only [Block.listCount] at hn
      have := count_pos b
      omega
  | n + 1, 0, bs, _, hm => by
    match bs with
    | [] => rw [mapListF_nil, mapListF_nil]
    | b :: rest =>
      simp only [Block.listCount] at hm
      have := count_pos b
      omega
  | n + 1, m + 1, bs, hn, hm => by
    match bs with
    | [] => rw [mapListF_nil, mapListF_nil]
    | b :: rest =>
      simp only [Block.listCount] at hn hm
      simp only [Block.mapListF]
      rw [Block.mapF_saturate fi fb n m b (by omega) (by omega),
        Block.mapListF_saturate fi fb n m rest (by omega) (by omega)]
end

-- A rewrite that preserves every block's node count leaves `Block.listCount` alone, and so
-- leaves the fuel any later traversal computes from it alone. `sanitizeBlock` is such a
-- rewrite: it turns `.htmlBlock` into `.paragraph []`, and both count 1.

private theorem foldl_listCount_map (g : List Block → List Block)
    (hg : ∀ c, Block.listCount (g c) = Block.listCount c) (items : List (List Block)) :
    ∀ init : Nat, (items.map g).foldl (fun acc c => acc + Block.listCount c) init
      = items.foldl (fun acc c => acc + Block.listCount c) init := by
  induction items with
  | nil => intro init; simp
  | cons x rest ih => intro init; simp only [List.map_cons, List.foldl_cons, hg]; exact ih _

mutual
theorem Block.count_mapF (fi : Inline → Inline) (fb : Block → Block)
    (hfb : ∀ b, Block.count (fb b) = Block.count b) :
    (n : Nat) → (b : Block) → Block.count (Block.mapF fi fb n b) = Block.count b
  | 0, _ => rfl
  | n + 1, b => by
    match b with
    | .paragraph _ => simp [Block.mapF, hfb, Block.count]
    | .heading .. => simp [Block.mapF, hfb, Block.count]
    | .codeBlock .. => simp [Block.mapF, hfb, Block.count]
    | .thematicBreak => simp [Block.mapF, hfb, Block.count]
    | .htmlBlock _ => simp [Block.mapF, hfb, Block.count]
    | .blockQuote content =>
      simp only [Block.mapF, hfb, Block.count]
      rw [Block.listCount_mapListF fi fb hfb n content]
    | .list kind tight items =>
      simp only [Block.mapF, hfb, Block.count]
      rw [foldl_listCount_map _ (Block.listCount_mapListF fi fb hfb n) items]

theorem Block.listCount_mapListF (fi : Inline → Inline) (fb : Block → Block)
    (hfb : ∀ b, Block.count (fb b) = Block.count b) :
    (n : Nat) → (bs : List Block) →
      Block.listCount (Block.mapListF fi fb n bs) = Block.listCount bs
  | 0, _ => rfl
  | n + 1, bs => by
    match bs with
    | [] => rfl
    | b :: rest =>
      simp only [Block.mapListF, Block.listCount]
      rw [Block.count_mapF fi fb hfb n b, Block.listCount_mapListF fi fb hfb n rest]
end

theorem count_sanitizeBlock (b : Block) : Block.count (sanitizeBlock b) = Block.count b := by
  match b with
  | .htmlBlock _ => simp [sanitizeBlock, Block.count]
  | .paragraph _ | .heading .. | .codeBlock .. | .thematicBreak | .blockQuote _ | .list .. => rfl

/-- `Document.sanitize` leaves `Block.listCount` alone, so the fuel `renderBlocks` computes
    from the sanitized document is the fuel `Document.sanitize` itself ran at. -/
theorem Document.listCount_sanitize (doc : Document) :
    Block.listCount (Document.sanitize doc) = Block.listCount doc :=
  Block.listCount_mapListF sanitizeInline sanitizeBlock count_sanitizeBlock _ doc

end CommonMark
