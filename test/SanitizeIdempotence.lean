-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import AstFuelLaws

@[expose] public section

-- Sanitizing an already-sanitized document changes nothing. `SanitizeSafety.lean` proves the
-- rewrite establishes its two properties; this proves it stops there, so a caller that
-- sanitizes defensively at more than one layer gets the same document rather than a
-- progressively degraded one.

namespace CommonMark

private theorem isSafeUriScheme_sanitizeDest (dest : String) :
    isSafeUriScheme (sanitizeDest dest) = true := by
  unfold sanitizeDest
  split
  · assumption
  · decide

theorem sanitizeDest_idem (dest : String) :
    sanitizeDest (sanitizeDest dest) = sanitizeDest dest := by
  show (if isSafeUriScheme (sanitizeDest dest) then sanitizeDest dest else "")
    = sanitizeDest dest
  simp [isSafeUriScheme_sanitizeDest dest]

mutual
theorem Inline.map_sanitizeInline_idem : (i : Inline) →
    Inline.map sanitizeInline (Inline.map sanitizeInline i) = Inline.map sanitizeInline i
  | .text _ | .code _ | .math .. | .softBreak | .lineBreak | .htmlInline _ => rfl
  | .emph content => by
    simp only [Inline.map, sanitizeInline]
    rw [Inline.mapList_sanitizeInline_idem content]
  | .strong content => by
    simp only [Inline.map, sanitizeInline]
    rw [Inline.mapList_sanitizeInline_idem content]
  | .link dest _ content => by
    simp only [Inline.map, sanitizeInline]
    rw [Inline.mapList_sanitizeInline_idem content, sanitizeDest_idem dest]
  | .image dest _ content => by
    simp only [Inline.map, sanitizeInline]
    rw [Inline.mapList_sanitizeInline_idem content, sanitizeDest_idem dest]

theorem Inline.mapList_sanitizeInline_idem : (l : List Inline) →
    Inline.mapList sanitizeInline (Inline.mapList sanitizeInline l)
      = Inline.mapList sanitizeInline l
  | [] => rfl
  | i :: rest => by
    simp only [Inline.mapList]
    rw [Inline.map_sanitizeInline_idem i, Inline.mapList_sanitizeInline_idem rest]
end

mutual
theorem Block.mapF_sanitize_idem : (n : Nat) → (b : Block) →
    Block.mapF sanitizeInline sanitizeBlock n (Block.mapF sanitizeInline sanitizeBlock n b)
      = Block.mapF sanitizeInline sanitizeBlock n b
  | 0, _ => rfl
  | n + 1, b => by
    match b with
    | .paragraph content =>
      simp only [Block.mapF, sanitizeBlock]
      rw [Inline.mapList_sanitizeInline_idem content]
    | .heading _ content =>
      simp only [Block.mapF, sanitizeBlock]
      rw [Inline.mapList_sanitizeInline_idem content]
    | .codeBlock .. => rfl
    | .thematicBreak => rfl
    | .htmlBlock _ => rfl
    | .blockQuote content =>
      simp only [Block.mapF, sanitizeBlock]
      rw [Block.mapListF_sanitize_idem n content]
    | .list _ _ items =>
      simp only [Block.mapF, sanitizeBlock, List.map_map]
      congr 1
      refine List.map_congr_left ?_
      intro c _
      exact Block.mapListF_sanitize_idem n c

theorem Block.mapListF_sanitize_idem : (n : Nat) → (bs : List Block) →
    Block.mapListF sanitizeInline sanitizeBlock n
        (Block.mapListF sanitizeInline sanitizeBlock n bs)
      = Block.mapListF sanitizeInline sanitizeBlock n bs
  | 0, _ => rfl
  | n + 1, bs => by
    match bs with
    | [] => rfl
    | b :: rest =>
      simp only [Block.mapListF]
      rw [Block.mapF_sanitize_idem n b, Block.mapListF_sanitize_idem n rest]
end

/-- Sanitizing is idempotent: it reaches a fixed point in one pass. -/
theorem Document.sanitize_idem (doc : Document) :
    Document.sanitize (Document.sanitize doc) = Document.sanitize doc := by
  show Block.mapListF sanitizeInline sanitizeBlock (Block.listCount (Document.sanitize doc))
    (Document.sanitize doc) = Document.sanitize doc
  rw [Document.listCount_sanitize]
  exact Block.mapListF_sanitize_idem _ doc

end CommonMark
