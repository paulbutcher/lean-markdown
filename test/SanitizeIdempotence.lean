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

/-- `sanitizeDest` never yields a destination unsafe to emit as an `href`/`src`, whatever it is
    handed.

    The same claim `SanitizeSafety.lean` proves under this name, restated because that copy is
    `private` to its module. It is what tells the theorem below which branch of `sanitizeDest`'s
    `if` a second pass takes. -/
private theorem isSafeUriScheme_sanitizeDest (dest : String) :
    isSafeUriScheme (sanitizeDest dest) = true := by
  unfold sanitizeDest
  split
  · assumption
  · decide

/-- Sanitizing a destination twice is sanitizing it once: a second defensive pass cannot clear
    a destination the first pass kept.

    An equality between strings, not a safety claim: safety is the theorem above, and this
    says the rewrite stops once it has been applied. It rules out both ways idempotence could
    fail, since the destination a first pass keeps is by that theorem one the second accepts,
    and the empty string a first pass substitutes has no scheme and so is kept in turn. -/
theorem sanitizeDest_idem (dest : String) :
    sanitizeDest (sanitizeDest dest) = sanitizeDest dest := by
  show (if isSafeUriScheme (sanitizeDest dest) then sanitizeDest dest else "")
    = sanitizeDest dest
  simp [isSafeUriScheme_sanitizeDest dest]

mutual
/-- A second sanitizing pass over an inline tree changes nothing.

    Both sides are `Inline.map sanitizeInline`, the whole-tree rewrite, not `sanitizeInline`
    alone, so the claim is about what a caller actually applies. The `.htmlInline` case turns
    on the replacement being `.text ""`, which sanitizing leaves alone; a replacement that
    itself needed sanitizing would make the equality false. -/
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

/-- The same of a list of inline nodes.

    `Inline.mapList` is how `Inline.map` reaches a node's children, so the claim above holds
    only as far as this one does; the two are proved together for that reason. -/
theorem Inline.mapList_sanitizeInline_idem : (l : List Inline) →
    Inline.mapList sanitizeInline (Inline.mapList sanitizeInline l)
      = Inline.mapList sanitizeInline l
  | [] => rfl
  | i :: rest => by
    simp only [Inline.mapList]
    rw [Inline.map_sanitizeInline_idem i, Inline.mapList_sanitizeInline_idem rest]
end

mutual
/-- A second sanitizing pass over a block changes nothing, at whatever depth the first ran.

    The same `n` governs both passes, which is the claim wanted: the outer pass is given the
    fuel the inner one had, and `Document.listCount_sanitize` is what lets the document-level
    theorem below recompute that fuel from the sanitized document and get the same number. At
    `n = 0` both sides are `b` untouched, so the case is true without saying anything. -/
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

/-- The same of a list of blocks, which is the shape a `Document` has and so the form the
    theorem below instantiates.

    `Block.mapListF` spends a level per element, so the shared `n` carries the same meaning
    here as above: both passes are allowed the same depth. -/
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

/-- Sanitizing reaches a fixed point in one pass, so a caller that sanitizes defensively at
    more than one layer gets the same document back rather than a progressively degraded one.

    The proposition is an equality between documents, which is stronger than saying the second
    pass leaves the document safe: it says the second pass does nothing whatever. The two
    passes compute their fuel from different documents, the outer from the sanitized one, so
    `Document.listCount_sanitize` has to line the two numbers up before the fuel-indexed lemma
    above applies. -/
theorem Document.sanitize_idem (doc : Document) :
    Document.sanitize (Document.sanitize doc) = Document.sanitize doc := by
  show Block.mapListF sanitizeInline sanitizeBlock (Block.listCount (Document.sanitize doc))
    (Document.sanitize doc) = Document.sanitize doc
  rw [Document.listCount_sanitize]
  exact Block.mapListF_sanitize_idem _ doc

end CommonMark
