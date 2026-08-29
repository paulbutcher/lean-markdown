-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import GfmAstFuelLaws
public import SanitizeIdempotence

@[expose] public section

-- `SanitizeIdempotence.lean`'s claim, for the GFM variant. Reuses that module's
-- `sanitizeDest_idem`, this variant's sanitizer sharing `CommonMark`'s scheme allowlist.

namespace GFMarkdown

open CommonMark.Parser (RawInline)
open CommonMark (sanitizeDest sanitizeDest_idem)

mutual
theorem sanitizeInline_idem : (i : RawInline) →
    sanitizeInline (sanitizeInline i) = sanitizeInline i
  | .text _ | .code _ | .math .. | .softBreak | .lineBreak | .htmlInline _ => rfl
  | .emph content => by
    simp only [sanitizeInline]
    rw [sanitizeInlineList_idem content]
  | .strong content => by
    simp only [sanitizeInline]
    rw [sanitizeInlineList_idem content]
  | .strikethrough content => by
    simp only [sanitizeInline]
    rw [sanitizeInlineList_idem content]
  | .link dest _ content => by
    simp only [sanitizeInline]
    rw [sanitizeInlineList_idem content, sanitizeDest_idem dest]
  | .image dest _ content => by
    simp only [sanitizeInline]
    rw [sanitizeInlineList_idem content, sanitizeDest_idem dest]

theorem sanitizeInlineList_idem : (l : List RawInline) →
    sanitizeInlineList (sanitizeInlineList l) = sanitizeInlineList l
  | [] => rfl
  | i :: rest => by
    simp only [sanitizeInlineList]
    rw [sanitizeInline_idem i, sanitizeInlineList_idem rest]
end

mutual
theorem sanitizeBlockF_idem : (n : Nat) → (b : Block) →
    sanitizeBlockF n (sanitizeBlockF n b) = sanitizeBlockF n b
  | 0, _ => rfl
  | n + 1, b => by
    match b with
    | .paragraph content =>
      simp only [sanitizeBlockF]
      rw [sanitizeInlineList_idem content]
    | .heading _ content =>
      simp only [sanitizeBlockF]
      rw [sanitizeInlineList_idem content]
    | .codeBlock .. => rfl
    | .thematicBreak => rfl
    | .htmlBlock _ => rfl
    | .blockQuote content =>
      simp only [sanitizeBlockF]
      rw [sanitizeBlockListF_idem n content]
    | .list _ _ items =>
      simp only [sanitizeBlockF, List.map_map]
      congr 1
      refine List.map_congr_left ?_
      intro c _
      simp only [Function.comp_apply]
      rw [sanitizeBlockListF_idem n c.2]
    | .table header _ rows =>
      simp only [sanitizeBlockF, List.map_map]
      congr 1
      · exact List.map_congr_left (fun c _ => sanitizeInlineList_idem c)
      · refine List.map_congr_left ?_
        intro row _
        simp only [Function.comp_apply, List.map_map]
        exact List.map_congr_left (fun c _ => sanitizeInlineList_idem c)

theorem sanitizeBlockListF_idem : (n : Nat) → (bs : List Block) →
    sanitizeBlockListF n (sanitizeBlockListF n bs) = sanitizeBlockListF n bs
  | 0, _ => rfl
  | n + 1, bs => by
    match bs with
    | [] => rfl
    | b :: rest =>
      simp only [sanitizeBlockListF]
      rw [sanitizeBlockF_idem n b, sanitizeBlockListF_idem n rest]
end

/-- Sanitizing is idempotent: it reaches a fixed point in one pass. -/
theorem Document.sanitize_idem (doc : Document) :
    Document.sanitize (Document.sanitize doc) = Document.sanitize doc := by
  show sanitizeBlockListF (Block.listCount (Document.sanitize doc) + 1) (Document.sanitize doc)
    = Document.sanitize doc
  rw [Document.listCount_sanitize]
  exact sanitizeBlockListF_idem _ doc

end GFMarkdown
