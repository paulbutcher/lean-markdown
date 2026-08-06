-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import CommonMark

-- Algebraic properties of parser building blocks, proven here since nothing in the
-- library depends on them.

namespace CommonMark.Parser

-- `normalizeGo` only ever writes `'\n'` or an already-given character to its accumulator,
-- never `'\r'`, so its output is `'\r'`-free regardless of input.
theorem normalizeGo_no_cr (acc l : List Char) (hacc : ∀ c ∈ acc, c ≠ '\r') :
    ∀ c ∈ normalizeGo acc l, c ≠ '\r' := by
  induction acc, l using normalizeGo.induct with
  | case1 acc =>
    simp only [normalizeGo]
    exact fun c hc => hacc c (List.mem_reverse.mp hc)
  | case2 acc rest ih =>
    simp only [normalizeGo]
    apply ih
    intro c hc
    rcases List.mem_cons.mp hc with hc | hc
    · rw [hc]; decide
    · exact hacc c hc
  | case3 acc rest _hexcl ih =>
    simp only [normalizeGo]
    apply ih
    intro c hc
    rcases List.mem_cons.mp hc with hc | hc
    · rw [hc]; decide
    · exact hacc c hc
  | case4 acc c rest _hexcl hcne ih =>
    simp only [normalizeGo]
    apply ih
    intro c' hc'
    rcases List.mem_cons.mp hc' with hc' | hc'
    · rw [hc']; exact hcne
    · exact hacc c' hc'

-- A `'\r'`-free input passes through unchanged (up to the accumulator prefix): there's
-- nothing left for `normalizeGo` to rewrite.
theorem normalizeGo_eq_of_no_cr (acc l : List Char) (hl : ∀ c ∈ l, c ≠ '\r') :
    normalizeGo acc l = acc.reverse ++ l := by
  induction acc, l using normalizeGo.induct with
  | case1 acc => simp [normalizeGo]
  | case2 acc rest ih => exact absurd rfl (hl '\r' (by simp))
  | case3 acc rest _hexcl ih => exact absurd rfl (hl '\r' (by simp))
  | case4 acc c rest _hexcl hcne ih =>
    have hrest : ∀ x ∈ rest, x ≠ '\r' := fun x hx => hl x (List.mem_cons_of_mem c hx)
    simp only [normalizeGo]
    rw [ih hrest]
    simp [List.reverse_cons]

-- Idempotence: normalizing an already-normalized document is a no-op, since normalization
-- only ever removes `'\r'` and there's none left after the first pass.
theorem normalizeNewlines_idem (s : String) :
    normalizeNewlines (normalizeNewlines s) = normalizeNewlines s := by
  simp only [normalizeNewlines]
  congr 1
  have hnocr : ∀ c ∈ normalizeGo [] s.toList, c ≠ '\r' := normalizeGo_no_cr [] s.toList (by simp)
  simp only [String.toList_ofList]
  exact normalizeGo_eq_of_no_cr [] (normalizeGo [] s.toList) hnocr

end CommonMark.Parser
