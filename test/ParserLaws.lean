-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import CommonMark

@[expose] public section

-- Algebraic properties of parser building blocks, proven here since nothing in the
-- library depends on them.

namespace CommonMark.Parser

/-- `normalizeGo` never leaves a `'\r'` behind, whatever it is given, since it only ever writes
    `'\n'` or an already-given character to its accumulator.

    The proposition quantifies over the accumulator as well as the input, with the hypothesis
    that the accumulator is already `'\r'`-free, because that is what an induction over
    `normalizeGo`'s own recursion needs: each step extends the accumulator, so the claim has to
    be about every reachable state, not only the empty start. `normalizeNewlines_idem` below
    instantiates it at `acc := []`, where the hypothesis is vacuous. -/
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

/-- A `'\r'`-free input passes through `normalizeGo` unchanged: there is nothing left to
    rewrite.

    The right-hand side is `acc.reverse ++ l` rather than `l` because `normalizeGo` builds its
    result reversed in the accumulator and reverses at the end; at `acc := []`, where the
    theorem below uses it, that is exactly `l`. The hypothesis is on the input alone, no
    condition on `acc` being needed, since untouched input is copied whatever preceded it. -/
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

/-- Normalizing an already-normalized document is a no-op, so nothing downstream has to care
    how many times normalization ran.

    Idempotence is the strongest form this claim admits without saying what normalization
    does, and the two theorems above are what make the proposition true rather than merely
    plausible: the first says a pass leaves no `'\r'`, the second says a `'\r'`-free input
    survives a pass intact. -/
theorem normalizeNewlines_idem (s : String) :
    normalizeNewlines (normalizeNewlines s) = normalizeNewlines s := by
  simp only [normalizeNewlines]
  congr 1
  have hnocr : ∀ c ∈ normalizeGo [] s.toList, c ≠ '\r' := normalizeGo_no_cr [] s.toList (by simp)
  simp only [String.toList_ofList]
  exact normalizeGo_eq_of_no_cr [] (normalizeGo [] s.toList) hnocr

end CommonMark.Parser
