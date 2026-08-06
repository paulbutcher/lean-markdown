-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import CommonMark

-- A genuine security property (HTML injection), not just a correctness nicety: no AST
-- leaf's literal string content can produce unescaped `<`, `>`, `&`, or unescaped `"`
-- inside an attribute in `renderHtml`'s output. Proven here, against the renderer's
-- escaping primitives, rather than in the library itself, since nothing in the library
-- depends on these theorems; they exist purely to certify the guarantee `renderHtml`'s
-- doc comment (`CommonMark/Render/Html.lean`) advertises.

namespace CommonMark

-- Escaping-safety: `escapeChar`/`escapeText` never let a `<`, `>`, or `"` through raw, no
-- matter what string they're given. This is the load-bearing fact behind every attribute
-- and text node the renderer produces from AST leaf content.

theorem escapeChar_safe (c : Char) :
    ∀ d ∈ (escapeChar c).toList, d ≠ '<' ∧ d ≠ '>' ∧ d ≠ '"' := by
  unfold escapeChar
  split <;> first
    | decide
    | (intro d hd
       simp only [Char.toString, String.toList_singleton, List.mem_singleton] at hd
       subst hd
       simp_all)

-- General shape shared by every "concatenate an escaped/safe piece per element" fold
-- below (`escapeText`, and later `plainTextOfInlines`): if every piece `g x` is safe
-- and the starting accumulator is safe, so is the whole fold, regardless of what `g` is.
-- Kept independent of `Inline`/`Char` specifics (and of the `escapeChar`/`plainTextOf`
-- mutual-recursion groups) so it can be reused without disturbing their termination proofs.
theorem foldl_append_safe {α : Type} (g : α → String) (l : List α) (acc : String)
    (hacc : ∀ d ∈ acc.toList, d ≠ '<' ∧ d ≠ '>' ∧ d ≠ '"')
    (hg : ∀ x d, d ∈ (g x).toList → d ≠ '<' ∧ d ≠ '>' ∧ d ≠ '"') :
    ∀ d ∈ (l.foldl (fun acc x => acc ++ g x) acc).toList, d ≠ '<' ∧ d ≠ '>' ∧ d ≠ '"' := by
  induction l generalizing acc with
  | nil => simpa using hacc
  | cons x rest ih =>
    apply ih
    intro d hd
    rw [String.toList_append] at hd
    rcases List.mem_append.mp hd with hd' | hd'
    · exact hacc d hd'
    · exact hg x d hd'

-- Lets a cons-headed fold be split into its head's contribution and the fold over the
-- tail, which is what keeps the mutual safety proof below in exactly the head/tail shape
-- Lean's termination checker already accepts for `plainTextOf`/`plainTextOfInlines`
-- themselves, rather than routing through an accumulator-generalized helper (whose extra
-- parameter the checker can't line up against the other mutual member's single argument).
theorem foldl_append_eq {α : Type} (g : α → String) (l : List α) (c : String) :
    l.foldl (fun acc x => acc ++ g x) c = c ++ l.foldl (fun acc x => acc ++ g x) "" := by
  induction l generalizing c with
  | nil => simp
  | cons x rest ih =>
    calc (x :: rest).foldl (fun acc y => acc ++ g y) c
        = rest.foldl (fun acc y => acc ++ g y) (c ++ g x) := rfl
      _ = (c ++ g x) ++ rest.foldl (fun acc y => acc ++ g y) "" := ih (c ++ g x)
      _ = c ++ (g x ++ rest.foldl (fun acc y => acc ++ g y) "") := String.append_assoc
      _ = c ++ rest.foldl (fun acc y => acc ++ g y) (g x) := by rw [ih (g x)]
      _ = c ++ (x :: rest).foldl (fun acc y => acc ++ g y) "" := rfl

theorem escapeText_safe (s : String) :
    ∀ d ∈ (escapeText s).toList, d ≠ '<' ∧ d ≠ '>' ∧ d ≠ '"' := by
  unfold escapeText
  rw [String.foldl_eq_foldl_toList]
  exact foldl_append_safe escapeChar s.toList "" (by simp) escapeChar_safe

-- `escapeUri` is `escapeText` applied to whatever `percentEncodeUriF` produces, so its
-- safety follows regardless of what that intermediate string looks like.
theorem escapeUri_safe (s : String) :
    ∀ d ∈ (escapeUri s).toList, d ≠ '<' ∧ d ≠ '>' ∧ d ≠ '"' :=
  escapeText_safe _

-- `plainTextOf`/`plainTextOfInlines` strip markup down to text, but the leftover text is
-- still leaf content and needs the same guarantee: dropping into `.htmlInline` returns ""
-- rather than the raw markup, so alt text built from it can't smuggle a tag through either.
mutual
theorem plainTextOf_safe (i : Inline) :
    ∀ d ∈ (plainTextOf i).toList, d ≠ '<' ∧ d ≠ '>' ∧ d ≠ '"' := by
  match i with
  | .text s => simp only [plainTextOf]; exact escapeText_safe s
  | .code s => simp only [plainTextOf]; exact escapeText_safe s
  | .emph content => simp only [plainTextOf]; exact plainTextOfInlines_safe content
  | .strong content => simp only [plainTextOf]; exact plainTextOfInlines_safe content
  | .link _ _ content => simp only [plainTextOf]; exact plainTextOfInlines_safe content
  | .image _ _ content => simp only [plainTextOf]; exact plainTextOfInlines_safe content
  | .htmlInline _ => simp [plainTextOf]
  | .softBreak => simp [plainTextOf]
  | .lineBreak => simp [plainTextOf]

theorem plainTextOfInlines_safe (content : List Inline) :
    ∀ d ∈ (plainTextOfInlines content).toList, d ≠ '<' ∧ d ≠ '>' ∧ d ≠ '"' := by
  match content with
  | [] => simp [plainTextOfInlines]
  | i :: rest =>
    simp only [plainTextOfInlines]
    show ∀ d ∈ (rest.foldl (fun acc j => acc ++ plainTextOf j) (plainTextOf i)).toList,
        d ≠ '<' ∧ d ≠ '>' ∧ d ≠ '"'
    rw [foldl_append_eq plainTextOf rest (plainTextOf i)]
    intro d hd
    rw [String.toList_append] at hd
    rcases List.mem_append.mp hd with hd' | hd'
    · exact plainTextOf_safe i d hd'
    · exact plainTextOfInlines_safe rest d (by simpa [plainTextOfInlines] using hd')
end

end CommonMark
