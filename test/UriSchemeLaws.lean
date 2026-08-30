-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import CommonMark

@[expose] public section

-- `isSafeUriScheme` lowercases a destination's scheme before testing it against
-- `allowedUriSchemes`, so every casing of a given scheme stands or falls together and the
-- mixed-case bypass (`JaVaScRiPt:`) that defeats a naive filter cannot get through. That is a
-- claim about a pure total function over a finite allowlist, so it is proved here rather than
-- sampled: one proof covers every casing of every scheme.

namespace CommonMark

def lowerString (s : String) : String :=
  String.ofList (s.toList.map Char.toLower)

/-- A character whose lowercasing is a lower-case letter was a letter to begin with.

    The hypothesis is about `c.toLower` and the conclusion about `c`, which is the direction
    the caller needs: it knows only what lowercasing produced, and has to recover the shape of
    what was written. `Char.toLower` moves nothing but `'A'`-`'Z'`, so `c` is either an
    upper-case letter or unchanged, and `isAlpha` holds either way. -/
private theorem isAlpha_of_toLower_isLower {c : Char} (h : c.toLower.isLower = true) :
    c.isAlpha = true := by
  by_cases hc : c.val ≥ 'A'.val ∧ c.val ≤ 'Z'.val
  · simp only [Char.isAlpha, Char.isUpper, Bool.or_eq_true, decide_eq_true_eq]
    exact Or.inl hc
  · rw [show c.toLower = c from by
      simp [Char.toLower]
      intro h'
      exact absurd h' hc] at h
    simp [Char.isAlpha, h]

/-- No letter is a control character, so `stripControlChars` never eats one.

    `isUriControlChar` is "below `0x20`, or `0x7F`", and a letter's code point lies in 65-90 or
    97-122, so both disjuncts fail. Stated as `= false` rather than as a negation because
    `stripControlChars` filters on the `Bool`. -/
private theorem isUriControlChar_eq_false_of_isAlpha {c : Char} (h : c.isAlpha = true) :
    isUriControlChar c = false := by
  simp only [Char.isAlpha, Char.isUpper, Char.isLower, Bool.or_eq_true, decide_eq_true_eq,
    Bool.and_eq_true, UInt32.le_iff_toNat_le] at h
  have hA : 'A'.val.toNat = 65 := rfl
  have hZ : 'Z'.val.toNat = 90 := rfl
  have ha : 'a'.val.toNat = 97 := rfl
  have hz : 'z'.val.toNat = 122 := rfl
  simp only [isUriControlChar, Bool.or_eq_false_iff, decide_eq_false_iff_not,
    beq_eq_false_iff_ne, Char.toNat]
  omega

/-- Every letter is a scheme character, so `takeWhile isSchemeChar` cannot stop part way
    through a scheme spelled with letters.

    `isSchemeChar` admits alphanumerics and `'+'`, `'-'`, `'.'`, of which the letters are a
    subset; the converse is false and is not wanted, a scheme being allowed digits too. -/
private theorem isSchemeChar_of_isAlpha {c : Char} (h : c.isAlpha = true) :
    isSchemeChar c = true := by
  simp [isSchemeChar, Char.isAlphanum, h]

/-- `takeWhile` stops at the first element that fails the test, so given a prefix that all
    passes and an element that fails, it returns exactly that prefix.

    The two hypotheses are the general form of "the scheme is all scheme characters" and "the
    `':'` after it is not one". `l₂` carries no hypothesis because `takeWhile` never looks past
    the element that stopped it, which is what makes the destination's arbitrary remainder
    irrelevant. Nothing about URIs is used, hence the statement over any `α` and `p`. -/
private theorem takeWhile_append_cons {α : Type} (p : α → Bool) (l₁ : List α) (x : α)
    (l₂ : List α) (h₁ : ∀ a ∈ l₁, p a = true) (hx : p x = false) :
    (l₁ ++ x :: l₂).takeWhile p = l₁ := by
  induction l₁ with
  | nil => simp [hx]
  | cons a rest ih =>
    simp only [List.cons_append, List.takeWhile_cons, h₁ a (List.mem_cons_self ..), reduceIte]
    rw [ih (fun b hb => h₁ b (List.mem_cons_of_mem _ hb))]

/-- A destination written as a letters-only scheme, a colon, and anything at all has that
    scheme found in it, even though control characters are stripped first.

    `extractScheme` returns `some scheme` as written, not its lowercasing, leaving the casing
    decision to `isSafeUriScheme`. `rest` is unconstrained, so control characters hidden
    anywhere after the colon cannot dislodge what is found; the scheme itself survives the
    strip because letters are never control characters. Requiring the scheme to be all letters
    is stronger than RFC 3986, which also admits digits and `'+'`, `'-'`, `'.'`, but it is what
    the schemes at issue need and what makes both steps above apply. -/
private theorem extractScheme_append (scheme rest : String)
    (hne : scheme.toList ≠ [])
    (halpha : ∀ a ∈ scheme.toList, a.isAlpha = true) :
    extractScheme (stripControlChars (scheme ++ ":" ++ rest)) = some scheme := by
  match hs : scheme.toList, hne with
  | c :: cs, _ =>
    have hc : c.isAlpha = true := halpha c (hs ▸ List.mem_cons_self ..)
    have hcs : ∀ a ∈ cs, a.isAlpha = true := fun a ha =>
      halpha a (hs ▸ List.mem_cons_of_mem _ ha)
    have hcat : (scheme ++ ":" ++ rest).toList = scheme.toList ++ ':' :: rest.toList := by
      simp [String.toList_append]
    have hkeep : scheme.toList.filter (fun c => !isUriControlChar c) = c :: cs :=
      hs ▸ List.filter_eq_self.mpr (fun a ha => by
        simp [isUriControlChar_eq_false_of_isAlpha (halpha a ha)])
    have hstrip : (stripControlChars (scheme ++ ":" ++ rest)).toList
        = c :: (cs ++ ':' :: rest.toList.filter (fun c => !isUriControlChar c)) := by
      simp only [stripControlChars, String.toList_ofList, hcat, List.filter_append, hkeep,
        List.filter_cons, show (!isUriControlChar ':') = true from by decide, reduceIte,
        List.cons_append]
    simp only [extractScheme, hstrip,
      show isSchemeStartChar c = true from by simpa [isSchemeStartChar] using hc, reduceIte]
    rw [takeWhile_append_cons _ cs ':' _ (fun a ha => isSchemeChar_of_isAlpha (hcs a ha))
      (by decide), List.drop_left, ← hs, String.ofList_toList]
    rfl

/-- A destination whose letters-only scheme is not on the allowlist is rejected, however it is
    capitalized.

    The hypothesis names `lowerString scheme`, not `scheme`, and that is the whole point: one
    assumption about the lowercased form yields the conclusion for every casing that lowercases
    to it, because `isSafeUriScheme` lowercases before consulting `allowedUriSchemes`. `rest`
    is unconstrained, nothing after the colon being able to make an unlisted scheme safe. -/
theorem not_isSafeUriScheme_of_alpha_scheme (scheme rest : String)
    (hne : scheme.toList ≠ [])
    (halpha : ∀ a ∈ scheme.toList, a.isAlpha = true)
    (hno : allowedUriSchemes.contains (lowerString scheme) = false) :
    isSafeUriScheme (scheme ++ ":" ++ rest) = false := by
  simp only [isSafeUriScheme, extractScheme_append scheme rest hne halpha]
  simpa [lowerString] using hno

/-- Every casing of `javascript:` is rejected. This is the claim the mixed-case bypass would
    have to break, and the one a filter that compares the scheme as written gets wrong.

    `lowerString scheme = "javascript"` picks out exactly the strings that lowercase to it,
    `JaVaScRiPt` among them, so the proposition covers every capitalization at once rather than
    the few a sampled test would reach. `rest` is unconstrained, so the payload the URL carries
    plays no part. -/
theorem not_isSafeUriScheme_javascript (scheme rest : String)
    (h : lowerString scheme = "javascript") :
    isSafeUriScheme (scheme ++ ":" ++ rest) = false := by
  have hmap : scheme.toList.map Char.toLower = "javascript".toList := by
    simpa [lowerString] using congrArg String.toList h
  have halpha : ∀ a ∈ scheme.toList, a.isAlpha = true := by
    intro a hasm
    refine isAlpha_of_toLower_isLower ?_
    have hmem : a.toLower ∈ "javascript".toList := hmap ▸ List.mem_map_of_mem hasm
    have hall : ∀ x ∈ "javascript".toList, x.isLower = true := by decide
    exact hall _ hmem
  refine not_isSafeUriScheme_of_alpha_scheme scheme rest ?_ halpha (by rw [h]; decide)
  intro hnil
  rw [hnil] at hmap
  simp at hmap

end CommonMark
