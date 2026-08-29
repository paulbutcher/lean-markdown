-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import CommonMark
public import Plausible
meta import CommonMark
meta import Plausible

@[expose] public section

namespace CommonMark.Parser

-- `normalizeMathContent` maps line endings to spaces and leaves everything else alone. The
-- neighbouring `normalizeCodeSpanContent` additionally strips one surrounding space, and
-- copying that here would be wrong: md4c keeps both spaces of `$ 4 $`. Stating the invariant
-- as a length equality is what makes that mistake fail to compile rather than fail a guard,
-- since any stripping rule shortens some input.
theorem normalizeMathContent_length (raw : List Char) :
    (normalizeMathContent raw).length = raw.length := by
  simp [normalizeMathContent]

end CommonMark.Parser

-- Whole-pipeline claims, checked observably rather than proved, for the reason
-- `GfmNonEmissionProperties.lean` gives at length: the parsing path runs through `Id.run`/
-- `for`/`mut` loops (`tokenizeF`, `resolveEmphasis`, `resolveBrackets`) that this codebase has
-- no tactic machinery for. Plausible fuzzes each shape and fails the build the moment one does
-- not hold.

open CommonMark.Parser (containsSubstr)

private def mathDollars (n : Nat) : String := String.ofList (List.replicate (n % 2 + 1) '$')

private def mathInner (n : Nat) : String := String.ofList (List.replicate (n % 6 + 1) 'x')

private def mathMarkdown (dollars innerLen : Nat) : String :=
  mathDollars dollars ++ mathInner innerLen ++ mathDollars dollars ++ "\n"

-- With the extension off, a math-shaped input is ordinary text: every dollar survives to the
-- output. This is what makes the opt-in real, and it is the claim the whole `Options` design
-- rests on.
#eval Plausible.Testable.check
  (∀ dollars innerLen : Nat,
    containsSubstr (CommonMark.renderHtml (CommonMark.parseDocument (mathMarkdown dollars innerLen)))
      (mathDollars dollars) = true)

-- With it on, the same input becomes a math span whose LaTeX source is carried through intact.
#eval Plausible.Testable.check
  (∀ dollars innerLen : Nat,
    let out := CommonMark.renderHtml
      (CommonMark.parseDocumentWith { math := true } (mathMarkdown dollars innerLen))
    (containsSubstr out "class=\"math " && containsSubstr out (mathInner innerLen)) = true)

-- No dollar reaches the output once the delimiters have been consumed: the span's markers are
-- replaced by the LaTeX delimiters rather than being emitted alongside them.
#eval Plausible.Testable.check
  (∀ dollars innerLen : Nat,
    containsSubstr (CommonMark.renderHtml
      (CommonMark.parseDocumentWith { math := true } (mathMarkdown dollars innerLen))) "$" = false)
