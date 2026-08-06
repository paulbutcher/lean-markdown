-- Copyright (c) 2026 Paul Butcher. All rights reserved.
import CommonMark
import SpecExamples

-- A machine-checked certificate that the implementation reproduces every example in the
-- official CommonMark 0.31.2 conformance suite (see test/vendor/spec.json for provenance).
-- `native_decide` compiles the parser, the renderer, and this check to native code and
-- evaluates that, rather than reducing everything in the kernel's term evaluator, which
-- would be far too slow across all 652 examples; the kernel instead checks the compiled
-- result via the trusted `Lean.ofReduceBool` axiom.
theorem commonmark_conformance :
    specExamples.all
      (fun ex => CommonMark.renderHtml (CommonMark.parseDocument ex.markdown) == ex.html) = true := by
  native_decide
