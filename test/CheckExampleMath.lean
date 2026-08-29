-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import CommonMark

@[expose] public section

-- As `checkExample` (`CheckExample.lean`), but with the LaTeX math extension enabled.
def checkExampleMath (exampleNum : Nat) (sectionName markdown expected : String) : Bool :=
  let actual := CommonMark.renderHtml (CommonMark.parseDocumentWith { math := true } markdown)
  if actual == expected then true
  else
    dbg_trace s!"math example {exampleNum} ({sectionName}) failed\nexpected: {expected}\nactual:   {actual}"
    false
