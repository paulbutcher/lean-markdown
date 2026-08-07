-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import CommonMark

-- `dbg_trace` runs (and prints to stderr) even in this pure, non-`IO` context, so a failing
-- `#guard` in SpecGuards.lean still reports what the renderer actually produced instead of
-- just "did not evaluate to `true`".
def checkExample (exampleNum : Nat) (sectionName markdown expected : String) : Bool :=
  let actual := CommonMark.renderHtml (CommonMark.parseDocument markdown)
  if actual == expected then true
  else
    dbg_trace s!"example {exampleNum} ({sectionName}) failed\nexpected: {expected}\nactual:   {actual}"
    false
