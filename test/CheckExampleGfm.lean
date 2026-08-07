-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import GFMarkdown

-- As `checkExample` (`CheckExample.lean`), but against the GFM entry points.
def checkExampleGfm (exampleNum : Nat) (sectionName markdown expected : String) : Bool :=
  let actual := GFMarkdown.renderHtml (GFMarkdown.parseDocument markdown)
  if actual == expected then true
  else
    dbg_trace s!"GFM example {exampleNum} ({sectionName}) failed\nexpected: {expected}\nactual:   {actual}"
    false
