-- Copyright (c) 2026 Paul Butcher. All rights reserved.
import CommonMark
import SpecExamples
import Conformance

def checkExample (ex : SpecExample) : IO Bool := do
  let actual := CommonMark.renderHtml (CommonMark.parseDocument ex.markdown)
  if actual == ex.html then
    pure true
  else
    IO.eprintln s!"example {ex.example_} ({ex.section_}) failed\nexpected: {ex.html}\nactual:   {actual}"
    pure false

def main : IO Unit := do
  let mut passed := 0
  for ex in specExamples do
    if ← checkExample ex then
      passed := passed + 1
  IO.println s!"{passed}/{specExamples.length} spec examples passed"
  if passed != specExamples.length then
    IO.Process.exit 1
