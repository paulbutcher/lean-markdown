-- Copyright (c) 2026 Paul Butcher. All rights reserved.
import CommonMark
import Lean.Data.Json

open Lean (Json)

structure SpecExample where
  markdown : String
  html : String
  example_ : Nat
  section_ : String

def parseSpecExample (j : Json) : Except String SpecExample := do
  let markdown ← (← j.getObjVal? "markdown").getStr?
  let html ← (← j.getObjVal? "html").getStr?
  let example_ ← (← j.getObjVal? "example").getNat?
  let section_ ← (← j.getObjVal? "section").getStr?
  pure { markdown, html, example_, section_ }

def loadSpecExamples (path : System.FilePath) : IO (Array SpecExample) := do
  let contents ← IO.FS.readFile path
  match Json.parse contents >>= Json.getArr? >>= (·.mapM parseSpecExample) with
  | .ok examples => pure examples
  | .error e => throw (IO.userError s!"failed to load {path}: {e}")

def checkExample (ex : SpecExample) : IO Bool := do
  let actual := CommonMark.renderHtml (CommonMark.parseDocument ex.markdown)
  if actual == ex.html then
    pure true
  else
    IO.eprintln s!"example {ex.example_} ({ex.section_}) failed\nexpected: {ex.html}\nactual:   {actual}"
    pure false

-- Covers the block- and inline-structure constructs implemented so far. Not the full suite:
-- driving that to 100% (and asserting it) is Phase 5's job, once every construct is in place.
def regressionExamples : List Nat :=
  [43, 62, 83, 107, 119, 228, 231, 269, 650,
   12, 25, 328, 350, 361, 400, 482, 572, 594, 613, 633, 648,
   61, 21, 176, 592, 284]

def main : IO Unit := do
  let examples ← loadSpecExamples "test/vendor/spec.json"
  let mut allPassed := true
  for n in regressionExamples do
    match examples.find? (·.example_ == n) with
    | none => throw (IO.userError s!"example {n} not found in spec.json")
    | some ex =>
      if ← checkExample ex then
        IO.println s!"spec example {n} ({ex.section_}) passed"
      else
        allPassed := false
  if !allPassed then IO.Process.exit 1
