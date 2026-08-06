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

def main : IO Unit := do
  let examples ← loadSpecExamples "test/vendor/spec.json"
  let some ex650 := examples.find? (·.example_ == 650)
    | throw (IO.userError "example 650 not found in spec.json")
  if ← checkExample ex650 then
    IO.println s!"spec example 650 ({ex650.section_}) passed end-to-end"
  else
    IO.Process.exit 1
