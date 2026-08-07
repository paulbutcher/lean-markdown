-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import CommonMark
import Plausible

-- `RawBlock.table`'s fallback arm in `CommonMark.Parser.rawBlockToBlockF` and
-- `narrowInline`'s `.strikethrough` fallback arm in `CommonMark.Parser.narrowInline`
-- (`CommonMark/Parser/Block.lean`, `CommonMark/Parser/Inline.lean`) both collapse their input
-- to an empty/lossy result (`.paragraph []`, `.text ""`). That's only safe because the plain
-- (non-GFM) parsing path is believed to never actually reach either arm. Proving that formally
-- would mean reasoning about `Id.run`/`for`/`mut` loops (`closeFramesTo`, `matchContainers`,
-- `resolveEmphasis`, `resolveBrackets`, ...) that this codebase has no existing tactic
-- machinery for; the properties below check the same claim indirectly but observably instead,
-- entirely through the public `CommonMark.parseDocument`/`CommonMark.renderHtml` API: if either
-- fallback ever fired on the plain path, the corresponding table/strikethrough-shaped input's
-- text would go missing from the rendered output. Plausible fuzzes many instances of each
-- shape and fails the build (`Testable.check` throws) the moment one does.

open CommonMark.Parser (containsSubstr)

private def tableMarkdown (numCols numRows : Nat) : String :=
  let cols := numCols % 4 + 1
  let rows := numRows % 4
  let colIdxs := List.range cols
  let header := "| " ++ String.intercalate " | " (colIdxs.map fun i => s!"h{i}") ++ " |"
  let delim := "| " ++ String.intercalate " | " (colIdxs.map fun _ => "---") ++ " |"
  let rowLines := (List.range rows).map fun r =>
    "| " ++ String.intercalate " | " (colIdxs.map fun c => s!"r{r}c{c}") ++ " |"
  String.intercalate "\n" (header :: delim :: rowLines) ++ "\n"

private def tableCellLabels (numCols numRows : Nat) : List String :=
  let cols := numCols % 4 + 1
  let rows := numRows % 4
  let colIdxs := List.range cols
  colIdxs.map (s!"h{·}") ++ (List.range rows).flatMap fun r => colIdxs.map fun c => s!"r{r}c{c}"

#eval Plausible.Testable.check
  (∀ numCols numRows : Nat,
    (tableCellLabels numCols numRows).all (fun label =>
      containsSubstr (CommonMark.renderHtml (CommonMark.parseDocument (tableMarkdown numCols numRows)))
        label) = true)

private def strikethroughTildes (tildeCount : Nat) : String :=
  String.ofList (List.replicate (tildeCount % 2 + 1) '~')

private def strikethroughMarkdown (tildeCount innerLen : Nat) : String :=
  let inner := String.ofList (List.replicate (innerLen % 6 + 1) 'x')
  let tildes := strikethroughTildes tildeCount
  tildes ++ inner ++ tildes ++ "\n"

#eval Plausible.Testable.check
  (∀ tildeCount innerLen : Nat,
    containsSubstr (CommonMark.renderHtml (CommonMark.parseDocument (strikethroughMarkdown tildeCount innerLen)))
      (strikethroughTildes tildeCount) = true)
