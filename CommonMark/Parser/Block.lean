-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import CommonMark.Ast
import CommonMark.Parser.Inline

namespace CommonMark.Parser

def columnWidth (chars : List Char) : Nat :=
  chars.foldl (fun col c => if c == '\t' then col + (4 - col % 4) else col + 1) 0

def leadingWhitespaceChars (s : String) : List Char :=
  s.toList.takeWhile (fun c => c == ' ' || c == '\t')

def leadingWhitespaceWidth (s : String) : Nat :=
  columnWidth (leadingWhitespaceChars s)

-- As `leadingWhitespaceWidth`, but for text that doesn't itself start at column 0 (e.g. the
-- text following a list marker): a tab's expansion depends on its true starting column, so
-- measuring `chars` in isolation from column 0 would be wrong whenever it starts with a tab.
def leadingWhitespaceWidthFrom (startCol : Nat) (chars : List Char) : Nat :=
  let wsChars := chars.takeWhile (fun c => c == ' ' || c == '\t')
  (wsChars.foldl (fun col c => if c == '\t' then col + (4 - col % 4) else col + 1) startCol) - startCol

def isBlank (s : String) : Bool :=
  s.toList.all (fun c => c == ' ' || c == '\t')

-- Fully expands the leading run of tabs/spaces into literal spaces (tracking true column
-- position throughout), leaving the rest of the line untouched. Used once a tab has only
-- been partially consumed by `dropIndentGo`: representing its unconsumed remainder as a bare
-- '\t' character would make a later, independent width measurement of the resulting string
-- restart column tracking from 0 and so expand any *further* tabs to the wrong width, since
-- a tab's expansion depends on which column it actually starts at.
def expandLeadingTabsGo : List Char → Nat → List Char
  | [], _ => []
  | ' ' :: rest, col => ' ' :: expandLeadingTabsGo rest (col + 1)
  | '\t' :: rest, col =>
    let nextStop := col + (4 - col % 4)
    List.replicate (nextStop - col) ' ' ++ expandLeadingTabsGo rest nextStop
  | rest, _ => rest

def dropIndentGo : List Char → Nat → Nat → List Char
  | [], _, _ => []
  | c :: rest, _, 0 => c :: rest
  | c :: rest, col, remaining =>
    match c with
    | ' ' => dropIndentGo rest (col + 1) (remaining - 1)
    | '\t' =>
      let nextStop := col + (4 - col % 4)
      let consumed := nextStop - col
      if consumed <= remaining then
        dropIndentGo rest nextStop (remaining - consumed)
      else
        List.replicate (consumed - remaining) ' ' ++ expandLeadingTabsGo rest nextStop
    | _ => c :: rest

def dropIndent (s : String) (n : Nat) : String :=
  String.ofList (dropIndentGo s.toList 0 n)

def stripUpTo3 (s : String) : String :=
  dropIndent s (min (leadingWhitespaceWidth s) 3)

def stripLeadingWs (s : String) : String :=
  dropIndent s (leadingWhitespaceWidth s)

def stripTrailingWs (s : String) : String :=
  String.ofList (s.toList.reverse.dropWhile (fun c => c == ' ' || c == '\t') |>.reverse)

def containsSubstrChars : List Char → List Char → Bool
  | [], needle => needle.isEmpty
  | h :: t, needle => isPrefixOfChars needle (h :: t) || containsSubstrChars t needle

def containsSubstr (s needle : String) : Bool :=
  containsSubstrChars s.toList needle.toList

def digitsToNat (cs : List Char) : Nat :=
  cs.foldl (fun acc c => acc * 10 + (c.toNat - '0'.toNat)) 0

def stripTrailingBlankLines (lines : List String) : List String :=
  (lines.reverse.dropWhile isBlank).reverse

def matchThematicBreak (line : String) : Bool :=
  let w := leadingWhitespaceWidth line
  if w ≥ 4 then false
  else
    let rest := (dropIndent line w).toList.filter (fun c => c ≠ ' ' && c ≠ '\t')
    match rest with
    | [] => false
    | c :: _ => (c == '-' || c == '_' || c == '*') && rest.length ≥ 3 && rest.all (· == c)

def stripAtxTrailing (s : String) : String :=
  let t := stripTrailingWs s
  let revChars := t.toList.reverse
  let trailingHashes := revChars.takeWhile (· == '#')
  if trailingHashes.isEmpty then t
  else
    let beforeHashes := revChars.drop trailingHashes.length
    match beforeHashes with
    | [] => ""
    | c :: _ =>
      if c == ' ' || c == '\t' then stripTrailingWs (String.ofList beforeHashes.reverse) else t

def matchAtxHeading (line : String) : Option (Nat × String) :=
  let w := leadingWhitespaceWidth line
  if w ≥ 4 then none
  else
    let rest := (dropIndent line w).toList
    let hashes := rest.takeWhile (· == '#')
    let level := hashes.length
    if level == 0 || level > 6 then none
    else
      let afterHashes := rest.drop level
      match afterHashes with
      | [] => some (level, "")
      | c :: _ =>
        if c == ' ' || c == '\t' then
          let content := String.ofList (afterHashes.dropWhile (fun c => c == ' ' || c == '\t'))
          some (level, stripAtxTrailing content)
        else none

def matchSetextUnderline (line : String) : Option Nat :=
  let w := leadingWhitespaceWidth line
  if w ≥ 4 then none
  else
    let core := (stripTrailingWs (dropIndent line w)).toList
    if core.isEmpty then none
    else if core.all (· == '=') then some 1
    else if core.all (· == '-') then some 2
    else none

def matchFenceStart (line : String) : Option (Char × Nat × Nat × Option String) :=
  let w := leadingWhitespaceWidth line
  if w ≥ 4 then none
  else
    match (dropIndent line w).toList with
    | c :: cs =>
      if c == '`' || c == '~' then
        let fenceLen := (c :: cs).takeWhile (· == c) |>.length
        if fenceLen < 3 then none
        else
          let afterFence := (c :: cs).drop fenceLen
          let infoRaw := String.ofList afterFence
          if c == '`' && infoRaw.toList.any (· == '`') then none
          else
            let info := resolveEscapesAndEntities infoRaw.trimAscii.toString
            some (c, fenceLen, w, if info.isEmpty then none else some info)
      else none
    | [] => none

def matchFenceEnd (fenceChar : Char) (fenceLen : Nat) (line : String) : Bool :=
  let w := leadingWhitespaceWidth line
  if w ≥ 4 then false
  else
    let rest := (dropIndent line w).toList
    let run := rest.takeWhile (· == fenceChar)
    run.length ≥ fenceLen && (rest.drop run.length).all (fun c => c == ' ' || c == '\t')

def matchBlockQuoteStart (line : String) : Option String :=
  let w := leadingWhitespaceWidth line
  if w ≥ 4 then none
  else
    match (dropIndent line w).toList with
    | '>' :: '\t' :: rest =>
      let col := w + 1
      let tabWidth := 4 - col % 4
      let extra := tabWidth - 1
      some (String.ofList (List.replicate extra ' ' ++ expandLeadingTabsGo rest (col + tabWidth)))
    | '>' :: ' ' :: rest => some (String.ofList rest)
    | '>' :: rest => some (String.ofList rest)
    | _ => none

def spacesAndIndent (markerWidth : Nat) (afterMarker : List Char) : Nat × String :=
  let afterStr := String.ofList afterMarker
  if isBlank afterStr then (markerWidth + 1, "")
  else
    let w := leadingWhitespaceWidthFrom markerWidth afterMarker
    if w ≥ 5 then (markerWidth + 1, String.ofList (dropIndentGo afterMarker markerWidth 1))
    else (markerWidth + w, String.ofList (dropIndentGo afterMarker markerWidth w))

def matchListMarker (line : String) : Option (ListType × Nat × String) :=
  let indentW := leadingWhitespaceWidth line
  if indentW ≥ 4 then none
  else
    match (dropIndent line indentW).toList with
    | [] => none
    | c :: cs =>
      if c == '-' || c == '+' || c == '*' then
        let markerWidth := indentW + 1
        match cs with
        | [] => some (.bullet c, markerWidth + 1, "")
        | d :: _ =>
          if d == ' ' || d == '\t' then
            let (ci, rem) := spacesAndIndent markerWidth cs
            some (.bullet c, ci, rem)
          else none
      else if c.isDigit then
        let allChars := c :: cs
        let digits := allChars.takeWhile Char.isDigit
        let afterDigits := allChars.drop digits.length
        if digits.length > 9 then none
        else
          match afterDigits with
          | [] => none
          | delim :: tail =>
            if delim == '.' || delim == ')' then
              let markerWidth := indentW + digits.length + 1
              let start := digitsToNat digits
              match tail with
              | [] => some (.ordered start delim, markerWidth + 1, "")
              | t :: _ =>
                if t == ' ' || t == '\t' then
                  let (ci, rem) := spacesAndIndent markerWidth tail
                  some (.ordered start delim, ci, rem)
                else none
            else none
      else none

def listMarkerCanInterrupt (kind : ListType) (afterMarker : String) : Bool :=
  !isBlank afterMarker &&
  match kind with
  | .bullet _ => true
  | .ordered start _ => start == 1

def sameListKind : ListType → ListType → Bool
  | .bullet a, .bullet b => a == b
  | .ordered _ d1, .ordered _ d2 => d1 == d2
  | _, _ => false

inductive HtmlEndKind where
  | untilBlank
  | untilNeedle (needle : String)

def html1Tags : List String := ["script", "pre", "style", "textarea"]

def html6Tags : List String :=
  ["address", "article", "aside", "base", "basefont", "blockquote", "body", "caption",
   "center", "col", "colgroup", "dd", "details", "dialog", "dir", "div", "dl", "dt",
   "fieldset", "figcaption", "figure", "footer", "form", "frame", "frameset", "h1", "h2",
   "h3", "h4", "h5", "h6", "head", "header", "hr", "html", "iframe", "legend", "li", "link",
   "main", "menu", "menuitem", "nav", "noframes", "ol", "optgroup", "option", "p", "param",
   "section", "summary", "table", "tbody", "td", "tfoot", "th", "thead", "title", "tr",
   "track", "ul"]

def parseTagName (chars : List Char) : Option (String × List Char) :=
  match chars with
  | [] => none
  | c :: _ =>
    if !c.isAlpha then none
    else
      let name := chars.takeWhile (fun c => c.isAlphanum || c == '-')
      some (String.ofList name, chars.drop name.length)

-- The type 6 condition only needs to recognize the tag name and what immediately follows
-- it; type 7 (any other tag name) instead requires the whole line to be a single complete
-- tag, so it's validated with the same tag grammar used for inline HTML.
def matchHtmlType67Close (cs : List Char) (canInterrupt : Bool) : Option HtmlEndKind :=
  match parseTagName cs with
  | some (name, after) =>
    let lname := toLowerStr name
    if html6Tags.contains lname then
      let followedOk :=
        after.isEmpty || after.head? == some ' ' || after.head? == some '\t' ||
        after.head? == some '>'
      if followedOk then some .untilBlank else none
    else
      match matchCloseTag cs with
      | some rest => if isBlank (String.ofList rest) then
          (if canInterrupt then none else some .untilBlank)
        else none
      | none => none
  | none => none

def matchHtmlType67Open (cs : List Char) (canInterrupt : Bool) : Option HtmlEndKind :=
  match parseTagName cs with
  | some (name, after) =>
    let lname := toLowerStr name
    if html6Tags.contains lname then
      let ok := after.isEmpty
        || after.head? == some ' ' || after.head? == some '\t' || after.head? == some '>'
        || (after.head? == some '/' && (after.drop 1).head? == some '>')
      if ok then some .untilBlank else none
    else
      match matchOpenTag cs with
      | some rest => if isBlank (String.ofList rest) then
          (if canInterrupt then none else some .untilBlank)
        else none
      | none => none
  | none => none

def matchHtmlBlockStart (line : String) (canInterruptParagraph : Bool) : Option HtmlEndKind :=
  let w := leadingWhitespaceWidth line
  if w ≥ 4 then none
  else
    match (dropIndent line w).toList with
    | '<' :: rest =>
      let lower := toLowerStr (String.ofList rest)
      if lower.toList.take 3 == "!--".toList then some (.untilNeedle "-->")
      else if rest.head? == some '?' then some (.untilNeedle "?>")
      else if lower.toList.take 8 == "![cdata[".toList then some (.untilNeedle "]]>")
      else if rest.head? == some '!' && ((rest.drop 1).head?.map Char.isUpper).getD false then
        some (.untilNeedle ">")
      else
        match rest with
        | '/' :: cs => matchHtmlType67Close cs canInterruptParagraph
        | cs =>
          match parseTagName cs with
          | some (name, after) =>
            let lname := toLowerStr name
            if html1Tags.contains lname &&
               (after.isEmpty || after.head? == some ' ' || after.head? == some '\t' ||
                after.head? == some '>') then
              some (.untilNeedle ("</" ++ lname ++ ">"))
            else matchHtmlType67Open cs canInterruptParagraph
          | none => none
    | _ => none

-- `some rest` when nothing but spaces/tabs remain before the next line ending (or the end
-- of input); `rest` starts at the following line. `none` means something else follows.
def endOfLineAfterWs (chars : List Char) : Option (List Char) :=
  match chars.dropWhile (fun c => c == ' ' || c == '\t') with
  | [] => some []
  | '\n' :: rest => some rest
  | _ => none

-- A link reference definition is only ever recognized as a (possibly multi-line) prefix of
-- what would otherwise be paragraph text, stripped off when that paragraph's accumulated
-- lines are closed; see `State.closeLeaf`. Since paragraph accumulation already stops at any
-- blank line, `chars` can never contain two consecutive newlines, so skipping whitespace
-- freely (including newlines) between components can never accidentally cross a blank line.
def tryParseOneLinkRefDef (chars : List Char) :
    Option ((String × String × Option String) × List Char) :=
  match chars with
  | '[' :: rest =>
    match takeLabelChars rest with
    | none => none
    | some (labelRaw, afterLabel) =>
      if labelRaw.isEmpty || labelRaw.length > 999 || labelRaw.all isUnicodeWhitespace then none
      else
        match afterLabel with
        | ':' :: afterColon =>
          let afterWs1 := afterColon.dropWhile isUnicodeWhitespace
          let isAngle := afterWs1.head? == some '<'
          match parseLinkDest afterWs1 with
          | none => none
          | some (destChars, afterDest) =>
            if destChars.isEmpty && !isAngle then none
            else
              let label := String.ofList labelRaw
              let dest := resolveEscapesAndEntities (String.ofList destChars)
              let afterWs2 := afterDest.dropWhile isUnicodeWhitespace
              let hadWs := afterWs2.length < afterDest.length
              let withTitle : Option ((String × Option String) × List Char) :=
                match if hadWs then parseTitle afterWs2 else none with
                | some (titleChars, afterTitle) =>
                  match endOfLineAfterWs afterTitle with
                  | some rem =>
                    some ((dest, some (resolveEscapesAndEntities (String.ofList titleChars))), rem)
                  | none => none
                | none => none
              match withTitle with
              | some ((d, t), rem) => some ((label, d, t), rem)
              | none =>
                match endOfLineAfterWs afterDest with
                | some rem => some ((label, dest, none), rem)
                | none => none
        | _ => none
  | _ => none

def stripLinkRefDefsF :
    Nat → List Char → List (String × String × Option String) × List Char
  | 0, chars => ([], chars)
  | fuel + 1, chars =>
    match tryParseOneLinkRefDef chars with
    | some (linkDef, rest) =>
      let (more, finalRest) := stripLinkRefDefsF fuel rest
      (linkDef :: more, finalRest)
    | none => ([], chars)

def stripLinkRefDefs (chars : List Char) : List (String × String × Option String) × List Char :=
  stripLinkRefDefsF (chars.length + 1) chars

-- `strictListInterrupt` applies the "ordered lists can only interrupt a paragraph if they
-- start at 1" rule. That rule exists to stop plain text like "2. bar" from accidentally
-- starting a list where none was already open; it does not apply when the paragraph being
-- considered is itself the content of an already-open list item (i.e. deciding whether that
-- list continues with a new sibling item, not whether a list starts fresh).
def startsNewBlock (strictListInterrupt : Bool) (remainder : String) : Bool :=
  isBlank remainder
  || matchThematicBreak remainder
  || (matchAtxHeading remainder).isSome
  || (matchFenceStart remainder).isSome
  || (matchHtmlBlockStart remainder true).isSome
  || (matchBlockQuoteStart remainder).isSome
  || (match matchListMarker remainder with
      | some (kind, _, afterMarker) =>
        !strictListInterrupt || (!isBlank afterMarker && listMarkerCanInterrupt kind afterMarker)
      | none => false)

inductive RawBlock where
  | paragraph  (text : String)
  | heading    (level : Nat) (text : String)
  | codeBlock  (info : Option String) (literal : String)
  | blockQuote (content : List RawBlock)
  | thematicBreak
  | htmlBlock  (text : String)
  | listItem   (kind : ListType) (loose : Bool) (content : List RawBlock)

inductive Container where
  | blockQuote
  | item (kind : ListType) (indent : Nat)

inductive OpenLeaf where
  | empty
  | paragraph (lines : Array String)
  | indentedCode (lines : Array String)
  | fenced (fenceChar : Char) (fenceLen : Nat) (indent : Nat) (info : Option String) (lines : Array String)
  | html (endKind : HtmlEndKind) (lines : Array String)

structure Frame where
  container    : Container
  siblings     : Array RawBlock
  pendingBlank : Bool
  loose        : Bool

structure State where
  rootSiblings : Array RawBlock
  frames       : Array Frame
  leaf         : OpenLeaf
  linkDefs     : Array (String × String × Option String)

def initialState : State := { rootSiblings := #[], frames := #[], leaf := .empty, linkDefs := #[] }

def State.pushBlock (st : State) (b : RawBlock) : State :=
  match st.frames.back? with
  | some f =>
    let f' := { f with
      siblings := f.siblings.push b,
      loose := f.loose || (f.pendingBlank && !f.siblings.isEmpty),
      pendingBlank := false }
    { st with frames := st.frames.pop.push f' }
  | none => { st with rootSiblings := st.rootSiblings.push b }

def State.markPendingBlank (st : State) : State :=
  match st.frames.back? with
  | some f => { st with frames := st.frames.pop.push { f with pendingBlank := true } }
  | none => st

def State.setLeafEmpty (st : State) : State := { st with leaf := .empty }

def State.appendParagraphLine (st : State) (line : String) : State :=
  match st.leaf with
  | .paragraph lines => { st with leaf := .paragraph (lines.push line) }
  | _ => st

def finalizeLeaf : OpenLeaf → Option RawBlock
  | .empty => none
  | .paragraph lines => some (.paragraph (String.intercalate "\n" lines.toList))
  | .indentedCode lines =>
    let trimmed := stripTrailingBlankLines lines.toList
    if trimmed.isEmpty then some (.codeBlock none "")
    else some (.codeBlock none (String.intercalate "\n" trimmed ++ "\n"))
  | .fenced _ _ _ info lines =>
    if lines.toList.isEmpty then some (.codeBlock info "")
    else some (.codeBlock info (String.intercalate "\n" lines.toList ++ "\n"))
  | .html _ lines =>
    some (.htmlBlock (String.intercalate "\n" lines.toList ++ "\n"))

-- Link reference definitions are only recognized as a (possibly multi-line) prefix of what
-- would otherwise be a paragraph, so they're stripped off here rather than in `finalizeLeaf`.
def State.closeLeaf (st : State) : State :=
  match st.leaf with
  | .paragraph lines =>
    let (defs, remChars) := stripLinkRefDefs (String.intercalate "\n" lines.toList).toList
    let st1 := { st with linkDefs := defs.foldl (fun acc d => acc.push d) st.linkDefs }
    (if remChars.isEmpty then st1 else st1.pushBlock (.paragraph (String.ofList remChars))).setLeafEmpty
  | leaf =>
    match finalizeLeaf leaf with
    | some b => (st.pushBlock b).setLeafEmpty
    | none => st.setLeafEmpty

def frameToRawBlock (f : Frame) : RawBlock :=
  match f.container with
  | .blockQuote => .blockQuote f.siblings.toList
  | .item kind _ => .listItem kind f.loose f.siblings.toList

def State.closeFramesTo (st : State) (target : Nat) : State × Option (ListType × Bool) :=
  Id.run do
    let mut s := st
    let mut firstResult : Option (ListType × Bool) := none
    for _ in [0 : st.frames.size - target] do
      match s.frames.back? with
      | none => pure ()
      | some f =>
        let rest := s.frames.pop
        -- A blank line only counts as a separator (towards the next sibling, or towards
        -- whatever follows in the enclosing container) if it followed actual content; an
        -- item whose very first line is blank (a bare marker like "-") isn't itself one.
        let trailingBlank := f.pendingBlank && !f.siblings.isEmpty
        if firstResult.isNone then
          match f.container with
          | .item kind _ => firstResult := some (kind, trailingBlank)
          | .blockQuote => pure ()
        -- If the parent frame is itself about to close in this same call (i.e. it's not
        -- staying open at `target`), it's not going to receive any further content that a
        -- trailing blank here could separate, so the flag isn't propagated to it.
        let rest' :=
          if trailingBlank && rest.size == target then
            match rest.back? with
            | some pf => rest.pop.push { pf with pendingBlank := true }
            | none => rest
          else rest
        s := { s with frames := rest' }
        s := s.pushBlock (frameToRawBlock f)
    return (s, firstResult)

def matchContainers (frames : Array Frame) (line : String) : Nat × String :=
  Id.run do
    let mut i := 0
    let mut rem := line
    for f in frames do
      match f.container with
      | .blockQuote =>
        match matchBlockQuoteStart rem with
        | some r => rem := r; i := i + 1
        | none => break
      | .item _ indent =>
        if isBlank rem then
          rem := ""
          i := i + 1
        else if leadingWhitespaceWidth rem ≥ indent then
          rem := dropIndent rem indent
          i := i + 1
        else break
    return (i, rem)

def tryOpenContainers (fuel : Nat) (remainder : String) : Array Container × String :=
  Id.run do
    let mut conts : Array Container := #[]
    let mut rem := remainder
    for _ in [0 : fuel] do
      if matchThematicBreak rem then
        break
      else
        match matchBlockQuoteStart rem with
        | some r => conts := conts.push .blockQuote; rem := r
        | none =>
          match matchListMarker rem with
          | some (kind, ci, r) => conts := conts.push (.item kind ci); rem := r
          | none => break
    return (conts, rem)

def startHtmlLeaf (st : State) (endKind : HtmlEndKind) (firstLine : String) : State :=
  match endKind with
  | .untilBlank =>
    if isBlank firstLine then st.markPendingBlank
    else { st with leaf := .html .untilBlank #[firstLine] }
  | .untilNeedle needle =>
    if containsSubstr firstLine needle then st.pushBlock (.htmlBlock firstLine)
    else { st with leaf := .html (.untilNeedle needle) #[firstLine] }

def startBlockFrom (st : State) (remainder : String) (carry : Option (ListType × Bool)) : State :=
  let (newConts, remainder2) := tryOpenContainers (remainder.length + 1) remainder
  let st1 := Id.run do
    let mut s := st
    let mut firstPush := true
    for c in newConts do
      let loose0 :=
        if firstPush then
          match c, carry with
          | .item kind _, some (ckind, true) => sameListKind kind ckind
          | _, _ => false
        else false
      s := { s with frames := s.frames.push { container := c, siblings := #[], pendingBlank := false, loose := loose0 } }
      firstPush := false
    return s
  if isBlank remainder2 then
    st1.markPendingBlank
  else if matchThematicBreak remainder2 then
    st1.pushBlock .thematicBreak
  else
    match matchAtxHeading remainder2 with
    | some (level, text) => st1.pushBlock (.heading level text)
    | none =>
      match matchFenceStart remainder2 with
      | some (ch, len, ind, info) => { st1 with leaf := .fenced ch len ind info #[] }
      | none =>
        match matchHtmlBlockStart remainder2 false with
        | some endKind => startHtmlLeaf st1 endKind remainder2
        | none =>
          if leadingWhitespaceWidth remainder2 ≥ 4 then
            { st1 with leaf := .indentedCode #[dropIndent remainder2 4] }
          else
            { st1 with leaf := .paragraph #[stripUpTo3 remainder2] }

def processLine (st : State) (line : String) : State :=
  let (m, remainder) := matchContainers st.frames line
  let n := st.frames.size
  if m == n then
    match st.leaf with
    | .indentedCode lines =>
      if leadingWhitespaceWidth remainder ≥ 4 then
        { st with leaf := .indentedCode (lines.push (dropIndent remainder 4)) }
      else if isBlank remainder then
        { st with leaf := .indentedCode (lines.push "") }
      else
        startBlockFrom st.closeLeaf remainder none
    | .fenced ch len ind info lines =>
      if matchFenceEnd ch len remainder then st.closeLeaf
      else
        { st with leaf := .fenced ch len ind info (lines.push (dropIndent remainder (min ind (leadingWhitespaceWidth remainder)))) }
    | .html .untilBlank lines =>
      if isBlank remainder then (st.closeLeaf).markPendingBlank
      else { st with leaf := .html .untilBlank (lines.push remainder) }
    | .html (.untilNeedle needle) lines =>
      let lines' := lines.push remainder
      if containsSubstr remainder needle then
        { st with leaf := .html (.untilNeedle needle) lines' }.closeLeaf
      else { st with leaf := .html (.untilNeedle needle) lines' }
    | .paragraph lines =>
      if isBlank remainder then
        (st.closeLeaf).markPendingBlank
      else
        match matchSetextUnderline remainder with
        | some level =>
          -- Any link reference definitions at the front of the buffered paragraph text
          -- are stripped first; if nothing but definitions remain, there's no paragraph
          -- left to convert, so the underline line is instead processed as a fresh line.
          let (defs, remChars) := stripLinkRefDefs (String.intercalate "\n" lines.toList).toList
          let st1 := { st with linkDefs := defs.foldl (fun acc d => acc.push d) st.linkDefs }
          if remChars.isEmpty then
            startBlockFrom { st1 with leaf := .empty } remainder none
          else
            ({ st1 with leaf := .empty }).pushBlock (.heading level (String.ofList remChars))
        | none =>
          if startsNewBlock true remainder then
            startBlockFrom st.closeLeaf remainder none
          else
            st.appendParagraphLine (stripLeadingWs remainder)
    | .empty =>
      -- A list item can begin with at most one blank line: a second consecutive blank line
      -- while the innermost item still has no content ends that item as empty right away,
      -- rather than letting a later indented line join it.
      match st.frames.back? with
      | some f =>
        let isItem := match f.container with | .item _ _ => true | .blockQuote => false
        if isBlank remainder && isItem && f.siblings.isEmpty && f.pendingBlank then
          let st1 := { st with frames := st.frames.pop.push { f with loose := true } }
          let (st2, _) := st1.closeFramesTo (st1.frames.size - 1)
          st2.markPendingBlank
        else
          startBlockFrom st remainder none
      | none => startBlockFrom st remainder none
  else
    match st.leaf with
    | .paragraph _ =>
      if isBlank remainder || startsNewBlock false remainder then
        let st1 := st.closeLeaf
        let (st2, carry) := st1.closeFramesTo m
        if isBlank remainder then st2.markPendingBlank
        else startBlockFrom st2 remainder carry
      else
        st.appendParagraphLine (stripLeadingWs remainder)
    | _ =>
      let st1 := st.closeLeaf
      let (st2, carry) := st1.closeFramesTo m
      if isBlank remainder then st2.markPendingBlank
      else startBlockFrom st2 remainder carry

def runLines (lines : List String) : State :=
  lines.foldl processLine initialState

def finalizeState (st : State) : List RawBlock × LinkDefs :=
  let st1 := st.closeLeaf
  let (st2, _) := st1.closeFramesTo 0
  (st2.rootSiblings.toList, st2.linkDefs)

-- Tail-recursive (accumulate reversed, reverse once at the end) rather than the more
-- obvious `c :: normalizeGo rest`: that form isn't a tail call, so it holds one stack
-- frame per input character, which risks overflowing the stack on a large document.
def normalizeGo (acc : List Char) : List Char → List Char
  | [] => acc.reverse
  | '\r' :: '\n' :: rest => normalizeGo ('\n' :: acc) rest
  | '\r' :: rest => normalizeGo ('\n' :: acc) rest
  | c :: rest => normalizeGo (c :: acc) rest

def normalizeNewlines (s : String) : String :=
  String.ofList (normalizeGo [] s.toList)

def splitLines (s : String) : List String :=
  let parts := (normalizeNewlines s).splitOn "\n"
  match parts.reverse with
  | "" :: (rest@(_ :: _)) => rest.reverse
  | _ => parts

def headingLevelToFin (level : Nat) : Fin 6 :=
  ⟨(level - 1) % 6, Nat.mod_lt _ (by decide)⟩

def takeSameKindItems (kind : ListType) :
    List RawBlock → List (ListType × Bool × List RawBlock) × List RawBlock
  | .listItem k l c :: rest =>
    if sameListKind kind k then
      let (more, rest') := takeSameKindItems kind rest
      ((k, l, c) :: more, rest')
    else ([], .listItem k l c :: rest)
  | rest => ([], rest)

mutual
def rawBlockCount : RawBlock → Nat
  | .blockQuote content => 1 + rawBlockListCount content
  | .listItem _ _ content => 1 + rawBlockListCount content
  | _ => 1

def rawBlockListCount : List RawBlock → Nat
  | [] => 0
  | b :: rest => 1 + rawBlockCount b + rawBlockListCount rest
end

-- Mutual structural recursion between rawBlockToBlock/groupAndConvert can't be verified
-- automatically because takeSameKindItems hides the sub-list relationship from the
-- termination checker, so recursion is instead driven by an explicit fuel value (bounded
-- by the total node count, which is always enough since no subtree exceeds the whole tree).
mutual
def rawBlockToBlockF (defs : LinkDefs) : Nat → RawBlock → CommonMark.Block
  | 0, _ => .paragraph []
  | _ + 1, .paragraph text => .paragraph (parseInline defs text)
  | _ + 1, .heading level text => .heading (headingLevelToFin level) (parseInline defs text)
  | _ + 1, .codeBlock info lit => .codeBlock info lit
  | _ + 1, .thematicBreak => .thematicBreak
  | _ + 1, .htmlBlock s => .htmlBlock s
  | fuel + 1, .blockQuote content => .blockQuote (groupAndConvertF defs fuel content)
  | fuel + 1, .listItem kind _ content => .list kind false [groupAndConvertF defs fuel content]

def groupAndConvertF (defs : LinkDefs) : Nat → List RawBlock → List CommonMark.Block
  | 0, _ => []
  | _ + 1, [] => []
  | fuel + 1, .listItem kind loose content :: rest =>
    let (siblings, rest') := takeSameKindItems kind rest
    let allItems := (kind, loose, content) :: siblings
    let looseOverall := allItems.any (fun (_, l, _) => l)
    let items := allItems.map (fun (_, _, c) => groupAndConvertF defs fuel c)
    .list kind (!looseOverall) items :: groupAndConvertF defs fuel rest'
  | fuel + 1, b :: rest => rawBlockToBlockF defs fuel b :: groupAndConvertF defs fuel rest
end

def groupAndConvert (defs : LinkDefs) (blocks : List RawBlock) : List CommonMark.Block :=
  groupAndConvertF defs (rawBlockListCount blocks + 1) blocks

end CommonMark.Parser

namespace CommonMark

/-- Parses a CommonMark document into an AST. Total: every input string, including
    malformed or adversarial input, produces a `Document` rather than panicking or
    looping. Matches the official example suite exactly (see
    `test/Conformance.lean`'s `commonmark_conformance` theorem). -/
def parseDocument (s : String) : Document :=
  let (blocks, defs) := Parser.finalizeState (Parser.runLines (Parser.splitLines s))
  Parser.groupAndConvert defs blocks

end CommonMark
