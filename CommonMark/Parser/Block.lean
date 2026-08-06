-- Copyright (c) 2026 Paul Butcher. All rights reserved.
import CommonMark.Ast
import CommonMark.Parser.Inline

namespace CommonMark.Parser

def columnWidth (chars : List Char) : Nat :=
  chars.foldl (fun col c => if c == '\t' then col + (4 - col % 4) else col + 1) 0

def leadingWhitespaceChars (s : String) : List Char :=
  s.toList.takeWhile (fun c => c == ' ' || c == '\t')

def leadingWhitespaceWidth (s : String) : Nat :=
  columnWidth (leadingWhitespaceChars s)

def isBlank (s : String) : Bool :=
  s.toList.all (fun c => c == ' ' || c == '\t')

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
        List.replicate (consumed - remaining) ' ' ++ rest
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
            let info := infoRaw.trimAscii.toString
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
      some (String.ofList (List.replicate extra ' ' ++ rest))
    | '>' :: ' ' :: rest => some (String.ofList rest)
    | '>' :: rest => some (String.ofList rest)
    | _ => none

def spacesAndIndent (markerWidth : Nat) (afterMarker : List Char) : Nat × String :=
  let afterStr := String.ofList afterMarker
  if isBlank afterStr then (markerWidth + 1, "")
  else
    let w := leadingWhitespaceWidth afterStr
    if w ≥ 5 then (markerWidth + 1, dropIndent afterStr 1)
    else (markerWidth + w, dropIndent afterStr w)

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

def matchHtmlType67Close (cs : List Char) (canInterrupt : Bool) : Option HtmlEndKind :=
  match parseTagName cs with
  | some (name, after) =>
    let lname := toLowerStr name
    let followedOk :=
      after.isEmpty || after.head? == some ' ' || after.head? == some '\t' ||
      after.head? == some '>'
    if html6Tags.contains lname then
      if followedOk then some .untilBlank else none
    else if followedOk then
      if canInterrupt then none else some .untilBlank
    else none
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
      let ok := after.isEmpty || after == ['>'] || after == ['/', '>']
      if ok then (if canInterrupt then none else some .untilBlank) else none
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

def matchLinkRefDef (line : String) : Option (String × String × Option String) :=
  let w := leadingWhitespaceWidth line
  if w ≥ 4 then none
  else
    match (dropIndent line w).toList with
    | '[' :: cs =>
      let label := cs.takeWhile (· ≠ ']')
      let afterLabel := cs.drop label.length
      match afterLabel with
      | ']' :: ':' :: cs2 =>
        let cs3 := cs2.dropWhile (fun c => c == ' ' || c == '\t')
        let (destChars, cs3b) :=
          match cs3 with
          | '<' :: csA =>
            let d := csA.takeWhile (· ≠ '>')
            (d, csA.drop (d.length + 1))
          | _ =>
            let d := cs3.takeWhile (fun c => c ≠ ' ' && c ≠ '\t')
            (d, cs3.drop d.length)
        if destChars.isEmpty || label.isEmpty then none
        else
          let afterDest := cs3b.dropWhile (fun c => c == ' ' || c == '\t')
          match afterDest with
          | [] => some (String.ofList label, String.ofList destChars, none)
          | '"' :: cs4 =>
            let title := cs4.takeWhile (· ≠ '"')
            let afterTitle := cs4.drop title.length
            match afterTitle with
            | '"' :: rest5 =>
              if rest5.all (fun c => c == ' ' || c == '\t') then
                some (String.ofList label, String.ofList destChars, some (String.ofList title))
              else none
            | _ => none
          | _ => none
      | _ => none
    | _ => none

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
        !isBlank afterMarker && (!strictListInterrupt || listMarkerCanInterrupt kind afterMarker)
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

def State.closeLeaf (st : State) : State :=
  match finalizeLeaf st.leaf with
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
        if firstResult.isNone then
          match f.container with
          | .item kind _ => firstResult := some (kind, f.pendingBlank)
          | .blockQuote => pure ()
        s := { s with frames := rest }
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
            match matchLinkRefDef remainder2 with
            | some (label, dest, title) => { st1 with linkDefs := st1.linkDefs.push (label, dest, title) }
            | none => { st1 with leaf := .paragraph #[stripUpTo3 remainder2] }

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
          let text := String.intercalate "\n" lines.toList
          ({ st with leaf := .empty }).pushBlock (.heading level text)
        | none =>
          if startsNewBlock true remainder then
            startBlockFrom st.closeLeaf remainder none
          else
            st.appendParagraphLine (stripLeadingWs remainder)
    | .empty => startBlockFrom st remainder none
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

def normalizeGo : List Char → List Char
  | [] => []
  | '\r' :: '\n' :: rest => '\n' :: normalizeGo rest
  | '\r' :: rest => '\n' :: normalizeGo rest
  | c :: rest => c :: normalizeGo rest

def normalizeNewlines (s : String) : String :=
  String.ofList (normalizeGo s.toList)

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

def parseDocument (s : String) : Document :=
  let (blocks, defs) := Parser.finalizeState (Parser.runLines (Parser.splitLines s))
  Parser.groupAndConvert defs blocks

end CommonMark
