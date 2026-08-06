-- Copyright (c) 2026 Paul Butcher. All rights reserved.
import CommonMark.Ast
import CommonMark.Parser.Entities

namespace CommonMark.Parser

abbrev LinkDefs := Array (String × String × Option String)

def toLowerStr (s : String) : String :=
  String.ofList (s.toList.map Char.toLower)

def collapseWhitespace (s : String) : String :=
  String.intercalate " " ((s.splitOn " ").filter (· ≠ "") )

def normalizeLabel (s : String) : String :=
  let collapsed := collapseWhitespace (String.ofList (s.toList.map (fun c => if c == '\t' || c == '\n' then ' ' else c)))
  toLowerStr (collapsed.trimAscii.toString)

def lookupLinkDef (defs : LinkDefs) (label : String) : Option (String × Option String) :=
  let target := normalizeLabel label
  (defs.toList.find? (fun (l, _, _) => normalizeLabel l == target)).map (fun (_, d, t) => (d, t))

def isEscapable (c : Char) : Bool :=
  "!\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~".toList.contains c

def isAsciiPunct (c : Char) : Bool :=
  "!\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~".toList.contains c

def isUnicodeWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == Char.ofNat 12

def isWsOrNone (oc : Option Char) : Bool :=
  match oc with
  | none => true
  | some c => isUnicodeWhitespace c

def isPunctChar (oc : Option Char) : Bool :=
  match oc with
  | none => false
  | some c => isAsciiPunct c

def skipLeadingSpacesTabs : List Char → List Char
  | c :: rest => if c == ' ' || c == '\t' then skipLeadingSpacesTabs rest else c :: rest
  | [] => []

def takePlainRun (chars : List Char) : String × List Char :=
  let isTrigger (c : Char) : Bool :=
    c == '\\' || c == '`' || c == '&' || c == '<' || c == '[' || c == ']' ||
    c == '!' || c == '*' || c == '_' || c == '\n'
  let plain := chars.takeWhile (fun c => !isTrigger c)
  (String.ofList plain, chars.drop plain.length)

def findCodeSpanEndF (n : Nat) : Nat → List Char → Option (List Char × List Char)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, c :: rest =>
    if c == '`' then
      let run := (c :: rest).takeWhile (· == '`')
      if run.length == n then some ([], (c :: rest).drop n)
      else
        match findCodeSpanEndF n fuel ((c :: rest).drop run.length) with
        | some (before, after) => some (run ++ before, after)
        | none => none
    else
      match findCodeSpanEndF n fuel rest with
      | some (before, after) => some (c :: before, after)
      | none => none

def findCodeSpanEnd (n : Nat) (chars : List Char) : Option (List Char × List Char) :=
  findCodeSpanEndF n (chars.length + 1) chars

def normalizeCodeSpanContent (raw : List Char) : String :=
  let collapsed := raw.map (fun c => if c == '\n' then ' ' else c)
  let allSpaces := collapsed.all (· == ' ')
  if !allSpaces && collapsed.head? == some ' ' && collapsed.getLast? == some ' ' then
    String.ofList (collapsed.drop 1).dropLast
  else
    String.ofList collapsed

def replacementChar : Char := Char.ofNat 0xFFFD

def codepointToStr (cp : Nat) : String :=
  if cp == 0 || cp > 0x10FFFF then replacementChar.toString
  else (Char.ofNat cp).toString

def isHexDigit (c : Char) : Bool :=
  c.isDigit || ('a' ≤ c.toLower && c.toLower ≤ 'f')

def hexVal (c : Char) : Nat :=
  if c.isDigit then c.toNat - '0'.toNat else (c.toLower.toNat - 'a'.toNat) + 10

-- chars is positioned right after "&#"
def parseNumericRef (chars : List Char) : Option (String × List Char) :=
  match chars with
  | c :: rest =>
    if c == 'x' || c == 'X' then
      let digits := rest.takeWhile isHexDigit
      if digits.isEmpty || digits.length > 6 then none
      else
        match rest.drop digits.length with
        | ';' :: after => some (codepointToStr (digits.foldl (fun acc d => acc * 16 + hexVal d) 0), after)
        | _ => none
    else
      let digits := chars.takeWhile Char.isDigit
      if digits.isEmpty || digits.length > 7 then none
      else
        match chars.drop digits.length with
        | ';' :: after =>
          some (codepointToStr (digits.foldl (fun acc d => acc * 10 + (d.toNat - '0'.toNat)) 0), after)
        | _ => none
  | [] => none

-- chars is positioned right after "&"
def parseNamedRef (chars : List Char) : Option (String × List Char) :=
  let name := chars.takeWhile (fun c => c.isAlphanum)
  if name.isEmpty then none
  else
    match chars.drop name.length with
    | ';' :: after =>
      (lookupEntity (String.ofList name)).map (fun s => (s, after))
    | _ => none

def parseEntityRef (chars : List Char) : Option (String × List Char) :=
  match chars with
  | '#' :: rest => parseNumericRef rest
  | _ => parseNamedRef chars

def isAsciiLetter (c : Char) : Bool :=
  'a' ≤ c.toLower && c.toLower ≤ 'z'

def isSchemeChar (c : Char) : Bool :=
  c.isAlphanum || c == '+' || c == '.' || c == '-'

-- chars is positioned right after '<'
def matchUriAutolink (chars : List Char) : Option (String × List Char) :=
  match chars with
  | c :: rest =>
    if !isAsciiLetter c then none
    else
      let schemeRest := rest.takeWhile isSchemeChar
      let scheme := c :: schemeRest
      if scheme.length < 2 || scheme.length > 32 then none
      else
        match rest.drop schemeRest.length with
        | ':' :: afterColon =>
          let content := afterColon.takeWhile
            (fun ch => ch ≠ '<' && ch ≠ '>' && !isUnicodeWhitespace ch && ch.toNat ≥ 32 && ch.toNat ≠ 127)
          match afterColon.drop content.length with
          | '>' :: after => some (String.ofList (scheme ++ ':' :: content), after)
          | _ => none
        | _ => none
  | [] => none

def isEmailLocalChar (c : Char) : Bool :=
  c.isAlphanum || "!#$%&'*+/=?^_`{|}~.-".toList.contains c

def isEmailLabelChar (c : Char) : Bool :=
  c.isAlphanum || c == '-'

def takeEmailLabel (chars : List Char) : List Char :=
  chars.takeWhile isEmailLabelChar

def validEmailLabel (l : List Char) : Bool :=
  !l.isEmpty && l.head? ≠ some '-' && l.getLast? ≠ some '-'

def parseEmailDomainF : Nat → List Char → Option (List Char × List Char)
  | 0, _ => none
  | fuel + 1, chars =>
    let l := takeEmailLabel chars
    if !validEmailLabel l then none
    else
      let restAfterLabel := chars.drop l.length
      match restAfterLabel with
      | '.' :: rest2 =>
        match parseEmailDomainF fuel rest2 with
        | some (moreDomain, after) => some (l ++ '.' :: moreDomain, after)
        | none => some (l, restAfterLabel)
      | _ => some (l, restAfterLabel)

def parseEmailDomain (chars : List Char) : Option (List Char × List Char) :=
  parseEmailDomainF (chars.length + 1) chars

-- chars is positioned right after '<'
def matchEmailAutolink (chars : List Char) : Option (String × List Char) :=
  let localPart := chars.takeWhile isEmailLocalChar
  if localPart.isEmpty then none
  else
    match chars.drop localPart.length with
    | '@' :: afterAt =>
      match parseEmailDomain afterAt with
      | some (domain, after) =>
        match after with
        | '>' :: rest => some (String.ofList (localPart ++ '@' :: domain), rest)
        | _ => none
      | none => none
    | _ => none

-- chars is positioned right after '<'; result is (content, isEmail, restAfterClosingAngle)
def matchAutolink (chars : List Char) : Option (String × Bool × List Char) :=
  match matchUriAutolink chars with
  | some (content, rest) => some (content, false, rest)
  | none =>
    match matchEmailAutolink chars with
    | some (content, rest) => some (content, true, rest)
    | none => none

def isPrefixOfChars : List Char → List Char → Bool
  | [], _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a == b && isPrefixOfChars as bs

def findNeedleF (needle : List Char) : Nat → List Char → Option (List Char × List Char)
  | 0, _ => none
  | fuel + 1, chars =>
    if isPrefixOfChars needle chars then some ([], chars.drop needle.length)
    else
      match chars with
      | c :: rest =>
        match findNeedleF needle fuel rest with
        | some (before, after) => some (c :: before, after)
        | none => none
      | [] => none

def findNeedle (needle : List Char) (chars : List Char) : Option (List Char × List Char) :=
  findNeedleF needle (chars.length + 1) chars

def isTagNameStart (c : Char) : Bool := c.isAlpha
def isTagNameChar (c : Char) : Bool := c.isAlphanum || c == '-'
def isAttrNameStart (c : Char) : Bool := c.isAlpha || c == '_' || c == ':'
def isAttrNameChar (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '.' || c == ':' || c == '-'

def isUnquotedAttrValueChar (c : Char) : Bool :=
  !isUnicodeWhitespace c && c ≠ '"' && c ≠ '\'' && c ≠ '=' && c ≠ '<' && c ≠ '>' && c ≠ '`'

-- Consumes one leading-whitespace-prefixed `name` or `name=value` attribute; `none` means
-- no attribute could be consumed here (not that the tag itself is invalid).
def parseAttr (chars : List Char) : Option (List Char) :=
  let afterWs := chars.dropWhile isUnicodeWhitespace
  if afterWs.length == chars.length then none
  else
    match afterWs with
    | c :: cs =>
      if !isAttrNameStart c then none
      else
        let nameRest := cs.takeWhile isAttrNameChar
        let afterName := cs.drop nameRest.length
        let afterNameWs := afterName.dropWhile isUnicodeWhitespace
        match afterNameWs with
        | '=' :: afterEq =>
          let afterEqWs := afterEq.dropWhile isUnicodeWhitespace
          match afterEqWs with
          | '"' :: v =>
            let val := v.takeWhile (· ≠ '"')
            match v.drop val.length with
            | '"' :: after => some after
            | _ => none
          | '\'' :: v =>
            let val := v.takeWhile (· ≠ '\'')
            match v.drop val.length with
            | '\'' :: after => some after
            | _ => none
          | _ =>
            let val := afterEqWs.takeWhile isUnquotedAttrValueChar
            if val.isEmpty then none else some (afterEqWs.drop val.length)
        | _ => some afterName
    | [] => none

def parseAttrsF : Nat → List Char → List Char
  | 0, chars => chars
  | fuel + 1, chars =>
    match parseAttr chars with
    | some rest => parseAttrsF fuel rest
    | none => chars

def parseAttrs (chars : List Char) : List Char :=
  parseAttrsF (chars.length + 1) chars

-- chars is positioned right after '<'
def matchOpenTag (chars : List Char) : Option (List Char) :=
  match chars with
  | c :: cs =>
    if !isTagNameStart c then none
    else
      let nameRest := cs.takeWhile isTagNameChar
      let afterName := cs.drop nameRest.length
      let afterAttrs := parseAttrs afterName
      let afterWs := afterAttrs.dropWhile isUnicodeWhitespace
      match afterWs with
      | '/' :: '>' :: after => some after
      | '>' :: after => some after
      | _ => none
  | [] => none

-- chars is positioned right after '</'
def matchCloseTag (chars : List Char) : Option (List Char) :=
  match chars with
  | c :: cs =>
    if !isTagNameStart c then none
    else
      let nameRest := cs.takeWhile isTagNameChar
      let afterName := cs.drop nameRest.length
      let afterWs := afterName.dropWhile isUnicodeWhitespace
      match afterWs with
      | '>' :: after => some after
      | _ => none
  | [] => none

-- chars is positioned right after '<'; result is (full raw text incl. delimiters, rest)
def matchInlineHtml (chars : List Char) : Option (String × List Char) :=
  let lower := toLowerStr (String.ofList chars)
  if lower.toList.take 3 == "!--".toList then
    match findNeedle "-->".toList chars with
    | some (content, after) => some ("<" ++ String.ofList content ++ "-->", after)
    | none => none
  else if chars.head? == some '?' then
    match findNeedle "?>".toList chars with
    | some (content, after) => some ("<" ++ String.ofList content ++ "?>", after)
    | none => none
  else if lower.toList.take 8 == "![cdata[".toList then
    match findNeedle "]]>".toList chars with
    | some (content, after) => some ("<" ++ String.ofList content ++ "]]>", after)
    | none => none
  else if chars.head? == some '!' && ((chars.drop 1).head?.map Char.isUpper).getD false then
    match findNeedle ">".toList chars with
    | some (content, after) => some ("<" ++ String.ofList content ++ ">", after)
    | none => none
  else
    match chars with
    | '/' :: cs =>
      match matchCloseTag cs with
      | some after => some ("</" ++ String.ofList (cs.take (cs.length - after.length)), after)
      | none => none
    | cs =>
      match matchOpenTag cs with
      | some after => some ("<" ++ String.ofList (cs.take (cs.length - after.length)), after)
      | none => none

def leftFlanking (before after : Option Char) : Bool :=
  !isWsOrNone after && (!isPunctChar after || isWsOrNone before || isPunctChar before)

def rightFlanking (before after : Option Char) : Bool :=
  !isWsOrNone before && (!isPunctChar before || isWsOrNone after || isPunctChar after)

def canOpenDelim (c : Char) (before after : Option Char) : Bool :=
  let lf := leftFlanking before after
  if c == '_' then lf && (!rightFlanking before after || isPunctChar before) else lf

def canCloseDelim (c : Char) (before after : Option Char) : Bool :=
  let rf := rightFlanking before after
  if c == '_' then rf && (!leftFlanking before after || isPunctChar after) else rf

def multipleOf3Ok (openLen closeLen : Nat) (openCanClose closeCanOpen : Bool) : Bool :=
  if openCanClose || closeCanOpen then
    !((openLen + closeLen) % 3 == 0 && !(openLen % 3 == 0 && closeLen % 3 == 0))
  else true

def findMatchingBracketF : Nat → Nat → List Char → Option (List Char × List Char)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | fuel + 1, depth, '\\' :: c :: rest =>
    match findMatchingBracketF fuel depth rest with
    | some (before, after) => some ('\\' :: c :: before, after)
    | none => none
  | _ + 1, _, '\\' :: [] => none
  | fuel + 1, depth, '[' :: rest =>
    match findMatchingBracketF fuel (depth + 1) rest with
    | some (before, after) => some ('[' :: before, after)
    | none => none
  | fuel + 1, depth, ']' :: rest =>
    if depth == 0 then some ([], rest)
    else
      match findMatchingBracketF fuel (depth - 1) rest with
      | some (before, after) => some (']' :: before, after)
      | none => none
  | fuel + 1, depth, c :: rest =>
    match findMatchingBracketF fuel depth rest with
    | some (before, after) => some (c :: before, after)
    | none => none

def findMatchingBracket (chars : List Char) : Option (List Char × List Char) :=
  findMatchingBracketF (chars.length + 1) 0 chars

def parseAngleDestF : Nat → List Char → Option (List Char × List Char)
  | 0, _ => none
  | fuel + 1, '\\' :: c :: rest =>
    match parseAngleDestF fuel rest with
    | some (before, after) => some ('\\' :: c :: before, after)
    | none => none
  | _ + 1, '\\' :: [] => none
  | _ + 1, '>' :: rest => some ([], rest)
  | _ + 1, '<' :: _ => none
  | _ + 1, '\n' :: _ => none
  | fuel + 1, c :: rest =>
    match parseAngleDestF fuel rest with
    | some (before, after) => some (c :: before, after)
    | none => none
  | _ + 1, [] => none

def parseAngleDest (chars : List Char) : Option (List Char × List Char) :=
  parseAngleDestF (chars.length + 1) chars

def parseBareDestF : Nat → Nat → List Char → List Char × List Char
  | 0, _, chars => ([], chars)
  | fuel + 1, depth, '\\' :: c :: rest =>
    let (before, after) := parseBareDestF fuel depth rest
    ('\\' :: c :: before, after)
  | _ + 1, _, '\\' :: [] => ([], [])
  | fuel + 1, depth, '(' :: rest =>
    let (before, after) := parseBareDestF fuel (depth + 1) rest
    ('(' :: before, after)
  | fuel + 1, depth, ')' :: rest =>
    if depth == 0 then ([], ')' :: rest)
    else
      let (before, after) := parseBareDestF fuel (depth - 1) rest
      (')' :: before, after)
  | fuel + 1, depth, c :: rest =>
    if isUnicodeWhitespace c || c.toNat < 32 then ([], c :: rest)
    else
      let (before, after) := parseBareDestF fuel depth rest
      (c :: before, after)
  | _ + 1, _, [] => ([], [])

def parseBareDest (chars : List Char) : List Char × List Char :=
  parseBareDestF (chars.length + 1) 0 chars

def parseLinkDest (chars : List Char) : Option (List Char × List Char) :=
  match chars with
  | '<' :: rest => parseAngleDest rest
  | _ => some (parseBareDest chars)

def parseQuotedTitleF (closeChar : Char) : Nat → List Char → Option (List Char × List Char)
  | 0, _ => none
  | fuel + 1, '\\' :: c :: rest =>
    match parseQuotedTitleF closeChar fuel rest with
    | some (before, after) => some ('\\' :: c :: before, after)
    | none => none
  | _ + 1, '\\' :: [] => none
  | fuel + 1, c :: rest =>
    if c == closeChar then some ([], rest)
    else
      match parseQuotedTitleF closeChar fuel rest with
      | some (before, after) => some (c :: before, after)
      | none => none
  | _ + 1, [] => none

def parseTitle (chars : List Char) : Option (List Char × List Char) :=
  match chars with
  | '"' :: rest => parseQuotedTitleF '"' (rest.length + 1) rest
  | '\'' :: rest => parseQuotedTitleF '\'' (rest.length + 1) rest
  | '(' :: rest => parseQuotedTitleF ')' (rest.length + 1) rest
  | _ => none

def parseInlineLinkTail (chars : List Char) : Option (String × Option String × List Char) :=
  let afterWs1 := chars.dropWhile isUnicodeWhitespace
  match afterWs1 with
  | ')' :: after => some ("", none, after)
  | _ =>
    match parseLinkDest afterWs1 with
    | none => none
    | some (destChars, afterDest) =>
      let afterWs2 := afterDest.dropWhile isUnicodeWhitespace
      match afterWs2 with
      | ')' :: after => some (String.ofList destChars, none, after)
      | _ =>
        match parseTitle afterWs2 with
        | none => none
        | some (titleChars, afterTitle) =>
          let afterWs3 := afterTitle.dropWhile isUnicodeWhitespace
          match afterWs3 with
          | ')' :: after => some (String.ofList destChars, some (String.ofList titleChars), after)
          | _ => none

def parseRefLabel (chars : List Char) : Option (String × List Char) :=
  match findMatchingBracket chars with
  | some (labelChars, after) =>
    if labelChars.length > 999 then none else some (String.ofList labelChars, after)
  | none => none

def tryLinkTail (defs : LinkDefs) (linkTextChars : List Char) (afterBracket : List Char) :
    Option (String × Option String × List Char) :=
  match afterBracket with
  | '(' :: rest => parseInlineLinkTail rest
  | '[' :: rest =>
    match parseRefLabel rest with
    | some (label, after) =>
      let effectiveLabel := if label.isEmpty then String.ofList linkTextChars else label
      match lookupLinkDef defs effectiveLabel with
      | some (dest, title) => some (dest, title, after)
      | none => none
    | none => none
  | _ =>
    match lookupLinkDef defs (String.ofList linkTextChars) with
    | some (dest, title) => some (dest, title, afterBracket)
    | none => none

def findEmphCloserF (delimChar : Char) (openLen : Nat) (openCanClose : Bool) :
    Nat → Option Char → List Char → Option (Nat × List Char × List Char)
  | 0, _, _ => none
  | _ + 1, _, [] => none
  | fuel + 1, _, '\\' :: c :: rest =>
    match findEmphCloserF delimChar openLen openCanClose fuel (some c) rest with
    | some (usedLen, before, after) => some (usedLen, '\\' :: c :: before, after)
    | none => none
  | _ + 1, _, '\\' :: [] => none
  | fuel + 1, _, '`' :: rest =>
    let openRun := ('`' :: rest).takeWhile (· == '`')
    let afterOpenRun := ('`' :: rest).drop openRun.length
    match findCodeSpanEnd openRun.length afterOpenRun with
    | some (spanContent, afterSpan) =>
      match findEmphCloserF delimChar openLen openCanClose fuel (some '`') afterSpan with
      | some (usedLen, before, after) => some (usedLen, openRun ++ spanContent ++ openRun ++ before, after)
      | none => none
    | none =>
      match findEmphCloserF delimChar openLen openCanClose fuel (some '`') afterOpenRun with
      | some (usedLen, before, after) => some (usedLen, openRun ++ before, after)
      | none => none
  | fuel + 1, prev, c :: rest =>
    if c == delimChar then
      let run := (c :: rest).takeWhile (· == c)
      let afterRun := (c :: rest).drop run.length
      let closeCanClose := canCloseDelim c prev afterRun.head?
      let closeCanOpen := canOpenDelim c prev afterRun.head?
      if closeCanClose && multipleOf3Ok openLen run.length openCanClose closeCanOpen then
        let usedLen := if openLen ≥ 2 && run.length ≥ 2 then 2 else 1
        let leftover := List.replicate (run.length - usedLen) c
        some (usedLen, [], leftover ++ afterRun)
      else if closeCanOpen then
        -- This run can't close our opener, but it can open its own (nested) emphasis of the
        -- same delimiter character. Skip over that whole nested span as an opaque unit (it
        -- gets reparsed normally once this content is recursively parsed later) rather than
        -- treating it as literal text, so its closer isn't mistaken for ours.
        match findEmphCloserF c run.length closeCanClose fuel (some c) afterRun with
        | some (_, _, afterNested) =>
          let consumedLen := afterRun.length - afterNested.length
          let nestedSpanChars := afterRun.take consumedLen
          match findEmphCloserF delimChar openLen openCanClose fuel (some c) afterNested with
          | some (usedLen, before, after) => some (usedLen, run ++ nestedSpanChars ++ before, after)
          | none => none
        | none =>
          match findEmphCloserF delimChar openLen openCanClose fuel (some c) afterRun with
          | some (usedLen, before, after) => some (usedLen, run ++ before, after)
          | none => none
      else
        match findEmphCloserF delimChar openLen openCanClose fuel (some c) afterRun with
        | some (usedLen, before, after) => some (usedLen, run ++ before, after)
        | none => none
    else
      match findEmphCloserF delimChar openLen openCanClose fuel (some c) rest with
      | some (usedLen, before, after) => some (usedLen, c :: before, after)
      | none => none

def findEmphCloser (delimChar : Char) (openLen : Nat) (openCanClose : Bool) (chars : List Char) :
    Option (Nat × List Char × List Char) :=
  findEmphCloserF delimChar openLen openCanClose (chars.length + 1) (some delimChar) chars

def parseInlinesF (defs : LinkDefs) (insideLink : Bool) :
    Nat → Option Char → List Char → List CommonMark.Inline
  | 0, _, _ => []
  | _ + 1, _, [] => []
  | fuel + 1, _, '\\' :: c :: rest =>
    if isEscapable c then
      .text c.toString :: parseInlinesF defs insideLink fuel (some c) rest
    else if c == '\n' then
      .lineBreak :: parseInlinesF defs insideLink fuel none (skipLeadingSpacesTabs rest)
    else
      .text "\\" :: parseInlinesF defs insideLink fuel (some '\\') (c :: rest)
  | _ + 1, _, '\\' :: [] => [.text "\\"]
  | fuel + 1, _, '`' :: rest =>
    let openRun := ('`' :: rest).takeWhile (· == '`')
    let afterOpen := ('`' :: rest).drop openRun.length
    match findCodeSpanEnd openRun.length afterOpen with
    | some (content, after) =>
      .code (normalizeCodeSpanContent content) :: parseInlinesF defs insideLink fuel (some '`') after
    | none =>
      .text (String.ofList openRun) :: parseInlinesF defs insideLink fuel (some '`') afterOpen
  | fuel + 1, _, '&' :: rest =>
    match parseEntityRef rest with
    | some (txt, after) =>
      .text txt :: parseInlinesF defs insideLink fuel txt.toList.getLast? after
    | none => .text "&" :: parseInlinesF defs insideLink fuel (some '&') rest
  | fuel + 1, _, '<' :: rest =>
    match matchAutolink rest with
    | some (content, isEmail, after) =>
      let dest := if isEmail then "mailto:" ++ content else content
      .link dest none [.text content] :: parseInlinesF defs insideLink fuel (some '>') after
    | none =>
      match matchInlineHtml rest with
      | some (raw, after) =>
        .htmlInline raw :: parseInlinesF defs insideLink fuel raw.toList.getLast? after
      | none => .text "<" :: parseInlinesF defs insideLink fuel (some '<') rest
  | fuel + 1, _, '!' :: '[' :: rest =>
    match findMatchingBracket rest with
    | some (labelChars, after) =>
      match tryLinkTail defs labelChars after with
      | some (dest, title, restAfter) =>
        let content := parseInlinesF defs false fuel none labelChars
        let closeChar := if after.head? == some '(' then ')' else ']'
        .image dest title content :: parseInlinesF defs insideLink fuel (some closeChar) restAfter
      | none => .text "![" :: parseInlinesF defs insideLink fuel (some '[') rest
    | none => .text "![" :: parseInlinesF defs insideLink fuel (some '[') rest
  | fuel + 1, _, '!' :: rest => .text "!" :: parseInlinesF defs insideLink fuel (some '!') rest
  | fuel + 1, _, '[' :: rest =>
    if insideLink then
      .text "[" :: parseInlinesF defs insideLink fuel (some '[') rest
    else
      match findMatchingBracket rest with
      | some (labelChars, after) =>
        match tryLinkTail defs labelChars after with
        | some (dest, title, restAfter) =>
          let content := parseInlinesF defs true fuel none labelChars
          let closeChar := if after.head? == some '(' then ')' else ']'
          .link dest title content :: parseInlinesF defs insideLink fuel (some closeChar) restAfter
        | none => .text "[" :: parseInlinesF defs insideLink fuel (some '[') rest
      | none => .text "[" :: parseInlinesF defs insideLink fuel (some '[') rest
  | fuel + 1, _, ']' :: rest => .text "]" :: parseInlinesF defs insideLink fuel (some ']') rest
  | fuel + 1, _, '\n' :: rest =>
    .softBreak :: parseInlinesF defs insideLink fuel none (skipLeadingSpacesTabs rest)
  | fuel + 1, prev, c :: rest =>
    if c == '*' || c == '_' then
      let chars := c :: rest
      let run := chars.takeWhile (· == c)
      let afterRun := chars.drop run.length
      let openCanOpen := canOpenDelim c prev afterRun.head?
      let openCanClose := canCloseDelim c prev afterRun.head?
      if openCanOpen then
        match findEmphCloser c run.length openCanClose afterRun with
        | some (usedLen, content, afterClose) =>
          let leftoverOpen := run.length - usedLen
          let node : CommonMark.Inline :=
            if usedLen ≥ 2 then .strong (parseInlinesF defs insideLink fuel none content)
            else .emph (parseInlinesF defs insideLink fuel none content)
          let openLeftoverText : List CommonMark.Inline :=
            if leftoverOpen > 0 then [.text (String.ofList (List.replicate leftoverOpen c))] else []
          openLeftoverText ++ (node :: parseInlinesF defs insideLink fuel (some c) afterClose)
        | none => .text (String.ofList run) :: parseInlinesF defs insideLink fuel (some c) afterRun
      else
        .text (String.ofList run) :: parseInlinesF defs insideLink fuel (some c) afterRun
    else
      let (plain, rest') := takePlainRun (c :: rest)
      match rest' with
      | '\n' :: afterNl =>
        let plainChars := plain.toList
        let trailingSpaces := (plainChars.reverse.takeWhile (· == ' ')).length
        let core := String.ofList (plainChars.reverse.drop trailingSpaces).reverse
        let brk : CommonMark.Inline := if trailingSpaces ≥ 2 then .lineBreak else .softBreak
        let afterBreak := parseInlinesF defs insideLink fuel none (skipLeadingSpacesTabs afterNl)
        (if core.isEmpty then [] else [.text core]) ++ (brk :: afterBreak)
      | _ => .text plain :: parseInlinesF defs insideLink fuel plain.toList.getLast? rest'

-- Trailing spaces/tabs at the very end of the block's text are never meaningful (mid-text
-- trailing spaces before an embedded newline are already handled as break markers).
def stripTrailingWsChars (chars : List Char) : List Char :=
  (chars.reverse.dropWhile (fun c => c == ' ' || c == '\t')).reverse

def parseInline (defs : LinkDefs) (s : String) : List CommonMark.Inline :=
  let chars := stripTrailingWsChars s.toList
  parseInlinesF defs false (chars.length + 1) none chars

end CommonMark.Parser
