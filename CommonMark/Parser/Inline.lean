-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import CommonMark.Ast
import CommonMark.Parser.Entities
import UnicodeBasic

namespace CommonMark.Parser

abbrev LinkDefs := Array (String × String × Option String)

def toLowerStr (s : String) : String :=
  String.ofList (s.toList.map Char.toLower)

def collapseWhitespace (s : String) : String :=
  String.intercalate " " ((s.splitOn " ").filter (· ≠ "") )

-- `Unicode.getLowerChar` is Unicode's *simple* (one-char-to-one-char) case mapping, covering
-- every script's lowercase mapping. Label matching needs *full* case fold instead, which
-- differs from simple mapping only for a handful of code points whose fold expands to more
-- than one character (e.g. ẞ U+1E9E -> "ss"); `expandSharpS` below handles those separately
-- since `labelFoldChar` can only ever produce one `Char`.
def labelFoldChar (c : Char) : Char := Unicode.getLowerChar c

-- Unicode's *full* case fold (as opposed to simple, one-char-to-one-char case mapping) maps
-- ẞ (U+1E9E) to the two characters "ss", not to ß; that's the mapping label matching needs
-- so `[ẞ]` can match a definition labelled `SS`.
def expandSharpS (s : String) : String :=
  String.join (s.toList.map (fun c => if c.toNat == 0x1E9E then "ss" else c.toString))

def normalizeLabel (s : String) : String :=
  let collapsed :=
    collapseWhitespace (String.ofList ((expandSharpS s).toList.map (fun c => if c == '\t' || c == '\n' then ' ' else c)))
  String.ofList ((collapsed.trimAscii.toString).toList.map labelFoldChar)

def lookupLinkDef (defs : LinkDefs) (label : String) : Option (String × Option String) :=
  let target := normalizeLabel label
  (defs.toList.find? (fun (l, _, _) => normalizeLabel l == target)).map (fun (_, d, t) => (d, t))

def isEscapable (c : Char) : Bool :=
  "!\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~".toList.contains c

def isAsciiPunct (c : Char) : Bool :=
  "!\"#$%&'()*+,-./:;<=>?@[\\]^_`{|}~".toList.contains c

def isUnicodeWhitespace (c : Char) : Bool :=
  c == ' ' || c == '\t' || c == '\n' || c == '\r' || c == Char.ofNat 12

-- Flanking classification uses the spec's broader "Unicode whitespace" (Unicode Zs category,
-- or tab/LF/FF/CR), which also covers e.g. non-breaking space; link destination/title parsing
-- elsewhere intentionally uses the narrower `isUnicodeWhitespace` above (space/tab/line
-- ending only), since a non-breaking space there is just an ordinary destination character.
def isFlankingWhitespace (c : Char) : Bool :=
  isUnicodeWhitespace c || Unicode.GeneralCategory.isSpaceSeparator c

def isWsOrNone (oc : Option Char) : Bool :=
  match oc with
  | none => true
  | some c => isFlankingWhitespace c

-- The spec's "Unicode punctuation character" is any character in the Unicode P (punctuation)
-- or S (symbol) general category.
def isUnicodePunctOrSymbol (c : Char) : Bool :=
  Unicode.GeneralCategory.isPunctuation c || Unicode.GeneralCategory.isSymbol c

def isPunctChar (oc : Option Char) : Bool :=
  match oc with
  | none => false
  | some c => isUnicodePunctOrSymbol c

def skipLeadingSpacesTabs : List Char → List Char
  | c :: rest => if c == ' ' || c == '\t' then skipLeadingSpacesTabs rest else c :: rest
  | [] => []

-- `gfmStrikethrough` only adds `~` to the trigger set; with it `false`, this is byte-for-byte
-- what it was before `~` existed, so the plain (non-GFM) path's behavior is unchanged.
def takePlainRun (gfmStrikethrough : Bool) (chars : List Char) : String × List Char :=
  let isTrigger (c : Char) : Bool :=
    c == '\\' || c == '`' || c == '&' || c == '<' || c == '[' || c == ']' ||
    c == '!' || c == '*' || c == '_' || c == '\n' || (gfmStrikethrough && c == '~')
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

-- Link destinations, titles, and fenced code info strings undergo backslash-escape and
-- entity resolution, but not the rest of inline parsing (no emphasis, code spans, links).
def resolveEscapesAndEntitiesF : Nat → List Char → String
  | 0, _ => ""
  | _ + 1, [] => ""
  | fuel + 1, '\\' :: c :: rest =>
    if isEscapable c then c.toString ++ resolveEscapesAndEntitiesF fuel rest
    else "\\" ++ resolveEscapesAndEntitiesF fuel (c :: rest)
  | _ + 1, '\\' :: [] => "\\"
  | fuel + 1, '&' :: rest =>
    match parseEntityRef rest with
    | some (txt, after) => txt ++ resolveEscapesAndEntitiesF fuel after
    | none => "&" ++ resolveEscapesAndEntitiesF fuel rest
  | fuel + 1, c :: rest => c.toString ++ resolveEscapesAndEntitiesF fuel rest

def resolveEscapesAndEntities (s : String) : String :=
  resolveEscapesAndEntitiesF (s.length + 1) s.toList

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

-- A link label ends at the first unescaped `]`; unescaped brackets of either kind aren't
-- allowed anywhere inside one (unlike link text, which supports nested brackets). Shared by
-- reference-style links here and by link reference definitions.
def takeLabelCharsF : Nat → List Char → Option (List Char × List Char)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, '\\' :: c :: rest =>
    match takeLabelCharsF fuel rest with
    | some (before, after) => some ('\\' :: c :: before, after)
    | none => none
  | _ + 1, '\\' :: [] => none
  | _ + 1, ']' :: rest => some ([], rest)
  | _ + 1, '[' :: _ => none
  | fuel + 1, c :: rest =>
    match takeLabelCharsF fuel rest with
    | some (before, after) => some (c :: before, after)
    | none => none

def takeLabelChars (chars : List Char) : Option (List Char × List Char) :=
  takeLabelCharsF (chars.length + 1) chars

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

-- A backslash only pairs with a following ASCII-punctuation character (matching
-- `isAsciiPunct`'s escapable set); otherwise it's just an ordinary literal character, and the
-- char after it is re-examined on its own (so e.g. a backslash immediately before whitespace
-- still ends the destination there, rather than being swallowed as part of an escape).
def parseBareDestF : Nat → Nat → List Char → List Char × List Char
  | 0, _, chars => ([], chars)
  | fuel + 1, depth, '\\' :: c :: rest =>
    if isAsciiPunct c then
      let (before, after) := parseBareDestF fuel depth rest
      ('\\' :: c :: before, after)
    else
      let (before, after) := parseBareDestF fuel depth (c :: rest)
      ('\\' :: before, after)
  | _ + 1, _, '\\' :: [] => (['\\'], [])
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
    else if closeChar == ')' && c == '(' then none
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
      let dest := resolveEscapesAndEntities (String.ofList destChars)
      let afterWs2 := afterDest.dropWhile isUnicodeWhitespace
      let hadWs := afterWs2.length < afterDest.length
      match afterWs2 with
      | ')' :: after => some (dest, none, after)
      | _ =>
        match if hadWs then parseTitle afterWs2 else none with
        | none => none
        | some (titleChars, afterTitle) =>
          let afterWs3 := afterTitle.dropWhile isUnicodeWhitespace
          match afterWs3 with
          | ')' :: after =>
            some (dest, some (resolveEscapesAndEntities (String.ofList titleChars)), after)
          | _ => none

def parseRefLabel (chars : List Char) : Option (String × List Char) :=
  match takeLabelChars chars with
  | some (labelChars, after) =>
    if labelChars.length > 999 then none else some (String.ofList labelChars, after)
  | none => none

def tryLinkTail (defs : LinkDefs) (linkTextChars : List Char) (afterBracket : List Char) :
    Option (String × Option String × List Char) :=
  let shortcut : Option (String × Option String × List Char) :=
    match lookupLinkDef defs (String.ofList linkTextChars) with
    | some (dest, title) => some (dest, title, afterBracket)
    | none => none
  match afterBracket with
  -- A malformed `(...)` tail isn't consumed as if it were a failed link; it's simply not
  -- there, so a shortcut reference against the link text alone is still tried.
  | '(' :: rest =>
    match parseInlineLinkTail rest with
    | some r => some r
    | none => shortcut
  | '[' :: rest =>
    match parseRefLabel rest with
    | some (label, after) =>
      let effectiveLabel := if label.isEmpty then String.ofList linkTextChars else label
      match lookupLinkDef defs effectiveLabel with
      | some (dest, title) => some (dest, title, after)
      | none => none
    | none => none
  | _ => shortcut

/-- Mirrors `CommonMark.Inline` exactly, plus `strikethrough`, for the GFM variant's inline
    pipeline (the tokenizer/delimiter-stack machinery below is shared by both variants, gated
    behind `gfmStrikethrough : Bool`; see `parseInline`/`parseInlineRaw`). Lives alongside
    `INode` rather than in the `GFMarkdown` namespace for the same reason `RawBlock`/
    `TableAlignment` do: it's needed by machinery in `CommonMark.Parser`, which can't depend
    on `GFMarkdown`. -/
inductive RawInline where
  | text          (s : String)
  | code          (s : String)
  | emph          (content : List RawInline)
  | strong        (content : List RawInline)
  | link          (dest : String) (title : Option String) (content : List RawInline)
  | image         (dest : String) (title : Option String) (content : List RawInline)
  | htmlInline    (s : String)
  | softBreak
  | lineBreak
  | strikethrough (content : List RawInline)
  deriving Repr, BEq, Inhabited

-- The tokenized form of an inline text run: characters that can never interact with later
-- delimiter matching (escapes, entities, code spans, autolinks, raw HTML, breaks) are
-- resolved immediately; `*`/`_`/`~` runs and bracket markers are left as unresolved markers
-- to be matched up afterwards by `resolveBrackets`/`resolveEmphasis`, mirroring the spec
-- appendix's delimiter-stack algorithm (this is what makes constructs like `__foo_ bar_`,
-- where a partially-used opener is reused by a later closer, and link/emphasis interaction
-- like `*[bar*](/url)`, resolve correctly, unlike a naive single left-to-right descent).
inductive INode where
  | text (s : String)
  | resolved (i : RawInline)
  -- `origN` is the delimiter run's length as first tokenized, kept unchanged through any
  -- number of partial matches that shrink `n`; the rule-of-3 check in `resolveEmphasis`
  -- depends on it (see the comment there), mirroring how the reference implementation's
  -- `delimiter->length` field is set once and never mutated even as the associated text
  -- node's length shrinks.
  | delim (c : Char) (n : Nat) (origN : Nat) (canOpen canClose : Bool)
  | openBracket (isImage : Bool) (active : Bool)
  | closeBracket (isImage : Bool) (dest : String) (title : Option String) (rawTailText : String)
  | closeBracketFail
  deriving Inhabited

def tokenizeF (defs : LinkDefs) (gfmStrikethrough : Bool) :
    Nat → List (Bool × List Char) → Option Char → List Char → List INode
  | 0, _, _, _ => []
  | _ + 1, _, _, [] => []
  | fuel + 1, stack, _, '\\' :: c :: rest =>
    if isEscapable c then
      .text c.toString :: tokenizeF defs gfmStrikethrough fuel stack (some c) rest
    else if c == '\n' then
      .resolved .lineBreak :: tokenizeF defs gfmStrikethrough fuel stack none (skipLeadingSpacesTabs rest)
    else
      .text "\\" :: tokenizeF defs gfmStrikethrough fuel stack (some '\\') (c :: rest)
  | _ + 1, _, _, '\\' :: [] => [.text "\\"]
  | fuel + 1, stack, _, '`' :: rest =>
    let openRun := ('`' :: rest).takeWhile (· == '`')
    let afterOpen := ('`' :: rest).drop openRun.length
    match findCodeSpanEnd openRun.length afterOpen with
    | some (content, after) =>
      .resolved (.code (normalizeCodeSpanContent content)) ::
        tokenizeF defs gfmStrikethrough fuel stack (some '`') after
    | none =>
      .text (String.ofList openRun) :: tokenizeF defs gfmStrikethrough fuel stack (some '`') afterOpen
  | fuel + 1, stack, _, '&' :: rest =>
    match parseEntityRef rest with
    | some (txt, after) =>
      .text txt :: tokenizeF defs gfmStrikethrough fuel stack txt.toList.getLast? after
    | none => .text "&" :: tokenizeF defs gfmStrikethrough fuel stack (some '&') rest
  | fuel + 1, stack, _, '<' :: rest =>
    match matchAutolink rest with
    | some (content, isEmail, after) =>
      let dest := if isEmail then "mailto:" ++ content else content
      .resolved (.link dest none [.text content]) ::
        tokenizeF defs gfmStrikethrough fuel stack (some '>') after
    | none =>
      match matchInlineHtml rest with
      | some (raw, after) =>
        .resolved (.htmlInline raw) :: tokenizeF defs gfmStrikethrough fuel stack raw.toList.getLast? after
      | none => .text "<" :: tokenizeF defs gfmStrikethrough fuel stack (some '<') rest
  | fuel + 1, stack, _, '!' :: '[' :: rest =>
    .openBracket true true :: tokenizeF defs gfmStrikethrough fuel ((true, rest) :: stack) (some '[') rest
  | fuel + 1, stack, _, '!' :: rest =>
    .text "!" :: tokenizeF defs gfmStrikethrough fuel stack (some '!') rest
  | fuel + 1, stack, _, '[' :: rest =>
    .openBracket false true :: tokenizeF defs gfmStrikethrough fuel ((false, rest) :: stack) (some '[') rest
  | fuel + 1, stack, _, ']' :: rest =>
    match stack with
    | [] => .text "]" :: tokenizeF defs gfmStrikethrough fuel stack (some ']') rest
    | (isImage, startChars) :: restStack =>
      let labelChars := startChars.take (startChars.length - (rest.length + 1))
      match tryLinkTail defs labelChars rest with
      | some (dest, title, restAfterTail) =>
        let consumedLen := rest.length - restAfterTail.length
        let rawTailText := String.ofList (rest.take consumedLen)
        let prev' := if rawTailText.isEmpty then some ']' else rawTailText.toList.getLast?
        .closeBracket isImage dest title rawTailText ::
          tokenizeF defs gfmStrikethrough fuel restStack prev' restAfterTail
      | none => .closeBracketFail :: tokenizeF defs gfmStrikethrough fuel restStack (some ']') rest
  | fuel + 1, stack, _, '\n' :: rest =>
    .resolved .softBreak :: tokenizeF defs gfmStrikethrough fuel stack none (skipLeadingSpacesTabs rest)
  | fuel + 1, stack, prev, c :: rest =>
    if c == '*' || c == '_' then
      let chars := c :: rest
      let run := chars.takeWhile (· == c)
      let afterRun := chars.drop run.length
      let co := canOpenDelim c prev afterRun.head?
      let cc := canCloseDelim c prev afterRun.head?
      .delim c run.length run.length co cc :: tokenizeF defs gfmStrikethrough fuel stack (some c) afterRun
    else if gfmStrikethrough && c == '~' then
      -- GFM only ever treats a run of exactly one or two tildes as an operable delimiter
      -- (`resolveEmphasis`'s tilde matching requires an exact-length pair besides); any other
      -- run length is never eligible, so it's just literal text from the start.
      let chars := c :: rest
      let run := chars.takeWhile (· == c)
      let afterRun := chars.drop run.length
      if run.length == 1 || run.length == 2 then
        let co := canOpenDelim c prev afterRun.head?
        let cc := canCloseDelim c prev afterRun.head?
        .delim c run.length run.length co cc :: tokenizeF defs gfmStrikethrough fuel stack (some c) afterRun
      else
        .text (String.ofList run) :: tokenizeF defs gfmStrikethrough fuel stack run.getLast? afterRun
    else
      let (plain, rest') := takePlainRun gfmStrikethrough (c :: rest)
      match rest' with
      | '\n' :: afterNl =>
        let plainChars := plain.toList
        let trailingSpaces := (plainChars.reverse.takeWhile (· == ' ')).length
        let core := String.ofList (plainChars.reverse.drop trailingSpaces).reverse
        let brk : INode := .resolved (if trailingSpaces ≥ 2 then .lineBreak else .softBreak)
        let afterBreak := tokenizeF defs gfmStrikethrough fuel stack none (skipLeadingSpacesTabs afterNl)
        (if core.isEmpty then [] else [.text core]) ++ (brk :: afterBreak)
      | _ => .text plain :: tokenizeF defs gfmStrikethrough fuel stack plain.toList.getLast? rest'

def flattenNode : INode → RawInline
  | .text s => .text s
  | .resolved i => i
  | .delim c n _ _ _ => .text (String.ofList (List.replicate n c))
  | .openBracket isImage _ => .text (if isImage then "![" else "[")
  | .closeBracket _ _ _ rawTailText => .text ("]" ++ rawTailText)
  | .closeBracketFail => .text "]"

def flattenNodes (arr : Array INode) : List RawInline :=
  (arr.map flattenNode).toList

-- The spec appendix's `openers_bottom`: once a closer of a given (character, closer-run-length
-- mod 3, can-also-open) bucket has scanned back to some point and found no usable opener, no
-- later closer in the *same* bucket needs to rescan that far, since `multipleOf3Ok`'s outcome
-- for any given opener depends only on that bucket key, not on the closer's exact length.
-- Without this, a run of many closers with no matching openers (e.g. many `foo*` in a row)
-- costs O(n) per closer, O(n²) overall; this is the spec's own fix for that, not a bespoke one.
def emphBucket (c : Char) (closeLen : Nat) (closerCanOpen : Bool) : Nat :=
  (if c == '_' then 0 else 1) * 6 + (closeLen % 3) * 2 + (if closerCanOpen then 1 else 0)

-- The spec appendix's "process emphasis" step: scan left to right for a closer, scan back
-- from it for the nearest matching opener, and wrap the span between them. A leftover
-- (partially used) opener or closer is kept in place with the reduced count so it remains
-- available to match again later, which is what makes e.g. `__foo_ bar_` nest correctly.
def resolveEmphasis (arr0 : Array INode) : Array INode :=
  Id.run do
    let mut arr := arr0
    let mut i := 0
    -- No usable opener remains at or below index `bottoms[bucket]` for that bucket.
    let mut bottoms : Array Nat := Array.replicate 12 0
    -- Separate from `bottoms`: GFM strikethrough matching requires an *exact*-length pair (no
    -- rule-of-3, no partial consumption -- see the `c == '~'` branch below), so unlike `*`/`_`
    -- it only ever needs the *nearest* unconsumed `~` opener, not a bucketed multi-candidate
    -- search; one bottom covers it.
    let mut tildeBottom : Nat := 0
    -- Each step either consumes at least one unit from some delimiter run's count (bounded
    -- by the total character count) or moves past a node for good (bounded by array size).
    let fuel := 2 * arr0.size + (arr0.foldl (init := 0) fun acc n =>
      acc + (match n with | .delim _ n _ _ _ => n | _ => 1)) + 4
    for _ in [0 : fuel] do
      if i ≥ arr.size then break
      match arr[i]! with
      | .delim c n origN closerCanOpen canClose =>
        if !canClose || n == 0 then
          i := i + 1
        else if c == '~' then
          let mut foundJ : Option Nat := none
          for k in [0 : i - tildeBottom] do
            let j := i - 1 - k
            match arr[j]! with
            | .delim cj _ _ coj _ => if cj == '~' && coj then foundJ := some j; break
            | _ => pure ()
          match foundJ with
          | none =>
            tildeBottom := i
            i := i + 1
          | some j =>
            match arr[j]!, arr[i]! with
            | .delim _ nj _ _ _, .delim _ ni _ _ _ =>
              -- Unlike `*`/`_`, a length mismatch isn't "no opener found here, keep the
              -- delimiters live for a future match" -- cmark-gfm's own algorithm discards
              -- both outright, back to plain literal tildes, the moment a same-bucket pair is
              -- found and fails the exact-length check (verified against `extensions.txt`'s
              -- "No ~mismatch~~" case).
              if nj == ni then
                let innerContent := flattenNodes (arr.extract (j + 1) i)
                let newNode : INode := .resolved (.strikethrough innerContent)
                arr := arr.extract 0 j ++ #[newNode] ++ arr.extract (i + 1) arr.size
                tildeBottom := min tildeBottom j
                bottoms := bottoms.map (min · j)
                i := j + 1
              else
                arr := arr.set! j (.text (String.ofList (List.replicate nj '~')))
                arr := arr.set! i (.text (String.ofList (List.replicate ni '~')))
                i := i + 1
            | _, _ => i := i + 1
        else
          -- The rule-of-3 check (`multipleOf3Ok`) and the bucket a closer is filed under both
          -- use each delimiter's *original* run length (`origN`), not its current, possibly
          -- already-reduced count `n`/`nj` -- mirroring the reference implementation, where a
          -- delimiter's `length` field is set once at tokenize time and never mutated even as
          -- the associated text shrinks from earlier partial matches. Using the live count
          -- here instead is what let `a***b* c*` resolve wrongly: after `***` gives up one `*`
          -- to close against `b`'s following `*`, its remaining live count (2) no longer
          -- reflects the original 3-length run that the rule-of-3 check needs to see.
          let bucket := emphBucket c origN closerCanOpen
          let bottom := bottoms[bucket]!
          let mut foundJ : Option Nat := none
          for k in [0 : i - bottom] do
            let j := i - 1 - k
            match arr[j]! with
            | .delim cj nj origNj coj ccj =>
              if cj == c && coj && nj > 0 && multipleOf3Ok origNj origN ccj closerCanOpen then
                foundJ := some j
                break
            | _ => pure ()
          match foundJ with
          | none =>
            -- No opener for this bucket down to the old bottom, so nothing has changed; no
            -- future closer in this bucket needs to search this far again.
            bottoms := bottoms.set! bucket i
            if !closerCanOpen then
              arr := arr.set! i (.text (String.ofList (List.replicate n c)))
            i := i + 1
          | some j =>
            match arr[j]!, arr[i]! with
            | .delim cj nj origNj coj ccj, .delim ci ni origNi coi cci =>
              let strong := nj ≥ 2 && ni ≥ 2
              let usedLen := if strong then 2 else 1
              let innerContent := flattenNodes (arr.extract (j + 1) i)
              let newNode : INode :=
                .resolved (if strong then .strong innerContent else .emph innerContent)
              let openerLeftover : Array INode :=
                if nj - usedLen == 0 then #[] else #[.delim cj (nj - usedLen) origNj coj ccj]
              let closerLeftoverN := ni - usedLen
              if closerLeftoverN == 0 then
                arr := arr.extract 0 j ++ openerLeftover ++ #[newNode] ++ arr.extract (i + 1) arr.size
              else
                arr := arr.extract 0 j ++ openerLeftover ++
                  #[newNode, .delim ci closerLeftoverN origNi coi cci] ++ arr.extract (i + 1) arr.size
              -- Everything from `j` on was just renumbered (or removed); any bucket's bottom
              -- that pointed past `j` no longer means anything, so pull it back to `j`.
              bottoms := bottoms.map (min · j)
              i := j + openerLeftover.size + 1
            | _, _ => i := i + 1
      | _ => i := i + 1
    return arr

-- The "look for link or image" step: scan left to right for a `]`, and pair it with the
-- nearest still-open `[`/`![` marker. A successful link/image wraps the enclosed span
-- (resolving its emphasis first, scoped to just that span) and, for a link, deactivates
-- every earlier opener so links can't nest; a failed match falls back to literal text.
def resolveBrackets (defs : LinkDefs) (gfmStrikethrough : Bool) (arr0 : Array INode) : Array INode :=
  Id.run do
    let mut arr := arr0
    let mut i := 0
    -- No `.openBracket` remains at or below this index: once a search has scanned this far
    -- and found none, none can appear there later (openBrackets only ever turn into text,
    -- never the reverse), so no later search needs to rescan that range. Without this, a
    -- run of many `]` with nothing to match (e.g. many `[foo` never closed as links) costs
    -- O(n) per `]`, O(n²) overall.
    let mut bottom := 0
    let fuel := arr0.size + 4
    for _ in [0 : fuel] do
      if i ≥ arr.size then break
      let findOpener : Id (Option Nat) := do
        let mut foundJ : Option Nat := none
        for k in [0 : i - bottom] do
          let j := i - 1 - k
          match arr[j]! with
          | .openBracket _ _ => foundJ := some j; break
          | _ => pure ()
        return foundJ
      match arr[i]! with
      | .closeBracketFail =>
        match ← findOpener with
        | some j =>
          let openText := match arr[j]! with | .openBracket isImg _ => (if isImg then "![" else "[") | _ => ""
          arr := arr.set! j (.text openText)
          arr := arr.set! i (.text "]")
        | none =>
          arr := arr.set! i (.text "]")
          bottom := i
        i := i + 1
      | .closeBracket isImage dest title rawTailText =>
        match ← findOpener with
        | none =>
          arr := arr.set! i (.text ("]" ++ rawTailText))
          bottom := i
          i := i + 1
        | some j =>
          let isActive := match arr[j]! with | .openBracket _ act => act | _ => false
          if !isActive then
            -- The already-consumed tail text (e.g. "(/url)" or "[ref]") never gets used, so
            -- it's re-tokenized as ordinary content rather than left as inert literal text:
            -- a reference-style tail like "[ref]" is real bracket syntax that can go on to
            -- form its own independent link, as in `[foo [bar](/1)][ref]`.
            let openText := match arr[j]! with | .openBracket isImg _ => (if isImg then "![" else "[") | _ => ""
            arr := arr.set! j (.text openText)
            let freshTail :=
              (tokenizeF defs gfmStrikethrough (rawTailText.length + 1) [] (some ']')
                rawTailText.toList).toArray
            arr := arr.extract 0 i ++ #[.text "]"] ++ freshTail ++ arr.extract (i + 1) arr.size
            i := i + 1
          else
            let content := flattenNodes (resolveEmphasis (arr.extract (j + 1) i))
            let newNode : INode := .resolved (if isImage then .image dest title content else .link dest title content)
            -- Only plain `[` openers are deactivated: an image can freely contain a link in
            -- its (alt-text-only) content, so `![` openers stay usable.
            if !isImage then
              for k2 in [0 : j] do
                match arr[k2]! with
                | .openBracket false true => arr := arr.set! k2 (.openBracket false false)
                | _ => pure ()
            arr := arr.extract 0 j ++ #[newNode] ++ arr.extract (i + 1) arr.size
            -- Same renumbering hazard as in `resolveEmphasis`: `j` and everything after it
            -- just shifted, so a bottom that pointed past `j` is stale.
            bottom := min bottom j
            i := j + 1
      | _ => i := i + 1
    return arr

-- Trailing spaces/tabs at the very end of the block's text are never meaningful (mid-text
-- trailing spaces before an embedded newline are already handled as break markers).
def stripTrailingWsChars (chars : List Char) : List Char :=
  (chars.reverse.dropWhile (fun c => c == ' ' || c == '\t')).reverse

-- Narrows `RawInline` down to `CommonMark.Inline`. Mirrors the structure precisely (both
-- recurse structurally over `List RawInline`/`List Inline`, so no fuel is needed here either,
-- as with `CommonMark.Ast`'s `Inline.map`/`Inline.mapList`).
mutual
def narrowInline : RawInline → CommonMark.Inline
  | .text s => .text s
  | .code s => .code s
  | .emph content => .emph (narrowInlineList content)
  | .strong content => .strong (narrowInlineList content)
  | .link dest title content => .link dest title (narrowInlineList content)
  | .image dest title content => .image dest title (narrowInlineList content)
  | .htmlInline s => .htmlInline s
  | .softBreak => .softBreak
  | .lineBreak => .lineBreak
  -- Only ever produced when `gfmStrikethrough = true` (`resolveEmphasis`'s `c == '~'`
  -- branch, reachable only from a `.delim '~' ...` node, itself only ever tokenized when
  -- `gfmStrikethrough = true`); on the plain CommonMark path this arm is unreachable, but
  -- the match still has to be total over all of `RawInline`. Same idiom as `RawBlock.table`'s
  -- fallback in `Block.lean`'s `rawBlockToBlockF`.
  | .strikethrough _ => .text ""

def narrowInlineList : List RawInline → List CommonMark.Inline
  | [] => []
  | i :: rest => narrowInline i :: narrowInlineList rest
end

/-- The generalized inline parser shared by both variants: `gfmStrikethrough = true` lets `~`/
    `~~` runs compete as delimiters in `resolveEmphasis`'s scan, same as `*`/`_`; `false`
    leaves `~` as ordinary text, byte-for-byte what `tokenizeF`/`takePlainRun` did before `~`
    existed (see their doc comments). -/
def parseInlineRaw (gfmStrikethrough : Bool) (defs : LinkDefs) (s : String) : List RawInline :=
  let chars := stripTrailingWsChars s.toList
  let tokens := (tokenizeF defs gfmStrikethrough (chars.length + 1) [] none chars).toArray
  flattenNodes (resolveEmphasis (resolveBrackets defs gfmStrikethrough tokens))

def parseInline (defs : LinkDefs) (s : String) : List CommonMark.Inline :=
  narrowInlineList (parseInlineRaw false defs s)

end CommonMark.Parser
