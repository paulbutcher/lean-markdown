-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import GFMarkdown.Ast

-- GFM's "extended autolinks": bare `http://`/`https://`/`ftp://`/`www.` URLs and bare/
-- `mailto:`/`xmpp:` email addresses, recognized in ordinary text without CommonMark's
-- `<...>` angle brackets. Grounded directly in cmark-gfm's `extensions/autolink.c`
-- (`www_match`/`url_match`/`postprocess_text`), fetched and read rather than re-derived from
-- the example suite alone, since several rules (trailing-punctuation trimming, the domain
-- underscore rule, the `mailto:`/`xmpp:` word-boundary check) aren't fully pinned down by
-- examples. Implemented as a post-process over an already-parsed `Document`
-- (`autolinkDocument`), walking `.text` leaves, rather than as part of the tokenizer: unlike
-- strikethrough, autolinks don't need to compete with `*`/`_` in `resolveEmphasis`'s
-- delimiter-stack scan, so there's no need to touch the shared inline pipeline at all. This
-- mirrors cmark-gfm's own architecture for the email case (its `postprocess_text` is likewise
-- a separate later pass over the fully-resolved tree); its `www_match`/`url_match` are
-- ordinary mid-tokenize character dispatches there, but reimplementing them as a post-process
-- pass here only matters observably at boundaries the example suite doesn't exercise (see
-- `matchScheme`'s comment).
namespace GFMarkdown

open CommonMark.Parser (RawInline TableAlignment isUnicodeWhitespace isUnicodePunctOrSymbol)

def isValidHostChar (c : Char) : Bool :=
  !isUnicodeWhitespace c && !isUnicodePunctOrSymbol c

-- Mirrors cmark-gfm's `check_domain`: scans from the *second* character (the caller has
-- already matched a fixed prefix -- `www.` or `://` -- so the first domain character is
-- assumed valid) up to (not including) the last character of `chars`, rejecting a domain with
-- an underscore in either of its last two dot-separated segments (bare host names disallow
-- underscores; full domain names allow them). `allowShort` skips the "must contain a dot"
-- requirement (used after `://`, where a bare host like `http://localhost` is still valid;
-- `www.` links always require one, since `www.foo` alone isn't a recognizable domain). Doesn't
-- replicate the source's escaped-character skip inside a domain: no vendored example needs it,
-- and a stray backslash there is vanishingly rare in practice.
def checkDomainGo : Nat → List Char → Nat → Nat → Nat → Nat → Nat × Nat × Nat × Nat
  | 0, _, consumed, np, u1, u2 => (consumed, np, u1, u2)
  | _ + 1, [], consumed, np, u1, u2 => (consumed, np, u1, u2)
  | _ + 1, [_], consumed, np, u1, u2 => (consumed, np, u1, u2)
  | fuel + 1, c :: rest, consumed, np, u1, u2 =>
    if c == '_' then checkDomainGo fuel rest (consumed + 1) np u1 (u2 + 1)
    else if c == '.' then checkDomainGo fuel rest (consumed + 1) (np + 1) u2 0
    else if isValidHostChar c || c == '-' then checkDomainGo fuel rest (consumed + 1) np u1 u2
    else (consumed, np, u1, u2)

def checkDomain (allowShort : Bool) (chars : List Char) : Nat :=
  let (consumed, np, u1, u2) := checkDomainGo (chars.length + 1) (chars.drop 1) 1 0 0 0
  if (u1 > 0 || u2 > 0) && np ≤ 10 then 0
  else if allowShort then consumed
  else if np > 0 then consumed
  else 0

private def parenCounts (chars : List Char) : Nat × Nat :=
  chars.foldl (fun (o, c) ch =>
    if ch == '(' then (o + 1, c) else if ch == ')' then (o, c + 1) else (o, c)) (0, 0)

private def autolinkDelimGo : Nat → List Char → Nat → Nat → List Char
  | 0, revChars, _, _ => revChars
  | _ + 1, [], _, _ => []
  | fuel + 1, c :: rest, opening, closing =>
    match c with
    | ')' =>
      if closing ≤ opening then c :: rest else autolinkDelimGo fuel rest opening (closing - 1)
    | '?' | '!' | '.' | ',' | ':' | '*' | '_' | '~' | '\'' | '"' =>
      autolinkDelimGo fuel rest opening closing
    | ';' =>
      -- A trailing HTML entity reference (e.g. a stray `&amp;` swept up at the end of the
      -- match) is stripped whole; anything less -- no letters, or letters with no `&` before
      -- them -- just drops the `;` itself.
      let alphaRun := rest.takeWhile Char.isAlpha
      let afterAlpha := rest.drop alphaRun.length
      if !alphaRun.isEmpty && afterAlpha.head? == some '&' then
        autolinkDelimGo fuel (afterAlpha.drop 1) opening closing
      else
        autolinkDelimGo fuel rest opening closing
    | _ => c :: rest

-- Trims trailing punctuation that reads as prose following a link rather than part of it, and
-- drops a trailing unbalanced `)` while leaving balanced ones alone (so
-- `Pikachu_(Electric)` keeps its closing paren, but `(see Pikachu_(Electric))`'s outer one
-- doesn't get swept in). `chars` is a tentative match already extended to the first
-- whitespace/`<`; also re-truncates at an embedded `<` for parity with the source, though the
-- callers below never actually produce one.
def autolinkDelim (chars : List Char) : List Char :=
  let truncated := chars.takeWhile (· ≠ '<')
  let (opening, closing) := parenCounts truncated
  (autolinkDelimGo (truncated.length + 1) truncated.reverse opening closing).reverse

private def extendToBoundary (chars : List Char) : List Char :=
  chars.takeWhile (fun c => !isUnicodeWhitespace c && c ≠ '<')

-- `www.`-prefixed bare links: only recognized when immediately preceded by whitespace, one of
-- `*_~(`, or nothing (start of the run) -- otherwise `xwww.foo.com` would wrongly linkify.
def matchWww (prev : Option Char) (chars : List Char) : Option (List Char) :=
  let boundaryOk := match prev with
    | none => true
    | some c => c == '*' || c == '_' || c == '~' || c == '(' || isUnicodeWhitespace c
  if !boundaryOk then none
  else
    match chars with
    | 'w' :: 'w' :: 'w' :: '.' :: _ =>
      let domainLen := checkDomain false chars
      if domainLen == 0 then none
      else
        let extended := chars.take domainLen ++ extendToBoundary (chars.drop domainLen)
        let trimmed := autolinkDelim extended
        if trimmed.isEmpty then none else some trimmed
    | _ => none

private def dropPrefixCI : List Char → List Char → Option (List Char)
  | [], rest => some rest
  | _ :: _, [] => none
  | p :: ps, c :: cs => if p.toLower == c.toLower then dropPrefixCI ps cs else none

private def matchSchemeWith (schemeText : List Char) (chars : List Char) : Option (List Char) :=
  match dropPrefixCI schemeText chars with
  | none => none
  | some afterScheme =>
    let domainLen := checkDomain true afterScheme
    if domainLen == 0 then none
    else
      let extended := afterScheme.take domainLen ++ extendToBoundary (afterScheme.drop domainLen)
      let trimmed := autolinkDelim (schemeText ++ extended)
      if trimmed.isEmpty then none else some trimmed

-- `http://`/`https://`/`ftp://` links, case-insensitive. Mirrors `url_match`'s rewind-then-
-- validate check (only an *alphabetic* preceding character blocks a match, so `9http://x.com`
-- still linkifies -- a digit is never itself part of a rewound scheme name) by testing directly
-- at each position instead of literally rewinding: since the schemes are a fixed, known list,
-- "rewind from `:` and compare the rewound text to a known scheme" and "check whether a known
-- scheme starts here, given the one character before it" decide the same cases. Where this
-- can genuinely differ from `url_match` is a scheme spanning more than one already-resolved
-- inline node (e.g. straddling a backslash escape or an entity reference) -- not exercised by
-- the vendored example suite, and an acceptable gap for the same reason `checkDomainGo` skips
-- escaped-character handling.
def matchScheme (prev : Option Char) (chars : List Char) : Option (List Char) :=
  if (match prev with | none => false | some c => c.isAlpha) then none
  else
    match matchSchemeWith "http://".toList chars with
    | some m => some m
    | none =>
      match matchSchemeWith "https://".toList chars with
      | some m => some m
      | none => matchSchemeWith "ftp://".toList chars

private def flushText (pendingRev : List Char) (tail : List RawInline) : List RawInline :=
  if pendingRev.isEmpty then tail else .text (String.ofList pendingRev.reverse) :: tail

def scanUrlWwwGo : Nat → Option Char → List Char → List Char → List RawInline
  | 0, _, pending, _ => flushText pending []
  | _ + 1, _, pending, [] => flushText pending []
  | fuel + 1, prev, pending, c :: rest =>
    let matched := match matchWww prev (c :: rest) with
      | some m => some ("http://" ++ String.ofList m, m)
      | none => (matchScheme prev (c :: rest)).map (fun m => (String.ofList m, m))
    match matched with
    | some (href, m) =>
      let remaining := (c :: rest).drop m.length
      flushText pending
        (RawInline.link href none [.text (String.ofList m)] :: scanUrlWwwGo fuel m.getLast? [] remaining)
    | none => scanUrlWwwGo fuel (some c) (c :: pending) rest

-- Bare `http://`/`https://`/`ftp://`/`www.` links (email addresses are handled separately by
-- `scanEmail`, mirroring cmark-gfm's own two-pass split).
def scanUrlWww (s : String) : List RawInline :=
  scanUrlWwwGo (s.length + 1) none [] s.toList

def emailLocalChar (c : Char) : Bool :=
  c.isAlphanum || c == '.' || c == '+' || c == '-' || c == '_'

-- Total access: an out-of-bounds index (which the bounds checks throughout this file are
-- meant to prevent, but a single NUL is a harmless fallback either way, matching none of the
-- characters any caller here checks for) returns `'\x00'` rather than panicking. Keeping this
-- total is exactly what `test/GfmGuards.lean`'s "shouldn't crash everything" example checks.
private def charAt (chars : Array Char) (i : Nat) : Char := chars.getD i (Char.ofNat 0)

-- Does `chars[.. colonIdx]` end with `protocol` (a literal like `"mailto:"`), and -- unless
-- `protocol` starts right at `windowStart` (the text run's own start, or the boundary left by
-- an earlier match) -- is the character right before it non-alphanumeric? Mirrors
-- `validate_protocol`'s word-boundary check: this is what makes "mmmmailto:x@y.z" *not* treat
-- "mmmmailto:" as part of the address (the `m` right before "mailto:" is alphanumeric), while
-- "This is a mailto:x@y.z" does (preceded by a space).
private def matchProtocolBefore (chars : Array Char) (windowStart colonIdx : Nat)
    (protocol : List Char) : Bool :=
  let len := protocol.length
  if len > colonIdx + 1 - windowStart then false
  else
    let startIdx := colonIdx + 1 - len
    let slice := (List.range len).map (fun k => charAt chars (startIdx + k))
    if slice ≠ protocol then false
    else if startIdx == windowStart then true
    else !(charAt chars (startIdx - 1)).isAlphanum

-- Rewinds from `atIdx` (an `@` position) over the local part: alnum/`.`/`+`/`-`/`_`, or a
-- literal `mailto:`/`xmpp:` marker at a word boundary (absorbed whole, then rewinding
-- continues *past* it too -- letters of "mailto"/"xmpp" are alnum, so they're naturally
-- consumed one at a time by the same rule on the next steps). Bounded by `windowStart`: never
-- rewinds into text already spoken for by an earlier match (or before the start of the run).
def rewindEmailLocal : Nat → Array Char → Nat → Nat → Nat → Bool → Bool → Nat × Bool × Bool
  | 0, _, _, _, rewindLen, isXmpp, autoMailto => (rewindLen, isXmpp, autoMailto)
  | fuel + 1, chars, windowStart, atIdx, rewindLen, isXmpp, autoMailto =>
    if atIdx - rewindLen ≤ windowStart then (rewindLen, isXmpp, autoMailto)
    else
      let idx := atIdx - rewindLen - 1
      let c := charAt chars idx
      if emailLocalChar c then
        rewindEmailLocal fuel chars windowStart atIdx (rewindLen + 1) isXmpp autoMailto
      else if c == ':' && matchProtocolBefore chars windowStart idx "mailto:".toList then
        rewindEmailLocal fuel chars windowStart atIdx (rewindLen + 1) isXmpp false
      else if c == ':' && matchProtocolBefore chars windowStart idx "xmpp:".toList then
        rewindEmailLocal fuel chars windowStart atIdx (rewindLen + 1) true false
      else (rewindLen, isXmpp, autoMailto)

-- Scans forward from `atIdx` (an `@` position) over the domain: alnum, `-`/`_`, `/` (only
-- inside an `xmpp:` address, for its optional resource part), or a `.` that's itself followed
-- by another alnum char (an internal, "real" dot -- `np` counts these; a trailing or doubled
-- dot isn't one, and ends the scan instead).
def scanEmailDomainGo : Nat → Array Char → Nat → Bool → Nat → Nat → Nat × Nat
  | 0, _, _, _, linkEnd, np => (linkEnd, np)
  | fuel + 1, chars, atIdx, isXmpp, linkEnd, np =>
    if atIdx + linkEnd ≥ chars.size then (linkEnd, np)
    else
      let c := charAt chars (atIdx + linkEnd)
      if c.isAlphanum then scanEmailDomainGo fuel chars atIdx isXmpp (linkEnd + 1) np
      else if c == '.' && atIdx + linkEnd + 1 < chars.size && (charAt chars (atIdx + linkEnd + 1)).isAlphanum then
        scanEmailDomainGo fuel chars atIdx isXmpp (linkEnd + 1) (np + 1)
      else if c == '/' && isXmpp then scanEmailDomainGo fuel chars atIdx isXmpp (linkEnd + 1) np
      else if c ≠ '-' && c ≠ '_' then (linkEnd, np)
      else scanEmailDomainGo fuel chars atIdx isXmpp (linkEnd + 1) np

-- One attempt at an email match anchored on the `@` at `atIdx`. `none` on rejection (too short
-- a local part, no domain, no internal dot, or a domain not ending in a letter/`.`) --
-- the caller then just moves on to the next `@`, rather than replicating the source's exact
-- "skip past the whole failed span" offset arithmetic: since a rejected attempt never produces
-- a link either way, the only way this could observably differ is an `@`-heavy adversarial
-- input finding a *different* (but still spec-shaped) match than cmark-gfm would; not
-- exercised by the vendored example suite.
def tryEmailAt (chars : Array Char) (windowStart atIdx : Nat) : Option (Nat × Nat × String) :=
  let (rewindLen, isXmpp, autoMailto) :=
    rewindEmailLocal (atIdx - windowStart + 1) chars windowStart atIdx 0 false true
  if rewindLen == 0 then none
  else
    let (domainLen, np) := scanEmailDomainGo (chars.size + 1) chars atIdx isXmpp 1 0
    let lastChar := charAt chars (atIdx + domainLen - 1)
    let lastOk := domainLen ≥ 2 && (lastChar.isAlpha || lastChar == '.')
    if domainLen < 2 || np == 0 || !lastOk then none
    else
      let spanStart := atIdx - rewindLen
      let span := (List.range (rewindLen + domainLen)).map (fun k => charAt chars (spanStart + k))
      let trimmed := autolinkDelim span
      if trimmed.isEmpty then none
      else
        let href := (if autoMailto then "mailto:" else "") ++ String.ofList trimmed
        some (spanStart, trimmed.length, href)

def scanEmailGo : Nat → Array Char → Nat → Nat → List RawInline
  | 0, chars, pos, _ => [.text (String.ofList (chars.toList.drop pos))]
  | fuel + 1, chars, pos, searchFrom =>
    match (chars.toList.drop searchFrom).findIdx? (· == '@') with
    | none => [.text (String.ofList (chars.toList.drop pos))]
    | some relIdx =>
      let atIdx := searchFrom + relIdx
      match tryEmailAt chars pos atIdx with
      | some (spanStart, spanLen, href) =>
        let before := String.ofList ((chars.toList.drop pos).take (spanStart - pos))
        let matchedText := String.ofList ((chars.toList.drop spanStart).take spanLen)
        let linkNode := RawInline.link href none [.text matchedText]
        let rest := scanEmailGo fuel chars (spanStart + spanLen) (spanStart + spanLen)
        if before.isEmpty then linkNode :: rest else .text before :: linkNode :: rest
      | none => scanEmailGo fuel chars pos (atIdx + 1)

def scanEmail (s : String) : List RawInline :=
  let chars := s.toList.toArray
  scanEmailGo (chars.size + 1) chars 0 0

-- The full autolink pass over one already-consolidated run of plain text: bare/scheme URLs
-- first, then emails within whatever plain text is left over -- mirrors cmark-gfm's own
-- two-pass split (`www_match`/`url_match` during tokenization, `postprocess_text` afterward).
def autolinkText (s : String) : List RawInline :=
  (scanUrlWww s).flatMap fun
    | .text t => scanEmail t
    | other => [other]

-- Merges adjacent `.text` siblings into one (mirrors cmark-gfm's own
-- `cmark_consolidate_text_nodes`, run before its email pass, so a run split across e.g. a
-- backslash escape still autolinks as one), without touching non-text nodes or recursing into
-- their content -- that happens separately, in `autolinkListRawF` below.
def mergeAdjacentTextGo (pendingRev : List String) : List RawInline → List RawInline
  | [] => if pendingRev.isEmpty then [] else [.text (String.join pendingRev.reverse)]
  | .text s :: rest => mergeAdjacentTextGo (s :: pendingRev) rest
  | i :: rest =>
    let flushed := if pendingRev.isEmpty then [] else [.text (String.join pendingRev.reverse)]
    flushed ++ i :: mergeAdjacentTextGo [] rest

def mergeAdjacentText (l : List RawInline) : List RawInline := mergeAdjacentTextGo [] l

-- Total node count, used to size fuel for the mutual recursion below (same reason
-- `Block.count`/`listCount` need it: the nested `List RawInline` fields hide the structural
-- relationship from the termination checker once `mergeAdjacentText` sits between the two
-- recursive calls).
mutual
def rawInlineCount : RawInline → Nat
  | .emph content | .strong content | .strikethrough content | .image _ _ content =>
    1 + rawInlineListCount content
  | .link _ _ content => 1 + rawInlineListCount content
  | _ => 1

-- The extra `1 +` (on top of `rawInlineCount i`, itself always ≥ 1) accounts for the fuel
-- `autolinkListRawF` spends on its own list-cons step, separately from what `autolinkInlineF`
-- spends dispatching on the node itself -- mirrors `rawBlockListCount`'s identical `1 +`
-- (`CommonMark/Parser/Block.lean`), needed for the same reason.
def rawInlineListCount : List RawInline → Nat
  | [] => 0
  | i :: rest => 1 + rawInlineCount i + rawInlineListCount rest
end

-- Runs `autolinkText` over each merged `.text` run and recurses into emphasis/strong/
-- strikethrough/image content, but not into an already-formed `.link`'s content (matching
-- cmark-gfm's own `in_link` skip in `postprocess`, so link text never gets re-linked).
mutual
def autolinkInlineF : Nat → RawInline → List RawInline
  | 0, i => [i]
  | _ + 1, .text s => autolinkText s
  | fuel + 1, .emph content => [.emph (autolinkListF fuel content)]
  | fuel + 1, .strong content => [.strong (autolinkListF fuel content)]
  | fuel + 1, .strikethrough content => [.strikethrough (autolinkListF fuel content)]
  | fuel + 1, .image dest title content => [.image dest title (autolinkListF fuel content)]
  | _ + 1, i => [i]

def autolinkListRawF : Nat → List RawInline → List RawInline
  | 0, l => l
  | _ + 1, [] => []
  | fuel + 1, i :: rest => autolinkInlineF fuel i ++ autolinkListRawF fuel rest

def autolinkListF (fuel : Nat) (l : List RawInline) : List RawInline :=
  autolinkListRawF fuel (mergeAdjacentText l)
end

def autolinkList (l : List RawInline) : List RawInline :=
  autolinkListF (rawInlineListCount l + 1) l

-- Mirrors `renderBlockNodesF`/`renderBlocksNodeF`'s fuel-bounded mutual recursion (same reason:
-- the doubly-nested `list` items hide the structural relationship from the termination
-- checker).
mutual
def autolinkBlockF : Nat → Block → Block
  | 0, b => b
  | _ + 1, .paragraph content => .paragraph (autolinkList content)
  | _ + 1, .heading level content => .heading level (autolinkList content)
  | _ + 1, .codeBlock info lit => .codeBlock info lit
  | fuel + 1, .blockQuote content => .blockQuote (autolinkBlockListF fuel content)
  | fuel + 1, .list kind tight items => .list kind tight (autolinkItemsF fuel items)
  | _ + 1, .thematicBreak => .thematicBreak
  | _ + 1, .htmlBlock s => .htmlBlock s
  | _ + 1, .table header alignments rows =>
    .table (header.map autolinkList) alignments (rows.map (List.map autolinkList))

def autolinkBlockListF : Nat → List Block → List Block
  | 0, bs => bs
  | _ + 1, [] => []
  | fuel + 1, b :: rest => autolinkBlockF fuel b :: autolinkBlockListF fuel rest

def autolinkItemsF : Nat → List (Option Bool × List Block) → List (Option Bool × List Block)
  | 0, items => items
  | _ + 1, [] => []
  | fuel + 1, (checked, c) :: rest => (checked, autolinkBlockListF fuel c) :: autolinkItemsF fuel rest
end

/-- Extended-autolink post-process over a whole `Document`: bare/scheme URLs and bare/`mailto:`/
    `xmpp:` emails in ordinary text become links, matching GFM's `autolink` extension. -/
def autolinkDocument (doc : Document) : Document :=
  autolinkBlockListF (Block.listCount doc + 1) doc

end GFMarkdown
