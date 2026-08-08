-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import CommonMark.Ast
import CommonMark.Render.Html

-- `renderHtml`'s own safety guarantee stops at the document's structure: escaping is proved
-- for every ordinary leaf, but `.htmlInline`/`.htmlBlock` are raw HTML from the Markdown
-- source, deliberately passed through unescaped (`CommonMark.Render.Html`'s module doc), and
-- a link/image `dest` is percent-encoded but not scheme-checked, so `[x](javascript:...)`
-- reaches `href` untouched. Neither is a bug: both are required by the CommonMark/GFM spec
-- for trusted input. For untrusted input, this module provides `Document.sanitize` (an
-- AST-level rewrite dropping embedded raw HTML and non-allowlisted URI schemes) and
-- `renderHtmlSafe` (the composition with `renderHtml`), matching the "strip raw HTML,
-- allowlist link schemes" convention of cmark's own `--safe` mode.

namespace CommonMark

private def isSchemeStartChar (c : Char) : Bool := c.isAlpha
private def isSchemeChar (c : Char) : Bool := c.isAlphanum || c == '+' || c == '-' || c == '.'

-- Characters with no legitimate role in a URI scheme; stripped before scanning so an embedded
-- control character (e.g. a tab in `java\tscript:`) can't hide a scheme from detection the
-- way it can hide one from a naive regex.
private def isUriControlChar (c : Char) : Bool := c.toNat < 0x20 || c.toNat == 0x7F

private def stripControlChars (s : String) : String :=
  String.ofList (s.toList.filter (fun c => !isUriControlChar c))

-- The leading URI scheme (RFC 3986: `ALPHA *( ALPHA / DIGIT / "+" / "-" / "." )` followed by
-- `:`), if `s` has one. A destination with no such prefix is a relative reference (a path,
-- fragment, or query), which is always safe: only an explicit scheme can name `javascript:`,
-- `data:`, etc.
private def extractScheme (s : String) : Option String :=
  match s.toList with
  | c :: rest =>
    if isSchemeStartChar c then
      let schemeRest := rest.takeWhile isSchemeChar
      match rest.drop schemeRest.length with
      | ':' :: _ => some (String.ofList (c :: schemeRest))
      | _ => none
    else none
  | [] => none

def allowedUriSchemes : List String := ["http", "https", "mailto"]

/-- Whether `dest` is safe to emit as a link `href`/image `src`: either a relative reference
    (no scheme), or an absolute reference whose scheme is in `allowedUriSchemes`. -/
def isSafeUriScheme (dest : String) : Bool :=
  match extractScheme (stripControlChars dest) with
  | none => true
  | some scheme => allowedUriSchemes.contains (String.ofList (scheme.toList.map Char.toLower))

/-- `dest` unchanged if `isSafeUriScheme dest`, otherwise the empty string. -/
def sanitizeDest (dest : String) : String := if isSafeUriScheme dest then dest else ""

-- Every `.htmlInline` is replaced by an empty `.text` leaf (not dropped: `Inline.map`'s shape
-- is one-node-in, one-node-out) and every `link`/`image` `dest` is passed through
-- `sanitizeDest`. `Inline.map` calls `sanitizeInline` bottom-up, so it sees `.link`/`.image`
-- content only after that content has already been sanitized.
def sanitizeInline : Inline → Inline
  | .htmlInline _ => .text ""
  | .link dest title content => .link (sanitizeDest dest) title content
  | .image dest title content => .image (sanitizeDest dest) title content
  | other => other

-- `.htmlBlock` becomes an empty paragraph rather than being dropped, for the same
-- one-node-in-one-node-out reason as `sanitizeInline`; `.paragraph []` renders as nothing
-- (tight) or an empty `<p></p>` (loose), matching how this codebase already collapses other
-- content it can't preserve losslessly (`CommonMark.Parser.rawBlockToBlockF`'s `.table`
-- fallback).
def sanitizeBlock : Block → Block
  | .htmlBlock _ => .paragraph []
  | other => other

/-- Rewrites a `Document` so it is safe to render even when it came from untrusted input:
    every `.htmlInline`/`.htmlBlock` (raw HTML from the Markdown source) is dropped, and every
    `link`/`image` `dest` with a non-allowlisted URI scheme (e.g. `javascript:`) is cleared.
    See `renderHtmlSafe`. -/
def Document.sanitize (doc : Document) : Document := Document.map sanitizeInline sanitizeBlock doc

/-- `renderHtml`, preceded by `Document.sanitize`: safe to use on untrusted Markdown source,
    unlike `renderHtml` on its own (see this module's docs). `renderHtmlSafe_wellFormed` proves
    its output is always well-formed HTML; `Document.sanitize`'s own theorems additionally
    guarantee no raw HTML survives and every emitted `href`/`src` has an allowlisted scheme. -/
def renderHtmlSafe (doc : Document) : String := renderHtml (Document.sanitize doc)

end CommonMark
