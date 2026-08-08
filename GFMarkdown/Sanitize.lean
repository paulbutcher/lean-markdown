-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import GFMarkdown.Ast
import GFMarkdown.Render.Html
import CommonMark.Sanitize

-- Mirrors `CommonMark.Sanitize`'s `Document.sanitize`/`renderHtmlSafe` for the GFM variant:
-- see that module's docs for why `renderHtml` alone isn't safe on untrusted input. Written as
-- its own fuel-bounded pass over `GFMarkdown.Block`/`RawInline` (mirroring `TagFilter.lean`'s
-- structure) rather than through a generic map combinator, since `GFMarkdown.Ast` has none
-- (unlike `CommonMark.Ast`'s `Document.map`). Reuses `CommonMark.isSafeUriScheme`/
-- `sanitizeDest` rather than redefining the scheme allowlist.

namespace GFMarkdown

open CommonMark.Parser (RawInline)
open CommonMark (sanitizeDest)

-- Mirrors `TagFilter.lean`'s `filterInline`/`filterInlineList`: `RawInline` recurses
-- structurally (like `CommonMark.Inline`), so no fuel is needed here.
mutual
def sanitizeInline : RawInline → RawInline
  | .htmlInline _ => .text ""
  | .emph content => .emph (sanitizeInlineList content)
  | .strong content => .strong (sanitizeInlineList content)
  | .strikethrough content => .strikethrough (sanitizeInlineList content)
  | .link dest title content => .link (sanitizeDest dest) title (sanitizeInlineList content)
  | .image dest title content => .image (sanitizeDest dest) title (sanitizeInlineList content)
  | other => other

def sanitizeInlineList : List RawInline → List RawInline
  | [] => []
  | i :: rest => sanitizeInline i :: sanitizeInlineList rest
end

-- Mirrors `TagFilter.lean`'s `filterBlockF`/`filterBlockListF`'s fuel-bounded mutual
-- recursion (same reason: the doubly-nested `list` items hide the structural relationship
-- from the termination checker). `.htmlBlock` becomes an empty paragraph rather than being
-- dropped, matching `CommonMark.sanitizeBlock`'s own choice (see its docs). Unlike
-- `TagFilter.lean`'s `filterItemsF`, `list`'s items are rewritten with a plain `.map` sharing
-- one `fuel` value across every item (mirroring `CommonMark.Block.mapF`'s own `.list` case),
-- not a further per-item peel: every item independently needs at most as much fuel as the
-- deepest single item, not the sum across all of them.
mutual
def sanitizeBlockF : Nat → Block → Block
  | 0, b => b
  | _ + 1, .paragraph content => .paragraph (sanitizeInlineList content)
  | _ + 1, .heading level content => .heading level (sanitizeInlineList content)
  | _ + 1, .codeBlock info literal => .codeBlock info literal
  | fuel + 1, .blockQuote content => .blockQuote (sanitizeBlockListF fuel content)
  | fuel + 1, .list kind tight items =>
    .list kind tight (items.map (fun (checked, c) => (checked, sanitizeBlockListF fuel c)))
  | _ + 1, .thematicBreak => .thematicBreak
  | _ + 1, .htmlBlock _ => .paragraph []
  | _ + 1, .table header alignments rows =>
    .table (header.map sanitizeInlineList) alignments (rows.map (List.map sanitizeInlineList))

def sanitizeBlockListF : Nat → List Block → List Block
  | 0, bs => bs
  | _ + 1, [] => []
  | fuel + 1, b :: rest => sanitizeBlockF fuel b :: sanitizeBlockListF fuel rest
end

/-- Rewrites a `Document` so it is safe to render even when it came from untrusted input, same
    contract as `CommonMark.Document.sanitize`: every `.htmlInline`/`.htmlBlock` is dropped,
    and every `link`/`image` `dest` with a non-allowlisted URI scheme is cleared. Uses the same
    fuel convention as `tagFilterDocument` (`TagFilter.lean`). -/
def Document.sanitize (doc : Document) : Document :=
  sanitizeBlockListF (Block.listCount doc + 1) doc

/-- `renderHtml`, preceded by `Document.sanitize`: safe to use on untrusted Markdown source,
    unlike `renderHtml` on its own. See `CommonMark.Sanitize`'s module docs. -/
def renderHtmlSafe (doc : Document) : String := renderHtml (Document.sanitize doc)

end GFMarkdown
