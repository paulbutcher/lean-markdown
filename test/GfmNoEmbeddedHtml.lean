-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import GFMarkdown

@[expose] public section

-- `NoEmbeddedHtml.lean`'s predicates, adapted to `GFMarkdown`'s own (structurally similar but
-- independent) `Block`/`RawInline`, and shared by `GfmHtmlWellFormedness.lean` and
-- `GfmSanitizeSafety.lean` for the same reason.

namespace GFMarkdown

open CommonMark.Parser (RawInline)

mutual
def RawInline.noEmbeddedHtml : RawInline → Bool
  | .htmlInline _ => false
  | .emph content => RawInline.noEmbeddedHtmlList content
  | .strong content => RawInline.noEmbeddedHtmlList content
  | .link _ _ content => RawInline.noEmbeddedHtmlList content
  | .image _ _ content => RawInline.noEmbeddedHtmlList content
  | .strikethrough content => RawInline.noEmbeddedHtmlList content
  | .text _ | .code _ | .math .. | .softBreak | .lineBreak => true

def RawInline.noEmbeddedHtmlList : List RawInline → Bool
  | [] => true
  | i :: rest => RawInline.noEmbeddedHtml i && RawInline.noEmbeddedHtmlList rest
end

mutual
def Block.noEmbeddedHtmlF : Nat → Block → Bool
  | 0, _ => true
  | _ + 1, .paragraph content => RawInline.noEmbeddedHtmlList content
  | _ + 1, .heading _ content => RawInline.noEmbeddedHtmlList content
  | _ + 1, .codeBlock .. => true
  | _ + 1, .thematicBreak => true
  | _ + 1, .htmlBlock _ => false
  | fuel + 1, .blockQuote content => Block.noEmbeddedHtmlListF fuel content
  | fuel + 1, .list _ _ items => items.all (fun (_, c) => Block.noEmbeddedHtmlListF fuel c)
  | _ + 1, .table header _ rows =>
    header.all RawInline.noEmbeddedHtmlList &&
      rows.all (fun row => row.all RawInline.noEmbeddedHtmlList)

def Block.noEmbeddedHtmlListF : Nat → List Block → Bool
  | 0, _ => true
  | _ + 1, [] => true
  | fuel + 1, b :: rest => Block.noEmbeddedHtmlF fuel b && Block.noEmbeddedHtmlListF fuel rest
end

/-- Whether a `Document` contains any embedded raw HTML (`.htmlInline`/`.htmlBlock`),
    the only channel through which `renderHtml` can produce output that isn't
    `Html.Node.WellFormed`. -/
def Document.hasEmbeddedHtml (doc : Document) : Bool :=
  !Block.noEmbeddedHtmlListF (Block.listCount doc + 1) doc

end GFMarkdown
