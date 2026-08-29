-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import CommonMark

@[expose] public section

-- `.htmlInline`/`.htmlBlock` are the only leaves `renderHtml` passes through unescaped
-- (`Html.Node.unsafeRaw`), so their absence is both the hypothesis under which
-- `HtmlWellFormedness.lean` proves the output well-formed and the property
-- `SanitizeSafety.lean` proves `Document.sanitize` establishes. Sharing one definition is what
-- lets `RenderSafeWellFormedness.lean` compose those two directly.
--
-- Fuel-bounded for `Block` and structural for `Inline`, mirroring `Block.mapF` and
-- `renderBlocksNodeF` so that proofs can induct case-for-case alongside either.

namespace CommonMark

mutual
def Inline.noEmbeddedHtml : Inline → Bool
  | .htmlInline _ => false
  | .emph content => Inline.noEmbeddedHtmlList content
  | .strong content => Inline.noEmbeddedHtmlList content
  | .link _ _ content => Inline.noEmbeddedHtmlList content
  | .image _ _ content => Inline.noEmbeddedHtmlList content
  | .text _ | .code _ | .math .. | .softBreak | .lineBreak => true

def Inline.noEmbeddedHtmlList : List Inline → Bool
  | [] => true
  | i :: rest => Inline.noEmbeddedHtml i && Inline.noEmbeddedHtmlList rest
end

mutual
def Block.noEmbeddedHtmlF : Nat → Block → Bool
  | 0, _ => true
  | _ + 1, .paragraph content => Inline.noEmbeddedHtmlList content
  | _ + 1, .heading _ content => Inline.noEmbeddedHtmlList content
  | _ + 1, .codeBlock .. => true
  | _ + 1, .thematicBreak => true
  | _ + 1, .htmlBlock _ => false
  | fuel + 1, .blockQuote content => Block.noEmbeddedHtmlListF fuel content
  | fuel + 1, .list _ _ items => items.all (Block.noEmbeddedHtmlListF fuel)

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

end CommonMark
