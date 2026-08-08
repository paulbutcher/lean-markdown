-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import CommonMark

-- `Document.sanitize` (`CommonMark.Sanitize`) is meant to make `renderHtmlSafe`'s output safe
-- to serve from untrusted Markdown source: no embedded raw HTML, and no link/image `dest`
-- with a non-allowlisted URI scheme. This proves both, mirroring `HtmlWellFormedness.lean`'s
-- own `noHtml`-style predicates and fuel-bounded mutual-induction structure, but stated with
-- an explicit fuel argument matching `Document.sanitize`'s own (`Block.listCount doc`) rather
-- than recomputing fuel from the sanitized document's own shape: `Block.mapListF`'s fuel
-- threading and these predicates' fuel threading are already the same recursion shape, so
-- using the construction fuel directly for observation avoids needing a separate
-- `Block.listCount`-is-preserved-by-`Block.mapF` lemma.

namespace CommonMark

mutual
def Inline.noEmbeddedHtml : Inline → Bool
  | .htmlInline _ => false
  | .emph content => Inline.noEmbeddedHtmlList content
  | .strong content => Inline.noEmbeddedHtmlList content
  | .link _ _ content => Inline.noEmbeddedHtmlList content
  | .image _ _ content => Inline.noEmbeddedHtmlList content
  | .text _ | .code _ | .softBreak | .lineBreak => true

def Inline.noEmbeddedHtmlList : List Inline → Bool
  | [] => true
  | i :: rest => Inline.noEmbeddedHtml i && Inline.noEmbeddedHtmlList rest
end

mutual
def Inline.allDestsSafe : Inline → Bool
  | .link dest _ content => isSafeUriScheme dest && Inline.allDestsSafeList content
  | .image dest _ content => isSafeUriScheme dest && Inline.allDestsSafeList content
  | .emph content => Inline.allDestsSafeList content
  | .strong content => Inline.allDestsSafeList content
  | .text _ | .code _ | .htmlInline _ | .softBreak | .lineBreak => true

def Inline.allDestsSafeList : List Inline → Bool
  | [] => true
  | i :: rest => Inline.allDestsSafe i && Inline.allDestsSafeList rest
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

mutual
def Block.allDestsSafeF : Nat → Block → Bool
  | 0, _ => true
  | _ + 1, .paragraph content => Inline.allDestsSafeList content
  | _ + 1, .heading _ content => Inline.allDestsSafeList content
  | _ + 1, .codeBlock .. => true
  | _ + 1, .thematicBreak => true
  | _ + 1, .htmlBlock _ => true
  | fuel + 1, .blockQuote content => Block.allDestsSafeListF fuel content
  | fuel + 1, .list _ _ items => items.all (Block.allDestsSafeListF fuel)

def Block.allDestsSafeListF : Nat → List Block → Bool
  | 0, _ => true
  | _ + 1, [] => true
  | fuel + 1, b :: rest => Block.allDestsSafeF fuel b && Block.allDestsSafeListF fuel rest
end

private theorem isSafeUriScheme_sanitizeDest (dest : String) :
    isSafeUriScheme (sanitizeDest dest) = true := by
  unfold sanitizeDest
  split
  · assumption
  · decide

-- Mirrors `Inline.map`/`Inline.mapList`'s own structural (fuel-free) mutual recursion
-- case-for-case: `sanitizeInline`'s only special cases are `.htmlInline`/`.link`/`.image`,
-- everything else passes through `Inline.map` unchanged.
mutual
theorem sanitizeInline_ok : (i : Inline) →
    Inline.noEmbeddedHtml (Inline.map sanitizeInline i) = true ∧
    Inline.allDestsSafe (Inline.map sanitizeInline i) = true
  | .text _ => by simp [Inline.map, sanitizeInline, Inline.noEmbeddedHtml, Inline.allDestsSafe]
  | .code _ => by simp [Inline.map, sanitizeInline, Inline.noEmbeddedHtml, Inline.allDestsSafe]
  | .htmlInline _ => by
    simp [Inline.map, sanitizeInline, Inline.noEmbeddedHtml, Inline.allDestsSafe]
  | .softBreak => by
    simp [Inline.map, sanitizeInline, Inline.noEmbeddedHtml, Inline.allDestsSafe]
  | .lineBreak => by
    simp [Inline.map, sanitizeInline, Inline.noEmbeddedHtml, Inline.allDestsSafe]
  | .emph content => by
    simp only [Inline.map, sanitizeInline, Inline.noEmbeddedHtml, Inline.allDestsSafe]
    exact sanitizeInlineList_ok content
  | .strong content => by
    simp only [Inline.map, sanitizeInline, Inline.noEmbeddedHtml, Inline.allDestsSafe]
    exact sanitizeInlineList_ok content
  | .link dest _ content => by
    simp only [Inline.map, sanitizeInline, Inline.noEmbeddedHtml, Inline.allDestsSafe,
      Bool.and_eq_true]
    exact ⟨(sanitizeInlineList_ok content).1,
      isSafeUriScheme_sanitizeDest dest, (sanitizeInlineList_ok content).2⟩
  | .image dest _ content => by
    simp only [Inline.map, sanitizeInline, Inline.noEmbeddedHtml, Inline.allDestsSafe,
      Bool.and_eq_true]
    exact ⟨(sanitizeInlineList_ok content).1,
      isSafeUriScheme_sanitizeDest dest, (sanitizeInlineList_ok content).2⟩

theorem sanitizeInlineList_ok : (l : List Inline) →
    Inline.noEmbeddedHtmlList (Inline.mapList sanitizeInline l) = true ∧
    Inline.allDestsSafeList (Inline.mapList sanitizeInline l) = true
  | [] => by simp [Inline.mapList, Inline.noEmbeddedHtmlList, Inline.allDestsSafeList]
  | i :: rest => by
    simp only [Inline.mapList, Inline.noEmbeddedHtmlList, Inline.allDestsSafeList,
      Bool.and_eq_true]
    exact ⟨⟨(sanitizeInline_ok i).1, (sanitizeInlineList_ok rest).1⟩,
      (sanitizeInline_ok i).2, (sanitizeInlineList_ok rest).2⟩
end

-- Mirrors `Block.mapF`/`Block.mapListF`'s own fuel-bounded mutual recursion case-for-case
-- (same shape `renderBlockNodesF_wellFormed` mirrors in `HtmlWellFormedness.lean`), proving
-- both properties together since the case split is identical either way.
mutual
theorem sanitizeBlockF_ok : (fuel : Nat) → (b : Block) →
    Block.noEmbeddedHtmlF fuel (Block.mapF sanitizeInline sanitizeBlock fuel b) = true ∧
    Block.allDestsSafeF fuel (Block.mapF sanitizeInline sanitizeBlock fuel b) = true
  | 0, _ => by simp [Block.noEmbeddedHtmlF, Block.allDestsSafeF]
  | _ + 1, .paragraph content => by
    simp only [Block.mapF, sanitizeBlock, Block.noEmbeddedHtmlF, Block.allDestsSafeF]
    exact sanitizeInlineList_ok content
  | _ + 1, .heading _ content => by
    simp only [Block.mapF, sanitizeBlock, Block.noEmbeddedHtmlF, Block.allDestsSafeF]
    exact sanitizeInlineList_ok content
  | _ + 1, .codeBlock .. => by
    simp [Block.mapF, sanitizeBlock, Block.noEmbeddedHtmlF, Block.allDestsSafeF]
  | _ + 1, .thematicBreak => by
    simp [Block.mapF, sanitizeBlock, Block.noEmbeddedHtmlF, Block.allDestsSafeF]
  | _ + 1, .htmlBlock _ => by
    simp [Block.mapF, sanitizeBlock, Block.noEmbeddedHtmlF, Block.allDestsSafeF,
      Inline.noEmbeddedHtmlList, Inline.allDestsSafeList]
  | fuel + 1, .blockQuote content => by
    simp only [Block.mapF, sanitizeBlock, Block.noEmbeddedHtmlF, Block.allDestsSafeF]
    exact sanitizeBlockListF_ok fuel content
  | fuel + 1, .list _ _ items => by
    simp only [Block.mapF, sanitizeBlock, Block.noEmbeddedHtmlF, Block.allDestsSafeF,
      List.all_eq_true]
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩ <;>
      · obtain ⟨c', hc', rfl⟩ := List.mem_map.mp hc
        first
          | exact (sanitizeBlockListF_ok fuel c').1
          | exact (sanitizeBlockListF_ok fuel c').2

theorem sanitizeBlockListF_ok : (fuel : Nat) → (bs : List Block) →
    Block.noEmbeddedHtmlListF fuel (Block.mapListF sanitizeInline sanitizeBlock fuel bs) = true ∧
    Block.allDestsSafeListF fuel (Block.mapListF sanitizeInline sanitizeBlock fuel bs) = true
  | 0, _ => by simp [Block.noEmbeddedHtmlListF, Block.allDestsSafeListF]
  | _ + 1, [] => by simp [Block.mapListF, Block.noEmbeddedHtmlListF, Block.allDestsSafeListF]
  | fuel + 1, b :: rest => by
    simp only [Block.mapListF, Block.noEmbeddedHtmlListF, Block.allDestsSafeListF,
      Bool.and_eq_true]
    exact ⟨⟨(sanitizeBlockF_ok fuel b).1, (sanitizeBlockListF_ok fuel rest).1⟩,
      (sanitizeBlockF_ok fuel b).2, (sanitizeBlockListF_ok fuel rest).2⟩
end

/-- `Document.sanitize doc` embeds no raw HTML (`.htmlInline`/`.htmlBlock`): every leaf that
    would otherwise reach `renderHtml`'s output through `Html.Node.unsafeRaw` has been
    removed. -/
theorem Document.sanitize_noEmbeddedHtml (doc : Document) :
    Block.noEmbeddedHtmlListF (Block.listCount doc) (Document.sanitize doc) = true :=
  (sanitizeBlockListF_ok (Block.listCount doc) doc).1

/-- Every `link`/`image` `dest` in `Document.sanitize doc` has a URI scheme in
    `allowedUriSchemes` (or none at all, i.e. a relative reference). -/
theorem Document.sanitize_allDestsSafe (doc : Document) :
    Block.allDestsSafeListF (Block.listCount doc) (Document.sanitize doc) = true :=
  (sanitizeBlockListF_ok (Block.listCount doc) doc).2

end CommonMark
