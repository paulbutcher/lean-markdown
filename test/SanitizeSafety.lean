-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import NoEmbeddedHtml

@[expose] public section

-- `Document.sanitize` (`CommonMark.Sanitize`) is meant to make `renderHtmlSafe`'s output safe
-- to serve from untrusted Markdown source: no embedded raw HTML, and no link/image `dest`
-- with a non-allowlisted URI scheme. This proves both, over `NoEmbeddedHtml.lean`'s shared
-- predicate and a destination-checking one of the same fuel-bounded shape. The underlying
-- claims are left general in their fuel argument so that `RenderSafeWellFormedness.lean` can
-- instantiate them at the fuel the renderer picks rather than the one `Document.sanitize`
-- itself ran at.

namespace CommonMark

mutual
def Inline.allDestsSafe : Inline → Bool
  | .link dest _ content => isSafeUriScheme dest && Inline.allDestsSafeList content
  | .image dest _ content => isSafeUriScheme dest && Inline.allDestsSafeList content
  | .emph content => Inline.allDestsSafeList content
  | .strong content => Inline.allDestsSafeList content
  | .text _ | .code _ | .math .. | .htmlInline _ | .softBreak | .lineBreak => true

def Inline.allDestsSafeList : List Inline → Bool
  | [] => true
  | i :: rest => Inline.allDestsSafe i && Inline.allDestsSafeList rest
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

/-- `sanitizeDest` never yields a destination unsafe to emit as an `href`/`src`, whatever it
    is handed.

    The proposition says that because `isSafeUriScheme` is this codebase's definition of safe
    to emit, an allowlisted scheme or no scheme at all, and because `dest` is universally
    quantified with no hypothesis on it: the claim covers hostile input, `javascript:alert(1)`
    included, and not only input that was already safe. -/
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
/-- Sanitizing an inline node leaves no raw HTML and no unsafe destination anywhere within
    it, at any depth.

    The proposition says that of `Inline.map sanitizeInline i`, that is `i` with
    `sanitizeInline` applied at every node, which is what ends up in the sanitized document;
    `sanitizeInline i` alone would rewrite only the root. `Inline.noEmbeddedHtml` answers
    `false` only at `.htmlInline` and otherwise recurses into `emph`/`strong`/`link`/`image`
    content, so `= true` says none survives; `Inline.allDestsSafe` recurses the same way and
    answers `isSafeUriScheme dest` at each `.link`/`.image`, so `= true` says every
    destination in the tree is safe. -/
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
  | .math .. => by
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

/-- Sanitizing a list of inline nodes leaves no raw HTML and no unsafe destination anywhere
    within any of them, at any depth.

    The proposition says that of `Inline.mapList sanitizeInline l` through the `...List`
    predicates, which are the conjunctions of their node-level counterparts over the elements.
    That is the form the claim above needs of a node's children, `Inline.map` descending into
    them through `Inline.mapList`, and the form the block cases below need of `.paragraph` and
    `.heading` content. -/
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
/-- Sanitizing a block leaves no raw HTML and no unsafe destination in it, as deep as the
    sanitizing itself went.

    The proposition says that of `Block.mapF ... fuel b`, `b` rewritten to a depth of `fuel`
    levels, by running both checks at a depth of `fuel` levels too. Either check alone is weak,
    since running out of levels makes it answer `true` without looking; the strength is in the
    two numbers being the same one. `Block.mapF` and both predicates spend a level per level of
    nesting over an identical case split, so a check stops exactly where the rewrite stopped,
    and every node the rewrite could have altered is one the check looked at. -/
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

/-- Sanitizing a list of blocks, which is what a `Document` is, leaves no raw HTML and no
    unsafe destination in any of them, as deep as the sanitizing itself went.

    `Document.sanitize doc` is by definition
    `Block.mapListF sanitizeInline sanitizeBlock (Block.listCount doc) doc`, so the proposition
    read at `fuel := Block.listCount doc` is already the two theorems below; leaving `fuel`
    quantified is what lets other callers read it at a depth of their own. -/
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
    would otherwise reach `renderHtml`'s output through `Html.Node.unsafeRaw` has been removed.

    The proposition says that because those two constructors are the only ones
    `Block.noEmbeddedHtmlListF` answers `false` on, the second through the inline predicate it
    defers to, so `= true` is exactly "neither occurs". Its first argument bounds how deep the
    reading goes, and `Document.noEmbeddedHtmlListF_saturate` (`AstFuelLaws.lean`) shows
    `Block.listCount doc` sufficient: no larger fuel gives a different answer, so the verdict
    here is not one reached by stopping short of something. -/
theorem Document.sanitize_noEmbeddedHtml (doc : Document) :
    Block.noEmbeddedHtmlListF (Block.listCount doc) (Document.sanitize doc) = true :=
  (sanitizeBlockListF_ok (Block.listCount doc) doc).1

/-- Every `link`/`image` `dest` in `Document.sanitize doc` has a URI scheme in
    `allowedUriSchemes` (or none at all, i.e. a relative reference), so nothing can reach an
    `href`/`src` that `renderHtml`, which percent-encodes a destination but never inspects its
    scheme, would pass through unexamined.

    The proposition says that because `Block.allDestsSafeListF` answers `isSafeUriScheme dest`
    at every `.link` and `.image` it reaches, nested inline content included, and `true`
    elsewhere. -/
theorem Document.sanitize_allDestsSafe (doc : Document) :
    Block.allDestsSafeListF (Block.listCount doc) (Document.sanitize doc) = true :=
  (sanitizeBlockListF_ok (Block.listCount doc) doc).2

end CommonMark
