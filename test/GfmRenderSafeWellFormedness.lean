-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import GfmHtmlWellFormedness
public import GfmSanitizeSafety
public import GfmAstFuelLaws

@[expose] public section

-- `RenderSafeWellFormedness.lean`'s composition, for the GFM variant. Simpler here only
-- because this variant's `Document.sanitize` already runs at the fuel `renderBlocks` uses,
-- leaving count preservation as the whole of the reconciliation.

namespace GFMarkdown

/-- A sanitized document holds no raw HTML by the very measure `renderHtml_wellFormed` takes,
    which is what discharges that theorem's hypothesis.

    `Document.hasEmbeddedHtml` negates `Block.noEmbeddedHtmlListF` run at the document's node
    count plus one, so `= false` says no `.htmlBlock` and no `.htmlInline` was found. That is
    the depth this variant's `Document.sanitize` already maps at, so unlike the CommonMark
    proof no saturation is needed; `Document.listCount_sanitize` alone lets the count taken
    here of the sanitized document stand for the count taken of `doc`. -/
theorem Document.sanitize_hasEmbeddedHtml (doc : Document) :
    Document.hasEmbeddedHtml (Document.sanitize doc) = false := by
  simp [Document.hasEmbeddedHtml, Document.listCount_sanitize,
    Document.sanitize_noEmbeddedHtml doc]

/-- `renderHtmlSafe`'s output is well-formed for every document, with no side condition. This
    is the guarantee the untrusted-input path rests on.

    `Html.WellFormedHtml .xhtml` says the string is balanced, properly nested markup in the
    dialect `renderHtml` renders at, and at `.xhtml` it additionally carries
    `Html.WellFormedAttrs` for every attribute run, so the claim is well-formed XML rather than
    merely balanced HTML. `doc` carries no hypothesis, where `renderHtml_wellFormed` needs one,
    because `Document.sanitize` removes exactly the `.htmlInline`/`.htmlBlock` leaves that
    hypothesis excludes. -/
theorem renderHtmlSafe_wellFormed (doc : Document) :
    Html.WellFormedHtml .xhtml (renderHtmlSafe doc) :=
  renderHtml_wellFormed (Document.sanitize doc) (Document.sanitize_hasEmbeddedHtml doc)

/-- The tree `htmlNodesSafe` builds holds no verbatim markup, whatever the document and whatever
    the payload. A consumer that cannot insert raw HTML, such as a virtual DOM, can rely on this
    instead of handling verbatim leaves.

    `Node.hasVerbatim` answers `true` when a node holds verbatim markup at any depth, and the
    claim quantifies over every top-level node, so nothing nested escapes it. `P` is arbitrary
    because the payload only carries attributes, which `hasVerbatim` does not inspect. As with
    `renderHtmlSafe_wellFormed`, `doc` carries no hypothesis: `Document.sanitize_hasEmbeddedHtml`
    supplies the one `renderBlocksNodeF_wellFormed` needs. -/
theorem htmlNodesSafe_noVerbatim {P : Type} [HtmlModel.HtmlPayload P] (doc : Document) :
    ∀ n ∈ htmlNodesSafe (P := P) doc, n.hasVerbatim = false := by
  have h : Block.noEmbeddedHtmlListF (Block.listCount (Document.sanitize doc) + 1)
      (Document.sanitize doc) = true := by
    simpa [Document.hasEmbeddedHtml] using Document.sanitize_hasEmbeddedHtml doc
  unfold htmlNodesSafe htmlNodes blocksNodes
  exact renderBlocksNodeF_wellFormed false _ _ h

end GFMarkdown
