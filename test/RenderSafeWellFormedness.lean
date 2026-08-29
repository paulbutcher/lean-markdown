-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HtmlWellFormedness
public import SanitizeSafety
public import AstFuelLaws

@[expose] public section

-- `HtmlWellFormedness.lean` proves `renderHtml`'s output well-formed for a document with no
-- embedded raw HTML, and `SanitizeSafety.lean` proves `Document.sanitize` produces such a
-- document. Composing them retires the hypothesis: `renderHtmlSafe`'s output is well-formed
-- for *every* document, which is the guarantee the untrusted-input path actually rests on.
--
-- The two are stated at different fuels (`Document.sanitize` maps at `Block.listCount doc`,
-- `renderBlocks` renders at `Block.listCount doc + 1`), which is what `AstFuelLaws.lean`'s
-- saturation and count-preservation lemmas reconcile.

namespace CommonMark

theorem Document.sanitize_hasEmbeddedHtml (doc : Document) :
    Document.hasEmbeddedHtml (Document.sanitize doc) = false := by
  have hsat : Document.sanitize doc
      = Block.mapListF sanitizeInline sanitizeBlock (Block.listCount doc + 1) doc :=
    Block.mapListF_saturate sanitizeInline sanitizeBlock _ _ doc (Nat.le_refl _) (Nat.le_succ _)
  have key : Block.noEmbeddedHtmlListF (Block.listCount doc + 1) (Document.sanitize doc) = true := by
    rw [hsat]
    exact (sanitizeBlockListF_ok (Block.listCount doc + 1) doc).1
  simp [Document.hasEmbeddedHtml, Document.listCount_sanitize, key]

/-- `renderHtmlSafe`'s output is well-formed for every document, with no side condition:
    `Document.sanitize` removes exactly the `.htmlInline`/`.htmlBlock` leaves that
    `renderHtml_wellFormed` has to exclude. At `.xhtml` (the dialect `renderHtml` renders at)
    `Html.WellFormedHtml` additionally carries `Html.WellFormedAttrs` for every attribute run,
    so this says the output is well-formed XML, not merely balanced HTML. -/
theorem renderHtmlSafe_wellFormed (doc : Document) :
    Html.WellFormedHtml .xhtml (renderHtmlSafe doc) :=
  renderHtml_wellFormed (Document.sanitize doc) (Document.sanitize_hasEmbeddedHtml doc)

end CommonMark
