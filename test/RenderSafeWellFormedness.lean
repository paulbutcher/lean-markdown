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

/-- A sanitized document holds no raw HTML by the very measure `renderHtml_wellFormed` takes,
    which is what discharges that theorem's hypothesis.

    `Document.hasEmbeddedHtml` negates `Block.noEmbeddedHtmlListF` run at the document's node
    count plus one, so `= false` says no `.htmlBlock` and no `.htmlInline` was found, with a
    level of depth to spare. That spare level is the whole difficulty: `sanitizeBlockListF_ok`
    holds at the depth `Document.sanitize` mapped at, `Block.mapListF_saturate` supplies the
    extra one, and `Document.listCount_sanitize` lets the count taken here of the sanitized
    document stand for the count taken of `doc`. -/
theorem Document.sanitize_hasEmbeddedHtml (doc : Document) :
    Document.hasEmbeddedHtml (Document.sanitize doc) = false := by
  have hsat : Document.sanitize doc
      = Block.mapListF sanitizeInline sanitizeBlock (Block.listCount doc + 1) doc :=
    Block.mapListF_saturate sanitizeInline sanitizeBlock _ _ doc (Nat.le_refl _) (Nat.le_succ _)
  have key : Block.noEmbeddedHtmlListF (Block.listCount doc + 1) (Document.sanitize doc) = true := by
    rw [hsat]
    exact (sanitizeBlockListF_ok (Block.listCount doc + 1) doc).1
  simp [Document.hasEmbeddedHtml, Document.listCount_sanitize, key]

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

end CommonMark
