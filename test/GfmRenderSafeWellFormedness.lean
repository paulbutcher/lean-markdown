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

theorem Document.sanitize_hasEmbeddedHtml (doc : Document) :
    Document.hasEmbeddedHtml (Document.sanitize doc) = false := by
  simp [Document.hasEmbeddedHtml, Document.listCount_sanitize,
    Document.sanitize_noEmbeddedHtml doc]

/-- `renderHtmlSafe`'s output is well-formed for every document, with no side condition:
    `Document.sanitize` removes exactly the `.htmlInline`/`.htmlBlock` leaves that
    `renderHtml_wellFormed` has to exclude. At `.xhtml` (the dialect `renderHtml` renders at)
    `Html.WellFormedHtml` additionally carries `Html.WellFormedAttrs` for every attribute run,
    so this says the output is well-formed XML, not merely balanced HTML. -/
theorem renderHtmlSafe_wellFormed (doc : Document) :
    Html.WellFormedHtml .xhtml (renderHtmlSafe doc) :=
  renderHtml_wellFormed (Document.sanitize doc) (Document.sanitize_hasEmbeddedHtml doc)

end GFMarkdown
