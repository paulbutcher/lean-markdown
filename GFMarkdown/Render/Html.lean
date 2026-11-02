-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import GFMarkdown.Render.Nodes
public import CommonMark.Render.Html

@[expose] public section

namespace GFMarkdown

def renderBlocks (tight : Bool) (blocks : List Block) : String :=
  CommonMark.renderNodes (blocksNodes tight blocks)

/-- Renders a `Document` to HTML. Shares `CommonMark.renderHtml`'s escaping/safety guarantees
    (both are rendered by lean-html-renderer); the `<table>`/`<thead>`/`<tbody>` and `<del>`
    structure is built the same way. -/
def renderHtml (doc : Document) : String :=
  CommonMark.renderNodes (htmlNodes doc)

end GFMarkdown
