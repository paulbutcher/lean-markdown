-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import CommonMark.Render.Nodes
public import HtmlRenderer

@[expose] public section

namespace CommonMark

/-- `nodes` rendered at the dialect, and with the payload, the spec's output takes. -/
def renderNodes {cat : HtmlModel.Html.Cat} (nodes : List (HtmlNode Html.Attrs cat)) : String :=
  nodes.foldl (fun acc n => acc ++ Html.Node.render n .xhtml) ""

-- Public alongside `plainTextOf`/`plainTextOfInlines`, for the same reason: a
-- Markdown-extension AST that embeds `List Inline` at its leaves (e.g. a table cell's
-- content) needs to render that embedded content identically to this renderer.
def renderInline (i : Inline) : String := renderNodes (inlineNodes i)

def renderInlines (content : List Inline) : String := renderNodes (inlineListNodes content)

def renderBlocks (tight : Bool) (blocks : List Block) : String := renderNodes (blocksNodes tight blocks)

/-- Renders a `Document` to HTML per the spec's exact escaping and formatting rules.
    No AST leaf's string content can produce unescaped `<`, `>`, `&`, or unescaped `"`
    inside an attribute in the output: every leaf reaches the output only through
    `Html.escape`/`Html.Attrs.render`, proved safe by `Html.escape_safe`/
    `Html.Attrs.render_safe` (github.com/paulbutcher/lean-html-renderer), or as a verbatim
    leaf for `.htmlInline`/`.htmlBlock` passthrough, where HTML from the Markdown source is
    meant to reach the output unescaped. -/
def renderHtml (doc : Document) : String := renderNodes (htmlNodes doc)

end CommonMark
