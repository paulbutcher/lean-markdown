-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import HtmlRenderer

@[expose] public section

-- `Node.render_wellFormed` asks only that a node hold no verbatim markup, and `hasVerbatim`
-- is computed over the node's erasure. These let `simp` push that question through an element's
-- children, so a renderer's case reduces to the same question about each child.

namespace Html

/-- Erasing a list packed as `Nodes` gives the erasure of each node in turn. `HtmlNode.elem`
    packs an element's children with `Nodes.ofList`, so this turns a question about an
    element's erased children into one about the list the renderer built.

    The left side erases the packed list and the right side maps `erase` over the original;
    equality says packing neither adds, drops nor reorders a node. -/
@[simp] theorem nodes_ofList_erase {P : Type} {cat : Category} (l : List (HtmlModel.Web.Node P (.html cat))) :
    (HtmlModel.Nodes.ofList l).erase = l.map HtmlModel.Node.erase := by
  induction l with
  | nil => rfl
  | cons n l ih => simp [HtmlModel.Nodes.ofList, HtmlModel.Nodes.erase, ih]

/-- A list of nodes erases to trees with no verbatim markup exactly when each node does. This is
    the step from an element's children to a hypothesis about each child.

    `Tree.anyVerbatim` answers `true` when some tree in the list holds verbatim markup at any
    depth, and the right side asks the same of each node's erasure in turn; the two sides are
    the same question asked of the whole list and of its members. -/
@[simp] theorem anyVerbatim_map_erase {P : Type} {cat : Category} (l : List (HtmlModel.Web.Node P (.html cat))) :
    HtmlModel.Tree.anyVerbatim (l.map HtmlModel.Node.erase) = false ↔
      ∀ n ∈ l, n.erase.hasVerbatim = false := by
  induction l with
  | nil => simp [HtmlModel.Tree.anyVerbatim]
  | cons n l ih => simp [HtmlModel.Tree.anyVerbatim, ih]

/-- Concatenated children hold verbatim markup exactly when either part does. A renderer
    commonly builds an element's children by appending a prefix to the rendered content, and
    this splits the question along that seam.

    `Tree.anyVerbatim` answers `true` when some tree in the list holds verbatim markup at any
    depth; on the left it reads the concatenation, on the right each part, joined by `||`
    because a tree is in the concatenation exactly when it is in one of the parts. -/
@[simp] theorem anyVerbatim_append {P : Type} (ts us : List (HtmlModel.Web.Tree P)) :
    HtmlModel.Tree.anyVerbatim (ts ++ us) =
      (HtmlModel.Tree.anyVerbatim ts || HtmlModel.Tree.anyVerbatim us) := by
  induction ts with
  | nil => simp [HtmlModel.Tree.anyVerbatim]
  | cons t ts ih => simp [HtmlModel.Tree.anyVerbatim, ih, Bool.or_assoc]

end Html
