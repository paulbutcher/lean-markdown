-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import Html

@[expose] public section

-- `Node.render_wellFormed` asks only that a node hold no verbatim markup, and `hasVerbatim`
-- is computed over the node's erasure. These let `simp` push that question through a tag's
-- children, so a renderer's case reduces to the same question about each child.

namespace Html

/-- Erasing a list packed as `Nodes` gives the erasure of each node in turn. Every tag
    taking a list of children packs it with `Nodes.ofList`, so this turns a question about a
    tag's erased children into one about the list the renderer built.

    The left side erases the packed list and the right side maps `erase` over the original;
    equality says packing neither adds, drops nor reorders a node. -/
@[simp] theorem nodes_ofList_erase {cat : Category} (l : List (Node cat)) :
    (HtmlModel.Nodes.ofList l).erase = l.map HtmlModel.Node.erase := by
  induction l with
  | nil => rfl
  | cons n l ih => simp [HtmlModel.Nodes.ofList, HtmlModel.Nodes.erase, ih]

/-- A list of nodes erases to trees with no verbatim markup exactly when each node does. This is
    the step from an element's children to a hypothesis about each child.

    `Tree.anyVerbatim` answers `true` when some tree in the list holds verbatim markup at any
    depth, and the right side asks the same of each node's erasure in turn; the two sides are
    the same question asked of the whole list and of its members. -/
@[simp] theorem anyVerbatim_map_erase {cat : Category} (l : List (Node cat)) :
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
@[simp] theorem anyVerbatim_append (ts us : List Tree) :
    HtmlModel.Tree.anyVerbatim (ts ++ us) =
      (HtmlModel.Tree.anyVerbatim ts || HtmlModel.Tree.anyVerbatim us) := by
  induction ts with
  | nil => simp [HtmlModel.Tree.anyVerbatim]
  | cons t ts ih => simp [HtmlModel.Tree.anyVerbatim, ih, Bool.or_assoc]

end Html
