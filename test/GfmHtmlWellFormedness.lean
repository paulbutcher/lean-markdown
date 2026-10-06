-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import GfmNoEmbeddedHtml

@[expose] public section

-- Mirrors `HtmlWellFormedness.lean`'s structure exactly, adapted to `GFMarkdown`'s own
-- (structurally similar but independent) `Block`/`RawInline`/renderer: `renderHtml` builds
-- its entire output through `Html.Node`'s typed constructors except for
-- `.htmlInline`/`.htmlBlock`, so a `Document` containing neither renders to well-formed HTML.
-- `GfmRenderSafeWellFormedness.lean` retires that hypothesis for `renderHtmlSafe`.

namespace GFMarkdown

open CommonMark.Parser (RawInline)

open Html

/-- Rendering a list of well-formed nodes into a string leaves the string well-formed. This is
    the step from a claim about nodes to a claim about `renderHtml`'s actual output.

    The accumulator is quantified inside the conclusion, along with the assumption that it is
    already well-formed, because the fold grows it as it goes; the top-level call starts it at
    `""`. Identical in shape to `CommonMark.foldl_render_wellFormed`, re-derived because that
    one is `private` to its module. -/
private theorem foldl_render_wellFormed {cat : Category} (dialect : Dialect)
    (l : List (Node cat)) (h : ∀ n ∈ l, Node.WellFormed n) :
    ∀ acc, WellFormedHtml dialect acc →
      WellFormedHtml dialect
        (l.foldl (fun acc n => acc ++ n.render dialect) acc) := by
  induction l with
  | nil => intro acc hacc; simpa using hacc
  | cons n rest ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    exact ih (fun n' hn' => h n' (List.mem_cons_of_mem _ hn'))
      (acc ++ n.render dialect)
      (hacc.append (Node.render_wellFormed n (h n (List.mem_cons_self ..)) dialect))

/-- Anything found in a list built by conditionally inserting `x` between `A` and `B` came from
    `A`, is `x`, or came from `B`.

    The conclusion says nothing about `cond`, which is the point: a caller holding a membership
    hypothesis lets `cond`, `A`, `B` and `x` be fixed by unification instead of restating them.
    Identical in shape to `CommonMark.mem_ite_append`, re-derived because that one is
    `private`. -/
private theorem mem_ite_append {α : Type} (cond : Bool) (A B : List α) (x n : α)
    (hn : n ∈ (if cond = true then A ++ [x] ++ B else A ++ B)) : n ∈ A ∨ n = x ∨ n ∈ B := by
  by_cases hc : cond = true
  · rw [ite_eq_left hc] at hn
    rcases List.mem_append.mp hn with hn | hn
    · rcases List.mem_append.mp hn with hn | hn
      · exact Or.inl hn
      · exact Or.inr (Or.inl (List.mem_singleton.mp hn))
    · exact Or.inr (Or.inr hn)
  · rw [ite_eq_right hc] at hn
    rcases List.mem_append.mp hn with hn | hn
    · exact Or.inl hn
    · exact Or.inr (Or.inr hn)

/-- Anything found in a list accumulated by `foldl` came from the initial accumulator or from
    one of the pieces appended along the way.

    Turning a membership in the folded result into a membership in a single `f x` is what lets
    a per-item claim be applied to it. Identical in shape to `CommonMark.foldl_append_mem`,
    re-derived because that one is `private`. -/
private theorem foldl_append_mem {α β : Type} (f : α → List β) :
    (l : List α) → (init : List β) → ∀ y ∈ l.foldl (fun acc x => acc ++ f x) init,
      y ∈ init ∨ ∃ x ∈ l, y ∈ f x
  | [], _, y, hy => Or.inl hy
  | x :: xs, init, y, hy => by
    simp only [List.foldl_cons] at hy
    rcases foldl_append_mem f xs (init ++ f x) y hy with h | h
    · rcases List.mem_append.mp h with h' | h'
      · exact Or.inl h'
      · exact Or.inr ⟨x, List.mem_cons_self .., h'⟩
    · obtain ⟨x', hx', hy'⟩ := h
      exact Or.inr ⟨x', List.mem_cons_of_mem _ hx', hy'⟩

/-- Anything found in a list with newlines interleaved through it is either one of those
    newlines or one of the original nodes.

    The disjunction is all a well-formedness argument needs, since it never matters where in
    the list a node ended up, only where it came from; positions would have to be tracked to
    say more, and nothing here would use it. -/
private theorem interleaveNewlines_mem {cat : Category} :
    (l : List (Node cat)) → ∀ c ∈ interleaveNewlines l, c = ("\n" : Node cat) ∨ c ∈ l
  | [], c, hc => Or.inl (List.mem_singleton.mp hc)
  | n :: rest, c, hc => by
    simp only [interleaveNewlines, List.foldr_cons, List.mem_cons] at hc
    rcases hc with hc | hc | hc
    · exact Or.inl hc
    · exact Or.inr (hc ▸ List.mem_cons_self ..)
    · rcases interleaveNewlines_mem rest c hc with hc' | hc'
      · exact Or.inl hc'
      · exact Or.inr (List.mem_cons_of_mem _ hc')

/-- Interleaving newlines through a list of well-formed nodes leaves every node in it
    well-formed.

    The conclusion is stated over the interleaved list rather than the original because that
    is what the table constructors below hand to `Node.elementOf_wellFormed`; the added nodes
    are text, which is well-formed unconditionally, so the hypothesis need only cover the
    nodes that were already there. -/
private theorem interleaveNewlines_wellFormed {cat : Category} (nodes : List (Node cat))
    (h : ∀ n ∈ nodes, Node.WellFormed n) : ∀ c ∈ interleaveNewlines nodes, Node.WellFormed c := by
  intro c hc
  rcases interleaveNewlines_mem nodes c hc with hc' | hc'
  · subst hc'; exact Node.text_wellFormed "\n"
  · exact h c hc'

/-- A heading element is well-formed whenever its children are.

    Quantifying over `level : Fin 6` covers all six tags in one claim, `headingNode` choosing
    the tag by level and building every branch the same way, as phrasing children inside a flow
    element; nothing but the children can decide the question, hence the single hypothesis. -/
private theorem headingNode_wellFormed (level : Fin 6) (children : List (Node .phrasing))
    (h : ∀ c ∈ children, Node.WellFormed c) : Node.WellFormed (headingNode level children) := by
  unfold headingNode; split <;> exact Node.elementOf_wellFormed .flow .phrasing _ _ _ h

/-- A `<ul>` is well-formed whenever its items are.

    `attrs` carries no hypothesis because `Html.HtmlAttrs` is a typed record whose rendering is
    a well-formed attribute run by construction; only the children can break the claim. -/
private theorem ul_wellFormed (children : List (Node .listItem)) (attrs : Html.HtmlAttrs)
    (h : ∀ c ∈ children, Node.WellFormed c) : Node.WellFormed (Html.ul children attrs) := by
  unfold Html.ul; exact Node.elementOf_wellFormed .flow .listItem "ul" _ _ h

/-- An `<ol>` is well-formed whenever its items are.

    Stated separately from the `<ul>` claim because `Html.ol` takes `Html.OlAttrs`, a different
    attribute type carrying `start`; as there, the attributes need no hypothesis and the
    children need one. -/
private theorem ol_wellFormed (children : List (Node .listItem)) (attrs : Html.OlAttrs)
    (h : ∀ c ∈ children, Node.WellFormed c) : Node.WellFormed (Html.ol children attrs) := by
  unfold Html.ol; exact Node.elementOf_wellFormed .flow .listItem "ol" _ _ h

/-- The list element the renderer builds is well-formed whenever its items are, whichever kind
    of list it is and whether or not it carries a `start`.

    The proposition inlines the very `match` the renderer performs rather than naming a helper,
    so it applies to the renderer's own expression; its three branches, `<ul>`, plain `<ol>`,
    and `<ol start="n">`, are covered together, including the one whose attribute value is
    computed from the list's starting number. -/
private theorem listNode_wellFormed (kind : CommonMark.ListType) (children : List (Node .listItem))
    (h : ∀ c ∈ children, Node.WellFormed c) :
    Node.WellFormed (match kind with
      | .bullet _ => Html.ul children
      | .ordered start _ =>
        if start == 1 then Html.ol children else Html.ol children { start := toString start }) := by
  cases kind with
  | bullet _ => exact ul_wellFormed _ _ h
  | ordered start _ =>
    by_cases hs : start == 1
    · simpa [hs] using ol_wellFormed children {} h
    · simpa [hs] using ol_wellFormed children { start := toString start } h

/-- The nodes a task-list checkbox renders to are well-formed, checked or unchecked.

    `checked : Option Bool` covers all three cases at once, `none` producing no nodes at all
    and making the claim vacuous there, which is right: a list item that is not a task item
    gets no checkbox. What is produced is a void `<input>` and a literal space, and
    `Node.voidElement_wellFormed` asks nothing of the element's attributes, so the raw
    attribute run the renderer builds cannot break the claim. -/
private theorem checkboxNodes_wellFormed (checked : Option Bool) :
    ∀ c ∈ checkboxNodes checked, Node.WellFormed c := by
  cases checked with
  | none => intro c hc; simp [checkboxNodes] at hc
  | some isChecked =>
    intro c hc
    unfold checkboxNodes at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | hc
    · subst hc
      exact Node.toFlow_wellFormed (Node.voidElement_wellFormed .phrasing "input" _)
    · subst hc; exact Node.text_wellFormed " "

-- Mirrors `CommonMark.inlineNodes_wellFormed`/`inlineListNodes_wellFormed`'s own mutual
-- structural recursion case-for-case, extended with the `.strikethrough`/`<del>` case.
mutual
/-- Rendering an inline node that carries no raw HTML yields only well-formed nodes.

    The claim is about every node in the list `inlineNodes` returns, an inline being able to
    render as more than one, `.lineBreak` giving both a `<br/>` and a newline. The hypothesis
    travels down to a node's content in the recursive cases, `.strikethrough` and its `<del>`
    among them, and does real work in exactly one place, `.htmlInline`, where it is
    contradictory and the case closes. -/
theorem inlineNodes_wellFormed :
    (i : RawInline) → RawInline.noEmbeddedHtml i = true → ∀ n ∈ inlineNodes i, Node.WellFormed n
  | .text s, _ => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    exact Node.text_wellFormed s
  | .code s, _ => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    exact Node.element_wellFormed .phrasing "code" _ _ (by
      intro c hc; simp only [List.mem_singleton] at hc; subst hc; exact Node.text_wellFormed s)
  | .emph content, h => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    simp only [RawInline.noEmbeddedHtml] at h
    exact Node.element_wellFormed .phrasing "em" _ _ (inlineListNodes_wellFormed content h)
  | .strong content, h => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    simp only [RawInline.noEmbeddedHtml] at h
    exact Node.element_wellFormed .phrasing "strong" _ _ (inlineListNodes_wellFormed content h)
  | .link _ _ content, h => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    simp only [RawInline.noEmbeddedHtml] at h
    exact Node.transparentElement_wellFormed .phrasing "a" _ _ (inlineListNodes_wellFormed content h)
  | .image .., _ => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    exact Node.voidElement_wellFormed .phrasing "img" _
  | .htmlInline _, h => by simp [RawInline.noEmbeddedHtml] at h
  | .softBreak, _ => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    exact Node.text_wellFormed "\n"
  | .lineBreak, _ => by
    intro n hn; simp only [inlineNodes, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with hn | hn
    · subst hn; exact Node.voidElement_wellFormed .phrasing "br" _
    · subst hn; exact Node.text_wellFormed "\n"
  | .strikethrough content, h => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    simp only [RawInline.noEmbeddedHtml] at h
    exact Node.transparentElement_wellFormed .phrasing "del" _ _ (inlineListNodes_wellFormed content h)
  | .math .., _ => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    exact Node.element_wellFormed .phrasing "span" _ _ (by
      intro c hc; simp only [List.mem_singleton] at hc; subst hc
      split <;> exact Node.text_wellFormed _)

/-- Rendering a list of inline nodes that carry no raw HTML yields only well-formed nodes.

    `noEmbeddedHtmlList` is the conjunction over the elements and `inlineListNodes` is their
    renderings concatenated, so membership splits into head and tail exactly as the hypothesis
    does. This is the form the block and table cases need, all of which hold their content as
    a `List RawInline`. -/
theorem inlineListNodes_wellFormed :
    (l : List RawInline) → RawInline.noEmbeddedHtmlList l = true → ∀ n ∈ inlineListNodes l, Node.WellFormed n
  | [], _ => by intro n hn; simp [inlineListNodes] at hn
  | i :: rest, h => by
    simp only [RawInline.noEmbeddedHtmlList, Bool.and_eq_true] at h
    intro n hn
    simp only [inlineListNodes, List.mem_append] at hn
    rcases hn with hn | hn
    · exact inlineNodes_wellFormed i h.1 n hn
    · exact inlineListNodes_wellFormed rest h.2 n hn
end

/-- A table cell containing no raw HTML renders to a well-formed node.

    `isHeader` and `alignment` carry no hypotheses: the first only chooses between `<th>` and
    `<td>`, both built the same way, and the second only contributes a typed attribute, so
    neither can affect well-formedness. The content hypothesis is the same one the inline
    claim above needs, phrasing nodes being lifted into flow content within the cell. -/
private theorem tableCellNode_wellFormed (isHeader : Bool) (alignment : CommonMark.Parser.TableAlignment)
    (content : List RawInline) (h : RawInline.noEmbeddedHtmlList content = true) :
    Node.WellFormed (tableCellNode isHeader alignment content) := by
  unfold tableCellNode
  have hchildren : ∀ c ∈ (inlineListNodes content).map
      (fun (n : Node .phrasing) => (n : Node .flow)), Node.WellFormed c := by
    intro c hc
    obtain ⟨n, hn, hneq⟩ := List.mem_map.mp hc
    exact hneq ▸ Node.toFlow_wellFormed (inlineListNodes_wellFormed content h n hn)
  split
  · exact Node.elementOf_wellFormed .tableCell .flow "th" _ _ hchildren
  · exact Node.elementOf_wellFormed .tableCell .flow "td" _ _ hchildren

/-- Anything found in a `zipWith` is the function applied to some element of each list.

    The existentials are ordered so that the `b` drawn from the second list comes with its
    membership proof while the `a` does not, which is what the caller needs: alignments are
    zipped against cells, and it is the cell whose content the hypothesis is about. -/
private theorem mem_zipWith {α β γ : Type} (f : α → β → γ) :
    (as : List α) → (bs : List β) → ∀ c ∈ List.zipWith f as bs, ∃ b ∈ bs, ∃ a, c = f a b
  | [], _, c, hc => by simp at hc
  | _, [], c, hc => by simp at hc
  | a :: as, b :: bs, c, hc => by
    simp only [List.zipWith_cons_cons, List.mem_cons] at hc
    rcases hc with hc | hc
    · exact ⟨b, List.mem_cons_self .., a, hc⟩
    · obtain ⟨b', hb', a', hceq⟩ := mem_zipWith f as bs c hc
      exact ⟨b', List.mem_cons_of_mem _ hb', a', hceq⟩

/-- A table row whose cells contain no raw HTML renders to a well-formed node.

    The hypothesis is per-cell rather than about the row as a whole, matching how the row is
    built: cells are zipped against the column alignments, so the alignment list may be any
    length without weakening the claim, and the newlines interleaved between cells are text. -/
private theorem tableRowNode_wellFormed (isHeader : Bool) (alignments : List CommonMark.Parser.TableAlignment)
    (cells : List (List RawInline)) (h : ∀ content ∈ cells, RawInline.noEmbeddedHtmlList content = true) :
    Node.WellFormed (tableRowNode isHeader alignments cells) := by
  unfold tableRowNode
  apply Node.elementOf_wellFormed .tableRow .tableCell "tr" _ _
  apply interleaveNewlines_wellFormed
  intro c hc
  obtain ⟨content, hcontent, alignment, hceq⟩ := mem_zipWith (tableCellNode isHeader) alignments cells c hc
  exact hceq ▸ tableCellNode_wellFormed isHeader alignment content (h content hcontent)

/-- A table whose header and body cells contain no raw HTML renders to a well-formed node.

    Header and rows carry separate hypotheses because the renderer treats them separately,
    emitting a `<thead>` always and a `<tbody>` only when there are rows; both branches are
    covered, so an empty-bodied table is included rather than excluded. The row hypothesis is
    nested, per cell of per row, which is the shape `Block.noEmbeddedHtmlF` gives for a
    `.table`. -/
private theorem tableNode_wellFormed (header : List (List RawInline))
    (alignments : List CommonMark.Parser.TableAlignment) (rows : List (List (List RawInline)))
    (hheader : ∀ content ∈ header, RawInline.noEmbeddedHtmlList content = true)
    (hrows : ∀ row ∈ rows, ∀ content ∈ row, RawInline.noEmbeddedHtmlList content = true) :
    Node.WellFormed (tableNode header alignments rows) := by
  unfold tableNode
  have htheadNode : Node.WellFormed
      (Html.thead (interleaveNewlines [tableRowNode true alignments header])) := by
    apply Node.elementOf_wellFormed .tableSection .tableRow "thead" _ _
    apply interleaveNewlines_wellFormed
    intro c hc
    simp only [List.mem_singleton] at hc; subst hc
    exact tableRowNode_wellFormed true alignments header hheader
  split
  · exact Node.elementOf_wellFormed .flow .tableSection "table" _ _
      (interleaveNewlines_wellFormed _ (by
        intro c hc; simp only [List.mem_singleton] at hc; subst hc; exact htheadNode))
  · rename_i hrows'
    have htbodyNode : Node.WellFormed
        (Html.tbody (interleaveNewlines (rows.map (tableRowNode false alignments)))) := by
      apply Node.elementOf_wellFormed .tableSection .tableRow "tbody" _ _
      apply interleaveNewlines_wellFormed
      intro c hc
      obtain ⟨row, hrow, hceq⟩ := List.mem_map.mp hc
      exact hceq ▸ tableRowNode_wellFormed false alignments row (hrows row hrow)
    exact Node.elementOf_wellFormed .flow .tableSection "table" _ _
      (interleaveNewlines_wellFormed _ (by
        intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with hc | hc
        · subst hc; exact htheadNode
        · subst hc; exact htbodyNode))

-- Mirrors `CommonMark.renderBlockNodesF_wellFormed`/`renderBlocksNodeF_wellFormed`'s own
-- mutual, fuel-bounded recursion case-for-case, extended with `.table` (via
-- `tableNode_wellFormed`) and `.list`'s `(Option Bool × List Block)` items (via
-- `checkboxNodes_wellFormed` alongside the existing `itemPrefix`/`renderBlocksNodeF` cases).
mutual
/-- Rendering a block that carries no raw HTML yields only well-formed nodes, at whatever depth
    the renderer is working.

    One `fuel` governs both the hypothesis and the rendering, so what is assumed clean is
    exactly what will be visited; at fuel zero the renderer emits nothing and the claim is
    empty rather than false. `tight` is unconstrained, both list-spacing modes being rendered
    through the same constructors, and the constructors this variant adds are reached through
    the table and checkbox claims above. -/
theorem renderBlockNodesF_wellFormed :
    (tight : Bool) → (fuel : Nat) → (b : Block) → Block.noEmbeddedHtmlF fuel b = true →
      ∀ n ∈ renderBlockNodesF tight fuel b, Node.WellFormed n
  | _, 0, _, _ => by intro n hn; simp [renderBlockNodesF] at hn
  | tight, _ + 1, .paragraph content, h => by
    simp only [Block.noEmbeddedHtmlF] at h
    simp only [renderBlockNodesF]
    split
    · intro n hn
      obtain ⟨n', hn', hneq⟩ := List.mem_map.mp hn
      exact hneq ▸ Node.toFlow_wellFormed (inlineListNodes_wellFormed content h n' hn')
    · intro n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with hn | hn
      · subst hn
        exact Node.elementOf_wellFormed .flow .phrasing "p" _ _ (inlineListNodes_wellFormed content h)
      · subst hn; exact Node.text_wellFormed "\n"
  | _, _ + 1, .heading level content, h => by
    simp only [Block.noEmbeddedHtmlF] at h
    intro n hn
    simp only [renderBlockNodesF, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with hn | hn
    · subst hn; exact headingNode_wellFormed level _ (inlineListNodes_wellFormed content h)
    · subst hn; exact Node.text_wellFormed "\n"
  | _, _ + 1, .codeBlock _ literal, _ => by
    intro n hn
    unfold renderBlockNodesF at hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with hn | hn
    · subst hn
      exact Node.elementOf_wellFormed .flow .phrasing "pre" _ _ (by
        intro c hc; simp only [List.mem_singleton] at hc; subst hc
        exact Node.element_wellFormed .phrasing "code" _ _ (by
          intro c' hc'; simp only [List.mem_singleton] at hc'; subst hc'
          exact Node.text_wellFormed literal))
    · subst hn; exact Node.text_wellFormed "\n"
  | _, _ + 1, .thematicBreak, _ => by
    intro n hn
    simp only [renderBlockNodesF, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with hn | hn
    · subst hn; exact Node.voidElement_wellFormed .flow "hr" _
    · subst hn; exact Node.text_wellFormed "\n"
  | _, _ + 1, .htmlBlock _, h => by simp [Block.noEmbeddedHtmlF] at h
  | _, fuel + 1, .blockQuote content, h => by
    simp only [Block.noEmbeddedHtmlF] at h
    intro n hn
    simp only [renderBlockNodesF, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with hn | hn
    · subst hn
      exact Node.element_wellFormed .flow "blockquote" _ _ (by
        intro c hc
        simp only [List.mem_cons] at hc
        rcases hc with hc | hc
        · subst hc; exact Node.text_wellFormed "\n"
        · exact renderBlocksNodeF_wellFormed false fuel content h c hc)
    · subst hn; exact Node.text_wellFormed "\n"
  | _, fuel + 1, .list kind isTight items, h => by
    simp only [Block.noEmbeddedHtmlF] at h
    have hitems : ∀ p ∈ items, Block.noEmbeddedHtmlListF fuel p.2 = true := List.all_eq_true.mp h
    have hitemNode : ∀ p ∈ items, Node.WellFormed (itemNode isTight fuel p.1 p.2) := by
      intro (checked, content) hp
      unfold itemNode
      exact Node.elementOf_wellFormed .listItem .flow "li" _ _ (by
        intro c hc
        simp only [List.mem_append] at hc
        rcases hc with (hc | hc) | hc
        · exact checkboxNodes_wellFormed checked c hc
        · unfold itemPrefix at hc; split at hc <;> simp_all [Node.text_wellFormed]
        · exact renderBlocksNodeF_wellFormed isTight fuel content (hitems (checked, content) hp) c hc)
    have hitemNodes : ∀ c ∈ (("\n" : Node .listItem) ::
        items.foldl (fun acc (checked, content) =>
          acc ++ [itemNode isTight fuel checked content, "\n"]) []),
        Node.WellFormed c := by
      intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with hc | hc
      · subst hc; exact Node.text_wellFormed "\n"
      · rcases foldl_append_mem
          (fun (p : Option Bool × List Block) => [itemNode isTight fuel p.1 p.2, "\n"]) items [] c hc
          with hc' | ⟨p, hp, hc'⟩
        · simp at hc'
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
          rcases hc' with hc' | hc'
          · subst hc'; exact hitemNode p hp
          · subst hc'; exact Node.text_wellFormed "\n"
    intro n hn
    unfold renderBlockNodesF at hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with hn | hn
    · subst hn
      exact listNode_wellFormed kind _ hitemNodes
    · subst hn; exact Node.text_wellFormed "\n"
  | _, _ + 1, .table header alignments rows, h => by
    simp only [Block.noEmbeddedHtmlF, Bool.and_eq_true] at h
    have hheader : ∀ content ∈ header, RawInline.noEmbeddedHtmlList content = true := List.all_eq_true.mp h.1
    have hrows : ∀ row ∈ rows, ∀ content ∈ row, RawInline.noEmbeddedHtmlList content = true := by
      intro row hrow
      exact List.all_eq_true.mp (List.all_eq_true.mp h.2 row hrow)
    intro n hn
    simp only [renderBlockNodesF, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with hn | hn
    · subst hn; exact tableNode_wellFormed header alignments rows hheader hrows
    · subst hn; exact Node.text_wellFormed "\n"

/-- Rendering a list of blocks that carry no raw HTML yields only well-formed nodes, at
    whatever depth the renderer is working.

    The shape a `Document` has, and so the form the theorem below instantiates. As above the
    hypothesis and the rendering share one `fuel`, and the separator nodes the renderer inserts
    between blocks are text, which is where `mem_ite_append` above is spent. -/
theorem renderBlocksNodeF_wellFormed :
    (tight : Bool) → (fuel : Nat) → (bs : List Block) → Block.noEmbeddedHtmlListF fuel bs = true →
      ∀ n ∈ renderBlocksNodeF tight fuel bs, Node.WellFormed n
  | _, 0, _, _ => by intro n hn; simp [renderBlocksNodeF] at hn
  | _, _ + 1, [], _ => by intro n hn; simp [renderBlocksNodeF] at hn
  | tight, fuel + 1, b :: rest, h => by
    simp only [Block.noEmbeddedHtmlListF, Bool.and_eq_true] at h
    unfold renderBlocksNodeF
    dsimp only
    intro n hn
    rcases mem_ite_append _ _ _ _ _ hn with hn | hn | hn
    · exact renderBlockNodesF_wellFormed tight fuel b h.1 n hn
    · subst hn; exact Node.text_wellFormed "\n"
    · exact renderBlocksNodeF_wellFormed tight fuel rest h.2 n hn
end

/-- A document that embeds no raw HTML renders to well-formed HTML: balanced tags, no stray
    `<` or `>` outside tag delimiters, and every attribute run a sequence of quoted
    `name="value"` pairs. The exclusion is necessary, not a proof-technique limitation; see
    `CommonMark.renderHtml_wellFormed` for why it cannot be dropped.

    `doc.hasEmbeddedHtml = false` is the document-level form of the predicate the lemmas above
    carry, read at a fuel `Document.noEmbeddedHtmlListF_saturate` (`GfmAstFuelLaws.lean`) shows
    sufficient, so the hypothesis cannot be satisfied by a reading that stopped short. The
    conclusion is about the rendered string rather than the node list, which is what
    `foldl_render_wellFormed` bridges, and at `.xhtml`, the dialect `renderHtml` uses,
    `Html.WellFormedHtml` also carries `Html.WellFormedAttrs`, making the claim well-formed XML
    rather than merely balanced HTML. -/
theorem renderHtml_wellFormed (doc : Document) (h : doc.hasEmbeddedHtml = false) :
    Html.WellFormedHtml .xhtml (renderHtml doc) := by
  have h' : Block.noEmbeddedHtmlListF (Block.listCount doc + 1) doc = true := by
    simpa [Document.hasEmbeddedHtml] using h
  unfold renderHtml renderBlocks
  exact foldl_render_wellFormed .xhtml _ (renderBlocksNodeF_wellFormed false _ doc h')
    "" (WellFormedHtml.text (by simp))

end GFMarkdown
