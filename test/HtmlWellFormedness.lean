-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import NoEmbeddedHtml

@[expose] public section

-- `renderHtml` builds its entire output through `Html.Node`'s typed constructors except
-- for `.htmlInline`/`.htmlBlock`, which use `Html.Node.unsafeRaw` to pass literal HTML from
-- the Markdown source through verbatim -- the one place `Html.Node.WellFormed` can fail to
-- hold. So a `Document` containing no `.htmlInline`/`.htmlBlock` anywhere renders to
-- well-formed HTML: balanced tags, no stray `<`/`>` outside of tag syntax, and every
-- attribute run a sequence of quoted `name="value"` pairs (`Html.WellFormedHtml`, which at
-- the `.xhtml` dialect `renderHtml` uses makes that output well-formed XML). The proofs
-- mirror `renderBlockNodesF`/`renderBlocksNodeF`'s own structure so they can induct
-- case-for-case alongside the renderer.
--
-- `RenderSafeWellFormedness.lean` retires the no-embedded-HTML hypothesis for
-- `renderHtmlSafe`, which sanitizes it away.

namespace CommonMark

open Html

/-- Rendering a list of well-formed nodes into a string leaves the string well-formed. This is
    the step from a claim about nodes to a claim about `renderHtml`'s actual output.

    The accumulator is quantified inside the conclusion, along with the assumption that it is
    already well-formed, because the fold grows it as it goes and the induction has to speak
    about every intermediate value; the top-level call starts it at `""`. Each step is
    `WellFormedHtml.append` of what is built so far with `Node.render_wellFormed` for the next
    node, so well-formedness being closed under append is what carries the invariant. -/
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
    hypothesis lets `cond`, `A`, `B` and `x` be fixed by unification instead of restating them,
    where splitting on a multi-way `&&` condition would have to reconstruct it. The three-way
    disjunction is weaker than a case analysis and enough, `x` being a separator that is
    well-formed either way. -/
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

-- Mirrors `inlineNodes`/`inlineListNodes`'s own mutual structural recursion case-for-case,
-- so each case's induction hypothesis is exactly the fact needed about its recursive call.
mutual
/-- Rendering an inline node that carries no raw HTML yields only well-formed nodes.

    The claim is about every node in the list `inlineNodes` returns, an inline being able to
    render as more than one, `.lineBreak` giving both a `<br/>` and a newline. The hypothesis
    travels down to a node's content in the recursive cases and does real work in exactly one
    place, `.htmlInline`, where it is contradictory and the case closes; the leaf cases ignore
    it, being built from typed constructors that cannot produce anything ill-formed. -/
theorem inlineNodes_wellFormed :
    (i : Inline) → Inline.noEmbeddedHtml i = true → ∀ n ∈ inlineNodes i, Node.WellFormed n
  | .text s, _ => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    exact Node.text_wellFormed s
  | .code s, _ => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    exact Node.element_wellFormed .phrasing "code" _ _ (by
      intro c hc; simp only [List.mem_singleton] at hc; subst hc; exact Node.text_wellFormed s)
  | .emph content, h => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    simp only [Inline.noEmbeddedHtml] at h
    exact Node.element_wellFormed .phrasing "em" _ _ (inlineListNodes_wellFormed content h)
  | .strong content, h => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    simp only [Inline.noEmbeddedHtml] at h
    exact Node.element_wellFormed .phrasing "strong" _ _ (inlineListNodes_wellFormed content h)
  | .link _ _ content, h => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    simp only [Inline.noEmbeddedHtml] at h
    exact Node.element_wellFormed .phrasing "a" _ _ (inlineListNodes_wellFormed content h)
  | .image .., _ => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    exact Node.voidElement_wellFormed .phrasing "img" _
  | .htmlInline _, h => by simp [Inline.noEmbeddedHtml] at h
  | .softBreak, _ => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    exact Node.text_wellFormed "\n"
  | .lineBreak, _ => by
    intro n hn; simp only [inlineNodes, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with hn | hn
    · subst hn; exact Node.voidElement_wellFormed .phrasing "br" _
    · subst hn; exact Node.text_wellFormed "\n"
  | .math .., _ => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    exact Node.element_wellFormed .phrasing "span" _ _ (by
      intro c hc; simp only [List.mem_singleton] at hc; subst hc
      split <;> exact Node.text_wellFormed _)

/-- Rendering a list of inline nodes that carry no raw HTML yields only well-formed nodes.

    `noEmbeddedHtmlList` is the conjunction over the elements and `inlineListNodes` is their
    renderings concatenated, so membership splits into head and tail exactly as the hypothesis
    does. This is the form the block cases need, `.paragraph` and `.heading` content being a
    `List Inline`. -/
theorem inlineListNodes_wellFormed :
    (l : List Inline) → Inline.noEmbeddedHtmlList l = true → ∀ n ∈ inlineListNodes l, Node.WellFormed n
  | [], _ => by intro n hn; simp [inlineListNodes] at hn
  | i :: rest, h => by
    simp only [Inline.noEmbeddedHtmlList, Bool.and_eq_true] at h
    intro n hn
    simp only [inlineListNodes, List.mem_append] at hn
    rcases hn with hn | hn
    · exact inlineNodes_wellFormed i h.1 n hn
    · exact inlineListNodes_wellFormed rest h.2 n hn
end

/-- A heading element is well-formed whenever its children are.

    Quantifying over `level : Fin 6` covers all six tags in one claim, `headingNode` choosing
    the tag by level and building every branch the same way, as phrasing children inside a flow
    element; nothing but the children can decide the question, hence the single hypothesis. -/
private theorem headingNode_wellFormed (level : Fin 6) (children : List (Node .phrasing))
    (h : ∀ c ∈ children, Node.WellFormed c) : Node.WellFormed (headingNode level children) := by
  unfold headingNode; split <;> exact Node.elementOf_wellFormed .flow .phrasing _ _ _ h

/-- A `<ul>` is well-formed whenever its items are.

    `attrs` carries no hypothesis because `Html.HtmlAttrs` is a typed record whose rendering is
    a well-formed attribute run by construction; only the children can break the claim, hence
    the single hypothesis about them. -/
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
private theorem listNode_wellFormed (kind : ListType) (children : List (Node .listItem))
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

/-- Anything found in a list accumulated by `foldl` came from the initial accumulator or from
    one of the pieces appended along the way.

    Turning a membership in the folded result into a membership in a single `f x` is what lets
    the caller apply a per-item claim, which is how `itemNode`'s fold is reasoned about without
    generalizing the accumulator by hand at each step. `init` is quantified so the induction can
    hand the tail a grown accumulator. -/
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

-- Mirrors `renderBlockNodesF`/`renderBlocksNodeF`/`itemNode`'s own mutual, fuel-bounded
-- recursion case-for-case, exactly as `Block.noEmbeddedHtmlF`/`Block.noEmbeddedHtmlListF` were defined to.
mutual
/-- Rendering a block that carries no raw HTML yields only well-formed nodes, at whatever depth
    the renderer is working.

    One `fuel` governs both the hypothesis and the rendering, so what is assumed clean is
    exactly what will be visited; at fuel zero the renderer emits nothing and the claim is
    empty rather than false. `tight` is unconstrained, both list-spacing modes being rendered
    through the same constructors. -/
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
    have hitems : ∀ c ∈ items, Block.noEmbeddedHtmlListF fuel c = true := List.all_eq_true.mp h
    have hitemNode : ∀ content ∈ items, Node.WellFormed (itemNode isTight fuel content) := by
      intro content hcontent
      unfold itemNode
      exact Node.elementOf_wellFormed .listItem .flow "li" _ _ (by
        intro c hc
        simp only [List.mem_append] at hc
        rcases hc with hc | hc
        · unfold itemPrefix at hc; split at hc <;> simp_all [Node.text_wellFormed]
        · exact renderBlocksNodeF_wellFormed isTight fuel content (hitems content hcontent) c hc)
    have hitemNodes : ∀ c ∈ (("\n" : Node .listItem) ::
        items.foldl (fun acc content => acc ++ [itemNode isTight fuel content, "\n"]) []),
        Node.WellFormed c := by
      intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with hc | hc
      · subst hc; exact Node.text_wellFormed "\n"
      · rcases foldl_append_mem (fun content => [itemNode isTight fuel content, "\n"]) items [] c hc
          with hc' | ⟨content, hcontent, hc'⟩
        · simp at hc'
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
          rcases hc' with hc' | hc'
          · subst hc'; exact hitemNode content hcontent
          · subst hc'; exact Node.text_wellFormed "\n"
    intro n hn
    unfold renderBlockNodesF at hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with hn | hn
    · subst hn
      exact listNode_wellFormed kind _ hitemNodes
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
    `name="value"` pairs. The exclusion is not a proof-technique limitation but the real
    boundary: `renderHtml` passes `.htmlBlock`/`.htmlInline` content through unescaped, so a raw
    `<` in the source really can leave the output unbalanced.

    `doc.hasEmbeddedHtml = false` is the document-level form of the predicate the lemmas above
    carry, saturated at a depth past the document's own so that nothing escapes it. The
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

end CommonMark
