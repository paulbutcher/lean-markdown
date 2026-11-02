-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import GfmNoEmbeddedHtml
public import HtmlVerbatim

@[expose] public section

-- Mirrors `HtmlWellFormedness.lean`'s structure exactly, adapted to `GFMarkdown`'s own
-- (structurally similar but independent) `Block`/`RawInline`/renderer: the only verbatim
-- leaves in the tree `renderHtml` renders, the one thing `Html.Node.render_wellFormed` rules out,
-- are those built for `.htmlInline`/`.htmlBlock`. A `Document` containing neither renders to
-- well-formed HTML.
-- `GfmRenderSafeWellFormedness.lean` retires that hypothesis for `renderHtmlSafe`.

namespace GFMarkdown

open CommonMark.Parser (RawInline)

open Html HtmlModel CommonMark

attribute [local simp] HtmlModel.Node.hasVerbatim HtmlModel.Node.erase HtmlModel.Segs.erase
  HtmlModel.Seg.erase HtmlModel.Tree.hasVerbatim HtmlModel.Tree.anyVerbatim HtmlNode.text
  HtmlNode.newline HtmlNode.elem HtmlNode.void

/-- Rendering a list of nodes free of verbatim markup into a string leaves the string well-formed. This is
    the step from a claim about nodes to a claim about `renderHtml`'s actual output.

    The accumulator is quantified inside the conclusion, along with the assumption that it is
    already well-formed, because the fold grows it as it goes; the top-level call starts it at
    `""`. Identical in shape to `CommonMark.foldl_render_wellFormed`, re-derived because that
    one is `private` to its module. -/
private theorem foldl_render_wellFormed {cat : Category} (dialect : Dialect)
    (l : List (Node cat)) (h : ∀ n ∈ l, n.hasVerbatim = false) :
    ∀ acc, WellFormedHtml dialect acc →
      WellFormedHtml dialect
        (l.foldl (fun acc n => acc ++ Node.render n dialect) acc) := by
  induction l with
  | nil => intro acc hacc; simpa using hacc
  | cons n rest ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    exact ih (fun n' hn' => h n' (List.mem_cons_of_mem _ hn'))
      (acc ++ Node.render n dialect)
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
private theorem interleaveNewlines_mem {P : Type} {cat : Category} [HtmlModel.Web.Widens .ws (.html cat)] :
    (l : List (HtmlNode P cat)) → ∀ c ∈ interleaveNewlines l, c = (HtmlNode.newline : HtmlNode P cat) ∨ c ∈ l
  | [], c, hc => Or.inl (List.mem_singleton.mp hc)
  | n :: rest, c, hc => by
    simp only [interleaveNewlines, List.foldr_cons, List.mem_cons] at hc
    rcases hc with hc | hc | hc
    · exact Or.inl hc
    · exact Or.inr (hc ▸ List.mem_cons_self ..)
    · rcases interleaveNewlines_mem rest c hc with hc' | hc'
      · exact Or.inl hc'
      · exact Or.inr (List.mem_cons_of_mem _ hc')

/-- Interleaving newlines through a list of nodes free of verbatim markup leaves every node in
    it free of verbatim markup.

    The conclusion is stated over the interleaved list rather than the original because that
    is what the table constructors below take as children; the added nodes are whitespace,
    which holds no verbatim markup, so the hypothesis need only cover the nodes that were
    already there. -/
private theorem interleaveNewlines_wellFormed {P : Type} {cat : Category} [HtmlModel.Web.Widens .ws (.html cat)]
    (nodes : List (HtmlNode P cat)) (h : ∀ n ∈ nodes, n.hasVerbatim = false) :
    ∀ c ∈ interleaveNewlines nodes, c.hasVerbatim = false := by
  intro c hc
  rcases interleaveNewlines_mem nodes c hc with hc' | hc'
  · subst hc'; simp
  · exact h c hc'

variable {P : Type} [HtmlModel.HtmlPayload P]

/-- A heading element is free of verbatim markup whenever its children are.

    Quantifying over `level : Fin 6` covers all six tags in one claim, `headingNode` choosing
    the tag by level and building every branch the same way, as phrasing children inside a flow
    element; nothing but the children can decide the question, hence the single hypothesis. -/
private theorem headingNode_wellFormed (level : Fin 6) (children : List (HtmlNode P .phrasing))
    (h : ∀ c ∈ children, c.hasVerbatim = false) :
    (CommonMark.headingNode level children).hasVerbatim = false := by
  unfold CommonMark.headingNode
  split <;> simpa using h

/-- The list element the renderer builds is free of verbatim markup whenever its items are,
    whichever kind of list it is and whether or not it carries a `start`.

    `CommonMark.listNode` builds `<ul>`, plain `<ol>`, or `<ol start="n">` by `kind`, so
    quantifying over `kind` covers all three, including the one whose attribute value is
    computed from the list's starting number. Attributes carry no hypothesis, being the
    element's payload rather than children, which is all `hasVerbatim` inspects. -/
private theorem listNode_wellFormed (kind : CommonMark.ListType)
    (children : List (HtmlNode P .listItemOrScript)) (h : ∀ c ∈ children, c.hasVerbatim = false) :
    (CommonMark.listNode kind children).hasVerbatim = false := by
  cases kind with
  | bullet _ => simpa [CommonMark.listNode] using h
  | ordered _ _ => simpa [CommonMark.listNode] using h


/-- The nodes a task-list checkbox renders to are free of verbatim markup, checked or unchecked.

    `checked : Option Bool` covers all three cases at once, `none` producing no nodes at all
    and making the claim vacuous there, which is right: a list item that is not a task item
    gets no checkbox. What is produced is a void `<input>` and a literal space; attributes are
    not markup, so the raw attribute run the renderer builds cannot break the claim. -/
private theorem checkboxNodes_wellFormed (checked : Option Bool) :
    ∀ c ∈ checkboxNodes (P := P) checked, c.hasVerbatim = false := by
  cases checked with
  | none => simp [checkboxNodes]
  | some isChecked => simp [checkboxNodes]

-- Mirrors `CommonMark.inlineNodes_wellFormed`/`inlineListNodes_wellFormed`'s own mutual
-- structural recursion case-for-case, extended with the `.strikethrough`/`<del>` case.
mutual
/-- Rendering an inline node that carries no raw HTML yields only nodes free of verbatim
    markup.

    The claim is about every node in the list `inlineNodes` returns, an inline being able to
    render as more than one, `.lineBreak` giving both a `<br/>` and a newline. The hypothesis
    travels down to a node's content in the recursive cases, `.strikethrough` and its `<del>`
    among them, and does real work in exactly one place, `.htmlInline`, where it is
    contradictory and the case closes. -/
theorem inlineNodes_wellFormed :
    (i : RawInline) → RawInline.noEmbeddedHtml i = true → ∀ n ∈ inlineNodes (P := P) i, n.hasVerbatim = false
  | .text s, _ => by simp [inlineNodes]
  | .code s, _ => by simp [inlineNodes]
  | .emph content, h => by
    simp only [RawInline.noEmbeddedHtml] at h
    simpa [inlineNodes] using inlineListNodes_wellFormed content h
  | .strong content, h => by
    simp only [RawInline.noEmbeddedHtml] at h
    simpa [inlineNodes] using inlineListNodes_wellFormed content h
  | .link _ _ content, h => by
    simp only [RawInline.noEmbeddedHtml] at h
    simpa [inlineNodes] using inlineListNodes_wellFormed content h
  | .image .., _ => by simp [inlineNodes]
  | .htmlInline _, h => by simp [RawInline.noEmbeddedHtml] at h
  | .softBreak, _ => by simp [inlineNodes]
  | .lineBreak, _ => by simp [inlineNodes]
  | .strikethrough content, h => by
    simp only [RawInline.noEmbeddedHtml] at h
    simpa [inlineNodes] using inlineListNodes_wellFormed content h
  | .math .., _ => by simp [inlineNodes]

/-- Rendering a list of inline nodes that carry no raw HTML yields only nodes free of verbatim
    markup.

    `noEmbeddedHtmlList` is the conjunction over the elements and `inlineListNodes` is their
    renderings concatenated, so membership splits into head and tail exactly as the hypothesis
    does. This is the form the block and table cases need, all of which hold their content as
    a `List RawInline`. -/
theorem inlineListNodes_wellFormed :
    (l : List RawInline) → RawInline.noEmbeddedHtmlList l = true → ∀ n ∈ inlineListNodes (P := P) l, n.hasVerbatim = false
  | [], _ => by intro n hn; simp [inlineListNodes] at hn
  | i :: rest, h => by
    simp only [RawInline.noEmbeddedHtmlList, Bool.and_eq_true] at h
    intro n hn
    simp only [inlineListNodes, List.mem_append] at hn
    rcases hn with hn | hn
    · exact inlineNodes_wellFormed i h.1 n hn
    · exact inlineListNodes_wellFormed rest h.2 n hn
end

/-- A table cell containing no raw HTML renders to a node free of verbatim markup.

    `isHeader` and `alignment` carry no hypotheses: the first only chooses between `<th>` and
    `<td>`, both built the same way, and the second only contributes an attribute, which is not
    markup. The content hypothesis is the same one the inline claim above needs, phrasing nodes
    being lifted into flow content within the cell. -/
private theorem tableCellNode_wellFormed (isHeader : Bool) (alignment : CommonMark.Parser.TableAlignment)
    (content : List RawInline) (h : RawInline.noEmbeddedHtmlList content = true) :
    (tableCellNode (P := P) isHeader alignment content).hasVerbatim = false := by
  have hc := inlineListNodes_wellFormed (P := P) content h
  unfold tableCellNode
  split <;> simpa [Function.comp_def] using hc

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

/-- A table row whose cells contain no raw HTML renders to a node free of verbatim markup.

    The hypothesis is per-cell rather than about the row as a whole, matching how the row is
    built: cells are zipped against the column alignments, so the alignment list may be any
    length without weakening the claim, and the newlines interleaved between cells are text. -/
private theorem tableRowNode_wellFormed (isHeader : Bool) (alignments : List CommonMark.Parser.TableAlignment)
    (cells : List (List RawInline)) (h : ∀ content ∈ cells, RawInline.noEmbeddedHtmlList content = true) :
    (tableRowNode (P := P) isHeader alignments cells).hasVerbatim = false := by
  have hcells : ∀ c ∈ List.zipWith (fun a c => (Web.widen (tableCellNode isHeader a c) : HtmlNode P .tableCellOrScript))
      alignments cells, c.hasVerbatim = false := by
    intro c hc
    obtain ⟨content, hcontent, alignment, rfl⟩ := mem_zipWith _ alignments cells c hc
    simpa using tableCellNode_wellFormed isHeader alignment content (h content hcontent)
  simpa [tableRowNode] using interleaveNewlines_wellFormed _ hcells

/-- A table whose header and body cells contain no raw HTML renders to a node free of verbatim
    markup.

    Header and rows carry separate hypotheses because the renderer treats them separately,
    emitting a `<thead>` always and a `<tbody>` only when there are rows; both branches are
    covered, so an empty-bodied table is included rather than excluded. The row hypothesis is
    nested, per cell of per row, which is the shape `Block.noEmbeddedHtmlF` gives for a
    `.table`. -/
private theorem tableNode_wellFormed (header : List (List RawInline))
    (alignments : List CommonMark.Parser.TableAlignment) (rows : List (List (List RawInline)))
    (hheader : ∀ content ∈ header, RawInline.noEmbeddedHtmlList content = true)
    (hrows : ∀ row ∈ rows, ∀ content ∈ row, RawInline.noEmbeddedHtmlList content = true) :
    (tableNode (P := P) header alignments rows).hasVerbatim = false := by
  have hthead : ∀ c ∈ interleaveNewlines
      [(Web.widen (tableRowNode true alignments header) : HtmlNode P .tableRowOrScript)], c.hasVerbatim = false :=
    interleaveNewlines_wellFormed _ (by simpa using tableRowNode_wellFormed true alignments header hheader)
  have hbodyRows : ∀ c ∈ interleaveNewlines (rows.map fun r =>
      (Web.widen (tableRowNode false alignments r) : HtmlNode P .tableRowOrScript)), c.hasVerbatim = false := by
    apply interleaveNewlines_wellFormed
    intro c hc
    obtain ⟨row, hrow, rfl⟩ := List.mem_map.mp hc
    simpa using tableRowNode_wellFormed false alignments row (hrows row hrow)
  have hbody : ∀ c ∈ interleaveNewlines [(Web.widen (HtmlNode.elem .tbody .tableBody .tableRowOrScript (HtmlNode.payload []) (interleaveNewlines (rows.map fun r =>
      (Web.widen (tableRowNode false alignments r) : HtmlNode P .tableRowOrScript)))) : HtmlNode P .tableBodyOrScript)],
      c.hasVerbatim = false :=
    interleaveNewlines_wellFormed _ (by simpa using hbodyRows)
  simp only [HtmlModel.Node.hasVerbatim] at hthead hbody
  unfold tableNode
  split <;> simp_all

-- Mirrors `CommonMark.renderBlockNodesF_wellFormed`/`renderBlocksNodeF_wellFormed`'s own
-- mutual, fuel-bounded recursion case-for-case, extended with `.table` (via
-- `tableNode_wellFormed`) and `.list`'s `(Option Bool × List Block)` items (via
-- `checkboxNodes_wellFormed` alongside the existing `itemPrefix`/`renderBlocksNodeF` cases).
mutual
/-- Rendering a block that carries no raw HTML yields only nodes free of verbatim markup, at whatever depth
    the renderer is working.

    One `fuel` governs both the hypothesis and the rendering, so what is assumed clean is
    exactly what will be visited; at fuel zero the renderer emits nothing and the claim is
    empty rather than false. `tight` is unconstrained, both list-spacing modes being rendered
    through the same constructors, and the constructors this variant adds are reached through
    the table and checkbox claims above. -/
theorem renderBlockNodesF_wellFormed :
    (tight : Bool) → (fuel : Nat) → (b : Block) → Block.noEmbeddedHtmlF fuel b = true →
      ∀ n ∈ renderBlockNodesF (P := P) tight fuel b, n.hasVerbatim = false
  | _, 0, _, _ => by intro n hn; simp [renderBlockNodesF] at hn
  | tight, _ + 1, .paragraph content, h => by
    simp only [Block.noEmbeddedHtmlF] at h
    have hc := inlineListNodes_wellFormed (P := P) content h
    simp only [renderBlockNodesF]
    split <;> simpa using hc
  | _, _ + 1, .heading level content, h => by
    simp only [Block.noEmbeddedHtmlF] at h
    have hc := headingNode_wellFormed level _ (inlineListNodes_wellFormed (P := P) content h)
    simp only [HtmlModel.Node.hasVerbatim] at hc
    simp [renderBlockNodesF, hc]
  | _, _ + 1, .codeBlock _ _, _ => by unfold renderBlockNodesF; simp
  | _, _ + 1, .thematicBreak, _ => by simp [renderBlockNodesF]
  | _, _ + 1, .htmlBlock _, h => by simp [Block.noEmbeddedHtmlF] at h
  | _, fuel + 1, .blockQuote content, h => by
    simp only [Block.noEmbeddedHtmlF] at h
    simpa [renderBlockNodesF] using renderBlocksNodeF_wellFormed false fuel content h
  | _, fuel + 1, .list kind isTight items, h => by
    simp only [Block.noEmbeddedHtmlF] at h
    have hitems : ∀ p ∈ items, Block.noEmbeddedHtmlListF fuel p.2 = true := List.all_eq_true.mp h
    have hitemNode : ∀ p ∈ items, (itemNode (P := P) isTight fuel p.1 p.2).hasVerbatim = false := by
      intro (checked, content) hp
      have hcheckbox := checkboxNodes_wellFormed (P := P) checked
      have hprefix : ∀ c ∈ itemPrefix (P := P) isTight content, c.hasVerbatim = false := by
        unfold itemPrefix; split <;> simp
      have hblocks := renderBlocksNodeF_wellFormed isTight fuel content (hitems (checked, content) hp)
      simp only [HtmlModel.Node.hasVerbatim] at hcheckbox hprefix hblocks
      simp only [itemNode]
      simpa using ⟨hcheckbox, hprefix, hblocks⟩
    have hitemNodes : ∀ c ∈ ((HtmlNode.newline : HtmlNode P .listItemOrScript) ::
        items.foldl (fun acc (checked, content) =>
          acc ++ [(Web.widen (itemNode isTight fuel checked content) : HtmlNode P .listItemOrScript), HtmlNode.newline]) []),
        c.hasVerbatim = false := by
      intro c hc
      simp only [List.mem_cons] at hc
      rcases hc with hc | hc
      · subst hc; simp
      · rcases foldl_append_mem (fun (p : Option Bool × List Block) =>
            [(Web.widen (itemNode isTight fuel p.1 p.2) : HtmlNode P .listItemOrScript), HtmlNode.newline]) items [] c hc
          with hc' | ⟨p, hp, hc'⟩
        · simp at hc'
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
          have := hitemNode p hp
          simp only [HtmlModel.Node.hasVerbatim] at this
          rcases hc' with hc' | hc' <;> subst hc' <;> simp [this]
    intro n hn
    unfold renderBlockNodesF at hn
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with hn | hn
    · subst hn
      exact listNode_wellFormed kind _ hitemNodes
    · subst hn; simp
  | _, _ + 1, .table header alignments rows, h => by
    simp only [Block.noEmbeddedHtmlF, Bool.and_eq_true] at h
    have hheader : ∀ content ∈ header, RawInline.noEmbeddedHtmlList content = true := List.all_eq_true.mp h.1
    have hrows : ∀ row ∈ rows, ∀ content ∈ row, RawInline.noEmbeddedHtmlList content = true := by
      intro row hrow
      exact List.all_eq_true.mp (List.all_eq_true.mp h.2 row hrow)
    have ht := tableNode_wellFormed (P := P) header alignments rows hheader hrows
    simp only [HtmlModel.Node.hasVerbatim] at ht
    simp [renderBlockNodesF, ht]

/-- Rendering a list of blocks that carry no raw HTML yields only nodes free of verbatim markup, at
    whatever depth the renderer is working.

    The shape a `Document` has, and so the form the theorem below instantiates. As above the
    hypothesis and the rendering share one `fuel`, and the separator nodes the renderer inserts
    between blocks are text, which is where `mem_ite_append` above is spent. -/
theorem renderBlocksNodeF_wellFormed :
    (tight : Bool) → (fuel : Nat) → (bs : List Block) → Block.noEmbeddedHtmlListF fuel bs = true →
      ∀ n ∈ renderBlocksNodeF (P := P) tight fuel bs, n.hasVerbatim = false
  | _, 0, _, _ => by intro n hn; simp [renderBlocksNodeF] at hn
  | _, _ + 1, [], _ => by intro n hn; simp [renderBlocksNodeF] at hn
  | tight, fuel + 1, b :: rest, h => by
    simp only [Block.noEmbeddedHtmlListF, Bool.and_eq_true] at h
    unfold renderBlocksNodeF
    dsimp only
    intro n hn
    rcases mem_ite_append _ _ _ _ _ hn with hn | hn | hn
    · exact renderBlockNodesF_wellFormed tight fuel b h.1 n hn
    · subst hn; simp
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
  unfold renderHtml CommonMark.renderNodes htmlNodes blocksNodes
  exact foldl_render_wellFormed .xhtml _ (renderBlocksNodeF_wellFormed false _ doc h')
    "" (WellFormedHtml.text (by simp))

end GFMarkdown
