-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import GFMarkdown

-- Mirrors `HtmlWellFormedness.lean`'s structure exactly, adapted to `GFMarkdown`'s own
-- (structurally similar but independent) `Block`/`RawInline`/renderer: `renderHtml` builds
-- its entire output through `Html.Node`'s typed constructors except for
-- `.htmlInline`/`.htmlBlock`, so a `Document` containing neither renders to well-formed HTML.

namespace GFMarkdown

open CommonMark.Parser (RawInline)

mutual
def RawInline.noHtml : RawInline → Bool
  | .htmlInline _ => false
  | .emph content => RawInline.noHtmlList content
  | .strong content => RawInline.noHtmlList content
  | .link _ _ content => RawInline.noHtmlList content
  | .image _ _ content => RawInline.noHtmlList content
  | .strikethrough content => RawInline.noHtmlList content
  | .text _ | .code _ | .softBreak | .lineBreak => true

def RawInline.noHtmlList : List RawInline → Bool
  | [] => true
  | i :: rest => RawInline.noHtml i && RawInline.noHtmlList rest
end

mutual
def Block.noHtmlF : Nat → Block → Bool
  | 0, _ => true
  | _ + 1, .paragraph content => RawInline.noHtmlList content
  | _ + 1, .heading _ content => RawInline.noHtmlList content
  | _ + 1, .codeBlock .. => true
  | _ + 1, .thematicBreak => true
  | _ + 1, .htmlBlock _ => false
  | fuel + 1, .blockQuote content => Block.noHtmlListF fuel content
  | fuel + 1, .list _ _ items => items.all (fun (_, c) => Block.noHtmlListF fuel c)
  | _ + 1, .table header _ rows =>
    header.all RawInline.noHtmlList && rows.all (fun row => row.all RawInline.noHtmlList)

def Block.noHtmlListF : Nat → List Block → Bool
  | 0, _ => true
  | _ + 1, [] => true
  | fuel + 1, b :: rest => Block.noHtmlF fuel b && Block.noHtmlListF fuel rest
end

/-- Whether a `Document` contains any embedded raw HTML (`.htmlInline`/`.htmlBlock`),
    the only channel through which `renderHtml` can produce output that isn't
    `Html.Node.WellFormed`. -/
def Document.hasEmbeddedHtml (doc : Document) : Bool :=
  !Block.noHtmlListF (Block.listCount doc + 1) doc

open Html

/-- Folding `.render` over a list of already-`WellFormed` nodes, starting from an
    already-`WellFormedHtml` accumulator, stays `WellFormedHtml`. Identical in shape to
    `CommonMark.foldl_render_wellFormed`; re-derived here since that one is `private`. -/
private theorem foldl_render_wellFormed {cat : Category} (selfClosingVoid : Bool)
    (l : List (Node cat)) (h : ∀ n ∈ l, Node.WellFormed n) :
    ∀ acc, WellFormedHtml selfClosingVoid acc →
      WellFormedHtml selfClosingVoid
        (l.foldl (fun acc n => acc ++ n.render (selfClosingVoid := selfClosingVoid)) acc) := by
  induction l with
  | nil => intro acc hacc; simpa using hacc
  | cons n rest ih =>
    intro acc hacc
    simp only [List.foldl_cons]
    exact ih (fun n' hn' => h n' (List.mem_cons_of_mem _ hn'))
      (acc ++ n.render (selfClosingVoid := selfClosingVoid))
      (hacc.append (Node.render_wellFormed n (h n (List.mem_cons_self ..)) selfClosingVoid))

/-- Membership in `if cond then A ++ [x] ++ B else A ++ B`, regardless of `cond`. Identical in
    shape to `CommonMark.mem_ite_append`; re-derived here since that one is `private`. -/
private theorem mem_ite_append {α : Type} (cond : Bool) (A B : List α) (x n : α)
    (hn : n ∈ (if cond = true then A ++ [x] ++ B else A ++ B)) : n ∈ A ∨ n = x ∨ n ∈ B := by
  by_cases hc : cond = true
  · rw [if_pos hc] at hn
    rcases List.mem_append.mp hn with hn | hn
    · rcases List.mem_append.mp hn with hn | hn
      · exact Or.inl hn
      · exact Or.inr (Or.inl (List.mem_singleton.mp hn))
    · exact Or.inr (Or.inr hn)
  · rw [if_neg hc] at hn
    rcases List.mem_append.mp hn with hn | hn
    · exact Or.inl hn
    · exact Or.inr (Or.inr hn)

/-- Every element produced by `l.foldl (fun acc x => acc ++ f x) init` either came from
    `init` or from `f x` for some `x ∈ l`. Identical in shape to `CommonMark.foldl_append_mem`;
    re-derived here since that one is `private`. -/
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

/-- Every element produced by `interleaveNewlines l` is either a literal `"\n"` or came from
    `l` itself. -/
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

private theorem interleaveNewlines_wellFormed {cat : Category} (nodes : List (Node cat))
    (h : ∀ n ∈ nodes, Node.WellFormed n) : ∀ c ∈ interleaveNewlines nodes, Node.WellFormed c := by
  intro c hc
  rcases interleaveNewlines_mem nodes c hc with hc' | hc'
  · subst hc'; exact Node.text_wellFormed "\n"
  · exact h c hc'

private theorem headingNode_wellFormed (level : Fin 6) (children : List (Node .phrasing))
    (h : ∀ c ∈ children, Node.WellFormed c) : Node.WellFormed (headingNode level children) := by
  unfold headingNode; split <;> exact Node.elementOf_wellFormed .flow .phrasing _ _ _ h

private theorem ul_wellFormed (children : List (Node .listItem)) (attrs : Html.HtmlAttrs)
    (h : ∀ c ∈ children, Node.WellFormed c) : Node.WellFormed (Html.ul children attrs) := by
  unfold Html.ul; exact Node.elementOf_wellFormed .flow .listItem "ul" _ _ h

private theorem ol_wellFormed (children : List (Node .listItem)) (attrs : Html.OlAttrs)
    (h : ∀ c ∈ children, Node.WellFormed c) : Node.WellFormed (Html.ol children attrs) := by
  unfold Html.ol; exact Node.elementOf_wellFormed .flow .listItem "ol" _ _ h

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

-- `checkboxNodes` only ever produces a void `<input>` (generically `WellFormed` regardless of
-- its `rawAttrs`, since `voidElement_wellFormed` doesn't care what's inside `Attrs.render`)
-- plus a literal `" "` text node.
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
      exact Node.voidElement_wellFormed .phrasing "input" _
    · subst hc; exact Node.text_wellFormed " "

-- Mirrors `CommonMark.inlineNodes_wellFormed`/`inlineListNodes_wellFormed`'s own mutual
-- structural recursion case-for-case, extended with the `.strikethrough`/`<del>` case.
mutual
theorem inlineNodes_wellFormed :
    (i : RawInline) → RawInline.noHtml i = true → ∀ n ∈ inlineNodes i, Node.WellFormed n
  | .text s, _ => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    exact Node.text_wellFormed s
  | .code s, _ => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    exact Node.element_wellFormed .phrasing "code" _ _ (by
      intro c hc; simp only [List.mem_singleton] at hc; subst hc; exact Node.text_wellFormed s)
  | .emph content, h => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    simp only [RawInline.noHtml] at h
    exact Node.element_wellFormed .phrasing "em" _ _ (inlineListNodes_wellFormed content h)
  | .strong content, h => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    simp only [RawInline.noHtml] at h
    exact Node.element_wellFormed .phrasing "strong" _ _ (inlineListNodes_wellFormed content h)
  | .link _ _ content, h => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    simp only [RawInline.noHtml] at h
    exact Node.element_wellFormed .phrasing "a" _ _ (inlineListNodes_wellFormed content h)
  | .image .., _ => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    exact Node.voidElement_wellFormed .phrasing "img" _
  | .htmlInline _, h => by simp [RawInline.noHtml] at h
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
    simp only [RawInline.noHtml] at h
    exact Node.element_wellFormed .phrasing "del" _ _ (inlineListNodes_wellFormed content h)

theorem inlineListNodes_wellFormed :
    (l : List RawInline) → RawInline.noHtmlList l = true → ∀ n ∈ inlineListNodes l, Node.WellFormed n
  | [], _ => by intro n hn; simp [inlineListNodes] at hn
  | i :: rest, h => by
    simp only [RawInline.noHtmlList, Bool.and_eq_true] at h
    intro n hn
    simp only [inlineListNodes, List.mem_append] at hn
    rcases hn with hn | hn
    · exact inlineNodes_wellFormed i h.1 n hn
    · exact inlineListNodes_wellFormed rest h.2 n hn
end

private theorem tableCellNode_wellFormed (isHeader : Bool) (alignment : CommonMark.Parser.TableAlignment)
    (content : List RawInline) (h : RawInline.noHtmlList content = true) :
    Node.WellFormed (tableCellNode isHeader alignment content) := by
  unfold tableCellNode
  have hchildren : ∀ c ∈ (inlineListNodes content).map
      (fun (n : Node .phrasing) => (n : Node .flow)), Node.WellFormed c := by
    intro c hc
    obtain ⟨n, hn, hneq⟩ := List.mem_map.mp hc
    exact hneq ▸ inlineListNodes_wellFormed content h n hn
  split
  · exact Node.elementOf_wellFormed .tableCell .flow "th" _ _ hchildren
  · exact Node.elementOf_wellFormed .tableCell .flow "td" _ _ hchildren

/-- Every element produced by `List.zipWith f as bs` is `f a b` for some `a ∈ as`, `b ∈ bs`. -/
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

private theorem tableRowNode_wellFormed (isHeader : Bool) (alignments : List CommonMark.Parser.TableAlignment)
    (cells : List (List RawInline)) (h : ∀ content ∈ cells, RawInline.noHtmlList content = true) :
    Node.WellFormed (tableRowNode isHeader alignments cells) := by
  unfold tableRowNode
  apply Node.elementOf_wellFormed .tableRow .tableCell "tr" _ _
  apply interleaveNewlines_wellFormed
  intro c hc
  obtain ⟨content, hcontent, alignment, hceq⟩ := mem_zipWith (tableCellNode isHeader) alignments cells c hc
  exact hceq ▸ tableCellNode_wellFormed isHeader alignment content (h content hcontent)

private theorem tableNode_wellFormed (header : List (List RawInline))
    (alignments : List CommonMark.Parser.TableAlignment) (rows : List (List (List RawInline)))
    (hheader : ∀ content ∈ header, RawInline.noHtmlList content = true)
    (hrows : ∀ row ∈ rows, ∀ content ∈ row, RawInline.noHtmlList content = true) :
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
theorem renderBlockNodesF_wellFormed :
    (tight : Bool) → (fuel : Nat) → (b : Block) → Block.noHtmlF fuel b = true →
      ∀ n ∈ renderBlockNodesF tight fuel b, Node.WellFormed n
  | _, 0, _, _ => by intro n hn; simp [renderBlockNodesF] at hn
  | tight, _ + 1, .paragraph content, h => by
    simp only [Block.noHtmlF] at h
    simp only [renderBlockNodesF]
    split
    · intro n hn
      obtain ⟨n', hn', hneq⟩ := List.mem_map.mp hn
      exact hneq ▸ inlineListNodes_wellFormed content h n' hn'
    · intro n hn
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with hn | hn
      · subst hn
        exact Node.elementOf_wellFormed .flow .phrasing "p" _ _ (inlineListNodes_wellFormed content h)
      · subst hn; exact Node.text_wellFormed "\n"
  | _, _ + 1, .heading level content, h => by
    simp only [Block.noHtmlF] at h
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
  | _, _ + 1, .htmlBlock _, h => by simp [Block.noHtmlF] at h
  | _, fuel + 1, .blockQuote content, h => by
    simp only [Block.noHtmlF] at h
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
    simp only [Block.noHtmlF] at h
    have hitems : ∀ p ∈ items, Block.noHtmlListF fuel p.2 = true := List.all_eq_true.mp h
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
    simp only [Block.noHtmlF, Bool.and_eq_true] at h
    have hheader : ∀ content ∈ header, RawInline.noHtmlList content = true := List.all_eq_true.mp h.1
    have hrows : ∀ row ∈ rows, ∀ content ∈ row, RawInline.noHtmlList content = true := by
      intro row hrow
      exact List.all_eq_true.mp (List.all_eq_true.mp h.2 row hrow)
    intro n hn
    simp only [renderBlockNodesF, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with hn | hn
    · subst hn; exact tableNode_wellFormed header alignments rows hheader hrows
    · subst hn; exact Node.text_wellFormed "\n"

theorem renderBlocksNodeF_wellFormed :
    (tight : Bool) → (fuel : Nat) → (bs : List Block) → Block.noHtmlListF fuel bs = true →
      ∀ n ∈ renderBlocksNodeF tight fuel bs, Node.WellFormed n
  | _, 0, _, _ => by intro n hn; simp [renderBlocksNodeF] at hn
  | _, _ + 1, [], _ => by intro n hn; simp [renderBlocksNodeF] at hn
  | tight, fuel + 1, b :: rest, h => by
    simp only [Block.noHtmlListF, Bool.and_eq_true] at h
    unfold renderBlocksNodeF
    dsimp only
    intro n hn
    rcases mem_ite_append _ _ _ _ _ hn with hn | hn | hn
    · exact renderBlockNodesF_wellFormed tight fuel b h.1 n hn
    · subst hn; exact Node.text_wellFormed "\n"
    · exact renderBlocksNodeF_wellFormed tight fuel rest h.2 n hn
end

/-- If a `Document` embeds no raw HTML (`.htmlBlock`/`.htmlInline`), `renderHtml`'s output is
    well-formed: balanced tags, with no stray `<`/`>` anywhere outside of tag delimiters. Same
    shape and same necessary exclusion as `CommonMark.renderHtml_wellFormed`; see its own
    doc comment for why the `hasEmbeddedHtml` precondition can't be dropped. -/
theorem renderHtml_wellFormed (doc : Document) (h : doc.hasEmbeddedHtml = false) :
    Html.WellFormedHtml true (renderHtml doc) := by
  have h' : Block.noHtmlListF (Block.listCount doc + 1) doc = true := by
    simpa [Document.hasEmbeddedHtml] using h
  unfold renderHtml renderBlocks
  exact foldl_render_wellFormed true _ (renderBlocksNodeF_wellFormed false _ doc h')
    "" (WellFormedHtml.text (by simp))

end GFMarkdown
