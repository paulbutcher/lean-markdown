-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import CommonMark

-- `renderHtml` builds its entire output through `Html.Node`'s typed constructors except
-- for `.htmlInline`/`.htmlBlock`, which use `Html.Node.unsafeRaw` to pass literal HTML from
-- the Markdown source through verbatim -- the one place `Html.Node.WellFormed` can fail to
-- hold. So a `Document` containing no `.htmlInline`/`.htmlBlock` anywhere renders to
-- well-formed HTML: balanced tags, no stray `<`/`>` outside of tag syntax
-- (`Html.WellFormedHtml`). This mirrors `renderBlockNodesF`/`renderBlocksNodeF`'s own
-- structure (mutual, fuel-bounded for `Block`, plain structural for `Inline`) so the
-- well-formedness proof can induct case-for-case alongside the renderer.

namespace CommonMark

mutual
def Inline.noHtml : Inline → Bool
  | .htmlInline _ => false
  | .emph content => Inline.noHtmlList content
  | .strong content => Inline.noHtmlList content
  | .link _ _ content => Inline.noHtmlList content
  | .image _ _ content => Inline.noHtmlList content
  | .text _ | .code _ | .softBreak | .lineBreak => true

def Inline.noHtmlList : List Inline → Bool
  | [] => true
  | i :: rest => Inline.noHtml i && Inline.noHtmlList rest
end

mutual
def Block.noHtmlF : Nat → Block → Bool
  | 0, _ => true
  | _ + 1, .paragraph content => Inline.noHtmlList content
  | _ + 1, .heading _ content => Inline.noHtmlList content
  | _ + 1, .codeBlock .. => true
  | _ + 1, .thematicBreak => true
  | _ + 1, .htmlBlock _ => false
  | fuel + 1, .blockQuote content => Block.noHtmlListF fuel content
  | fuel + 1, .list _ _ items => items.all (Block.noHtmlListF fuel)

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
    already-`WellFormedHtml` accumulator, stays `WellFormedHtml`: each step is exactly
    `WellFormedHtml.append` of the accumulator so far with `Node.render_wellFormed` for
    the next node. -/
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

/-- Membership in `if cond then A ++ [x] ++ B else A ++ B`, regardless of `cond`: weakens to
    "came from `A`, is `x`, or came from `B`" without needing to know (or re-elaborate) what
    `cond` actually was -- letting the caller's own `hn` pin `cond`/`A`/`B`/`x` by unification
    instead of restating them, which is what a direct `split`/`by_cases` on a multi-way `&&`
    condition keeps failing to do reliably. -/
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

-- Mirrors `inlineNodes`/`inlineListNodes`'s own mutual structural recursion case-for-case,
-- so each case's induction hypothesis is exactly the fact needed about its recursive call.
mutual
theorem inlineNodes_wellFormed :
    (i : Inline) → Inline.noHtml i = true → ∀ n ∈ inlineNodes i, Node.WellFormed n
  | .text s, _ => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    exact Node.text_wellFormed s
  | .code s, _ => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    exact Node.element_wellFormed .phrasing "code" _ _ (by
      intro c hc; simp only [List.mem_singleton] at hc; subst hc; exact Node.text_wellFormed s)
  | .emph content, h => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    simp only [Inline.noHtml] at h
    exact Node.element_wellFormed .phrasing "em" _ _ (inlineListNodes_wellFormed content h)
  | .strong content, h => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    simp only [Inline.noHtml] at h
    exact Node.element_wellFormed .phrasing "strong" _ _ (inlineListNodes_wellFormed content h)
  | .link _ _ content, h => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    simp only [Inline.noHtml] at h
    exact Node.element_wellFormed .phrasing "a" _ _ (inlineListNodes_wellFormed content h)
  | .image .., _ => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    exact Node.voidElement_wellFormed .phrasing "img" _
  | .htmlInline _, h => by simp [Inline.noHtml] at h
  | .softBreak, _ => by
    intro n hn; simp only [inlineNodes, List.mem_singleton] at hn; subst hn
    exact Node.text_wellFormed "\n"
  | .lineBreak, _ => by
    intro n hn; simp only [inlineNodes, List.mem_cons, List.not_mem_nil, or_false] at hn
    rcases hn with hn | hn
    · subst hn; exact Node.voidElement_wellFormed .phrasing "br" _
    · subst hn; exact Node.text_wellFormed "\n"

theorem inlineListNodes_wellFormed :
    (l : List Inline) → Inline.noHtmlList l = true → ∀ n ∈ inlineListNodes l, Node.WellFormed n
  | [], _ => by intro n hn; simp [inlineListNodes] at hn
  | i :: rest, h => by
    simp only [Inline.noHtmlList, Bool.and_eq_true] at h
    intro n hn
    simp only [inlineListNodes, List.mem_append] at hn
    rcases hn with hn | hn
    · exact inlineNodes_wellFormed i h.1 n hn
    · exact inlineListNodes_wellFormed rest h.2 n hn
end

private theorem headingNode_wellFormed (level : Fin 6) (children : List (Node .phrasing))
    (h : ∀ c ∈ children, Node.WellFormed c) : Node.WellFormed (headingNode level children) := by
  unfold headingNode; split <;> exact Node.elementOf_wellFormed .flow .phrasing _ _ _ h

private theorem ul_wellFormed (children : List (Node .listItem)) (attrs : Html.HtmlAttrs)
    (h : ∀ c ∈ children, Node.WellFormed c) : Node.WellFormed (Html.ul children attrs) := by
  unfold Html.ul; exact Node.elementOf_wellFormed .flow .listItem "ul" _ _ h

private theorem ol_wellFormed (children : List (Node .listItem)) (attrs : Html.OlAttrs)
    (h : ∀ c ∈ children, Node.WellFormed c) : Node.WellFormed (Html.ol children attrs) := by
  unfold Html.ol; exact Node.elementOf_wellFormed .flow .listItem "ol" _ _ h

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

/-- Every element produced by `l.foldl (fun acc x => acc ++ f x) init` either came from
    `init` or from `f x` for some `x ∈ l` -- used to reason about `itemNodes`' `foldl`
    without needing to generalize the accumulator by hand at each step. -/
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
-- recursion case-for-case, exactly as `Block.noHtmlF`/`Block.noHtmlListF` were defined to.
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
    have hitems : ∀ c ∈ items, Block.noHtmlListF fuel c = true := List.all_eq_true.mp h
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

/-- If a `Document` embeds no raw HTML (`.htmlBlock`/`.htmlInline`), `renderHtml`'s output
    is well-formed: balanced tags, with no stray `<`/`>` anywhere outside of tag delimiters.
    The `.htmlBlock`/`.htmlInline` exclusion is necessary, not just a proof-technique
    limitation: `renderHtml` deliberately passes their content through unescaped
    (`Html.Node.unsafeRaw`), so a raw `<` in the source really can appear unbalanced in the
    output -- this theorem covers exactly the fragment of CommonMark where that can't
    happen. -/
theorem renderHtml_wellFormed (doc : Document) (h : doc.hasEmbeddedHtml = false) :
    Html.WellFormedHtml true (renderHtml doc) := by
  have h' : Block.noHtmlListF (Block.listCount doc + 1) doc = true := by
    simpa [Document.hasEmbeddedHtml] using h
  unfold renderHtml renderBlocks
  exact foldl_render_wellFormed true _ (renderBlocksNodeF_wellFormed false _ doc h')
    "" (WellFormedHtml.text (by simp))

end CommonMark
