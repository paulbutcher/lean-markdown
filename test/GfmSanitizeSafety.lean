-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import GfmNoEmbeddedHtml

@[expose] public section

-- Mirrors `SanitizeSafety.lean`'s structure and goal, adapted to `GFMarkdown.Sanitize`'s own
-- (structurally similar but independent, and self-fuel-matching rather than going through a
-- generic map combinator) `sanitizeInline`/`sanitizeBlockF`/`sanitizeBlockListF`/
-- `sanitizeItemsF`.

namespace GFMarkdown

open CommonMark.Parser (RawInline)

mutual
def RawInline.allDestsSafe : RawInline → Bool
  | .link dest _ content => CommonMark.isSafeUriScheme dest && RawInline.allDestsSafeList content
  | .image dest _ content => CommonMark.isSafeUriScheme dest && RawInline.allDestsSafeList content
  | .emph content => RawInline.allDestsSafeList content
  | .strong content => RawInline.allDestsSafeList content
  | .strikethrough content => RawInline.allDestsSafeList content
  | .text _ | .code _ | .math .. | .htmlInline _ | .softBreak | .lineBreak => true

def RawInline.allDestsSafeList : List RawInline → Bool
  | [] => true
  | i :: rest => RawInline.allDestsSafe i && RawInline.allDestsSafeList rest
end

mutual
def Block.allDestsSafeF : Nat → Block → Bool
  | 0, _ => true
  | _ + 1, .paragraph content => RawInline.allDestsSafeList content
  | _ + 1, .heading _ content => RawInline.allDestsSafeList content
  | _ + 1, .codeBlock .. => true
  | _ + 1, .thematicBreak => true
  | _ + 1, .htmlBlock _ => true
  | fuel + 1, .blockQuote content => Block.allDestsSafeListF fuel content
  | fuel + 1, .list _ _ items => items.all (fun (_, c) => Block.allDestsSafeListF fuel c)
  | _ + 1, .table header _ rows =>
    header.all RawInline.allDestsSafeList &&
      rows.all (fun row => row.all RawInline.allDestsSafeList)

def Block.allDestsSafeListF : Nat → List Block → Bool
  | 0, _ => true
  | _ + 1, [] => true
  | fuel + 1, b :: rest => Block.allDestsSafeF fuel b && Block.allDestsSafeListF fuel rest
end

/-- `sanitizeDest` never yields a destination unsafe to emit as an `href`/`src`, whatever it is
    handed.

    The same claim `SanitizeSafety.lean` proves, re-derived because that copy is `private` to
    its module; this variant reuses `CommonMark`'s destination sanitizer and allowlist, so the
    statement is about `CommonMark.sanitizeDest` rather than one of its own. It is what
    discharges the `.link` and `.image` cases below, where nothing is known about the original
    destination. -/
private theorem isSafeUriScheme_sanitizeDest (dest : String) :
    CommonMark.isSafeUriScheme (CommonMark.sanitizeDest dest) = true := by
  unfold CommonMark.sanitizeDest
  split
  · assumption
  · decide

-- Mirrors `sanitizeInline`/`sanitizeInlineList`'s own structural (fuel-free) mutual
-- recursion case-for-case, extended with the `.strikethrough` case.
mutual
/-- Sanitizing an inline node leaves no raw HTML and no unsafe destination anywhere within it,
    at any depth.

    `RawInline.noEmbeddedHtml` answers `false` only at `.htmlInline` and otherwise recurses
    into content, so `= true` says none survives; `RawInline.allDestsSafe` recurses the same
    way and answers `isSafeUriScheme dest` at each `.link`/`.image`. Both sides name
    `sanitizeInline` itself, not a traversal applied to it, this variant's sanitizer doing its
    own recursion; `.strikethrough` carries content like `emph` and is covered with it. -/
theorem sanitizeInline_ok : (i : RawInline) →
    RawInline.noEmbeddedHtml (sanitizeInline i) = true ∧
    RawInline.allDestsSafe (sanitizeInline i) = true
  | .text _ => by simp [sanitizeInline, RawInline.noEmbeddedHtml, RawInline.allDestsSafe]
  | .code _ => by simp [sanitizeInline, RawInline.noEmbeddedHtml, RawInline.allDestsSafe]
  | .htmlInline _ => by simp [sanitizeInline, RawInline.noEmbeddedHtml, RawInline.allDestsSafe]
  | .softBreak => by simp [sanitizeInline, RawInline.noEmbeddedHtml, RawInline.allDestsSafe]
  | .lineBreak => by simp [sanitizeInline, RawInline.noEmbeddedHtml, RawInline.allDestsSafe]
  | .math .. => by simp [sanitizeInline, RawInline.noEmbeddedHtml, RawInline.allDestsSafe]
  | .emph content => by
    simp only [sanitizeInline, RawInline.noEmbeddedHtml, RawInline.allDestsSafe]
    exact sanitizeInlineList_ok content
  | .strong content => by
    simp only [sanitizeInline, RawInline.noEmbeddedHtml, RawInline.allDestsSafe]
    exact sanitizeInlineList_ok content
  | .strikethrough content => by
    simp only [sanitizeInline, RawInline.noEmbeddedHtml, RawInline.allDestsSafe]
    exact sanitizeInlineList_ok content
  | .link dest _ content => by
    simp only [sanitizeInline, RawInline.noEmbeddedHtml, RawInline.allDestsSafe, Bool.and_eq_true]
    exact ⟨(sanitizeInlineList_ok content).1,
      isSafeUriScheme_sanitizeDest dest, (sanitizeInlineList_ok content).2⟩
  | .image dest _ content => by
    simp only [sanitizeInline, RawInline.noEmbeddedHtml, RawInline.allDestsSafe, Bool.and_eq_true]
    exact ⟨(sanitizeInlineList_ok content).1,
      isSafeUriScheme_sanitizeDest dest, (sanitizeInlineList_ok content).2⟩

/-- Sanitizing a list of inline nodes leaves no raw HTML and no unsafe destination anywhere
    within any of them, at any depth.

    The `...List` predicates are the conjunctions of their node-level counterparts over the
    elements. `sanitizeInline` reaches a node's children through `sanitizeInlineList`, so the
    claim above holds only as far as this one does; it is also the form `.paragraph`,
    `.heading` and `.table` cells need. -/
theorem sanitizeInlineList_ok : (l : List RawInline) →
    RawInline.noEmbeddedHtmlList (sanitizeInlineList l) = true ∧
    RawInline.allDestsSafeList (sanitizeInlineList l) = true
  | [] => by simp [sanitizeInlineList, RawInline.noEmbeddedHtmlList, RawInline.allDestsSafeList]
  | i :: rest => by
    simp only [sanitizeInlineList, RawInline.noEmbeddedHtmlList, RawInline.allDestsSafeList,
      Bool.and_eq_true]
    exact ⟨⟨(sanitizeInline_ok i).1, (sanitizeInlineList_ok rest).1⟩,
      (sanitizeInline_ok i).2, (sanitizeInlineList_ok rest).2⟩
end

-- Mirrors `sanitizeBlockF`/`sanitizeBlockListF`/`sanitizeItemsF`'s own fuel-bounded mutual
-- recursion case-for-case, extended with `.table` and `.list`'s `(Option Bool × List Block)`
-- items.
mutual
/-- Sanitizing a block leaves no raw HTML and no unsafe destination in it, as deep as the
    sanitizing itself went.

    One `fuel` governs both the rewrite and the two checks, which is what makes the checks
    non-vacuous: they descend in step, so a check stops exactly where the rewrite stopped. The
    constructors this variant adds are covered by the same claim, a `.table`'s cells and a
    list item's blocks being reached through the inline and block claims already stated. -/
theorem sanitizeBlockF_ok : (fuel : Nat) → (b : Block) →
    Block.noEmbeddedHtmlF fuel (sanitizeBlockF fuel b) = true ∧
    Block.allDestsSafeF fuel (sanitizeBlockF fuel b) = true
  | 0, _ => by simp [Block.noEmbeddedHtmlF, Block.allDestsSafeF]
  | _ + 1, .paragraph content => by
    simp only [sanitizeBlockF, Block.noEmbeddedHtmlF, Block.allDestsSafeF]
    exact sanitizeInlineList_ok content
  | _ + 1, .heading _ content => by
    simp only [sanitizeBlockF, Block.noEmbeddedHtmlF, Block.allDestsSafeF]
    exact sanitizeInlineList_ok content
  | _ + 1, .codeBlock .. => by simp [sanitizeBlockF, Block.noEmbeddedHtmlF, Block.allDestsSafeF]
  | _ + 1, .thematicBreak => by simp [sanitizeBlockF, Block.noEmbeddedHtmlF, Block.allDestsSafeF]
  | _ + 1, .htmlBlock _ => by
    simp [sanitizeBlockF, Block.noEmbeddedHtmlF, Block.allDestsSafeF,
      RawInline.noEmbeddedHtmlList, RawInline.allDestsSafeList]
  | fuel + 1, .blockQuote content => by
    simp only [sanitizeBlockF, Block.noEmbeddedHtmlF, Block.allDestsSafeF]
    exact sanitizeBlockListF_ok fuel content
  | fuel + 1, .list _ _ items => by
    simp only [sanitizeBlockF, Block.noEmbeddedHtmlF, Block.allDestsSafeF, List.all_eq_true,
      List.mem_map]
    refine ⟨fun p hp => ?_, fun p hp => ?_⟩ <;>
      · obtain ⟨⟨checked, c⟩, hc, rfl⟩ := hp
        first
          | exact (sanitizeBlockListF_ok fuel c).1
          | exact (sanitizeBlockListF_ok fuel c).2
  | _ + 1, .table header alignments rows => by
    simp only [sanitizeBlockF, Block.noEmbeddedHtmlF, Block.allDestsSafeF, Bool.and_eq_true,
      List.all_eq_true]
    refine ⟨⟨fun content hc => ?_, fun row hr => ?_⟩, fun content hc => ?_, fun row hr => ?_⟩
    · obtain ⟨c, _, rfl⟩ := List.mem_map.mp hc; exact (sanitizeInlineList_ok c).1
    · obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hr
      simp only [List.mem_map] at *
      intro content hc
      obtain ⟨c, _, rfl⟩ := hc
      exact (sanitizeInlineList_ok c).1
    · obtain ⟨c, _, rfl⟩ := List.mem_map.mp hc; exact (sanitizeInlineList_ok c).2
    · obtain ⟨r, hr', rfl⟩ := List.mem_map.mp hr
      simp only [List.mem_map] at *
      intro content hc
      obtain ⟨c, _, rfl⟩ := hc
      exact (sanitizeInlineList_ok c).2

/-- Sanitizing a list of blocks, which is what a `Document` is, leaves no raw HTML and no
    unsafe destination in any of them, as deep as the sanitizing itself went.

    `Document.sanitize doc` is by definition `sanitizeBlockListF (Block.listCount doc + 1) doc`,
    so this proposition read at that fuel is already the two theorems below; leaving `fuel`
    quantified is what lets other callers read it at a depth of their own. -/
theorem sanitizeBlockListF_ok : (fuel : Nat) → (bs : List Block) →
    Block.noEmbeddedHtmlListF fuel (sanitizeBlockListF fuel bs) = true ∧
    Block.allDestsSafeListF fuel (sanitizeBlockListF fuel bs) = true
  | 0, _ => by simp [Block.noEmbeddedHtmlListF, Block.allDestsSafeListF]
  | _ + 1, [] => by simp [sanitizeBlockListF, Block.noEmbeddedHtmlListF, Block.allDestsSafeListF]
  | fuel + 1, b :: rest => by
    simp only [sanitizeBlockListF, Block.noEmbeddedHtmlListF, Block.allDestsSafeListF,
      Bool.and_eq_true]
    exact ⟨⟨(sanitizeBlockF_ok fuel b).1, (sanitizeBlockListF_ok fuel rest).1⟩,
      (sanitizeBlockF_ok fuel b).2, (sanitizeBlockListF_ok fuel rest).2⟩
end

/-- `Document.sanitize doc` embeds no raw HTML (`.htmlInline`/`.htmlBlock`): every leaf that
    would otherwise reach `renderHtml`'s output through `Html.Node.unsafeRaw` has been removed.

    The proposition says that because those two constructors are the only ones
    `Block.noEmbeddedHtmlListF` answers `false` on, the second through the inline predicate it
    defers to, so `= true` is exactly "neither occurs". The reading is done at
    `Block.listCount doc + 1`, the depth this variant sanitizes at and the one `renderBlocks`
    later reads at; `Document.noEmbeddedHtmlListF_saturate` (`GfmAstFuelLaws.lean`) shows that
    fuel sufficient, no larger one giving a different answer. -/
theorem Document.sanitize_noEmbeddedHtml (doc : Document) :
    Block.noEmbeddedHtmlListF (Block.listCount doc + 1) (Document.sanitize doc) = true :=
  (sanitizeBlockListF_ok (Block.listCount doc + 1) doc).1

/-- Every `link`/`image` `dest` in `Document.sanitize doc` has a URI scheme in
    `CommonMark.allowedUriSchemes` (or none at all, i.e. a relative reference), so nothing can
    reach an `href`/`src` that `renderHtml`, which percent-encodes a destination but never
    inspects its scheme, would pass through unexamined.

    The proposition says that because `Block.allDestsSafeListF` answers `isSafeUriScheme dest`
    at every `.link` and `.image` it reaches, `.table` cells and list items included, and
    `true` elsewhere. -/
theorem Document.sanitize_allDestsSafe (doc : Document) :
    Block.allDestsSafeListF (Block.listCount doc + 1) (Document.sanitize doc) = true :=
  (sanitizeBlockListF_ok (Block.listCount doc + 1) doc).2

end GFMarkdown
