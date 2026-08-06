# CommonMark in Lean: Requirements & Project Plan

## 0. Context for whoever picks this up

You are working in a **fresh `lake new` Lean 4 project**. You do not have access to any
other repository, including the codebase this document was originally drafted alongside.
Treat this document as the complete brief. Where it references "the spec", it means the
CommonMark specification at https://spec.commonmark.org/0.31.2/ and the accompanying
example suite / reference implementations at https://github.com/commonmark/commonmark-spec,
https://github.com/commonmark/commonmark.js, and https://github.com/commonmark/cmark.

Before writing code, fetch and skim:
- spec.commonmark.org/0.31.2/ (the prose spec, including "Appendix: A parsing strategy")
- the example suite in that repo (spec.txt embeds ~649 markdown/HTML example pairs;
  the repo's tooling extracts these into `spec.json` for use as a test fixture)

Confirm the license terms on the spec text and on commonmark.js/cmark before copying any
substantial prose or code from them; this plan assumes you'll reimplement the *algorithm*
described in the appendix, not port source code.

## 1. Goal

Build a Lean 4 library that parses CommonMark-flavored Markdown into an AST and renders
that AST to HTML, matching the reference behavior defined by the official example suite,
while using Lean's strengths (precise inductive types, totality, theorem proving) to
provide guarantees the JS/C reference implementations cannot make about themselves.

This is a from-scratch reimplementation, not a port. The reference implementations' AST
and mutable Node API are *not* part of the specification (see Section 3) and should not
be copied structurally.

## 2. Scope & non-goals

**In scope (CommonMark core, 0.31.2):**
- Block structure: paragraphs, ATX and Setext headings, thematic breaks, indented and
  fenced code blocks, HTML blocks, block quotes, list items and lists (tight/loose),
  link reference definitions, blank line handling.
- Inline structure: backslash escapes, entity and numeric character references, code
  spans, emphasis/strong emphasis (the delimiter-run algorithm), links (inline,
  reference, shortcut, collapsed) and images, autolinks, raw inline HTML, hard/soft
  line breaks.
- HTML rendering matching the spec's exact escaping and formatting rules.
- The official conformance example suite as the acceptance oracle.

**Explicitly out of scope unless separately requested:**
- GitHub Flavored Markdown extensions (tables, strikethrough, task lists, autolink
  extension) — these are extensions to, not part of, CommonMark.
- Any non-HTML output target (LaTeX, man pages, etc.).
- Streaming/incremental parsing.
- Matching the reference implementations' performance characteristics exactly — the
  goal is *provably good* complexity, not micro-optimized parity.

## 3. What "conformance" means here

The specification's normative content is the input→HTML mapping demonstrated by its
example suite; it does not define or require any particular AST shape. Two important
consequences for this project:

1. **We are free to design the AST idiomatically for Lean** (Section 5) rather than
   mirroring commonmark.js's `Node` class or cmark's `cmark_node`.
2. **"Provably conformant to the spec" is not achievable in the strong sense** — the
   spec isn't a formal object. What *is* achievable and should be a first-class
   deliverable: encode the official example suite as a Lean value and prove, via
   `decide`/`native_decide`, the theorem
   `∀ ex ∈ commonmarkExamples, renderHtml (parseDocument ex.markdown) = ex.html`.
   This is a machine-checked certificate (checked by the kernel at build time) that the
   shipped implementation reproduces every published example — strictly stronger than an
   ordinary green test suite, even though it isn't universal correctness.
3. Where the prose spec is ambiguous, treat the appendix "A parsing strategy" algorithm
   as the intended semantics and, where practical, structure the implementation so it
   can be shown equivalent to that algorithm.

## 4. AST design

Plain inductive types, immutable, no parent/sibling pointers. This is the deliberate
departure from the reference implementations' mutable doubly-linked graph, and it's what
makes structural induction (and therefore proofs) natural later.

```lean
inductive Inline where
  | text       (s : String)
  | code       (s : String)
  | emph       (content : List Inline)
  | strong     (content : List Inline)
  | link       (dest title : String) (content : List Inline)
  | image      (dest title : String) (content : List Inline)
  | htmlInline (s : String)
  | softBreak
  | lineBreak
  deriving Repr, BEq

inductive ListType where
  | bullet (marker : Char)
  | ordered (start : Nat) (delimiter : Char)
  deriving Repr, BEq

inductive Block where
  | paragraph     (content : List Inline)
  | heading       (level : Fin 6) (content : List Inline)
  | codeBlock     (info : Option String) (literal : String)
  | blockQuote    (content : List Block)
  | list          (kind : ListType) (tight : Bool) (items : List (List Block))
  | thematicBreak
  | htmlBlock     (s : String)
  deriving Repr, BEq

abbrev Document := List Block
```

Adjust field details during implementation (e.g. source positions, link reference
resolution bookkeeping) but keep the shape: sum-of-products data, no mutation, no
identity/pointer semantics. Use refinement types where cheap (`Fin 6` for heading level
is already above) so invalid states are unrepresentable rather than runtime-checked.

**Editing API:** do not attempt to replicate commonmark.js's mutable `Node`
(`appendChild`/`unlink`/`next`/`prev`/`parent`). Instead provide a **zipper** over
`Document`/`Block`/`Inline` for cursor-style navigation and localized edits. It gives
similar ergonomics (move down/up/left/right, insert, replace, delete at a cursor) while
remaining pure data with a clean isomorphism back to the tree, and its laws
(`up (down z) = z`, `toTree (fromTree t) = t`, edit-then-reconstruct correctness) are
cheap, worthwhile theorems in their own right.

Provide standard `Functor`/traversal-style fold/map combinators over the tree in place
of the JS `.walker()` iterator.

## 5. Public API surface (target shape)

```lean
namespace CommonMark

def parseDocument : String → Document
def renderHtml : Document → String

-- zipper
structure Zipper (α : Type) where ...
def Zipper.down  : Zipper α → Option (Zipper α)
def Zipper.up    : Zipper α → Option (Zipper α)
def Zipper.left  : Zipper α → Option (Zipper α)
def Zipper.right : Zipper α → Option (Zipper α)
def Zipper.replace : Zipper α → α → Zipper α
def Zipper.toTree  : Zipper α → α

end CommonMark
```

`parseDocument` must be total (no `partial`, no possibility of an unhandled case) per
the project's Lean conventions (Section 8).

## 6. Formal verification goals

**Required (part of "done"):**
- No `partial` definitions anywhere; all recursion is structural or justified by an
  explicit well-founded relation with a termination proof.
- The example-suite conformance theorem described in Section 3, item 2.
- Zipper round-trip and navigation laws.
- A proof that `renderHtml` escapes all raw/text content correctly — i.e., no AST leaf's
  literal string content can produce unescaped `<`, `>`, `&`, or unescaped `"` inside an
  attribute in the output. This is a genuine security property (HTML injection), not
  just a correctness nicety.

**Stretch goals (pursue after the above is solid):**
- A proven worst-case time-complexity bound (target: linear or O(n log n) in input
  length) for `parseDocument`. This directly targets a known weakness class in existing
  CommonMark implementations (pathological/quadratic behavior on adversarial nesting or
  delimiter-heavy input) and would be a genuinely distinguishing result.
- Idempotence-style properties, e.g. re-rendering/re-parsing stability for restricted
  subsets of the AST, where a meaningful statement exists.
- Equivalence between the implementation and a direct formalization of the "Appendix: A
  parsing strategy" algorithm, if that formalization proves tractable.

Do not force a proof where the underlying fact is false or the formalization would be
more complex than the code it's proving (e.g. don't chase a complexity bound on the
inline delimiter-matching step before it's clear what that step's actual asymptotic
behavior is).

## 7. Testing philosophy

Follow the source project's general testing rules, since they're good defaults here too:
- No tests that just restate a literal with no computation in between — ask "could this
  fail from a real regression, or only by mistyping the expected value?" before adding one.
- Prefer the official example suite as the primary example-based test source over
  hand-written examples, since it's the actual conformance oracle.
- Use property-based testing (the `Plausible` library) for properties that aren't
  naturally example-shaped: e.g. "parseDocument never panics on arbitrary UTF-8 input",
  "renderHtml output is always valid UTF-8", escaping properties, zipper laws under
  random edit sequences.
- Theorems that exist purely to validate the implementation (not needed by production
  code) belong in test code, not the library proper.

## 8. Coding conventions

- All files start with:
  `Copyright (c) 2026 Paul Butcher. All rights reserved.`
  `Released under Apache 2.0 license as described in the file LICENSE.`
- No `partial` functions unless truly unavoidable — if you hit a case that seems to need
  one, stop and reconsider the recursion structure first.
- Comments only where they explain *why*, never restating what the code already says;
  no comments explaining Lean language features; no references to rejected designs,
  tickets, or project process.
- Never use an emdash; use a comma or semicolon instead.
- After editing a `.lean` file, verify with the Lean LSP diagnostics tool available in
  your environment before moving on; ignore generic IDE diagnostic hooks in favor of
  the Lean-specific ones.
- If a change adds/removes an `import`, rebuild via the Lean-aware build tool rather
  than assuming incremental diagnostics caught it.
- Before considering any milestone complete, run the full build and test suite from
  the repo root as ground truth.
- All code should compile with zero warnings.

## 9. Phased project plan

**Phase 0 — Scaffolding**
- `lake new` project set up (already done, presumably, if you're reading this inside one).
- Add dependencies: a JSON parser for loading the spec's example suite (Lean's own
  `Lean.Data.Json` is likely sufficient), `Plausible` for property testing.
- Vendor the official example suite (spec.json or an extraction script from spec.txt)
  into the repo as test data, with a note on its source/license.
- Module skeleton: `CommonMark.Ast`, `CommonMark.Parser.Block`,
  `CommonMark.Parser.Inline`, `CommonMark.Render.Html`, `CommonMark.Zipper`.

**Phase 1 — Walking skeleton**
- Minimal `Inline`/`Block` subset (plain text, paragraphs).
- `parseDocument` that handles a single paragraph of plain text; `renderHtml` for the
  same subset.
- Get one real example from the suite passing end-to-end. This validates the pipeline
  and build/test harness before block/inline complexity arrives.

**Phase 2 — Block-level parser**
- Implement the block-structure algorithm (open-block stack, line-by-line
  incorporation) for: thematic breaks, ATX and Setext headings, indented and fenced
  code blocks, HTML blocks, paragraphs, blank lines, block quotes, list items/lists
  (including tight/loose determination), link reference definitions.
- Inline content at this stage can remain "raw text" pending Phase 3.

**Phase 3 — Inline parser**
- Backslash escapes, entities/numeric character references, code spans.
- The delimiter-run algorithm for emphasis/strong emphasis.
- Links and images: inline, reference (full/collapsed/shortcut), resolving against
  link reference definitions collected in Phase 2.
- Autolinks, raw inline HTML, hard/soft line breaks.

**Phase 4 — Renderer completeness**
- Bring `renderHtml` up to full spec fidelity: exact escaping rules, tight vs. loose
  list rendering, blank-line placement, self-closing tag handling, etc.

**Phase 5 — Conformance**
- Wire up the full example suite as the acceptance test.
- Drive pass rate to 100%, tracking and triaging failures example-by-example.
- Once at 100%, add the `decide`/`native_decide` conformance theorem from Section 3.

**Phase 6 — Zipper & editing API**
- Implement the zipper, its navigation/edit operations, and the round-trip/law proofs.

**Phase 7 — Formal properties**
- Totality/no-`partial` audit (should already hold if Phases 1-6 respected the
  convention; treat any lapse found here as a design smell to fix, not a proof to
  route around).
- Escaping-safety proof.
- Attempt the complexity-bound stretch goal; write up findings even if the bound
  turns out weaker than hoped (that's a legitimate, useful result too).

**Phase 8 — Polish**
- API documentation, usage examples.
- Confirm the library is packageable as a `lake` dependency for consumption by other
  projects.

## 10. Risks & open questions

- The emphasis/delimiter-matching algorithm is the most intricate part of the spec and
  historically the source of both correctness bugs and performance pathologies in other
  implementations; budget real time for it and treat its complexity analysis as a
  distinct sub-task, not an afterthought of Phase 3.
- No independently formal grammar for CommonMark is known to exist; if one surfaces
  during research, re-evaluate Section 3's approach against it.
- Confirm licensing before vendoring spec.json or any reference-implementation source
  into this repo.
- Naming: this plan uses `CommonMark` as a placeholder namespace/package name; pick a
  final name during Phase 0.

## 11. References

- Spec: https://spec.commonmark.org/0.31.2/
- Spec repo (example suite, appendix algorithm): https://github.com/commonmark/commonmark-spec
- JS reference implementation: https://github.com/commonmark/commonmark.js
- C reference implementation: https://github.com/commonmark/cmark
- Djot (a redesign motivated by CommonMark's grammar/ambiguity/performance issues,
  useful background reading on where the hard parts are): https://github.com/jgm/djot
