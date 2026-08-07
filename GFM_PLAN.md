# GFM Support: Project Plan

How to add GitHub Flavored Markdown (GFM) support on top of this library's existing
CommonMark implementation while keeping the CommonMark path a fully conformant,
unmodified implementation — not just behaviorally, but at the type level, wherever
that's achievable without disproportionate cost.

## Decisions this plan encodes

- **The library is renamed `lean-markdown`** (from `lean-commonmark`), and hosts both the
  existing CommonMark implementation and a new GFM variant as two variants of one
  package, not two packages. No git remote or tag has been published under the old name,
  so this is a clean rename with nothing external to migrate.
- **Everything lives in one repo, one package.** The parser logic tables and
  strikethrough need (see Phase 2 below) is too tightly coupled to the existing
  `CommonMark/Parser/Block.lean`/`Inline.lean` state machines to fork into a separate
  package without wholesale duplication, so it has to live here regardless. Once that's
  true, splitting the *rest* of GFM support (task lists, autolinks, raw-HTML filtering —
  all pure post-processing, no parser access needed) into a second package would buy
  nothing: no independent versioning need, no second consumer, and this repo isn't even
  published yet, so a cross-repo dependency would be artificial from day one. The
  type-level separation that matters (CommonMark's public types staying untouched by GFM)
  is achieved by namespace/module separation within the package (see Phase 1), not by a
  repo boundary.
- **The existing `CommonMark` namespace, directory, and lean_lib are left alone** rather
  than nested under a new umbrella namespace. Renaming ~4,400 lines of already-correct,
  already-proven code (`namespace CommonMark` in every file, every `import CommonMark.X`,
  the `CommonMark` lean_lib target) to fit a new hierarchy is churn with no functional
  payoff. The GFM variant becomes a new sibling namespace/lean_lib instead, named
  `GFMarkdown`.
- **The CommonMark path's behavior does not change.** Every existing `#guard` in
  `test/SpecGuards.lean` keeps passing, unmodified, throughout every phase below.
- **GFM-only AST nodes stay out of the public `CommonMark.Block`/`CommonMark.Inline`
  types** wherever the cost is reasonable, via a raw/narrow split (Phase 2) rather than
  added as extra constructors on the shared closed type that every existing exhaustive
  match — including this library's own `Zipper.lean`/`Render/Html.lean` — would have to
  acknowledge forever.
- **Phase 2b (strikethrough) generalizes the existing inline pipeline and proves
  non-emission**, rather than duplicating it. See Phase 2b for the two options weighed;
  this was the single largest cost/uncertainty item in the plan, decided deliberately
  rather than defaulted into.
- **Raw-HTML filtering (Phase 5) is an AST-level pass**, walking `.htmlInline`/
  `.htmlBlock` via `Document.map` before render, rather than a render-time option.
- **Test suite scope covers all three of cmark-gfm's `test/` example suites**:
  `extensions.txt` (the GFM-equivalent of CommonMark's `spec.txt`), plus `regression.txt`
  and `smart_punct.txt`. All three are vendored in `test/vendor/GFM/` (Phase 0); Phase 6
  generates guards from all three.

## Phase 0 — Rename and groundwork

- Rename the package: `lakefile.toml`'s `name = "commonmark"` → `name = "markdown"`;
  repo/directory `lean-commonmark` → `lean-markdown`.
- Update `README.md`: title (`# lean-commonmark` → `# lean-markdown`), the intro
  description (currently "A CommonMark 0.31.2 parser and HTML renderer" — needs to cover
  both variants), and the `Installing` section's example `[[require]]` block (`name =
  "commonmark"` → `name = "markdown"`).
- Leave `CommonMark/`, `namespace CommonMark`, and the `CommonMark` lean_lib target
  exactly as they are (see decision above) — this phase adds the new `GFMarkdown`
  namespace alongside them, as an empty scaffold (`[[lean_lib]] name = "GFMarkdown"` in
  `lakefile.toml`, an empty root module) to confirm the package still builds cleanly
  under the new name before any GFM logic exists.
- `CLAUDE.md` and `KNOWN_ISSUES.md` don't reference the project name directly — no
  changes needed there for the rename itself, though `KNOWN_ISSUES.md` will eventually
  want its own GFM-specific gaps once Phase 2 onward surfaces any.
- Vendor cmark-gfm's `extensions.txt`, `regression.txt`, and `smart_punct.txt`, all from
  the `0.29.0.gfm.13` tag (the latest tagged release), into `test/vendor/GFM/`, alongside
  the existing `test/vendor/CommonMark/spec.txt`/`spec.json`. **Done**: `test/vendor/` is
  now split into `CommonMark/` and `GFM/` subdirectories so it's clear which files apply
  to which variant. All three GFM files use the same exact 32-backtick example-fence
  convention as `spec.txt` (`('`' x 32) . ' example'`), so `scripts/extract_spec.pl`
  needed no changes. `extensions.txt` opens with a YAML front-matter block
  (`---\ntitle: ...\n---`) that `spec.txt` doesn't have; confirmed the script's state
  machine skips it harmlessly, since it only reacts to the example-fence and
  `#`-heading patterns. Extraction verified against all three (30/26/16 examples
  respectively); not yet wired into generated guard files (Phase 6).

## Phase 1 — Raw/narrow split for blocks (enables tables)

- `RawBlock` (`CommonMark/Parser/Block.lean:398-405`) is already internal to
  `Parser/Block.lean` — nothing outside that file matches over it. Add
  `RawBlock.table (header rows : ...)` there; this doesn't touch any exhaustive match
  anywhere else in the library, since it isn't part of it yet.
- Thread a `gfmTables : Bool` parameter through `startsNewBlock`, `processLine`,
  `runLines`, defaulting to `false` at `parseDocument`'s existing call sites (behavior
  provably unchanged there — the new disjunct in `startsNewBlock`'s cascade is `gfmTables
  && ...`, so with `gfmTables = false` it reduces to exactly today's expression).
- Add a `GFMarkdown.Block` type:
  `.commonmark (b : CommonMark.Block) | .table (...)`. `CommonMark.Parser.groupAndConvert`'s
  existing job (`RawBlock → CommonMark.Block`, `CommonMark/Parser/Block.lean:744-745`)
  gets a sibling `groupAndConvertGfm : LinkDefs → List RawBlock → List GFMarkdown.Block`
  that maps `.table` `RawBlock`s to `GFMarkdown.Block.table` and delegates everything
  else to the existing conversion, wrapped in `.commonmark`.
- Table cell content: keep raw `String` in `RawBlock.table`, consistent with how
  `RawBlock.paragraph` defers inline parsing to the block→`Block` conversion step, rather
  than inline-parsing cells early.

## Phase 2 — Tables

Implement `matchTableStart` and the row/alignment/header parsing logic in
`Parser/Block.lean`, gated behind `gfmTables`, producing `RawBlock.table`. Cover the
spec's paragraph-interruption rule (a table can start where a paragraph would) and
column-count/alignment-row validation. Render the new `Block.table` case to
`<table>`/`<thead>`/`<tbody>` via the `Html` library's constructors, matching how
`Render/Html.lean` already builds output for the base `CommonMark.Block` cases.

## Phase 2b — Raw/narrow split and implementation for inlines (enables strikethrough)

Unlike tables, strikethrough can't be isolated as cleanly: GFM's `~~` delimiter has to
compete with `*`/`_` inside the *same* delimiter-stack resolution (`resolveEmphasis`,
`CommonMark/Parser/Inline.lean:668`) for correct nesting behavior — it can't be recognized
in a separate pass over already-tokenized text. `emphBucket`
(`CommonMark/Parser/Inline.lean:661-662`) hardcodes a two-way `*`/`_` split, and the
tokenizer (`CommonMark/Parser/Inline.lean:625`) hardcodes `c == '*' || c == '_'` as the
only delimiter-run characters. `INode.flattenNode` also returns `CommonMark.Inline`
concretely, not a type parameter. Two ways through this:

- **(i) Generalize the pipeline, prove non-emission.** Introduce `RawInline`
  (mirrors `CommonMark.Inline` plus `.strikethrough (content : List RawInline)`); make
  `INode`, `tokenizeF`, `resolveEmphasis`, `flattenNode` operate over `RawInline`;
  extend `emphBucket`'s bucketing and `resolveEmphasis`'s matching rules to cover `~~`
  (which has different matching arity rules than `*`/`_` — GFM only matches
  same-length 1-or-2-tilde runs, no partial-length matching). The plain
  (non-GFM) path gates the tokenizer so `~` is never treated as a delimiter, then proves
  a lemma (`∀ s defs, ¬ (parseInlineRaw false defs s).any .isStrikethrough` or similar) that
  lets a *total*, panic-free narrowing function `RawInline → CommonMark.Inline` be
  written for that path. One nontrivial proof, concentrated in one place; no code
  duplication; airtight, checked guarantee — consistent with how this project already
  handles other non-emission properties (`HtmlWellFormedness.lean`'s "no
  `.htmlInline`/`.htmlBlock`" precondition is the same shape of claim).
- **(ii) Duplicate the pipeline.** Copy `tokenizeF`/`resolveEmphasis`/`flattenNode` into a
  GFM-flavored variant that knows about `~~` from the start, leaving the original
  untouched. No proof burden, no generalization risk, but a second copy of ~200-300 lines
  of delicate delimiter-matching logic to keep in sync by hand if the CommonMark
  algorithm itself is ever touched.

**Decided: (i).** This project already prefers proofs over parallel implementations
where the proof is tractable, and a fork here is exactly the kind of duplication that
tends to silently drift. This is the single biggest cost/uncertainty item in the plan —
size it properly; it's probably the largest phase by effort.

**Verification gate for Phases 1-2b:** `lake build` and `lake test` green with zero
behavior change on the CommonMark path — the existing 652 `#guard`s in
`test/SpecGuards.lean` and all of `ZipperLaws.lean`/`ParserLaws.lean`/
`HtmlWellFormedness.lean` pass unmodified throughout.

## Phase 3 — Non-emission proofs

Formalize what Phases 1-2b established informally: `CommonMark.parseDocument` never
produces output requiring GFM-only handling, and (for whichever parts ended up inside the
shared type rather than behind the raw/narrow split) `CommonMark.renderHtml` never
depends on cases that can't occur. Land these as theorems in `test/`, matching the
existing convention (`ZipperLaws.lean`, `ParserLaws.lean`, `HtmlWellFormedness.lean`) of
proving properties nothing in the library itself depends on.

## Phase 4 — Task lists and extended autolinks

Both are pure post-processing over the GFM `Document` (or, for autolinks, even a plain
`CommonMark.Document`), independent of the harder table/strikethrough work, and can start
as soon as there's a document to operate on — task list items in particular don't even
need to wait on Phase 1 onward, since they only need a well-formed list item, which the
unmodified base parser already produces:

- **Task list items**: detect the `[ ] `/`[x] ` prefix on a list item's first inline
  content.
- **Extended autolinks**: bare URL/`www.`/email recognition over `.text` leaves, using
  `Document.mapInline` (`CommonMark/Ast.lean`). Distinct from this library's existing
  `matchAutolink`/`matchUriAutolink`/`matchEmailAutolink` (`Parser/Inline.lean`), which
  only handle CommonMark's angle-bracket form; those aren't reusable directly but are a
  good structural reference for the character-classification style to match.

## Phase 5 — Raw-HTML filter

Walk `.htmlInline`/`.htmlBlock` content and neuter GitHub's disallowed tag list before
render, as an AST-level pass (via `Document.map`), to keep it composable with the rest of
the pipeline.

## Phase 6 — GFM conformance suite

Adapt the two-stage pipeline this repo just adopted for its own CommonMark suite
(`scripts/extract_spec.pl`/`scripts/generate_guards.pl`, `test/CheckExample.lean`,
`test/SpecGuards.lean`) for cmark-gfm's `extensions.txt`, `regression.txt`, and
`smart_punct.txt` (all vendored in Phase 0), following the same pattern as a sibling test
target (mirroring `TestData`) rather than a separate project's test suite. Expect many
generated `#guard`s to fail until Phases 2-5 land — that's expected, and the generated
file doubles as a concrete, spec-derived checklist of remaining work rather than
something to write by hand.

## Phase 7 — Docs

Update `README.md`'s "Guarantees" section to describe the GFM entry points alongside the
existing CommonMark ones, being precise about which guarantees extend to GFM output and
which remain CommonMark-only. Add a GFM-specific section to `KNOWN_ISSUES.md` for any
spec gaps Phases 2-5 leave behind, in the same spirit as the existing CommonMark entries.
