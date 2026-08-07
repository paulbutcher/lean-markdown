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

## Phase 1 — Raw/narrow split for blocks (enables tables) — **Done**

- `RawBlock` (`CommonMark/Parser/Block.lean`) is already internal to `Parser/Block.lean` —
  nothing outside that file matches over it. Added `RawBlock.table (header : List String)
  (alignments : List TableAlignment) (rows : List (List String))`, plus the `TableAlignment`
  enum (`left`/`right`/`center`/`unset`) it needs. `rawBlockToBlockF`'s match over `RawBlock`
  lives in this same file, though, and *is* exhaustive over the type — adding a constructor
  there meant giving it a `.table` arm too. Since nothing produces `RawBlock.table` until
  `gfmTables` exists (Phase 2), that arm is presently unreachable dead code from the plain
  path's perspective; it returns `.paragraph []`, the same kind of total-but-unreachable
  fallback the file's fuel-exhaustion case (`| 0, _ => .paragraph []`) already uses. Phase 3
  formalizes the unreachability; until then it's an informal invariant, same as elsewhere in
  this file.
- Table cell content: kept raw `String` in `RawBlock.table`, consistent with how
  `RawBlock.paragraph` defers inline parsing to the block→`Block` conversion step, rather
  than inline-parsing cells early.
- **`GFMarkdown.Block` design changed from the original sketch.** The plan originally called
  for a flat `.commonmark (b : CommonMark.Block) | .table (...)` wrapper. That's a
  correctness bug: `CommonMark.Block.blockQuote`/`.list` hold `List CommonMark.Block`
  recursively, so once a block quote or list item's content is wrapped in `.commonmark`,
  there is no way for a table nested inside it to surface as `.table` — it would silently
  become an empty paragraph instead (cmark-gfm's own `extensions.txt` doesn't test nested
  tables, so this wouldn't have shown up as a conformance-suite failure, only as silent
  data loss on real input like a table inside a changelog list item). Decided: `GFMarkdown.Block`
  gets its own `blockQuote`/`list` constructors (recursing over `List GFMarkdown.Block`), so a
  table is recognized at any nesting depth. Every other CommonMark block kind (paragraph,
  heading, codeBlock, thematicBreak, htmlBlock) has no nested-block content, so those are
  still reused as-is via `commonmark` rather than restated — only the two recursive
  constructors needed duplicating. Landed in `GFMarkdown/Ast.lean`.
- `CommonMark.Parser.groupAndConvert`'s existing job (`RawBlock → CommonMark.Block`) gets a
  sibling `GFMarkdown.Parser.groupAndConvertGfm : LinkDefs → List RawBlock → List
  GFMarkdown.Block` (`GFMarkdown/Parser.lean`) that mirrors its mutual, fuel-bounded
  recursion, but recurses into `GFMarkdown.Block` for `blockQuote`/`listItem` instead of
  delegating to the plain conversion (required for the nested-table fix above); every other
  `RawBlock` constructor delegates to `CommonMark.Parser.rawBlockToBlockF` (called with
  fuel `1`, always sufficient since none of those constructors recurse) wrapped in
  `.commonmark`, avoiding restating `parseInline`/`headingLevelToFin` logic for them.
- **`gfmTables : Bool` threading deferred to Phase 2, bundled with `matchTableStart`.**
  Confirmed empirically that Lean's unused-variable linter fires on an unreferenced function
  parameter (`lake build` warning), so threading `gfmTables` through `startsNewBlock`/
  `processLine`/`runLines` now, with nothing yet consulting it, isn't viable without
  violating "no warnings." It has no genuine use until `matchTableStart` exists to be
  gated by it, so the two land together in Phase 2.

## Phase 2 — Tables — **Done**

Grounded in cmark-gfm's actual reference implementation (`extensions/table.c`,
`extensions/ext_scanners.re`, and the core block-opening precedence in `src/blocks.c`),
fetched and read directly, rather than re-deriving the algorithm from `extensions.txt`'s
~16 examples alone — several rules (exact escaping semantics, precedence against setext
headings/thematic breaks/list markers, the "only the paragraph's *last* line becomes the
header" rule) aren't fully pinned down by the example suite and would've been easy to get
subtly wrong otherwise.

- **`gfmTables` ended up threaded through only `processLine`/`runLines`, not
  `startsNewBlock`/`startBlockFrom` as originally planned.** Reading cmark-gfm's core
  block-opening chain (`src/blocks.c`'s `open_new_blocks`) showed table detection is
  strictly the *last* priority, tried only after blockquote/ATX/fence/HTML-block/setext/
  thematic-break/footnote/list-marker/indented-code have all already failed to match, and
  only when there's an *already-open paragraph* to retroactively convert (never as a fresh
  block open). That's exactly the position right after `startsNewBlock true remainder`
  returns `false` inside `processLine`'s `.paragraph` handling — not a new disjunct in
  `startsNewBlock` itself (which has no way to see "the paragraph's last buffered line"
  anyway, needed to check the delimiter row's column count against it).
- **`RawBlock.table`/`TableAlignment`, table cell/delimiter-row scanning
  (`stripTableLeadingPipe`/`scanTableCellChars`/`tableRowCellsGoF`/`unescapeTablePipesGo`/
  `matchTableRow`/`matchTableMarkerCell`/`matchTableDelimiterRow`), a new
  `OpenLeaf.table` accumulator, and `tryOpenTableFromParagraph` (the paragraph→table
  conversion, splitting off any leading lines before the header into their own paragraph)
  all landed in `CommonMark/Parser/Block.lean`, alongside `RawBlock` per Phase 1's
  reasoning. Cell scanning mirrors `row_from_string`'s escaped-pipe handling exactly
  (`isEscapable`-aware splitting, so `\|` doesn't split a cell but plain `|` does); pipe
  *unescaping* afterward deliberately reproduces cmark-gfm's narrower, non-`isEscapable`-aware
  `unescape_pipes` naive scan verbatim, including its quirks on inputs no real table needs
  (e.g. a cell ending `\\\|`).
- `GFMarkdown.parseDocument` (`GFMarkdown/Parser.lean`) runs the shared state machine with
  `gfmTables := true` and converts via `groupAndConvertGfm`.
- `GFMarkdown/Render/Html.lean` renders `.table` to `<table>`/`<thead>`/`<tbody>` via the
  `Html` library's typed table constructors (`rawAttrs` for the legacy `align="..."`
  attribute cmark-gfm still emits, since the library's typed `ThAttrs`/`TdAttrs` don't
  model it), and gives `GFMarkdown.Block` its own `renderBlockNodesF`/`renderBlocksNodeF`/
  `itemNode`, mirroring `CommonMark.Render.Html`'s (`commonmark`-wrapped leaves delegate to
  it directly with fuel `1`) rather than reusing it wholesale, since a mixed
  `GFMarkdown.Block` sibling list needs the tight-paragraph-separator logic to see across
  `.table`/`.blockQuote`/`.list` nodes too, not just plain CommonMark ones.
- Verified against all 16 table-related examples in `test/vendor/GFM/extensions.json`,
  landed as `test/GfmGuards.lean` (generated by `scripts/generate_guards.pl`, now
  generalized with optional checker/import arguments so it isn't
  CommonMark-`SpecGuards.lean`-specific — see `test/vendor/README.md` for the regeneration
  command; this file grows its example range as later phases add sections, rather than one
  file per feature) plus `test/CheckExampleGfm.lean`. Confirmed the plain
  `CommonMark.parseDocument` path still treats the same table-shaped input as an ordinary
  paragraph (no leakage).

## Phase 2b — Raw/narrow split and implementation for inlines (enables strikethrough) — **Done**

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
tends to silently drift.

**Landed**, grounded in cmark-gfm's actual `extensions/strikethrough.c` (fetched and read
directly, same approach as Phase 2's table work): confirmed `~` genuinely shares
`resolveEmphasis`'s delimiter-stack scan with `*`/`_` (`cmark_syntax_extension_set_emphasis`
marks it as participating in the same core scan), but with different matching rules —
exact-length pairs only (no partial consumption, no rule-of-3), and a failed same-bucket
match discards *both* delimiters outright rather than leaving them live for a later match
(verified against `extensions.txt`'s "No ~mismatch~~" case).

- `RawInline` (`CommonMark/Parser/Inline.lean`) mirrors `CommonMark.Inline` plus
  `strikethrough`; `INode.resolved`/`flattenNode` now carry/return it. `takePlainRun` and
  `tokenizeF` both gained a `gfmStrikethrough : Bool` parameter — `false` reduces every new
  branch to exactly the prior code path *syntactically* (not just behaviorally), which is
  what makes "the plain path is unchanged" checkable by inspection rather than resting on
  the harder non-emission proof alone. `resolveEmphasis`/`resolveBrackets` didn't need a
  new parameter: their behavior is entirely determined by whether a `.delim '~' ...` node
  already exists in their input array, which `gfmStrikethrough` controls upstream at
  tokenize time.
- `resolveEmphasis` gained a `c == '~'` branch alongside the existing `*`/`_` handling
  (same outer scan, same array, different matching rule once a same-character opener is
  found) — a *nearest*-opener search with its own `tildeBottom` (not the 12-way
  `*`/`_` bucket array: no rule-of-3 means no bucketing needed, just the one performance
  safeguard against rescanning a range with no available opener).
- `parseInlineRaw (gfmStrikethrough) (defs) (s) : List RawInline` is the new generalized
  entry point; `parseInline` (unchanged signature, `List CommonMark.Inline`) now calls it
  with `gfmStrikethrough := false` and narrows the result via `narrowInline`/
  `narrowInlineList : RawInline → CommonMark.Inline`, a total structural translation that's
  the identity on the 9 shared constructors and falls back to `.text ""` for
  `.strikethrough` — the same "informal now, total but presently-unreachable fallback"
  idiom `RawBlock.table`'s case in `rawBlockToBlockF` already established in Phase 1,
  **not yet backed by the formal non-emission proof** the original plan text above
  describes (`∀ s defs, ¬ (parseInlineRaw false defs s).any .isStrikethrough`-shaped).
  That proof is substantial on its own — `resolveEmphasis` is `Id.run`/`for`/`mut`
  imperative-style, not the equation-friendly pattern-matched recursion the rest of this
  file's proofs (`ZipperLaws`, `ParserLaws`, `HtmlWellFormedness`) work with — and Phase 3
  already exists for exactly this ("formalize what Phases 1-2b established informally"),
  so it's deferred there rather than blocking this phase. Confirmed empirically instead:
  all 652 `#guard`s in `SpecGuards.lean` plus `ZipperLaws`/`ParserLaws`/
  `HtmlWellFormedness` pass **unmodified** after this generalization.
- **`GFMarkdown.Block`'s design changed again**, for a reason structurally identical to
  Phase 1's nested-table fix: the Phase 1/2 `commonmark (b : CommonMark.Block)` wrapper
  (kept for non-recursive leaf kinds even after Phase 2 added `blockQuote`/`list` as
  GFMarkdown-native constructors) breaks once `paragraph`/`heading` need to hold content
  that can contain a `strikethrough`, since `CommonMark.Block.paragraph`'s content is fixed
  at `List CommonMark.Inline`, which can never hold one. `GFMarkdown.Block` is now a full,
  wrapper-free mirror of `CommonMark.Block`'s shape (`GFMarkdown/Ast.lean`) — every
  inline-bearing field is `List RawInline` instead of `List CommonMark.Inline`, plus
  `table`. `GFMarkdown.Parser.rawBlockToBlockGfmF`/`groupAndConvertGfmF`
  (`GFMarkdown/Parser.lean`) and the renderer (`GFMarkdown/Render/Html.lean`) both became
  fully independent mirrors of their `CommonMark` counterparts accordingly (nothing left to
  usefully delegate to fuel `1`, unlike Phase 1's version), with the renderer adding
  `<del>` for `strikethrough`.
- Verified against both Strikethroughs examples in `extensions.txt` (now examples 17-18 in
  `test/GfmGuards.lean`, widened from Phase 2's 1-16), plus ad hoc checks for interaction
  with tables and emphasis nesting (`~gone~ *ok*` in a table cell; `~~*x*~~`/`**~~x~~**`
  nesting both ways) — all correct.

**Verification gate for Phases 1-2b:** `lake build` and `lake test` green with zero
behavior change on the CommonMark path — the existing 652 `#guard`s in
`test/SpecGuards.lean` and all of `ZipperLaws.lean`/`ParserLaws.lean`/
`HtmlWellFormedness.lean` pass unmodified throughout. **Confirmed.**

## Phase 3 — Non-emission proofs

Formalize what Phases 1-2b established informally: `CommonMark.parseDocument` never
produces output requiring GFM-only handling, and (for whichever parts ended up inside the
shared type rather than behind the raw/narrow split) `CommonMark.renderHtml` never
depends on cases that can't occur. Land these as theorems in `test/`, matching the
existing convention (`ZipperLaws.lean`, `ParserLaws.lean`, `HtmlWellFormedness.lean`) of
proving properties nothing in the library itself depends on.

The concrete, known items: (1) `RawBlock.table`'s fallback case in
`CommonMark.Parser.rawBlockToBlockF` (`Block.lean`) is unreachable when `gfmTables = false`
in `runLines`/`processLine`'s call chain; (2) `narrowInline`'s `.strikethrough` fallback
(`Inline.lean`) is unreachable in `parseInline`'s call to `parseInlineRaw false defs s` —
this second one is the harder proof, since `resolveEmphasis`'s `Id.run`/`for`/`mut`
imperative style doesn't unfold equationally the way this project's other proofs
(pattern-matched recursion) do; expect to either find an induction principle that works
over its `for`-loop structure, or refactor it into an equivalent pattern-matched recursive
form first (which would itself need to preserve the file's own performance-safety
argument, the `bottoms`/`tildeBottom` O(n²)-avoidance comment) before the proof becomes
tractable. Both are the same shape of claim as `HtmlWellFormedness.lean`'s existing
"no `.htmlInline`/`.htmlBlock`" precondition, so that file's proof structure (`noHtml`-style
decidable predicate, structural induction showing the parser never produces `false` for it)
is the closest existing template, even though neither of *this* phase's two proofs are
about the renderer the way that one is.

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
something to write by hand. Phase 2 already generated `test/GfmTableGuards.lean` for
`extensions.txt` examples 1-16 (the table sections) using the same, by-then-already-
generalized `generate_guards.pl`; this phase's job is examples 17-30 (strikethrough,
autolinks, HTML tag filter, footnotes, task lists) plus `regression.txt`/`smart_punct.txt`,
either folded into one combined suite or left as `GfmTableGuards.lean` stays now (decide
when this phase starts, weighing one generated file against several).

## Phase 7 — Docs

Update `README.md`'s "Guarantees" section to describe the GFM entry points alongside the
existing CommonMark ones, being precise about which guarantees extend to GFM output and
which remain CommonMark-only. Add a GFM-specific section to `KNOWN_ISSUES.md` for any
spec gaps Phases 2-5 leave behind, in the same spirit as the existing CommonMark entries.
