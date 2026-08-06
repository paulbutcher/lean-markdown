-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
namespace CommonMark

/-- Inline-level content: the children of a paragraph, heading, or another inline node.
    `text`/`code`/`htmlInline`/`softBreak`/`lineBreak` are leaves; the rest carry nested
    content. -/
inductive Inline where
  | text       (s : String)
  | code       (s : String)
  | emph       (content : List Inline)
  | strong     (content : List Inline)
  | link       (dest : String) (title : Option String) (content : List Inline)
  | image      (dest : String) (title : Option String) (content : List Inline)
  | htmlInline (s : String)
  | softBreak
  | lineBreak
  deriving Repr, BEq

/-- A list's marker style: `bullet` for `-`/`*`/`+` lists, `ordered` for `1.`/`1)` lists
    starting from `start`. -/
inductive ListType where
  | bullet (marker : Char)
  | ordered (start : Nat) (delimiter : Char)
  deriving Repr, BEq

/-- Block-level content: the top-level elements of a `Document`, or the children of a
    block quote or list item. `heading`'s `level` is zero-indexed (`0` is `h1`, `5` is
    `h6`). `list`'s `tight`/`items` follow the spec's tight/loose distinction: a tight
    list renders its items' paragraphs without wrapping `<p>` tags. -/
inductive Block where
  | paragraph  (content : List Inline)
  | heading    (level : Fin 6) (content : List Inline)
  | codeBlock  (info : Option String) (literal : String)
  | blockQuote (content : List Block)
  | list       (kind : ListType) (tight : Bool) (items : List (List Block))
  | thematicBreak
  | htmlBlock  (s : String)
  deriving Repr, BEq

/-- A parsed CommonMark document: an ordered list of top-level blocks. -/
abbrev Document := List Block

-- Total node count, used to size fuel for the recursions below (and reused by the
-- renderer): the doubly-nested `list` items make the Block/List Block structural
-- relationship opaque to the termination checker, so recursion is fuel-bounded rather
-- than structural.
mutual
def Block.count : Block → Nat
  | .blockQuote content => 1 + Block.listCount content
  | .list _ _ items => 1 + items.foldl (fun acc c => acc + Block.listCount c) 0
  | _ => 1

def Block.listCount : List Block → Nat
  | [] => 0
  | b :: rest => 1 + Block.count b + Block.listCount rest
end

-- Traversal combinators over Inline/Block, in place of commonmark.js's `.walker()`
-- iterator. `Inline` recurses structurally (Lean can see the List Inline fields are
-- always smaller), so no fuel is needed there; `Block` needs it for the reason above.

mutual
/-- Rewrites every node bottom-up: `f` sees each node's already-rewritten children. -/
def Inline.map (f : Inline → Inline) (i : Inline) : Inline :=
  f (match i with
    | .emph content => .emph (Inline.mapList f content)
    | .strong content => .strong (Inline.mapList f content)
    | .link dest title content => .link dest title (Inline.mapList f content)
    | .image dest title content => .image dest title (Inline.mapList f content)
    | leaf => leaf)

def Inline.mapList (f : Inline → Inline) : List Inline → List Inline
  | [] => []
  | i :: rest => Inline.map f i :: Inline.mapList f rest
end

mutual
/-- Folds over every node, parent before children (matching `.walker()`'s entering
    order). -/
def Inline.foldl (f : β → Inline → β) (acc : β) (i : Inline) : β :=
  match i with
  | .emph content => Inline.foldlList f (f acc i) content
  | .strong content => Inline.foldlList f (f acc i) content
  | .link _ _ content => Inline.foldlList f (f acc i) content
  | .image _ _ content => Inline.foldlList f (f acc i) content
  | leaf => f acc leaf

def Inline.foldlList (f : β → Inline → β) (acc : β) : List Inline → β
  | [] => acc
  | i :: rest => Inline.foldlList f (Inline.foldl f acc i) rest
end

mutual
def Block.mapF (fi : Inline → Inline) (fb : Block → Block) : Nat → Block → Block
  | 0, b => b
  | _ + 1, .paragraph content => fb (.paragraph (Inline.mapList fi content))
  | _ + 1, .heading level content => fb (.heading level (Inline.mapList fi content))
  | fuel + 1, .blockQuote content => fb (.blockQuote (Block.mapListF fi fb fuel content))
  | fuel + 1, .list kind tight items =>
      fb (.list kind tight (items.map (Block.mapListF fi fb fuel)))
  | _ + 1, b => fb b

def Block.mapListF (fi : Inline → Inline) (fb : Block → Block) : Nat → List Block → List Block
  | 0, bs => bs
  | _ + 1, [] => []
  | fuel + 1, b :: rest => Block.mapF fi fb fuel b :: Block.mapListF fi fb fuel rest
end

/-- Rewrites every block and inline node bottom-up. Pass `id` for whichever of `fi`/`fb`
    you don't need. -/
def Block.map (fi : Inline → Inline) (fb : Block → Block) (b : Block) : Block :=
  Block.mapF fi fb b.count b

def Document.map (fi : Inline → Inline) (fb : Block → Block) (doc : Document) : Document :=
  Block.mapListF fi fb (Block.listCount doc) doc

/-- `Block.map` with no block-level rewrite, for callers that only touch inline content. -/
def Block.mapInline (f : Inline → Inline) (b : Block) : Block := Block.map f id b
def Document.mapInline (f : Inline → Inline) (doc : Document) : Document := Document.map f id doc

mutual
def Block.foldF (fi : β → Inline → β) (fb : β → Block → β) : Nat → β → Block → β
  | 0, acc, _ => acc
  | _ + 1, acc, b@(.paragraph content) => Inline.foldlList fi (fb acc b) content
  | _ + 1, acc, b@(.heading _ content) => Inline.foldlList fi (fb acc b) content
  | fuel + 1, acc, b@(.blockQuote content) => Block.foldListF fi fb fuel (fb acc b) content
  | fuel + 1, acc, b@(.list _ _ items) =>
      items.foldl (fun acc' c => Block.foldListF fi fb fuel acc' c) (fb acc b)
  | _ + 1, acc, b => fb acc b

def Block.foldListF (fi : β → Inline → β) (fb : β → Block → β) : Nat → β → List Block → β
  | 0, acc, _ => acc
  | _ + 1, acc, [] => acc
  | fuel + 1, acc, b :: rest => Block.foldListF fi fb fuel (Block.foldF fi fb fuel acc b) rest
end

/-- Folds over every block and inline node, parent before children. -/
def Block.fold (fi : β → Inline → β) (fb : β → Block → β) (init : β) (b : Block) : β :=
  Block.foldF fi fb b.count init b

def Document.fold (fi : β → Inline → β) (fb : β → Block → β) (init : β) (doc : Document) : β :=
  Block.foldListF fi fb (Block.listCount doc) init doc

end CommonMark
