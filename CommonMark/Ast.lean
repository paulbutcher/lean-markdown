-- Copyright (c) 2026 Paul Butcher. All rights reserved.
namespace CommonMark

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

inductive ListType where
  | bullet (marker : Char)
  | ordered (start : Nat) (delimiter : Char)
  deriving Repr, BEq

inductive Block where
  | paragraph  (content : List Inline)
  | heading    (level : Fin 6) (content : List Inline)
  | codeBlock  (info : Option String) (literal : String)
  | blockQuote (content : List Block)
  | list       (kind : ListType) (tight : Bool) (items : List (List Block))
  | thematicBreak
  | htmlBlock  (s : String)
  deriving Repr, BEq

abbrev Document := List Block

end CommonMark
