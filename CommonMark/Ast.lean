-- Copyright (c) 2026 Paul Butcher. All rights reserved.
namespace CommonMark

inductive Inline where
  | text (s : String)
  deriving Repr, BEq

inductive Block where
  | paragraph (content : List Inline)
  deriving Repr, BEq

abbrev Document := List Block

end CommonMark
