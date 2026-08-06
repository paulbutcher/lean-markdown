-- Copyright (c) 2026 Paul Butcher. All rights reserved.
import CommonMark.Ast

namespace CommonMark.Parser

def parseInline (s : String) : List CommonMark.Inline :=
  [.text s]

end CommonMark.Parser
