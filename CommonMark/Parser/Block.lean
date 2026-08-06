-- Copyright (c) 2026 Paul Butcher. All rights reserved.
import CommonMark.Ast
import CommonMark.Parser.Inline

namespace CommonMark

def parseDocument (s : String) : Document :=
  let trimmed := s.trimAscii.toString
  if trimmed.isEmpty then
    []
  else
    [.paragraph (Parser.parseInline trimmed)]

end CommonMark
