-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import CommonMark

-- Regression coverage for numeric character references invalid enough to require the
-- REPLACEMENT CHARACTER (U+FFFD) but not exercised by the vendored spec suite: lone UTF-16
-- surrogates, in both their hex and decimal forms.

private def replacement : String := (Char.ofNat 0xFFFD).toString

#guard CommonMark.renderHtml (CommonMark.parseDocument "&#xD800;\n") == s!"<p>{replacement}</p>\n"
#guard CommonMark.renderHtml (CommonMark.parseDocument "&#55296;\n") == s!"<p>{replacement}</p>\n"
#guard CommonMark.renderHtml (CommonMark.parseDocument "&#xDFFF;\n") == s!"<p>{replacement}</p>\n"

-- The boundary just outside the surrogate range, and the maximum valid code point, must still
-- resolve normally rather than being caught by an overly broad guard.
#guard CommonMark.renderHtml (CommonMark.parseDocument "&#xD7FF;\n") ==
  s!"<p>{(Char.ofNat 0xD7FF).toString}</p>\n"
#guard CommonMark.renderHtml (CommonMark.parseDocument "&#xE000;\n") ==
  s!"<p>{(Char.ofNat 0xE000).toString}</p>\n"
#guard CommonMark.renderHtml (CommonMark.parseDocument "&#x10FFFF;\n") ==
  s!"<p>{(Char.ofNat 0x10FFFF).toString}</p>\n"
