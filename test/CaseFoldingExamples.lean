-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import CommonMark

-- Regression coverage for a full-Unicode-case-fold exception not exercised by the vendored
-- spec suite: İ (U+0130, LATIN CAPITAL LETTER I WITH DOT ABOVE) folds to two characters, "i"
-- followed by COMBINING DOT ABOVE (U+0307), not to a single character.

private def combiningDotAbove : String := (Char.ofNat 0x0307).toString

#guard CommonMark.renderHtml (CommonMark.parseDocument s!"[İ]\n\n[i{combiningDotAbove}]: /url\n") ==
  s!"<p><a href=\"/url\">İ</a></p>\n"
