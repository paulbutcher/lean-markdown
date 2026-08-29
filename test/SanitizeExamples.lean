-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import CommonMark
public import GFMarkdown
meta import CommonMark
meta import GFMarkdown

@[expose] public section

-- `SanitizeSafety.lean`/`GfmSanitizeSafety.lean` prove `Document.sanitize`'s two properties
-- formally; these are a behavioral safety net on top, through the public
-- `parseDocument`/`renderHtmlSafe` API a caller actually uses: legitimate content isn't
-- needlessly lost (the proofs don't rule out a degenerate "always empty" sanitize), and
-- specific known-dangerous inputs (script tags, `javascript:`) are neutralized end-to-end.

open CommonMark.Parser (containsSubstr)

#guard !containsSubstr
  (CommonMark.renderHtmlSafe (CommonMark.parseDocument "Hello <script>alert(1)</script> world\n"))
  "<script>"

#guard !containsSubstr
  (CommonMark.renderHtmlSafe (CommonMark.parseDocument "<div onload=\"evil()\">x</div>\n\nSome *text*\n"))
  "<div"

#guard containsSubstr
  (CommonMark.renderHtmlSafe (CommonMark.parseDocument "<div onload=\"evil()\">x</div>\n\nSome *text*\n"))
  "<em>text</em>"

#guard !containsSubstr
  (CommonMark.renderHtmlSafe (CommonMark.parseDocument "[click me](javascript:alert(1))\n"))
  "javascript:"

#guard containsSubstr
  (CommonMark.renderHtmlSafe (CommonMark.parseDocument "[click me](javascript:alert(1))\n"))
  "click me"

#guard !containsSubstr
  (CommonMark.renderHtmlSafe (CommonMark.parseDocument "![alt](javascript:alert(1))\n"))
  "javascript:"

#guard containsSubstr
  (CommonMark.renderHtmlSafe (CommonMark.parseDocument "[a link](https://example.com/page)\n"))
  "href=\"https://example.com/page\""

#guard containsSubstr
  (CommonMark.renderHtmlSafe (CommonMark.parseDocument "[mail](mailto:a@b.com)\n"))
  "href=\"mailto:a@b.com\""

#guard !containsSubstr
  (CommonMark.renderHtmlSafe (CommonMark.parseDocument "[x](data:text/html,<script>alert(1)</script>)\n"))
  "data:"

#guard !containsSubstr
  (GFMarkdown.renderHtmlSafe (GFMarkdown.parseDocument "| a | b |\n| --- | --- |\n| <script>x</script> | [y](javascript:alert(1)) |\n"))
  "<script>"

#guard !containsSubstr
  (GFMarkdown.renderHtmlSafe (GFMarkdown.parseDocument "| a | b |\n| --- | --- |\n| <script>x</script> | [y](javascript:alert(1)) |\n"))
  "javascript:"

#guard containsSubstr
  (GFMarkdown.renderHtmlSafe (GFMarkdown.parseDocument "| a | b |\n| --- | --- |\n| <script>x</script> | [y](javascript:alert(1)) |\n"))
  "<a href=\"\">y</a>"

#guard !containsSubstr
  (GFMarkdown.renderHtmlSafe (GFMarkdown.parseDocument "~~<img src=x onerror=alert(1)>~~\n"))
  "<img"

-- One mixed-case `javascript:` end-to-end. Every other capitalization is covered by
-- `UriSchemeLaws.lean`'s `not_isSafeUriScheme_javascript`, which proves the whole family
-- rejected rather than sampling it.
#guard !containsSubstr
  (CommonMark.renderHtmlSafe (CommonMark.parseDocument "[x](JaVaScRiPt:alert(1))\n"))
  ":alert(1)"
