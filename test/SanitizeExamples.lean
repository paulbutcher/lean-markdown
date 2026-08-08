-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import CommonMark
import GFMarkdown
import Plausible

-- `SanitizeSafety.lean`/`GfmSanitizeSafety.lean` prove `Document.sanitize`'s two properties
-- formally; these are a behavioral safety net on top, through the public
-- `parseDocument`/`renderHtmlSafe` API a caller actually uses: legitimate content isn't
-- needlessly lost (the proofs don't rule out a degenerate "always empty" sanitize), and
-- specific known-dangerous inputs (script tags, `javascript:`, mixed-case scheme bypasses)
-- are neutralized end-to-end.

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

-- `javascript:` with a mixed-case scheme (a common naive-filter bypass) must be caught too:
-- `isSafeUriScheme` lowercases before checking the allowlist, so this fuzzes over every
-- capitalization rather than trusting a single hand-picked example.
private def mixedCaseJavascript (bits : Nat) : String :=
  let letters := "javascript".toList
  String.ofList (letters.mapIdx (fun i c => if bits >>> i &&& 1 == 1 then c.toUpper else c))

#eval Plausible.Testable.check
  (∀ bits : Nat,
    !containsSubstr
      (CommonMark.renderHtmlSafe
        (CommonMark.parseDocument s!"[x]({mixedCaseJavascript bits}:alert(1))\n"))
      ":alert(1)" = true)
