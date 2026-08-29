-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
module

public import CheckExampleMath
meta import CheckExampleMath

@[expose] public section

-- The inputs where this library's math output deliberately differs from md4c's, pinned so that
-- "fixing" one of them fails here and forces KNOWN_ISSUES.md to be updated alongside. Every
-- other case lives in the generated MathGuards.lean/MathInteractionGuards.lean, which hold
-- md4c's own answers. Those files hold only cases where the two agree, so
-- `scripts/verify_md4c.pl` can re-check every one of them against md4c itself with no
-- exclusion list to keep in step here.

-- Emphasis/math crossing (KNOWN_ISSUES.md 4). md4c resolves `$` in the same left-to-right mark
-- pass as `*`/`_`, so the span whose *closing* delimiter comes first wins and it retroactively
-- un-resolves whatever it swallowed; resolving math at tokenize time instead always gives math.
-- md4c: <p><em>a $b</em> c$</p>
#guard checkExampleMath 1 "Crossing" "*a $b* c$\n"
  "<p>*a <span class=\"math inline\">\\(b* c\\)</span></p>\n"
-- md4c: <p><em>a $b</em> c$</p>
#guard checkExampleMath 2 "Crossing" "_a $b_ c$\n"
  "<p>_a <span class=\"math inline\">\\(b_ c\\)</span></p>\n"
-- md4c: <p><strong>a $b</strong> c$</p>
#guard checkExampleMath 3 "Crossing" "**a $b** c$\n"
  "<p>**a <span class=\"math inline\">\\(b** c\\)</span></p>\n"

