-- Copyright (c) 2026 Paul Butcher. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
import Lake
open Lake DSL

package markdown where
  version := v!"0.8.0"
  leanOptions := #[⟨`warningAsError, true⟩]

require html from git "https://github.com/paulbutcher/lean-html" @ "v0.10.0"

require UnicodeBasic from git
  "https://github.com/fgdorais/lean4-unicode-basic.git" @
  "v2.0.4"

@[default_target]
lean_lib CommonMark

@[default_target]
lean_lib GFMarkdown

-- The tests are a separate package so that neither they nor their dependencies appear in
-- the dependency graph a consumer of this library resolves.
@[test_driver]
script tests do
  let child ← IO.Process.spawn
    { cmd := "lake", args := #["test"], cwd := __dir__ / "test" }
  child.wait
