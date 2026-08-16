import Lake
open Lake DSL

package markdown where
  version := v!"0.3.0"

require html from git "https://github.com/paulbutcher/lean-html" @ "v0.5.0"

require UnicodeBasic from git
  "https://github.com/fgdorais/lean4-unicode-basic.git" @
  "57acd424561ba8179487c4196a2a49a4775a333a"

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
