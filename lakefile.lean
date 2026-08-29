import Lake
open Lake DSL

package markdown where
  version := v!"0.6.0"

require html from git "https://github.com/paulbutcher/lean-html" @ "v0.9.0"

require UnicodeBasic from git
  "https://github.com/fgdorais/lean4-unicode-basic.git" @
  "bbb75c5c9b7f30d5e397f27bd099655aed7db410"

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
