import Lake
open Lake DSL

meta if get_config? doc = some "on" then
require «doc-gen4» from git "https://github.com/leanprover/doc-gen4" @ "main"

require std from git "https://github.com/leanprover/std4" @ "main"

package bourbaki where

lean_lib «Bourbaki»
lean_lib docs where
  roots := #[`docs]
