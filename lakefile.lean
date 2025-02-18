import Lake
open Lake DSL

package "DomainTheory" where
  version := v!"0.1.0"
  keywords := #["math"]
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩ -- pretty-prints `fun a ↦ b`
    -- ⟨`autoImplicit, false⟩
  ]

require "nomeata" / loogle @
  git "f9d2b41c350db78179d1b8bbabf0c44bf30c138b"

require "leanprover-community" / mathlib @
  git "v4.17.0-rc1"

@[default_target]
lean_lib «DomainTheory» where
  -- add any library configuration options here
