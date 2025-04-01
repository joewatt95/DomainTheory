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
  git "d56dbe9a1637c1160862deb9da8d621682e46013"

require "leanprover-community" / Duper @
  git "v0.0.24"

require "leanprover-community" / mathlib @
  git "v4.17.0"

@[default_target]
lean_lib «DomainTheory» where
  -- add any library configuration options here
