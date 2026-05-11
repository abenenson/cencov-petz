import Lake

open Lake DSL

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/

/-!
# Lakefile

Lake build configuration for the cencov-petz project.
-/

package «cencov-petz» where
  leanOptions := #[
    ⟨`autoImplicit, false⟩
  ]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.29.1"

@[default_target]
lean_lib «CencovPetz» where
  srcDir := "."
  roots := #[`CencovPetz]
