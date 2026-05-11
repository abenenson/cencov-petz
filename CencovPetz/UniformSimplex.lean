import CencovPetz.Simplex
import CencovPetz.Uniform

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/


/-!
# `CencovPetz.UniformSimplex`

Package the uniform distribution on a finite type as a point of the open simplex.
-/

namespace CencovPetz
open scoped BigOperators

variable {α : Type*} [Fintype α] [Nonempty α]

namespace Simplex

/-- The uniform point of the open simplex. -/
noncomputable def uniform : Simplex α where
  p := uniformDistribution (α := α)
  pos := by
    intro a
    have hcard : 0 < (Fintype.card α : ℝ) := by exact_mod_cast Fintype.card_pos
    simpa [uniformDistribution] using (one_div_pos.2 hcard)
  sum_eq_one := by
    simpa using (uniformDistribution_sum_one (α := α))

@[simp] lemma uniform_apply (a : α) :
    (uniform (α := α)).p a = 1 / (Fintype.card α : ℝ) :=
  rfl

end Simplex
end CencovPetz
