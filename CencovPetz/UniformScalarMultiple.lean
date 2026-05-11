import CencovPetz.PermutationInvariantBilinForm

/-
Copyright (c) 2026 Adam Benenson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adam Benenson
-/


/-!
# `CencovPetz.UniformScalarMultiple`

At the uniform point on a finite simplex, a monotone metric family's bilinear form is a scalar
multiple of the Fisher bilinear form.

This is an algebraic step in the finite Čencov/Chentsov uniqueness proof: permutation invariance
plus the `dij` relations imply that (at the uniform point) the metric is determined by a single
scalar.
-/

namespace CencovPetz
open scoped BigOperators

namespace TangentFin

namespace Bilin

  open Basis
  
  variable {n : ℕ} (G : MonotoneMetricFamily) [Nonempty (Fin n)]

  omit [Nonempty (Fin n)] in
  private lemma sum_smul_dij_eq (u : V n) (i0 : Fin n) :
      (∑ i : Fin n, ((u : Fin n → ℝ) i) • dij (n := n) i i0) = u := by
    classical
    ext k
    have hu_sum : (∑ i : Fin n, (u : Fin n → ℝ) i) = 0 :=
      (tangentSpace.mem_iff (α := Fin n) (u := (u : Fin n → ℝ))).1 u.property
    have h_pick :
        (∑ i : Fin n, (u : Fin n → ℝ) i * e (n := n) i k) = (u : Fin n → ℝ) k := by
      have :
          (∑ i : Fin n, (u : Fin n → ℝ) i * e (n := n) i k) =
            (u : Fin n → ℝ) k * e (n := n) k k := by
        refine
          (Fintype.sum_eq_single k
            (f := fun i : Fin n => (u : Fin n → ℝ) i * e (n := n) i k) ?_)
        intro i hi
        have hk : k ≠ i := by simpa [eq_comm] using hi
        have : e (n := n) i k = 0 := by
          simp [e, Pi.single_eq_of_ne hk]
        simp [this]
      simpa [e] using this
    have h_const :
        (∑ i : Fin n, (u : Fin n → ℝ) i * e (n := n) i0 k) =
          (∑ i : Fin n, (u : Fin n → ℝ) i) * e (n := n) i0 k := by
      simpa using
        (Finset.sum_mul (s := (Finset.univ : Finset (Fin n)))
          (f := fun i : Fin n => (u : Fin n → ℝ) i) (a := e (n := n) i0 k)).symm
    have h :
        (∑ i : Fin n, (u : Fin n → ℝ) i * (e (n := n) i k - e (n := n) i0 k))
          = (u : Fin n → ℝ) k := by
      calc
        (∑ i : Fin n, (u : Fin n → ℝ) i * (e (n := n) i k - e (n := n) i0 k))
            = (∑ i : Fin n, (u : Fin n → ℝ) i * e (n := n) i k)
                - (∑ i : Fin n, (u : Fin n → ℝ) i * e (n := n) i0 k) := by
                  simp [sub_eq_add_neg, mul_add, Finset.sum_add_distrib]
        _ = (u : Fin n → ℝ) k - ((∑ i : Fin n, (u : Fin n → ℝ) i) * e (n := n) i0 k) := by
              simp [h_pick, h_const]
        _ = (u : Fin n → ℝ) k := by
              simp [hu_sum]
    simpa [Basis.dij_coe, sub_eq_add_neg, mul_add, Finset.sum_add_distrib] using h
  set_option maxHeartbeats 250000 in
  theorem B_eq_smul_fisherBilin_uniform (i0 i1 : Fin n) (hi01 : i0 ≠ i1) :
    B (G := G) (n := n)
      =
        (B (G := G) (n := n) (dij (n := n) i0 i1) (dij (n := n) i0 i1) /
            (2 * (Fintype.card (Fin n) : ℝ))) • fisherBilin (Simplex.uniform (α := Fin n)) := by
    classical
    haveI : Nonempty (Fin n) := ⟨i0⟩
    -- Set the scalar `c` from the `dij` self-pairing.
    set c : ℝ := B (G := G) (n := n) (dij (n := n) i0 i1) (dij (n := n) i0 i1) with hc
    have hcard_ne : (Fintype.card (Fin n) : ℝ) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt Fintype.card_pos)
    -- Symmetry (for `ext_of_isSymm`).
    have hSymm₁ : (B (G := G) (n := n)).IsSymm := by
      refine ⟨fun u v => ?_⟩
      simpa using (B_symm (G := G) (n := n) u v)
    have hSymm₂ :
        (((c / (2 * (Fintype.card (Fin n) : ℝ))) •
          fisherBilin (Simplex.uniform (α := Fin n)))).IsSymm := by
      refine ⟨fun u v => ?_⟩
      simp [fisherBilin.comm (p := Simplex.uniform (α := Fin n))]
    -- Compute the diagonal `B u u` for an arbitrary tangent vector `u`.
    have hdiag : ∀ u : V n,
        B (G := G) (n := n) u u =
          ((c / (2 * (Fintype.card (Fin n) : ℝ))) •
            fisherBilin (Simplex.uniform (α := Fin n))) u u := by
      intro u
      -- Rewrite `u` in the `dij _ i0` spanning family.
      have hu_repr : (∑ i : Fin n, ((u : Fin n → ℝ) i) • dij (n := n) i i0) = u :=
        sum_smul_dij_eq (n := n) (u := u) (i0 := i0)
      -- First compute `B u u` as a double sum over the `dij` spanning family.
      have hB_sum :
          B (G := G) (n := n) u u =
            ∑ i : Fin n, ∑ j : Fin n,
              (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
                B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0) := by
        -- Expand both arguments using bilinearity.
        -- (Lean can do this with `simp` once `u` is rewritten as a sum.)
        calc
            B (G := G) (n := n) u u
                =
                  B (G := G) (n := n)
                    (∑ i : Fin n, ((u : Fin n → ℝ) i) • dij (n := n) i i0)
                    (∑ j : Fin n, ((u : Fin n → ℝ) j) • dij (n := n) j i0) := by
                      simp [hu_repr]
          _ = ∑ i : Fin n, ∑ j : Fin n,
                ((u : Fin n → ℝ) i) * ((u : Fin n → ℝ) j) *
                  B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0) := by
                    classical
                    have h :
                        B (G := G) (n := n)
                            (∑ i : Fin n, ((u : Fin n → ℝ) i) • dij (n := n) i i0)
                            (∑ j : Fin n, ((u : Fin n → ℝ) j) • dij (n := n) j i0)
                          =
                          ∑ x : Fin n, ∑ i : Fin n,
                            ((u : Fin n → ℝ) x) *
                              (((u : Fin n → ℝ) i) *
                                B (G := G) (n := n) (dij (n := n) x i0) (dij (n := n) i i0)) := by
                      simp [Finset.mul_sum, B_symm (G := G) (n := n)]
                    have h' :
                        (∑ x : Fin n, ∑ i : Fin n,
                              ((u : Fin n → ℝ) x) *
                                (((u : Fin n → ℝ) i) *
                                  B (G := G) (n := n) (dij (n := n) x i0) (dij (n := n) i i0)))
                          =
                          ∑ i : Fin n, ∑ j : Fin n,
                            ((u : Fin n → ℝ) i) * ((u : Fin n → ℝ) j) *
                              B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0) := by
                      calc
                        (∑ x : Fin n, ∑ i : Fin n,
                              ((u : Fin n → ℝ) x) *
                                (((u : Fin n → ℝ) i) *
                                  B (G := G) (n := n) (dij (n := n) x i0) (dij (n := n) i i0)))
                            =
                            (∑ i : Fin n, ∑ x : Fin n,
                              ((u : Fin n → ℝ) x) *
                                (((u : Fin n → ℝ) i) *
                                  B (G := G) (n := n)
                                    (dij (n := n) x i0)
                                    (dij (n := n) i i0))) := by
                              exact
                                (Finset.sum_comm :
                                  (∑ x : Fin n, ∑ i : Fin n,
                                    ((u : Fin n → ℝ) x) *
                                      (((u : Fin n → ℝ) i) *
                                        B (G := G) (n := n)
                                          (dij (n := n) x i0)
                                          (dij (n := n) i i0)))
                                    = _)
                        _ =
                            ∑ i : Fin n, ∑ j : Fin n,
                              ((u : Fin n → ℝ) i) * ((u : Fin n → ℝ) j) *
                                B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0) := by
                              simp [mul_assoc, mul_left_comm, B_symm (G := G) (n := n)]
                    exact h.trans h'
      -- Show the `dij` pairings reduce to the constant matrix
      -- (diagonal `c`, off-diagonal `c/2`) on `i0`-complements.
      have h_pair :
          ∀ i j : Fin n,
            B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0) =
              if i = i0 ∨ j = i0 then 0 else if i = j then c else (1 / 2 : ℝ) * c := by
        intro i j
        by_cases hi : i = i0
        · subst hi
          simp [Basis.dij_self]
        by_cases hj : j = i0
        · subst hj
          simp [Basis.dij_self]
        -- Reduce to the `i0`-anchored form using `dij i i0 = - dij i0 i`.
        have hneg_i : dij (n := n) i i0 = -dij (n := n) i0 i := by
          simpa using (Basis.dij_neg (n := n) i i0)
        have hneg_j : dij (n := n) j i0 = -dij (n := n) i0 j := by
          simpa using (Basis.dij_neg (n := n) j i0)
        -- Compute `B(dij i0 i, dij i0 j)`.
        by_cases hij : i = j
        · subst hij
          -- Self term: use a swap to compare with `c = B(dij i0 i1, dij i0 i1)`.
          by_cases hi1 : i = i1
          · subst hi1
            simp [hi, hneg_i, c]
          · have hi0i : i0 ≠ i := by
              intro h
              exact hi h.symm
            -- Apply permutation invariance with `σ = swap i1 i`.
            have hperm :=
              B_dij_dij_eq_of_perm (G := G) (n := n) (σ := Equiv.swap i1 i)
                (i := i0) (j := i1) (k := i0) (l := i1)
            have hσi0 : (Equiv.swap i1 i) i0 = i0 := by
              simp [Equiv.swap_apply_of_ne_of_ne hi01 hi0i]
            have hσi1 : (Equiv.swap i1 i) i1 = i := by simp [Equiv.swap_apply_left]
            -- Combine and simplify.
            have :
                B (G := G) (n := n) (dij (n := n) i0 i) (dij (n := n) i0 i)
                  = B (G := G) (n := n) (dij (n := n) i0 i1) (dij (n := n) i0 i1) := by
              simpa [hσi0, hσi1] using hperm
            have hself0 :
                B (G := G) (n := n) (dij (n := n) i0 i) (dij (n := n) i0 i) = c := by
              simpa [c] using this
            have :
                B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) i i0) = c := by
              simpa [hneg_i] using hself0
            simpa [hi, hj, c] using this
        · -- Cross term: use the `1/2` lemma at `i0`.
          have hi0i : i0 ≠ i := by
            intro h
            exact hi h.symm
          have hi0j : i0 ≠ j := by
            intro h
            exact hj h.symm
          have hij' : i ≠ j := hij
          have hhalf :
              B (G := G) (n := n) (dij (n := n) i0 i) (dij (n := n) i0 j)
                = (1 / 2 : ℝ) * B (G := G) (n := n) (dij (n := n) i0 i) (dij (n := n) i0 i) := by
            simpa using
              (B_dij_dij_eq_half_self (G := G) (n := n) (i := i0) (j := i) (k := j) hi0i hij' hi0j)
          -- Replace the self term with `c` using the same invariance trick as above.
          have hself :
              B (G := G) (n := n) (dij (n := n) i0 i) (dij (n := n) i0 i) = c := by
            by_cases hi1 : i = i1
            · subst hi1
              simp [c]
            · -- same permutation argument
              have hperm :=
                B_dij_dij_eq_of_perm (G := G) (n := n) (σ := Equiv.swap i1 i)
                  (i := i0) (j := i1) (k := i0) (l := i1)
              have hσi0 : (Equiv.swap i1 i) i0 = i0 := by
                simp [Equiv.swap_apply_of_ne_of_ne hi01 hi0i]
              have hσi1 : (Equiv.swap i1 i) i1 = i := by simp [Equiv.swap_apply_left]
              have :
                  B (G := G) (n := n) (dij (n := n) i0 i) (dij (n := n) i0 i)
                    = B (G := G) (n := n) (dij (n := n) i0 i1) (dij (n := n) i0 i1) := by
                simpa [hσi0, hσi1] using hperm
              simpa [c] using this
          -- Convert back to `dij _ i0` and eliminate `-` signs.
          have :
              B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0) =
                (1 / 2 : ℝ) * c := by
            -- `B (-u) (-v) = B u v`.
            -- Use the `1/2` relation at `i0`.
            calc
              B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0)
                  = B (G := G) (n := n) (-dij (n := n) i0 i) (-dij (n := n) i0 j) := by
                        simp [hneg_i, hneg_j]
              _ = B (G := G) (n := n) (dij (n := n) i0 i) (dij (n := n) i0 j) := by
                        simp
              _ = (1 / 2 : ℝ) * c := by
                        simpa [hself] using hhalf
          simpa [hi, hj, hij, c] using this
      -- Use the pairwise description to simplify the double sum.
      -- It collapses to `(c/2) * ∑ k, u(k)^2`.
      have hu_sum : (∑ i : Fin n, (u : Fin n → ℝ) i) = 0 :=
        (tangentSpace.mem_iff (α := Fin n) (u := (u : Fin n → ℝ))).1 u.property
      -- Let `S = univ.erase i0` and rewrite the diagonal expression in terms of sums over `S`.
      let S : Finset (Fin n) := (Finset.univ : Finset (Fin n)).erase i0
      have hsum_erase : (∑ i ∈ S, (u : Fin n → ℝ) i) = -(u : Fin n → ℝ) i0 := by
        classical
        have h :
            (∑ i : Fin n, (u : Fin n → ℝ) i) =
              (∑ i ∈ S, (u : Fin n → ℝ) i) + (u : Fin n → ℝ) i0 := by
          exact
            (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n)))
              (f := fun i : Fin n => (u : Fin n → ℝ) i) (a := i0) (Finset.mem_univ i0)).symm
        have hu' := hu_sum
        rw [h] at hu'
        -- `hu' : (∑ i ∈ S, u i) + u i0 = 0`.
        linarith
      -- Now finish by algebra.
      -- First simplify `B u u` to a weighted sum over `S × S`.
      have hB_quadratic :
          B (G := G) (n := n) u u =
            (c / 2) * (∑ k : Fin n, (u : Fin n → ℝ) k * (u : Fin n → ℝ) k) := by
        classical
        rw [hB_sum]
        have h_erase :
            (∑ i : Fin n, ∑ j : Fin n,
                (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
                  B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0))
              =
              ∑ i ∈ S, ∑ j ∈ S,
                (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
                  B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0) := by
          classical
          -- Outer split at `i0`.
          let g : Fin n → ℝ := fun i : Fin n =>
            ∑ j : Fin n,
              (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
                B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0)
          have h_outer : (∑ i : Fin n, g i) = g i0 + ∑ i ∈ S, g i := by
            have h :
                (∑ i : Fin n, g i) = (∑ i ∈ S, g i) + g i0 := by
              exact
                (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n))) (f := g) (a := i0)
                  (Finset.mem_univ i0)).symm
            calc
              (∑ i : Fin n, g i) = (∑ i ∈ S, g i) + g i0 := h
              _ = g i0 + ∑ i ∈ S, g i := by
                    ac_rfl
          have hg0 : g i0 = 0 := by
            simp [g, Basis.dij_self]
          have h_outer' : (∑ i : Fin n, g i) = ∑ i ∈ S, g i := by
            calc
              (∑ i : Fin n, g i) = g i0 + ∑ i ∈ S, g i := h_outer
              _ = ∑ i ∈ S, g i := by
                    simp [hg0]
          -- Now erase `i0` in the inner sum for each `i ∈ S`.
          have h_inner :
              (∑ i ∈ S, g i) =
                ∑ i ∈ S, ∑ j ∈ S,
                  (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
                    B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0) := by
            refine Finset.sum_congr rfl (fun i hiS => ?_)
            have h0 :
                (u : Fin n → ℝ) i * (u : Fin n → ℝ) i0 *
                    B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) i0 i0) = 0 := by
              simp [Basis.dij_self]
            have h :
                (∑ j : Fin n,
                      (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
                        B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0)) =
                    (∑ j ∈ S,
                        (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
                          B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0))
                      + (u : Fin n → ℝ) i * (u : Fin n → ℝ) i0 *
                          B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) i0 i0) := by
              exact
                (Finset.sum_erase_add (s := (Finset.univ : Finset (Fin n)))
                    (f := fun j : Fin n =>
                      (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
                        B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0))
                    (a := i0) (Finset.mem_univ i0)).symm
            have h' := h
            rw [h0] at h'
            simpa [g, add_assoc, add_comm, add_left_comm] using h'
          calc
            (∑ i : Fin n, ∑ j : Fin n,
                (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
                  B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0))
                = ∑ i : Fin n, g i := by
                      rfl
            _ = ∑ i ∈ S, g i := h_outer'
            _ = ∑ i ∈ S, ∑ j ∈ S,
                    (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
                      B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0) := h_inner
        have h_pairS (i : Fin n) (hiS : i ∈ S) : i ≠ i0 :=
          (Finset.mem_erase.1 hiS).1
        have hkernel :
            (∑ i ∈ S, ∑ j ∈ S,
                (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
                  B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0))
              =
              ∑ i ∈ S, ∑ j ∈ S,
                (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
                  (if i = j then c else (1 / 2 : ℝ) * c) := by
          refine Finset.sum_congr rfl (fun i hiS => ?_)
          refine Finset.sum_congr rfl (fun j hjS => ?_)
          have hi0 : i ≠ i0 := h_pairS i hiS
          have hj0 : j ≠ i0 := h_pairS j hjS
          have hb :
              B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0) =
                (if i = j then c else (1 / 2 : ℝ) * c) := by
            simpa [hi0, hj0] using (h_pair (i := i) (j := j))
          simp [hb, mul_assoc, mul_left_comm]
        have h_expandS :
            (∑ i ∈ S, ∑ j ∈ S,
                (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
                  (if i = j then c else (1 / 2 : ℝ) * c))
              =
              (c / 2) *
                (((∑ i ∈ S, (u : Fin n → ℝ) i) * (∑ j ∈ S, (u : Fin n → ℝ) j))
                  + (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i)) := by
          have hsplit (i j : Fin n) :
              (if i = j then c else (1 / 2 : ℝ) * c) = (c / 2) + (if i = j then c / 2 else 0) := by
            by_cases h : i = j
            · subst h
              simp
            · simp [h]
              ring
          have hsumSq_factor :
              (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i * (c / 2)) =
                (c / 2) * (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i) := by
            have h :
                (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i * (c / 2)) =
                  (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i) * (c / 2) := by
              exact
                (Finset.sum_mul (s := S)
                    (f := fun i : Fin n => (u : Fin n → ℝ) i * (u : Fin n → ℝ) i) (a := c / 2)).symm
            calc
              (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i * (c / 2)) =
                  (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i) * (c / 2) := h
              _ = (c / 2) * (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i) := by
                    ring
          have hconst :
              (∑ i ∈ S, ∑ j ∈ S,
                  (u : Fin n → ℝ) i * (u : Fin n → ℝ) j * (c / 2))
                =
                (c / 2) * ((∑ i ∈ S, (u : Fin n → ℝ) i) * (∑ j ∈ S, (u : Fin n → ℝ) j)) := by
            have hprod :
                (∑ i ∈ S, ∑ j ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) j) =
                  (∑ i ∈ S, (u : Fin n → ℝ) i) * (∑ j ∈ S, (u : Fin n → ℝ) j) := by
              exact
                (Finset.sum_mul_sum (s := S) (t := S) (f := fun i : Fin n => (u : Fin n → ℝ) i)
                    (g := fun j : Fin n => (u : Fin n → ℝ) j)).symm
            calc
              (∑ i ∈ S, ∑ j ∈ S,
                  (u : Fin n → ℝ) i * (u : Fin n → ℝ) j * (c / 2))
                  = (∑ i ∈ S, ∑ j ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) j) * (c / 2) := by
                        simp [Finset.sum_mul, mul_assoc]
              _ = (c / 2) * (∑ i ∈ S, ∑ j ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) j) := by
                        ring
              _ = (c / 2) * ((∑ i ∈ S, (u : Fin n → ℝ) i) * (∑ j ∈ S, (u : Fin n → ℝ) j)) := by
                        rw [hprod]
          have hdiag :
              (∑ i ∈ S, ∑ j ∈ S,
                  (u : Fin n → ℝ) i * (u : Fin n → ℝ) j * (if i = j then c / 2 else 0))
                =
                (c / 2) * (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i) := by
            have :
                (∑ i ∈ S, ∑ j ∈ S,
                    (u : Fin n → ℝ) i * (u : Fin n → ℝ) j * (if i = j then c / 2 else 0))
                  =
                  (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i * (c / 2)) := by
              simp
            calc
              (∑ i ∈ S, ∑ j ∈ S,
                    (u : Fin n → ℝ) i * (u : Fin n → ℝ) j * (if i = j then c / 2 else 0))
                  =
                  (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i * (c / 2)) := this
              _ = (c / 2) * (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i) := hsumSq_factor
          calc
            (∑ i ∈ S, ∑ j ∈ S,
                (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
                  (if i = j then c else (1 / 2 : ℝ) * c))
                =
                ∑ i ∈ S, ∑ j ∈ S,
                  (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
                    ((c / 2) + (if i = j then c / 2 else 0)) := by
                      refine Finset.sum_congr rfl (fun i hiS => ?_)
                      refine Finset.sum_congr rfl (fun j hjS => ?_)
                      rw [hsplit i j]
            _ =
                (∑ i ∈ S, ∑ j ∈ S,
                    (u : Fin n → ℝ) i * (u : Fin n → ℝ) j * (c / 2))
                  +
                  (∑ i ∈ S, ∑ j ∈ S,
                    (u : Fin n → ℝ) i * (u : Fin n → ℝ) j * (if i = j then c / 2 else 0)) := by
                      simp [mul_add, Finset.sum_add_distrib]
            _ =
                (c / 2) * ((∑ i ∈ S, (u : Fin n → ℝ) i) * (∑ j ∈ S, (u : Fin n → ℝ) j))
                  + (c / 2) * (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i) := by
                      rw [hconst]
                      rw [hdiag]
            _ =
                (c / 2) *
                  (((∑ i ∈ S, (u : Fin n → ℝ) i) * (∑ j ∈ S, (u : Fin n → ℝ) j))
                    + (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i)) := by
                      ring
        have hSsq :
            (∑ i ∈ S, (u : Fin n → ℝ) i) * (∑ j ∈ S, (u : Fin n → ℝ) j) =
              (u : Fin n → ℝ) i0 * (u : Fin n → ℝ) i0 := by
          calc
            (∑ i ∈ S, (u : Fin n → ℝ) i) * (∑ j ∈ S, (u : Fin n → ℝ) j) =
                (-(u : Fin n → ℝ) i0) * (-(u : Fin n → ℝ) i0) := by
                  simp [hsum_erase]
            _ = (u : Fin n → ℝ) i0 * (u : Fin n → ℝ) i0 := by
                  ring
        have hsq_split :
            (∑ k : Fin n, (u : Fin n → ℝ) k * (u : Fin n → ℝ) k) =
              (u : Fin n → ℝ) i0 * (u : Fin n → ℝ) i0 +
                ∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i := by
          have h :
              (∑ k : Fin n, (u : Fin n → ℝ) k * (u : Fin n → ℝ) k) =
                (∑ k ∈ S, (u : Fin n → ℝ) k * (u : Fin n → ℝ) k) +
                  (u : Fin n → ℝ) i0 * (u : Fin n → ℝ) i0 := by
            exact
              (Finset.sum_erase_add
                  (s := (Finset.univ : Finset (Fin n)))
                  (f := fun k : Fin n =>
                    (u : Fin n → ℝ) k * (u : Fin n → ℝ) k)
                  (a := i0) (Finset.mem_univ i0)).symm
          calc
            (∑ k : Fin n, (u : Fin n → ℝ) k * (u : Fin n → ℝ) k) =
                (∑ k ∈ S, (u : Fin n → ℝ) k * (u : Fin n → ℝ) k) +
                  (u : Fin n → ℝ) i0 * (u : Fin n → ℝ) i0 := h
            _ =
                (u : Fin n → ℝ) i0 * (u : Fin n → ℝ) i0 +
                  ∑ k ∈ S, (u : Fin n → ℝ) k * (u : Fin n → ℝ) k := by
                  ac_rfl
        calc
          (∑ i : Fin n, ∑ j : Fin n,
                (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
                  B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0))
              =
              ∑ i ∈ S, ∑ j ∈ S,
                (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
                  B (G := G) (n := n) (dij (n := n) i i0) (dij (n := n) j i0) := h_erase
          _ =
              ∑ i ∈ S, ∑ j ∈ S,
                (u : Fin n → ℝ) i * (u : Fin n → ℝ) j *
                  (if i = j then c else (1 / 2 : ℝ) * c) := hkernel
          _ =
              (c / 2) *
                (((∑ i ∈ S, (u : Fin n → ℝ) i) * (∑ j ∈ S, (u : Fin n → ℝ) j))
                  + (∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i)) := h_expandS
          _ =
              (c / 2) *
                ((u : Fin n → ℝ) i0 * (u : Fin n → ℝ) i0 +
                  ∑ i ∈ S, (u : Fin n → ℝ) i * (u : Fin n → ℝ) i) := by
                simp [hSsq]
          _ = (c / 2) * (∑ k : Fin n, (u : Fin n → ℝ) k * (u : Fin n → ℝ) k) := by
                simp [hsq_split]
      -- Now compute the scaled Fisher diagonal and match the expression.
      have hfisher :
          (fisherBilin (Simplex.uniform (α := Fin n)) u u) =
            (Fintype.card (Fin n) : ℝ) * (∑ k : Fin n, (u : Fin n → ℝ) k * (u : Fin n → ℝ) k) := by
        -- Unfold Fisher at uniform: divide by `1/card` multiplies by `card`.
        simp [fisherBilin.apply, Simplex.uniform_apply, div_eq_mul_inv, Finset.mul_sum]
        refine Finset.sum_congr rfl (fun x hx => ?_)
        ring
      -- Combine the pieces.
      have hscaled_fisher :
          (c / (2 * (Fintype.card (Fin n) : ℝ))) * fisherBilin (Simplex.uniform (α := Fin n)) u u =
            (c / 2) * (∑ k : Fin n, (u : Fin n → ℝ) k * (u : Fin n → ℝ) k) := by
        rw [hfisher]
        have hscale :
            (c / (2 * (Fintype.card (Fin n) : ℝ))) * (Fintype.card (Fin n) : ℝ) = c / 2 := by
          have hm : (Fintype.card (Fin n) : ℝ) ≠ 0 := hcard_ne
          rw [div_mul_eq_mul_div]
          exact mul_div_mul_right (a := c) (b := (2 : ℝ)) (c := (Fintype.card (Fin n) : ℝ)) hm
        -- Associate and rewrite by `hscale`.
        rw [← mul_assoc]
        rw [hscale]
      calc
          B (G := G) (n := n) u u
              = (c / 2) *
                  (∑ k : Fin n,
                    (u : Fin n → ℝ) k * (u : Fin n → ℝ) k) :=
                hB_quadratic
          _ = (c / (2 * (Fintype.card (Fin n) : ℝ))) *
                fisherBilin (Simplex.uniform (α := Fin n)) u u := by
                symm
                exact hscaled_fisher
          _ =
              (((c / (2 * (Fintype.card (Fin n) : ℝ))) •
                fisherBilin (Simplex.uniform (α := Fin n))) u) u := by
                rfl
    -- Diagonal equality implies full equality for symmetric bilinear forms.
    have hEq :=
      LinearMap.BilinForm.ext_of_isSymm hSymm₁ hSymm₂ hdiag
    -- Rewrite the scalar into the stated form.
    -- (`c` was defined from the `dij` self term.)
    simpa [c, hc] using hEq

end Bilin

end TangentFin
end CencovPetz
