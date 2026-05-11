# cencov-petz

Lean 4 proof of the **finite Čencov–Petz uniqueness theorem**: any continuous monotone metric family on the probability simplex is a scalar multiple of the Fisher information metric.

This is the finite/discrete case of the Čencov–Petz characterisation: the Fisher information metric is the unique (up to scale) Riemannian metric on the space of probability distributions monotone under Markov morphisms.

> **Build status:** Verified on Lean v4.29.1 with Mathlib. Zero sorries.

## Main result

```lean
theorem MonotoneMetricFamily.eq_smul_fisher_of_continuous (G : MonotoneMetricFamily)
    {α : Type} [Fintype α] [Nonempty α]
    {a0 a1 : α} (ha01 : a0 ≠ a1)
    (hG : ∀ u v : tangentSpace (α := α), Continuous fun p : Simplex α => G.g (α := α) p u v) :
    ∀ (p : Simplex α) (u v : tangentSpace (α := α)),
      G.g (α := α) p u v = (uniformScalar G 2 (by decide)) * fisherBilin p u v
```

## Proof strategy

1. Verify the scalar identity at the uniform distribution (`Uniform`)
2. Extend to rational simplex points via splitting invariance (`CencovSplitPoint`, `Splitting`)
3. Conclude everywhere by density of rational points and continuity of both sides (`CencovFinite`)

## Dependencies

Lean 4 + [Mathlib](https://github.com/leanprover-community/mathlib4). No external dependencies.

For more detail on the internal organization of the development, see
[`docs/overview.md`](docs/overview.md).

## Organization

The development separates reusable finite-simplex, Fisher-metric, Markov-morphism, and splitting
lemmas from the final finite Čencov theorem.

## References

- N. N. Čencov, *Statistical Decision Rules and Optimal Inference*, AMS, 1982
- D. Petz, "Monotone metrics on matrix spaces", *Linear Algebra and its Applications*, 244, 1996
