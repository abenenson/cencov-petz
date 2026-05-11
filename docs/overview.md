# Finite Čencov–Petz Overview

This project formalizes the finite/discrete Čencov–Petz uniqueness theorem:
a continuous metric family on finite probability simplexes that is monotone under Markov
morphisms is a scalar multiple of the Fisher information metric.

## Organization

The development is organized in reusable pieces:

1. finite-simplex and tangent-space API,
2. Fisher bilinear form and continuity lemmas,
3. Markov morphisms, sufficient statistics, splitting, and replication maps,
4. rational-point density and continuity extension,
5. the finite Čencov theorem.

This ordering separates generally useful probability-simplex infrastructure from the final theorem.

## Verification

The repository is pinned to Lean and Mathlib in `lean-toolchain` and `lake-manifest.json`.
The public CI uses `leanprover/lean-action` and docgen.
