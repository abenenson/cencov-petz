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
CI builds the complete library with warnings treated as errors, then builds its API
documentation with the matching `doc-gen4` release. Each successful run uploads the
`api-docs` artifact, including pull requests and manual runs.

To build the API documentation locally after `lake build`, run
`bash scripts/build-docs.sh`. The output is in `public-docs/docs`.

Publishing is optional: after configuring GitHub Pages to use GitHub Actions, set
the repository variable `PUBLISH_DOCS` to `true` to deploy documentation on pushes
to `main`.
