# Strain-tensor eigenvalue decomposition

Author: Benjamin Stanley Frohman
Affiliation: Independent Researcher, Texas, United States
ORCID: [0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718)
Email: frohmanbenjamin@gmail.com

This repository contains a Lean 4 formalization (`StrainEigenvalue.lean`)
and a short algebraic note (`paper/Strain_Eigenvalue_Breakdown.tex`, with a
compiled PDF). The note records the elementary eigenvalue decomposition of
the symmetric, trace-free strain-rate tensor of a divergence-free field, and
the consequences of that identity for the local vortex-stretching term.

## Honest scope

- **The paper's algebraic identities are formalized, with 0 `sorry`.**
  Proposition 1.1 (intermediate-eigenvalue representation) is proved on the
  actual quadratic form `ξ ⬝ᵥ (S *ᵥ ξ)` (`quadratic_form_intermediate`),
  and in eigen-coordinates (`intermediate_representation`). The skeleton's
  unit-vector hypothesis was corrected (see below).
- **This is not a Clay Millennium Navier–Stokes proof**, and it is not a
  regularity theorem for 3D Navier–Stokes. Large-data global regularity
  remains open.
- The identities are pointwise and algebraic. They do **not** imply
  integrability of \(\|S\|_{L^\infty}\) in time, and they do **not** prove
  Hypothesis B,
  \[
  \int_0^T \|S(t)\|_{L^\infty}\,dt < \infty,
  \]
  for arbitrary large smooth data. The supercritical gap between the energy
  inequality and the Beale–Kato–Majda criterion remains open.
- **A kernel check is not a geometric, analytic, or physical proof.** It
  only shows that the algebraic statements listed below are proved.
- Not formalized: vorticity, Navier–Stokes dynamics, Hölder conditions on
  the vorticity direction, Constantin–Fefferman desingularization, the
  angular-dispersion functional \(\mathcal{D}_{\boldsymbol{\xi}}\), and the
  classical geometric criteria (Neustupa–Penel, Miller).
- Mathlib's `IsHermitian.eigenvalues` are indexed by `Fin 3` after a
  cardinality reindexing. Lean index `1` plays the role of the paper's
  intermediate eigenvalue \(\lambda_2\). The algebra does not need the
  ordering \(\lambda_1\le\lambda_2\le\lambda_3\), and Lean does **not**
  prove that the indexing is sorted, or that \(\lambda_1\le 0\le\lambda_3\).

## What Lean actually proves

All of the following use only `propext`, `Classical.choice`, `Quot.sound`
(see `scripts/PrintAxioms.lean` and the CI log):

1. `StrainTensor.isHermitian`: a real symmetric matrix is Hermitian
   (compile adaptation, see below).
2. `eigenvalues_sum_zero`: \(\lambda_0+\lambda_1+\lambda_2=0\) for every
   `StrainTensor` (symmetric, trace zero).
3. `quadratic_form_eq_sum`: with `U = eigvecs S` the orthonormal
   eigenvector matrix from Mathlib's spectral theorem and
   `η = eigenCoords S ξ = Uᵀ ξ`, \(\xi\cdot S\xi=\sum_i\lambda_i\eta_i^2\)
   for every \(\xi\in\mathbb{R}^3\) (paper eq. (2)).
4. `sum_sq_eigenCoords`: \(\sum_i\eta_i^2=\sum_i\xi_i^2\).
5. `quadratic_form_intermediate` (paper Proposition 1.1): if
   \(\sum_i\xi_i^2=1\), then
   \(\xi\cdot S\xi=\lambda_1+(\lambda_0-\lambda_1)\eta_0^2+(\lambda_2-\lambda_1)\eta_2^2\).
5a. `intermediate_representation`: the same identity for `stretching`
   (eigen-coordinates).
6. `sum_sq_eq_one_not_imp_norm_eq_one`: counterexample showing
   \(\sum_i\xi_i^2=1\not\Rightarrow\|\xi\|=1\) on `Fin 3 → ℝ`.
7. Non-vacuity: `exampleStrain = diag(1, -1, 0)` is a `StrainTensor`;
   `exampleStrain_eigenvalues_ne_zero` (its eigenvalues are not all zero);
   `exampleStrain_intermediate_nontrivial` (for `ξ = (1,0,0)` the hypothesis
   holds and both sides of Proposition 1.1 equal `1`).

## Correction to the skeleton statement (this branch)

The original skeleton gave `stretching` the hypothesis `hξ : ‖ξ‖ = 1` and
`intermediate_representation` supplied it as `(by sorry)` from
`∑ i, (ξ i)^2 = 1`. On `Fin 3 → ℝ`, Mathlib's `‖ξ‖` is the **sup norm**, so
that step was false. Counterexample: `ξ = (3/5, 4/5, 0)` has `∑ ξᵢ² = 1` but
`‖ξ‖ = 4/5`. Lean checks this (`sum_sq_eq_one_not_imp_norm_eq_one`).

Minimal correction: `stretching` now takes `(hξ : ∑ i, (ξ i)^2 = 1)`, the
Euclidean unit condition the paper means, and `intermediate_representation`
passes `hξ`. `stretching` never used the hypothesis, so its value is
unchanged, and the right-hand side of `intermediate_representation` is
unchanged.

Sorry count: **0**. CI enforces zero `sorry`.

## Compile adaptations (no change to mathematical meaning)

The skeleton was originally written with `Matrix.IsHermitian.of_isSymm`
and without an import of the spectral file. Against the Mathlib pin used
in this repository (`v4.30.0-rc1`, commit
`0c154d67103f74be3a0f2c509f72ccbf5be9f2a7`, matching
`frohmanian-metriplectic-ns`):

1. Added `import Mathlib.Analysis.Matrix.Spectrum`, which is where
   `IsHermitian.eigenvalues` and `IsHermitian.trace_eq_sum_eigenvalues`
   live. The original imports did not expose those declarations.
2. Replaced `Matrix.IsHermitian.of_isSymm` (not present at this pin; it
   appears on later Mathlib as `isHermitian_iff_isSymm`) by a short lemma
   `isHermitian` that uses `IsHermitian.ext` and `star_trivial` on
   \(\mathbb{R}\). The statements of `eigenvalues` and
   `eigenvalues_sum_zero` are unchanged.
3. `lakefile.toml` originally started with a Lean-style `--` comment for
   the author header. Lake's TOML parser rejected it (`unexpected 'A';
   expected '='`). The header is now a TOML `#` comment. No package or
   pin change.
4. The compile adaptation lemma was originally named `isHermitian`. Lean
   field notation `S.isHermitian` looks up `StrainTensor.isHermitian`, so
   the CI run after the lakefile fix
   ([42919197798](https://github.com/BenFrohman/frohmanian-strain-eigenvalue/actions/runs/42919197798))
   failed with “Invalid field `isHermitian`” on the projections in
   `eigenvalues` and `eigenvalues_sum_zero`, and the trace-zero goal was
   left unsolved. The lemma was renamed to `StrainTensor.isHermitian`.
   The proof body of the conversion and the *statements* of
   `eigenvalues` and `eigenvalues_sum_zero` are unchanged.
5. After that rename, CI
   ([42919676638](https://github.com/BenFrohman/frohmanian-strain-eigenvalue/actions/runs/42919676638))
   failed because `rw [← h]` could not match Mathlib’s
   `trace = ∑ i, ↑(eigenvalues i)` against the goal
   `∑ i, eigenvalues S i = 0`. On `𝕜 = ℝ` the `↑` is a redundant
   coercion. The proof now unfolds `eigenvalues`, identifies the
   coercion, and then applies `trace_zero`. The theorem statement is
   unchanged.

No other Lean wording was changed in those adaptations. Later, the body of
`intermediate_representation` was proved and the declarations in items 3–7
above were added. The hypothesis of `stretching` was then corrected as described above.

## Reproducibility

- Toolchain: Lean 4.30.0-rc1, Mathlib `v4.30.0-rc1`
  (`0c154d67103f74be3a0f2c509f72ccbf5be9f2a7`), pinned in `lean-toolchain`
  and `lake-manifest.json` to the same versions as
  `frohmanian-metriplectic-ns`.
- One-command rebuild: `lake exe cache get && lake build`
- Kernel / sorry report: `./scripts/kernel_check.sh` after a successful
  build (`#print axioms` for every listed declaration; sorry tokens are counted
  and reported; they fail the job only if the file contains none, in
  which case zero sorry is enforced). `admit`, `native_decide`, and new
  `axiom` declarations still fail the job.
- The committed PDF under `paper/` is compiled from the committed `.tex`
  with Tectonic (`tectonic paper/Strain_Eigenvalue_Breakdown.tex`). The
  source uses a fixed date (10 November 2026).
- Commit SHA: recorded on GitHub after the initial push; rebuilds should
  name that commit.

## Related repositories

- [frohmanian-metriplectic-ns](https://github.com/BenFrohman/frohmanian-metriplectic-ns)
- [frohmanian-tether-conditional-regularity](https://github.com/BenFrohman/frohmanian-tether-conditional-regularity)
- [frohmanian-tether-sdiff](https://github.com/BenFrohman/frohmanian-tether-sdiff)
- [two-point-strain-coercivity](https://github.com/BenFrohman/two-point-strain-coercivity)
- [two-point-strain-direction-pairing-2026-11](https://github.com/BenFrohman/two-point-strain-direction-pairing-2026-11)

## License

- Code: Apache License 2.0 (`LICENSE`).
- Paper (LaTeX and PDF): CC BY 4.0 (`LICENSE-paper`).
