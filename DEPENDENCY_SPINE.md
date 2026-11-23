# Dependency Spine: Intermediate-Eigenvalue Identity

Author: Benjamin Stanley Frohman  
ORCID: [0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718)

Version DOI (v4): [10.5281/zenodo.24121987](https://doi.org/10.5281/zenodo.24121987).  
Concept DOI: [10.5281/zenodo.24083477](https://doi.org/10.5281/zenodo.24083477).

## Status

Fully closed algebraic package on `StrainTensor`. 0 `sorry` in every tracked `.lean` file. Official kernel certificate on parent commit [`d16c670ef54baa29aa99f50c7a8c71f4b5fd4261`](https://github.com/BenFrohman/frohmanian-strain-eigenvalue/commit/d16c670ef54baa29aa99f50c7a8c71f4b5fd4261) ([run 45139938920](https://github.com/BenFrohman/frohmanian-strain-eigenvalue/actions/runs/45139938920); Lean 4.30.0-rc1): every listed declaration in the built `StrainEigenvalue` module depends only on `propext`, `Classical.choice`, and `Quot.sound`. Later documentation and CI commits of this branch additionally kernel-certify `StrainEigenvalue.Eigenbasis` and `StrainEigenvalue.Semantics`. Purely pointwise. Does not imply any regularity or time-integrability of \(\|S\|_{L^\infty}\). Not a Clay Navier–Stokes result.

## Root

`Mathlib.Analysis.Matrix.Spectrum` (with `Mathlib.LinearAlgebra.Matrix.Symmetric`, eigenspace, and inner-product imports).

## Truth Gate theorem

The locked Truth Gate theorem is `StrainEigenvalue.quadratic_form_intermediate_of_eigenbasis` (`StrainEigenvalue/Eigenbasis.lean`; listed in `TRUTH_GATE.lock`). For any real strain `S`, any orthonormal `U` (`Uᵀ U = 1`) with `S U = U \mathrm{diag}(λ)`, and any monotone `λ`, if \(\sum_i \xi_i^2 = 1\), then

\[
\xi \cdot S\xi = \lambda_1 + (\lambda_0-\lambda_1)\eta_0^2 + (\lambda_2-\lambda_1)\eta_2^2,
\]

where \(\eta = U^T \xi\). Lean indices `0, 1, 2` are the paper's \(\lambda_1, \lambda_2, \lambda_3\).

## Primary spine (unique well-founded path)

1. `StrainTensor` structure (`mat`, `IsSymm`, `trace = 0`) and `StrainTensor.isHermitian` — symmetry over \(\mathbb{R}\) implies Hermitian.

2. Ordered eigenvalues via `Fin.rev` applied to Mathlib's antitone `eigenvalues₀`:  
   `eigenvalues_monotone`, `eigenvalues_ordered` (\(\lambda_0 \le \lambda_1 \le \lambda_2\)), `eigenvalues_sum_zero`, `eigenvalues_min_nonpos_max_nonneg` (\(\lambda_0 \le 0 \le \lambda_2\)).

3. Quadratic form: \(\xi \cdot S\xi = \sum_i \lambda_i \eta_i^2\) as `quadratic_form_eq_sum` (`ξ ⬝ᵥ (S.mat *ᵥ ξ)` in Lean), with Euclidean preservation `sum_sq_eigenCoords`.

4. Specialization of the locked theorem to the repository's ordered eigenbasis: `quadratic_form_intermediate`, under the Euclidean unit constraint \(\sum_i \xi_i^2 = 1\). Proof: `Fin.sum_univ_three`, `linarith`, and `ring`, after `quadratic_form_eq_sum` and `sum_sq_eigenCoords`. The identity's proof does not invoke `trace_zero`; the theorem is still stated on `StrainTensor`, which includes that field.

5. Non-vacuity: `exampleStrain` is \(\mathrm{diag}(1,-1,0)\). The Euclidean vs. sup-norm distinction is `sum_sq_eq_one_not_imp_norm_eq_one` (on `Fin 3 → ℝ`, `‖ξ‖` is the sup norm).

## Deferred side branches

Any analytic consequences, vorticity fields, Hölder direction conditions, or Navier–Stokes dynamics. Hypothesis B remains open.

## Build

```bash
lake exe cache get && lake build && ./scripts/kernel_check.sh
```
