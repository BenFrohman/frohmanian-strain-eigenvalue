# Dependency Spine: Intermediate-Eigenvalue Identity

Author: Benjamin Stanley Frohman
ORCID: 0009-0006-7068-3718

## Status
Fully closed algebraic package. 0 sorry. Standard axioms only (`propext`, `Classical.choice`, `Quot.sound`). Purely pointwise. Does not imply any regularity or time-integrability.

## Root
Mathlib.Analysis.Matrix.Spectrum

## Primary Spine (unique well-founded path)
1. StrainTensor structure + IsSymm → IsHermitian (ℝ) — `StrainTensor.isHermitian`
2. Ordered eigenvalues via Fin.rev: λ₀ ≤ λ₁ ≤ λ₂, sum zero, λ₀ ≤ 0 ≤ λ₂  — `eigenvalues_monotone`, `eigenvalues_ordered`, `eigenvalues_sum_zero`, `eigenvalues_min_nonpos_max_nonneg`
3. Quadratic form: ξ · S ξ = ∑ λᵢ ηᵢ²  — `quadratic_form_eq_sum`, `sum_sq_eigenCoords`
4. **Terminal node**: Intermediate-eigenvalue identity under Euclidean unit norm  — `quadratic_form_intermediate`  
   Under ∑ ξᵢ² = 1: ξ · S ξ = λ₁ + (λ₀-λ₁)η₀² + (λ₂-λ₁)η₂²  
   Pure algebra (`Fin.sum_univ_three` + `linarith` + `ring`). Trace-zero unused.
5. Non-vacuity (diag(1,-1,0)) and sup-norm vs Euclidean correction  — `exampleStrain`, `sum_sq_eq_one_not_imp_norm_eq_one`

## Deferred Side Branches
Any analytic consequences, vorticity fields, Hölder direction conditions, or Navier–Stokes dynamics.

## Build
`lake exe cache get && lake build && ./scripts/kernel_check.sh`
