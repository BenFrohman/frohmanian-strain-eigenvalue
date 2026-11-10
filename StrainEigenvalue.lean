/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Benjamin Stanley Frohman
-/

import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Matrix.Spectrum

/-!
# Strain-Tensor Eigenvalue Decomposition

Algebraic identities for the symmetric strain-rate tensor of a divergence-free field.
All results are pointwise and unconditional; they do not imply integrability of ‖S‖_∞.
-/

noncomputable section
open scoped Matrix

namespace StrainEigenvalue

variable {𝕜 : Type*} [RCLike 𝕜]

/-- A symmetric 3×3 matrix with vanishing trace. -/
structure StrainTensor (𝕜 : Type*) [RCLike 𝕜] where
  mat : Matrix (Fin 3) (Fin 3) 𝕜
  symm : mat.IsSymm
  trace_zero : mat.trace = 0

/-- On `ℝ`, conjugate-transpose coincides with transpose, so symmetry implies
`IsHermitian`. Written out because Mathlib `v4.30.0-rc1` (pin `0c154d6`) does
not provide `Matrix.IsHermitian.of_isSymm`. -/
lemma StrainTensor.isHermitian (S : StrainTensor ℝ) : S.mat.IsHermitian := by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simpa [star_trivial] using S.symm.apply i j

/-- The three real eigenvalues of a real symmetric matrix. -/
noncomputable def eigenvalues (S : StrainTensor ℝ) : Fin 3 → ℝ :=
  fun i => S.isHermitian.eigenvalues i

theorem eigenvalues_sum_zero (S : StrainTensor ℝ) :
    ∑ i, eigenvalues S i = 0 := by
  -- Trace equals sum of eigenvalues for a real symmetric matrix
  have h := S.isHermitian.trace_eq_sum_eigenvalues
  rw [← h, S.trace_zero]

/-- Quadratic form of the strain on a unit vector. -/
def stretching (S : StrainTensor ℝ) (ξ : Fin 3 → ℝ) (hξ : ‖ξ‖ = 1) : ℝ :=
  ∑ i, eigenvalues S i * (ξ i)^2

theorem intermediate_representation (S : StrainTensor ℝ) (ξ : Fin 3 → ℝ)
    (hξ : ∑ i, (ξ i)^2 = 1) :
    stretching S ξ (by sorry) =
      eigenvalues S 1 +
      (eigenvalues S 0 - eigenvalues S 1) * (ξ 0)^2 +
      (eigenvalues S 2 - eigenvalues S 1) * (ξ 2)^2 := by
  -- Algebraic rearrangement using ξ₁² = 1 - ξ₀² - ξ₂²
  sorry

end StrainEigenvalue
