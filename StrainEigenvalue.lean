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
  -- Trace equals sum of eigenvalues for a real symmetric matrix.
  -- Mathlib states this as `trace = ∑ i, (eigenvalues i : 𝕜)`. On `𝕜 = ℝ`
  -- that ascription is a redundant coercion, so `rw [← h]` cannot see
  -- `eigenvalues S i` in the goal. Unfold and identify the coercion,
  -- then apply `trace_zero`.
  calc
    ∑ i, eigenvalues S i
        = ∑ i, (S.isHermitian.eigenvalues i : ℝ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          -- The ascription `(· : ℝ)` is `RCLike.ofReal`, which is `id` on `ℝ`.
          simp [eigenvalues, RCLike.ofReal_real_eq_id]
    _ = S.mat.trace := S.isHermitian.trace_eq_sum_eigenvalues.symm
    _ = 0 := S.trace_zero

/-- Quadratic form of the strain on a unit vector, written in eigen-coordinates.
"Unit" is Euclidean: `∑ i, (ξ i)^2 = 1`. (On `Fin 3 → ℝ`, `‖ξ‖` is the sup
norm, so the earlier hypothesis `‖ξ‖ = 1` did not say this; see
`sum_sq_eq_one_not_imp_norm_eq_one`.) -/
def stretching (S : StrainTensor ℝ) (ξ : Fin 3 → ℝ) (_hξ : ∑ i, (ξ i)^2 = 1) : ℝ :=
  ∑ i, eigenvalues S i * (ξ i)^2

theorem intermediate_representation (S : StrainTensor ℝ) (ξ : Fin 3 → ℝ)
    (hξ : ∑ i, (ξ i)^2 = 1) :
    stretching S ξ hξ =
      eigenvalues S 1 +
      (eigenvalues S 0 - eigenvalues S 1) * (ξ 0)^2 +
      (eigenvalues S 2 - eigenvalues S 1) * (ξ 2)^2 := by
  -- Substitute ξ₁² = 1 - ξ₀² - ξ₂² and rearrange.
  have h1 : (ξ 1)^2 = 1 - (ξ 0)^2 - (ξ 2)^2 := by
    rw [Fin.sum_univ_three] at hξ
    linarith
  simp only [stretching, Fin.sum_univ_three]
  rw [h1]
  ring

/-! ## Why `stretching` takes `∑ i, (ξ i)^2 = 1` and not `‖ξ‖ = 1` -/

/-- Counterexample: `ξ = (3/5, 4/5, 0)` has `∑ ξᵢ² = 1`, but its `Pi` (sup)
norm is `4/5 ≠ 1`. So `∑ i, (ξ i)^2 = 1 → ‖ξ‖ = 1` is false on `Fin 3 → ℝ`. -/
theorem sum_sq_eq_one_not_imp_norm_eq_one :
    ¬ ∀ ξ : Fin 3 → ℝ, ∑ i, (ξ i)^2 = 1 → ‖ξ‖ = 1 := by
  intro h
  set ξ : Fin 3 → ℝ := ![3/5, 4/5, 0] with hξdef
  have hsum : ∑ i, (ξ i)^2 = 1 := by
    simp [hξdef, Fin.sum_univ_three]; norm_num
  have hle : ‖ξ‖ ≤ 4/5 := by
    refine (pi_norm_le_iff_of_nonneg (by norm_num)).2 fun i => ?_
    fin_cases i <;> simp [hξdef] <;> norm_num
  have := h ξ hsum
  linarith

/-! ## The paper's proposition, stated on the actual quadratic form `ξ · S ξ`

`stretching` is defined directly as `∑ λᵢ ξᵢ²`, i.e. it presupposes that `ξ` is
already written in eigenvector coordinates. The results below connect that to
the matrix: with `U` the orthonormal eigenvector matrix supplied by Mathlib's
spectral theorem and `η = Uᵀ ξ` the eigen-coordinates of `ξ`,
`ξ · S ξ = ∑ λᵢ ηᵢ²` and `∑ ηᵢ² = ∑ ξᵢ²`. -/

/-- Orthonormal eigenvector matrix of `S` (columns are eigenvectors). -/
noncomputable def eigvecs (S : StrainTensor ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (S.isHermitian.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℝ)

/-- Coordinates of `ξ` in the orthonormal eigenbasis of `S`. -/
noncomputable def eigenCoords (S : StrainTensor ℝ) (ξ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (star (eigvecs S)) *ᵥ ξ

/-- Spectral form of the quadratic form: `ξ · S ξ = ∑ λᵢ ηᵢ²` (paper eq. (2)). -/
theorem quadratic_form_eq_sum (S : StrainTensor ℝ) (ξ : Fin 3 → ℝ) :
    ξ ⬝ᵥ (S.mat *ᵥ ξ) = ∑ i, eigenvalues S i * (eigenCoords S ξ i)^2 := by
  have hA := S.isHermitian
  set U : Matrix (Fin 3) (Fin 3) ℝ := eigvecs S with hU
  have hs : S.mat = U * Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) * star U := by
    have := hA.spectral_theorem
    rwa [Unitary.conjStarAlgAut_apply] at this
  have hAξ : S.mat *ᵥ ξ =
      U *ᵥ (Matrix.diagonal (RCLike.ofReal ∘ hA.eigenvalues) *ᵥ (star U *ᵥ ξ)) := by
    conv_lhs => rw [hs]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc]
  rw [hAξ, Matrix.dotProduct_mulVec]
  have hT : ξ ᵥ* U = (star U) *ᵥ ξ := by
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
      Matrix.mulVec_transpose]
  rw [hT, dotProduct]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_diagonal]
  simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id, eigenvalues, eigenCoords, hU]
  ring

/-- The eigen-coordinates preserve the Euclidean sum of squares. -/
theorem sum_sq_eigenCoords (S : StrainTensor ℝ) (ξ : Fin 3 → ℝ) :
    ∑ i, (eigenCoords S ξ i)^2 = ∑ i, (ξ i)^2 := by
  set U : Matrix (Fin 3) (Fin 3) ℝ := eigvecs S with hU
  have key : ∀ v : Fin 3 → ℝ, ∑ i, (v i)^2 = v ⬝ᵥ v := fun v => by
    simp [dotProduct, sq]
  rw [key, key, eigenCoords, ← hU, Matrix.dotProduct_mulVec]
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    ← Matrix.mulVec_transpose, Matrix.transpose_transpose, Matrix.mulVec_mulVec]
  have h1 : U * Uᵀ = 1 := by
    have h2 : U * star U = 1 :=
      Unitary.mul_star_self_of_mem S.isHermitian.eigenvectorUnitary.2
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h2
  rw [h1, Matrix.one_mulVec]

/-- **Intermediate-eigenvalue representation (paper Proposition 1.1)**, on the
actual quadratic form, for every Euclidean unit vector `ξ`. Here `η` are the
eigen-coordinates of `ξ`, and Lean indices `0, 1, 2` play the roles of the
paper's `1, 2, 3`. Mathlib does not guarantee that this indexing is sorted. -/
theorem quadratic_form_intermediate (S : StrainTensor ℝ) (ξ : Fin 3 → ℝ)
    (hξ : ∑ i, (ξ i)^2 = 1) :
    ξ ⬝ᵥ (S.mat *ᵥ ξ) =
      eigenvalues S 1 +
      (eigenvalues S 0 - eigenvalues S 1) * (eigenCoords S ξ 0)^2 +
      (eigenvalues S 2 - eigenvalues S 1) * (eigenCoords S ξ 2)^2 := by
  have hη : ∑ i, (eigenCoords S ξ i)^2 = 1 := by rw [sum_sq_eigenCoords, hξ]
  have h1 : (eigenCoords S ξ 1)^2 = 1 - (eigenCoords S ξ 0)^2 - (eigenCoords S ξ 2)^2 := by
    rw [Fin.sum_univ_three] at hη
    linarith
  rw [quadratic_form_eq_sum, Fin.sum_univ_three, h1]
  ring

/-! ## Non-vacuity -/

/-- A concrete strain tensor: `diag(1, -1, 0)` (symmetric, trace zero, nonzero). -/
noncomputable def exampleStrain : StrainTensor ℝ where
  mat := Matrix.diagonal ![1, -1, 0]
  symm := Matrix.isSymm_diagonal _
  trace_zero := by simp [Matrix.trace, Fin.sum_univ_three]

/-- Its eigenvalues are not all zero (so `eigenvalues_sum_zero` is non-trivial). -/
theorem exampleStrain_eigenvalues_ne_zero : eigenvalues exampleStrain ≠ 0 := by
  intro h
  have h0 : exampleStrain.isHermitian.eigenvalues = 0 := h
  have hm := (exampleStrain.isHermitian.eigenvalues_eq_zero_iff).1 h0
  have := congrFun (congrFun hm 0) 0
  simp [exampleStrain] at this

/-- The hypotheses of `quadratic_form_intermediate` are satisfiable for
`exampleStrain` with `ξ = e₀`, and both sides equal `1 ≠ 0`, so the
representation is applied to a non-zero stretching rate. -/
theorem exampleStrain_intermediate_nontrivial :
    let ξ : Fin 3 → ℝ := ![1, 0, 0]
    (∑ i, (ξ i)^2 = 1) ∧ ξ ⬝ᵥ (exampleStrain.mat *ᵥ ξ) = 1 ∧
      eigenvalues exampleStrain 1 +
        (eigenvalues exampleStrain 0 - eigenvalues exampleStrain 1) *
          (eigenCoords exampleStrain ξ 0)^2 +
        (eigenvalues exampleStrain 2 - eigenvalues exampleStrain 1) *
          (eigenCoords exampleStrain ξ 2)^2 = 1 := by
  intro ξ
  have hs : ∑ i, (ξ i)^2 = 1 := by simp [ξ, Fin.sum_univ_three]
  have hq : ξ ⬝ᵥ (exampleStrain.mat *ᵥ ξ) = 1 := by
    simp [ξ, exampleStrain, dotProduct, Matrix.mulVec_diagonal, Fin.sum_univ_three]
  exact ⟨hs, hq, (quadratic_form_intermediate exampleStrain ξ hs).symm.trans hq⟩

end StrainEigenvalue
