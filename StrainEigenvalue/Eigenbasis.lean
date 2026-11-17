/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import StrainEigenvalue

/-!
# Proposition 1.1 for an arbitrary ordered orthonormal eigenbasis

The paper's Proposition 1.1 is stated for *an* orthonormal eigenbasis `e₁, e₂, e₃` of the strain
`S` with eigenvalues `λ₁ ≤ λ₂ ≤ λ₃`, not for one particular choice. This file proves it in that
generality: `U` is any real `3 × 3` matrix with `Uᵀ U = 1` whose columns are eigenvectors of `S`
(`S U = U diag(λ)`), `λ` is monotone, and the eigen-coordinates of `ξ` are `η = Uᵀ ξ`.
-/

noncomputable section
open scoped Matrix

namespace StrainEigenvalue

/-- **Proposition 1.1**, for any ordered orthonormal eigenbasis (columns of `U`). -/
theorem quadratic_form_intermediate_of_eigenbasis (S : StrainTensor ℝ)
    (U : Matrix (Fin 3) (Fin 3) ℝ) (l : Fin 3 → ℝ)
    (hU : Uᵀ * U = 1) (hSU : S.mat * U = U * Matrix.diagonal l) (_hl : Monotone l)
    (ξ : Fin 3 → ℝ) (hξ : ∑ i, (ξ i)^2 = 1) :
    ξ ⬝ᵥ (S.mat *ᵥ ξ) =
      l 1 + (l 0 - l 1) * ((Uᵀ *ᵥ ξ) 0)^2 + (l 2 - l 1) * ((Uᵀ *ᵥ ξ) 2)^2 := by
  have hUU : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
  set η := Uᵀ *ᵥ ξ with hη
  have hξη : ξ = U *ᵥ η := by
    rw [hη, Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
  have hq : ξ ⬝ᵥ (S.mat *ᵥ ξ) = ∑ i, l i * (η i)^2 := by
    have h1 : S.mat *ᵥ ξ = U *ᵥ (Matrix.diagonal l *ᵥ η) := by
      conv_lhs => rw [hξη]
      rw [Matrix.mulVec_mulVec, hSU, ← Matrix.mulVec_mulVec]
    rw [h1, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, ← hη]
    simp only [dotProduct, Matrix.mulVec_diagonal]
    refine Finset.sum_congr rfl fun i _ => by ring
  have hs : ∑ i, (η i)^2 = 1 := by
    have : η ⬝ᵥ η = ξ ⬝ᵥ ξ := by
      symm
      calc ξ ⬝ᵥ ξ = (U *ᵥ η) ⬝ᵥ (U *ᵥ η) := by rw [← hξη]
        _ = ((U *ᵥ η) ᵥ* U) ⬝ᵥ η := Matrix.dotProduct_mulVec _ _ _
        _ = η ⬝ᵥ η := by
          rw [← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
    rw [← hξ]
    simpa [dotProduct, pow_two] using this
  rw [hq]
  simp only [Fin.sum_univ_three] at hs ⊢
  linear_combination (l 1) * hs

end StrainEigenvalue
