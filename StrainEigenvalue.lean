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

Eigenvalues are indexed in *increasing* order `λ₀ ≤ λ₁ ≤ λ₂`, matching the paper's
`λ₁ ≤ λ₂ ≤ λ₃`. This is Mathlib's antitone family `IsHermitian.eigenvalues₀`,
reversed. Lean index `1` is therefore the intermediate eigenvalue. Eigenvectors and
eigen-coordinates use the same ordering.
-/

noncomputable section
open scoped Matrix
open Polynomial

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

/-! ## Ordered eigenvalues

Mathlib's `IsHermitian.eigenvalues` is `eigenvalues₀` after a choice-based
cardinality reindexing, so its index `1` need not be the middle eigenvalue.
`IsHermitian.eigenvalues₀` is antitone (`λ₀ ≥ λ₁ ≥ λ₂`). We reverse it so that
the public family is monotone, matching the paper's `λ₁ ≤ λ₂ ≤ λ₃`. -/

/-- Identification `Fin 3 ≃ Fin (Fintype.card (Fin 3))` used to index
`IsHermitian.eigenvalues₀`. -/
def fin3cardIso : Fin 3 ≃o Fin (Fintype.card (Fin 3)) :=
  Fin.castOrderIso (Fintype.card_fin 3).symm

/-- The (choice-based) cardinality equivalence Mathlib uses to reindex
`eigenvalues₀` as `IsHermitian.eigenvalues`. -/
noncomputable def mathlibEigenindexEquiv : Fin (Fintype.card (Fin 3)) ≃ Fin 3 :=
  Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin 3)))

/-- Permutation such that `IsHermitian.eigenvalues (eigenvalueSortPerm i)` is
the `i`-th eigenvalue in increasing order. -/
noncomputable def eigenvalueSortPerm : Equiv.Perm (Fin 3) :=
  Fin.revPerm.trans (fin3cardIso.toEquiv.trans mathlibEigenindexEquiv)

/-- The three real eigenvalues of a real symmetric matrix, in increasing order:
`λ₀ ≤ λ₁ ≤ λ₂`. This is Mathlib's antitone family `eigenvalues₀`, reversed, and
matches the paper's labelling `λ₁ ≤ λ₂ ≤ λ₃`. -/
noncomputable def eigenvalues (S : StrainTensor ℝ) : Fin 3 → ℝ :=
  fun i => S.isHermitian.eigenvalues₀ (fin3cardIso i.rev)

/-- Mathlib's arbitrarily labelled eigenvalues (used only as a stepping stone). -/
noncomputable def eigenvaluesUnsorted (S : StrainTensor ℝ) : Fin 3 → ℝ :=
  fun i => S.isHermitian.eigenvalues i

theorem eigenvalues_eq_unsorted (S : StrainTensor ℝ) (i : Fin 3) :
    eigenvalues S i = eigenvaluesUnsorted S (eigenvalueSortPerm i) := by
  simp only [eigenvalues, eigenvaluesUnsorted, eigenvalueSortPerm, mathlibEigenindexEquiv,
    Matrix.IsHermitian.eigenvalues, Equiv.trans_apply, OrderIso.coe_toEquiv,
    Fin.revPerm_apply, Equiv.symm_apply_apply]

/-- The eigenvalues are monotone: `λ₀ ≤ λ₁ ≤ λ₂`. -/
theorem eigenvalues_monotone (S : StrainTensor ℝ) : Monotone (eigenvalues S) := by
  intro i j hij
  unfold eigenvalues
  refine S.isHermitian.eigenvalues₀_antitone ?_
  exact fin3cardIso.le_iff_le.mpr ((Fin.rev_le_rev (i := j) (j := i)).mpr hij)

/-- Concrete form of the ordering (paper: `λ₁ ≤ λ₂ ≤ λ₃`). -/
theorem eigenvalues_ordered (S : StrainTensor ℝ) :
    eigenvalues S 0 ≤ eigenvalues S 1 ∧ eigenvalues S 1 ≤ eigenvalues S 2 :=
  ⟨eigenvalues_monotone S (by decide : (0 : Fin 3) ≤ 1),
    eigenvalues_monotone S (by decide : (1 : Fin 3) ≤ 2)⟩

theorem eigenvalues_sum_zero (S : StrainTensor ℝ) :
    ∑ i, eigenvalues S i = 0 := by
  -- Trace equals the sum of Mathlib's (arbitrarily labelled) eigenvalues;
  -- reindex by `eigenvalueSortPerm` to the increasing family.
  calc
    ∑ i, eigenvalues S i
        = ∑ i, eigenvaluesUnsorted S (eigenvalueSortPerm i) := by
          refine Finset.sum_congr rfl fun i _ => eigenvalues_eq_unsorted S i
    _ = ∑ i, eigenvaluesUnsorted S i :=
          Equiv.sum_comp eigenvalueSortPerm (fun j => eigenvaluesUnsorted S j)
    _ = ∑ i, (S.isHermitian.eigenvalues i : ℝ) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [eigenvaluesUnsorted]
    _ = S.mat.trace := S.isHermitian.trace_eq_sum_eigenvalues.symm
    _ = 0 := S.trace_zero

/-- Because the eigenvalues are ordered and sum to zero, the smallest is
non-positive and the largest is non-negative (paper: `λ₁ ≤ 0 ≤ λ₃`). -/
theorem eigenvalues_min_nonpos_max_nonneg (S : StrainTensor ℝ) :
    eigenvalues S 0 ≤ 0 ∧ 0 ≤ eigenvalues S 2 := by
  have hs := eigenvalues_sum_zero S
  rw [Fin.sum_univ_three] at hs
  have h01 := (eigenvalues_ordered S).1
  have h12 := (eigenvalues_ordered S).2
  constructor
  · have : eigenvalues S 0 + eigenvalues S 0 + eigenvalues S 0 ≤
        eigenvalues S 0 + eigenvalues S 1 + eigenvalues S 2 := by linarith
    linarith
  · have : eigenvalues S 0 + eigenvalues S 1 + eigenvalues S 2 ≤
        eigenvalues S 2 + eigenvalues S 2 + eigenvalues S 2 := by linarith
    linarith

/-- Quadratic form of the strain on a unit vector, written in *ordered*
eigen-coordinates. "Unit" is Euclidean: `∑ i, (ξ i)^2 = 1`. (On `Fin 3 → ℝ`,
`‖ξ‖` is the sup norm, so the earlier hypothesis `‖ξ‖ = 1` did not say this;
see `sum_sq_eq_one_not_imp_norm_eq_one`.) -/
def stretching (S : StrainTensor ℝ) (ξ : Fin 3 → ℝ) (_hξ : ∑ i, (ξ i)^2 = 1) : ℝ :=
  ∑ i, eigenvalues S i * (ξ i)^2

theorem intermediate_representation (S : StrainTensor ℝ) (ξ : Fin 3 → ℝ)
    (hξ : ∑ i, (ξ i)^2 = 1) :
    stretching S ξ hξ =
      eigenvalues S 1 +
      (eigenvalues S 0 - eigenvalues S 1) * (ξ 0)^2 +
      (eigenvalues S 2 - eigenvalues S 1) * (ξ 2)^2 := by
  -- Substitute ξ₁² = 1 - ξ₀² - ξ₂² and rearrange. Here index 1 is the
  -- intermediate eigenvalue, by `eigenvalues_ordered`.
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
already written in *ordered* eigenvector coordinates. The results below connect
that to the matrix: with `U` the orthonormal eigenvector matrix in the same
increasing-eigenvalue order and `η = Uᵀ ξ` the ordered eigen-coordinates of `ξ`,
`ξ · S ξ = ∑ λᵢ ηᵢ²` and `∑ ηᵢ² = ∑ ξᵢ²`. -/

/-- Orthonormal eigenvector matrix of `S` in Mathlib's (arbitrarily labelled)
order, used only as a stepping stone. -/
noncomputable def eigvecsUnsorted (S : StrainTensor ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  (S.isHermitian.eigenvectorUnitary : Matrix (Fin 3) (Fin 3) ℝ)

/-- Orthonormal eigenvector matrix of `S`, with column `i` belonging to the
increasing eigenvalue `eigenvalues S i` (paper's `e₁, e₂, e₃`). -/
noncomputable def eigvecs (S : StrainTensor ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => eigvecsUnsorted S i (eigenvalueSortPerm j)

/-- Mathlib-labelled coordinates of `ξ` (stepping stone). -/
noncomputable def eigenCoordsUnsorted (S : StrainTensor ℝ) (ξ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (star (eigvecsUnsorted S)) *ᵥ ξ

/-- Coordinates of `ξ` in the ordered orthonormal eigenbasis of `S`. -/
noncomputable def eigenCoords (S : StrainTensor ℝ) (ξ : Fin 3 → ℝ) : Fin 3 → ℝ :=
  (star (eigvecs S)) *ᵥ ξ

theorem eigenCoords_eq_unsorted (S : StrainTensor ℝ) (ξ : Fin 3 → ℝ) (i : Fin 3) :
    eigenCoords S ξ i = eigenCoordsUnsorted S ξ (eigenvalueSortPerm i) := by
  unfold eigenCoords eigenCoordsUnsorted eigvecs
  -- `(star U') i j = U' j i = U_unsorted j (σ i) = (star U_unsorted) (σ i) j`
  simp only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
  simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply]

/-- Spectral form of the quadratic form in Mathlib's labelling (stepping stone). -/
theorem quadratic_form_eq_sum_unsorted (S : StrainTensor ℝ) (ξ : Fin 3 → ℝ) :
    ξ ⬝ᵥ (S.mat *ᵥ ξ) = ∑ i, eigenvaluesUnsorted S i * (eigenCoordsUnsorted S ξ i)^2 := by
  have hA := S.isHermitian
  set U : Matrix (Fin 3) (Fin 3) ℝ := eigvecsUnsorted S with hU
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
  simp only [Function.comp_apply, RCLike.ofReal_real_eq_id, id, eigenvaluesUnsorted,
    eigenCoordsUnsorted, hU]
  ring

/-- Spectral form of the quadratic form: `ξ · S ξ = ∑ λᵢ ηᵢ²` (paper eq. (2)),
in the *increasing* eigenvalue order. -/
theorem quadratic_form_eq_sum (S : StrainTensor ℝ) (ξ : Fin 3 → ℝ) :
    ξ ⬝ᵥ (S.mat *ᵥ ξ) = ∑ i, eigenvalues S i * (eigenCoords S ξ i)^2 := by
  rw [quadratic_form_eq_sum_unsorted]
  have h : ∀ i, eigenvaluesUnsorted S i * (eigenCoordsUnsorted S ξ i)^2 =
      eigenvalues S (eigenvalueSortPerm.symm i) *
        (eigenCoords S ξ (eigenvalueSortPerm.symm i))^2 := by
    intro i
    rw [eigenvalues_eq_unsorted, eigenCoords_eq_unsorted, Equiv.apply_symm_apply]
  -- Reindex the unsorted sum by `σ⁻¹`, then cancel `σ ∘ σ⁻¹`.
  calc
    ∑ i, eigenvaluesUnsorted S i * (eigenCoordsUnsorted S ξ i)^2
        = ∑ i, eigenvalues S (eigenvalueSortPerm.symm i) *
            (eigenCoords S ξ (eigenvalueSortPerm.symm i))^2 :=
          Finset.sum_congr rfl fun i _ => h i
    _ = ∑ i, eigenvalues S i * (eigenCoords S ξ i)^2 :=
          Equiv.sum_comp eigenvalueSortPerm.symm
            (fun j => eigenvalues S j * (eigenCoords S ξ j)^2)

/-- The (unsorted) eigen-coordinates preserve the Euclidean sum of squares. -/
theorem sum_sq_eigenCoordsUnsorted (S : StrainTensor ℝ) (ξ : Fin 3 → ℝ) :
    ∑ i, (eigenCoordsUnsorted S ξ i)^2 = ∑ i, (ξ i)^2 := by
  set U : Matrix (Fin 3) (Fin 3) ℝ := eigvecsUnsorted S with hU
  have key : ∀ v : Fin 3 → ℝ, ∑ i, (v i)^2 = v ⬝ᵥ v := fun v => by
    simp [dotProduct, sq]
  rw [key, key, eigenCoordsUnsorted, ← hU, Matrix.dotProduct_mulVec]
  rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    ← Matrix.mulVec_transpose, Matrix.transpose_transpose, Matrix.mulVec_mulVec]
  have h1 : U * Uᵀ = 1 := by
    have h2 : U * star U = 1 :=
      Unitary.mul_star_self_of_mem S.isHermitian.eigenvectorUnitary.2
    rwa [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial] at h2
  rw [h1, Matrix.one_mulVec]

/-- The ordered eigen-coordinates preserve the Euclidean sum of squares. -/
theorem sum_sq_eigenCoords (S : StrainTensor ℝ) (ξ : Fin 3 → ℝ) :
    ∑ i, (eigenCoords S ξ i)^2 = ∑ i, (ξ i)^2 := by
  calc
    ∑ i, (eigenCoords S ξ i)^2
        = ∑ i, (eigenCoordsUnsorted S ξ (eigenvalueSortPerm i))^2 := by
          refine Finset.sum_congr rfl fun i _ => by rw [eigenCoords_eq_unsorted]
    _ = ∑ i, (eigenCoordsUnsorted S ξ i)^2 :=
          Equiv.sum_comp eigenvalueSortPerm (fun j => (eigenCoordsUnsorted S ξ j)^2)
    _ = ∑ i, (ξ i)^2 := sum_sq_eigenCoordsUnsorted S ξ

/-- **Intermediate-eigenvalue representation (paper Proposition 1.1)**, on the
actual quadratic form, for every Euclidean unit vector `ξ`. Here `η` are the
*ordered* eigen-coordinates of `ξ`, and Lean indices `0, 1, 2` are the paper's
`1, 2, 3`. Index `1` is the intermediate eigenvalue, by `eigenvalues_ordered`. -/
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

/-- The characteristic polynomial of `diag(1, -1, 0)` is `(X-1)(X+1)X`. -/
theorem exampleStrain_charpoly :
    exampleStrain.mat.charpoly =
      (X - C (1 : ℝ)) * (X - C (-1 : ℝ)) * (X - C (0 : ℝ)) := by
  change (Matrix.diagonal ![1, -1, 0]).charpoly = _
  rw [Matrix.charpoly_diagonal, Fin.prod_univ_three]
  simp

/-- The roots of that characteristic polynomial are `{1, -1, 0}`. -/
theorem exampleStrain_charpoly_roots :
    exampleStrain.mat.charpoly.roots = {1, -1, 0} := by
  rw [exampleStrain_charpoly]
  have h1 : (X - C (1 : ℝ)) ≠ 0 := X_sub_C_ne_zero _
  have h2 : (X - C (-1 : ℝ)) ≠ 0 := X_sub_C_ne_zero _
  have h3 : (X - C (0 : ℝ)) ≠ 0 := X_sub_C_ne_zero _
  have h12 : (X - C (1 : ℝ)) * (X - C (-1 : ℝ)) ≠ 0 := mul_ne_zero h1 h2
  rw [roots_mul (mul_ne_zero h12 h3), roots_mul h12, roots_X_sub_C, roots_X_sub_C,
    roots_X_sub_C]
  simp

/-- The multiset of Mathlib's antitone eigenvalues of `diag(1, -1, 0)`
is `{1, -1, 0}`. -/
theorem exampleStrain_eigenvalues₀_multiset :
    Multiset.map exampleStrain.isHermitian.eigenvalues₀ Finset.univ.val = {1, -1, 0} := by
  have hr : exampleStrain.mat.charpoly.roots =
      Multiset.map (RCLike.ofReal ∘ exampleStrain.isHermitian.eigenvalues₀)
        Finset.univ.val := exampleStrain.isHermitian.roots_charpoly_eq_eigenvalues₀
  have hid : Multiset.map (RCLike.ofReal ∘ exampleStrain.isHermitian.eigenvalues₀)
        Finset.univ.val =
      Multiset.map exampleStrain.isHermitian.eigenvalues₀ Finset.univ.val := by
    refine Multiset.map_congr rfl fun _ _ => ?_
    simp [RCLike.ofReal_real_eq_id]
  rw [← hid, ← hr, exampleStrain_charpoly_roots]

/-- Reindexing `eigenvalues₀` along `fin3cardIso` does not change the multiset. -/
theorem exampleStrain_eigenvalues₀_multiset_iso :
    Multiset.map (fun i : Fin 3 => exampleStrain.isHermitian.eigenvalues₀ (fin3cardIso i))
      Finset.univ.val = {1, -1, 0} := by
  have hperm :
      Multiset.map (fun i : Fin 3 => (fin3cardIso i : Fin (Fintype.card (Fin 3))))
        Finset.univ.val = Finset.univ.val := by
    trans (Finset.univ.map fin3cardIso.toEquiv.toEmbedding).val
    · rw [Finset.map_val]; rfl
    · have hU : (Finset.univ.map fin3cardIso.toEquiv.toEmbedding :
          Finset (Fin (Fintype.card (Fin 3)))) = Finset.univ := by
        ext x
        constructor
        · intro _; exact Finset.mem_univ x
        · intro _
          refine Finset.mem_map.mpr ?_
          exact ⟨fin3cardIso.symm x, Finset.mem_univ _, fin3cardIso.apply_symm_apply x⟩
      rw [hU]
  rw [← exampleStrain_eigenvalues₀_multiset, ← hperm, Multiset.map_map]
  rfl

/-- Mathlib's antitone family for `diag(1, -1, 0)`, transported to `Fin 3`,
is `(1, 0, -1)`. -/
theorem exampleStrain_eigenvalues₀_eq :
    ∀ i : Fin 3, exampleStrain.isHermitian.eigenvalues₀ (fin3cardIso i) =
      ![1, 0, -1] i := by
  set f : Fin 3 → ℝ :=
    fun i => exampleStrain.isHermitian.eigenvalues₀ (fin3cardIso i)
  have hms : Multiset.map f Finset.univ.val = {1, -1, 0} :=
    exampleStrain_eigenvalues₀_multiset_iso
  have hmem : ∀ i, f i = (1 : ℝ) ∨ f i = -1 ∨ f i = 0 := by
    intro i
    have : f i ∈ Multiset.map f Finset.univ.val :=
      Multiset.mem_map.mpr ⟨i, Finset.mem_val.mpr (Finset.mem_univ i), rfl⟩
    have h' : f i ∈ ({(1 : ℝ), -1, 0} : Multiset ℝ) := by
      rw [← hms]; exact this
    simpa using h'
  have hanti01 : f 1 ≤ f 0 :=
    exampleStrain.isHermitian.eigenvalues₀_antitone
      (fin3cardIso.le_iff_le.mpr (by decide : (0 : Fin 3) ≤ 1))
  have hanti12 : f 2 ≤ f 1 :=
    exampleStrain.isHermitian.eigenvalues₀_antitone
      (fin3cardIso.le_iff_le.mpr (by decide : (1 : Fin 3) ≤ 2))
  have hanti02 : f 2 ≤ f 0 := le_trans hanti12 hanti01
  -- 1 appears among the three values, and f 0 is the largest, so f 0 = 1.
  have hf0 : f 0 = 1 := by
    have h1 : (1 : ℝ) = f 0 ∨ 1 = f 1 ∨ 1 = f 2 := by
      have : (1 : ℝ) ∈ Multiset.map f Finset.univ.val := by simp [hms]
      simpa using this
    have hge : (1 : ℝ) ≤ f 0 := by
      rcases h1 with h | h | h <;> linarith
    have : f 0 ≤ 1 := by
      rcases hmem 0 with h | h | h <;> linarith
    linarith
  -- -1 appears among the three values, and f 2 is the smallest, so f 2 = -1.
  have hf2 : f 2 = -1 := by
    have hm1 : (-1 : ℝ) = f 0 ∨ -1 = f 1 ∨ -1 = f 2 := by
      have : (-1 : ℝ) ∈ Multiset.map f Finset.univ.val := by simp [hms]
      simpa using this
    have hle : f 2 ≤ (-1 : ℝ) := by
      rcases hm1 with h | h | h <;> linarith
    have : -1 ≤ f 2 := by
      rcases hmem 2 with h | h | h <;> linarith
    linarith
  -- The remaining value is 0.
  have hf1 : f 1 = 0 := by
    have hm0 : (0 : ℝ) = f 0 ∨ 0 = f 1 ∨ 0 = f 2 := by
      have : (0 : ℝ) ∈ Multiset.map f Finset.univ.val := by simp [hms]
      simpa using this
    rcases hm0 with h | h | h
    · have : (0 : ℝ) = 1 := h.trans hf0
      norm_num at this
    · exact h.symm
    · have : (0 : ℝ) = -1 := h.trans hf2
      norm_num at this
  intro i
  fin_cases i <;> simp [f, hf0, hf1, hf2]

/-- The increasing eigenvalues of `diag(1, -1, 0)` are `(-1, 0, 1)`. -/
theorem exampleStrain_eigenvalues_eq :
    eigenvalues exampleStrain = ![-1, 0, 1] := by
  ext i
  -- eigenvalues i = eigenvalues₀ (fin3cardIso i.rev)
  -- i.rev runs 2,1,0 as i runs 0,1,2, and eigenvalues₀ ∘ iso is ![1,0,-1]
  -- so we get ![-1, 0, 1]
  simp only [eigenvalues]
  have h := exampleStrain_eigenvalues₀_eq (i.rev)
  -- h : eigenvalues₀ (fin3cardIso i.rev) = ![1, 0, -1] i.rev
  -- and ![1, 0, -1] i.rev = ![-1, 0, 1] i
  rw [h]
  fin_cases i <;> simp

/-- Its eigenvalues are not all zero (so `eigenvalues_sum_zero` is non-trivial). -/
theorem exampleStrain_eigenvalues_ne_zero : eigenvalues exampleStrain ≠ 0 := by
  intro h
  have := congrFun h 0
  simp [exampleStrain_eigenvalues_eq] at this

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
