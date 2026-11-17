/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import StrainEigenvalue.Eigenbasis

/-!
# Truth Gate: semantics lock (see `TRUTH_GATE.md`)

PAPER_PATH: paper/Strain_Eigenvalue_Breakdown.tex
PAPER_SHA256: 9f1e2db28b8b73951d3068ecbf14744ea5c2849aae14ae928695e2d995a8f6e3
PAPER_SECTION: Section 1, Proposition "Intermediate-eigenvalue representation" (Proposition 1.1)

Locked paper claim, quoted verbatim (the setting, then the proposition):

PAPER_QUOTE_BEGIN
be the symmetric strain-rate tensor. Then \(\operatorname{tr}S=\nabla\cdot u=0\), so the three real eigenvalues satisfy (cf.\ Betchov~\cite{Betchov1956})
\begin{equation}\label{eq:trace}
\lambda_1\le\lambda_2\le\lambda_3,\qquad\lambda_1+\lambda_2+\lambda_3=0.
\end{equation}
At each point where \(S\) is continuous there exists an orthonormal eigenbasis \(\{e_1,e_2,e_3\}\). Writing the unit vorticity direction
\[
\boldsymbol{\xi}=\frac{\omega}{|\omega|}=\xi_1 e_1+\xi_2 e_2+\xi_3 e_3
\]
(with \(\xi_1^2+\xi_2^2+\xi_3^2=1\)) one obtains the quadratic form
PAPER_QUOTE_END

PAPER_QUOTE_BEGIN
\begin{proposition}[Intermediate-eigenvalue representation]
\[
\boldsymbol{\xi}\cdot S\boldsymbol{\xi}
=\lambda_2+(\lambda_1-\lambda_2)\xi_1^2+(\lambda_3-\lambda_2)\xi_3^2.
\]
PAPER_QUOTE_END

Reading of the paper's terms (fixed here, once, from the quoted text only; no repository
definition is used in `paper_claim`):
* `S` is a real symmetric `3 × 3` matrix with `tr S = 0` (the strain at a point);
* `λ₁ ≤ λ₂ ≤ λ₃` are real eigenvalues of `S` with an orthonormal eigenbasis `e₁, e₂, e₃`:
  `eᵢ · eⱼ = δᵢⱼ` and `S eᵢ = λᵢ eᵢ` (named `l₁, l₂, l₃`, since `λ` is a Lean keyword). The
  proposition is stated for such a basis, whichever one is chosen;
* `ξ = ξ₁e₁ + ξ₂e₂ + ξ₃e₃` with `ξ₁² + ξ₂² + ξ₃² = 1`;
* `ξ · S ξ` is the dot product of `ξ` with `S ξ`.
The trace identity `λ₁ + λ₂ + λ₃ = 0` in the quoted setting is a consequence, not a hypothesis,
and is not needed for the proposition.

`formal_claim` is the statement of `StrainEigenvalue.quadratic_form_intermediate_of_eigenbasis`:
for a `StrainTensor`, any `U` with `Uᵀ U = 1` and `S U = U diag(l)`, `l` monotone, and
`η = Uᵀ ξ`. `paper_claim` uses a raw matrix, three vectors and three reals, and builds `ξ` from
its coordinates. The correspondence assembles/disassembles the matrix `U` from/into its columns.
(The earlier lock read the paper through the repository's `eigenvalues`/`eigenCoords`; it was
reopened on 2026-11-16 for that reason.)

Non-vacuity: `nonvacuity_witness` below exhibits `S = diag(-1, 0, 1)`, eigenvalues `-1 ≤ 0 ≤ 1`,
the standard basis and `ξ = e₁`, satisfying every hypothesis of `paper_claim`; for that witness
both sides equal `-1`.

Scope: a pointwise algebraic identity. It gives no bound on `‖S‖_{L^∞}`, leaves Hypothesis B
open and makes no claim about the Clay Millennium problem.
-/

namespace TruthGate

open StrainEigenvalue
open scoped Matrix

-- TRUTH-GATE LOCK BEGIN
/-- The repository's main statement (`quadratic_form_intermediate_of_eigenbasis`): for any
ordered orthonormal eigenbasis, given as the columns of `U`. -/
def formal_claim : Prop :=
  ∀ (S : StrainTensor ℝ) (U : Matrix (Fin 3) (Fin 3) ℝ) (l : Fin 3 → ℝ),
    Uᵀ * U = 1 → S.mat * U = U * Matrix.diagonal l → Monotone l →
    ∀ (ξ : Fin 3 → ℝ), ∑ i, (ξ i)^2 = 1 →
      ξ ⬝ᵥ (S.mat *ᵥ ξ) =
        l 1 + (l 0 - l 1) * ((Uᵀ *ᵥ ξ) 0)^2 + (l 2 - l 1) * ((Uᵀ *ᵥ ξ) 2)^2

/-- Paper Proposition 1.1, in the paper's own terms: `S` symmetric with `tr S = 0`, real
eigenvalues `λ₁ ≤ λ₂ ≤ λ₃` with an orthonormal eigenbasis `e₁, e₂, e₃` (`S eᵢ = λᵢ eᵢ`), and
`ξ = ξ₁e₁ + ξ₂e₂ + ξ₃e₃` with `ξ₁² + ξ₂² + ξ₃² = 1`. Then
`ξ·Sξ = λ₂ + (λ₁ - λ₂) ξ₁² + (λ₃ - λ₂) ξ₃²`. (`λ` is a Lean keyword, so `l₁, l₂, l₃`.) -/
def paper_claim : Prop :=
  ∀ (A : Matrix (Fin 3) (Fin 3) ℝ), A.IsSymm → A.trace = 0 →
    ∀ (l₁ l₂ l₃ : ℝ) (e₁ e₂ e₃ : Fin 3 → ℝ),
      l₁ ≤ l₂ → l₂ ≤ l₃ →
      e₁ ⬝ᵥ e₁ = 1 → e₂ ⬝ᵥ e₂ = 1 → e₃ ⬝ᵥ e₃ = 1 →
      e₁ ⬝ᵥ e₂ = 0 → e₁ ⬝ᵥ e₃ = 0 → e₂ ⬝ᵥ e₃ = 0 →
      A *ᵥ e₁ = l₁ • e₁ → A *ᵥ e₂ = l₂ • e₂ → A *ᵥ e₃ = l₃ • e₃ →
      ∀ ξ₁ ξ₂ ξ₃ : ℝ, ξ₁^2 + ξ₂^2 + ξ₃^2 = 1 →
        (ξ₁ • e₁ + ξ₂ • e₂ + ξ₃ • e₃) ⬝ᵥ (A *ᵥ (ξ₁ • e₁ + ξ₂ • e₂ + ξ₃ • e₃)) =
          l₂ + (l₁ - l₂) * ξ₁^2 + (l₃ - l₂) * ξ₃^2

/-- Dot product of a combination of three orthonormal vectors with one of them. -/
theorem dot_combo (e₁ e₂ e₃ v : Fin 3 → ℝ) (a b c : ℝ) :
    (a • e₁ + b • e₂ + c • e₃) ⬝ᵥ v = a * (e₁ ⬝ᵥ v) + b * (e₂ ⬝ᵥ v) + c * (e₃ ⬝ᵥ v) := by
  simp [add_dotProduct, smul_dotProduct]

/-- The fixed correspondence between the formal statement and the paper's claim. -/
theorem intended_correspondence : formal_claim ↔ paper_claim := by
  constructor
  · intro h A hsymm htr l₁ l₂ l₃ e₁ e₂ e₃ hl12 hl23 h11 h22 h33 h12 h13 h23 he₁ he₂ he₃
      ξ₁ ξ₂ ξ₃ hξ
    let E : Fin 3 → Fin 3 → ℝ := ![e₁, e₂, e₃]
    let U : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of fun r c => E c r
    let l : Fin 3 → ℝ := ![l₁, l₂, l₃]
    have hUU : ∀ i j, (Uᵀ * U) i j = E i ⬝ᵥ E j := fun i j => by
      simp [Matrix.mul_apply, dotProduct, U]
    have hU : Uᵀ * U = 1 := by
      ext i j
      rw [hUU]
      fin_cases i <;> fin_cases j <;>
        simp [E, h11, h22, h33, h12, h13, h23, dotProduct_comm e₂ e₁, dotProduct_comm e₃ e₁,
          dotProduct_comm e₃ e₂]
    have hAU : ∀ r c, (A * U) r c = (A *ᵥ E c) r := fun r c => by
      simp [Matrix.mul_apply, Matrix.mulVec, dotProduct, U]
    have hSU : A * U = U * Matrix.diagonal l := by
      ext r c
      rw [hAU, Matrix.mul_diagonal]
      fin_cases c <;> simp [E, U, l, he₁, he₂, he₃, mul_comm]
    have hl : Monotone l := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [l, Fin.le_def] <;> linarith
    set ξ : Fin 3 → ℝ := ξ₁ • e₁ + ξ₂ • e₂ + ξ₃ • e₃ with hξdef
    have hcoord : ∀ i, (Uᵀ *ᵥ ξ) i = E i ⬝ᵥ ξ := fun i => by
      simp [Matrix.mulVec, dotProduct, U]
    have hd1 : e₁ ⬝ᵥ ξ = ξ₁ := by
      rw [dotProduct_comm, hξdef, dot_combo, h11, dotProduct_comm e₂ e₁, h12,
        dotProduct_comm e₃ e₁, h13]; ring
    have hd2 : e₂ ⬝ᵥ ξ = ξ₂ := by
      rw [dotProduct_comm, hξdef, dot_combo, h12, h22, dotProduct_comm e₃ e₂, h23]; ring
    have hd3 : e₃ ⬝ᵥ ξ = ξ₃ := by
      rw [dotProduct_comm, hξdef, dot_combo, h13, h23, h33]; ring
    have hnorm : ∑ i, (ξ i)^2 = 1 := by
      have : ∑ i, (ξ i)^2 = ξ ⬝ᵥ ξ := by simp [dotProduct, pow_two]
      rw [this]
      conv_lhs => rw [hξdef]
      rw [dot_combo, hd1, hd2, hd3, ← hξ]; ring
    have key := h ⟨A, hsymm, htr⟩ U l hU hSU hl ξ hnorm
    rw [hcoord, hcoord] at key
    simpa [E, l, hd1, hd3] using key
  · intro h S U l hU hSU hl ξ hξ
    have hUU : U * Uᵀ = 1 := mul_eq_one_comm.mp hU
    let e : Fin 3 → Fin 3 → ℝ := fun c r => U r c
    let η : Fin 3 → ℝ := Uᵀ *ᵥ ξ
    have hdot : ∀ i j, e i ⬝ᵥ e j = (1 : Matrix (Fin 3) (Fin 3) ℝ) i j := fun i j => by
      rw [← hU]; simp [Matrix.mul_apply, dotProduct, e]
    have heig : ∀ c, S.mat *ᵥ e c = l c • e c := fun c => by
      funext r
      have := congrFun (congrFun hSU r) c
      rw [Matrix.mul_diagonal, Matrix.mul_apply] at this
      simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul, e]
      rw [this]; ring
    have hξU : ξ = U *ᵥ η := by
      simp only [η]; rw [Matrix.mulVec_mulVec, hUU, Matrix.one_mulVec]
    have hξη : ξ = η 0 • e 0 + η 1 • e 1 + η 2 • e 2 := by
      conv_lhs => rw [hξU]
      funext r
      simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three, e, mul_comm]
    have hηn : (η 0)^2 + (η 1)^2 + (η 2)^2 = 1 := by
      have h1 : ξ ⬝ᵥ ξ = 1 := by rw [← hξ]; simp [dotProduct, pow_two]
      have h2 : η ⬝ᵥ η = ξ ⬝ᵥ ξ := by
        symm
        calc ξ ⬝ᵥ ξ = (U *ᵥ η) ⬝ᵥ (U *ᵥ η) := by rw [← hξU]
          _ = ((U *ᵥ η) ᵥ* U) ⬝ᵥ η := Matrix.dotProduct_mulVec _ _ _
          _ = η ⬝ᵥ η := by
            rw [← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hU, Matrix.one_mulVec]
      rw [h1] at h2
      simpa [dotProduct, Fin.sum_univ_three, pow_two] using h2
    have key := h S.mat S.symm S.trace_zero (l 0) (l 1) (l 2) (e 0) (e 1) (e 2)
      (hl (by decide)) (hl (by decide))
      (by rw [hdot]; simp) (by rw [hdot]; simp) (by rw [hdot]; simp)
      (by rw [hdot]; simp) (by rw [hdot]; simp) (by rw [hdot]; simp)
      (heig 0) (heig 1) (heig 2) (η 0) (η 1) (η 2) hηn
    rw [← hξη] at key
    exact key
-- TRUTH-GATE LOCK END

/-- The main theorem proves `formal_claim`. -/
theorem formal_claim_holds : formal_claim :=
  fun S U l hU hSU hl ξ hξ => quadratic_form_intermediate_of_eigenbasis S U l hU hSU hl ξ hξ

/-- The paper's claim, transported across the correspondence. -/
theorem paper_claim_holds : paper_claim :=
  intended_correspondence.mp formal_claim_holds

/-- Witness data: `S = diag(-1, 0, 1)` and its standard eigenbasis. -/
def witnessA : Matrix (Fin 3) (Fin 3) ℝ := Matrix.diagonal ![-1, 0, 1]
def we₁ : Fin 3 → ℝ := ![1, 0, 0]
def we₂ : Fin 3 → ℝ := ![0, 1, 0]
def we₃ : Fin 3 → ℝ := ![0, 0, 1]

/-- Non-vacuity witness: every hypothesis of `paper_claim` holds for `S = diag(-1, 0, 1)`,
`λ = (-1, 0, 1)`, the standard basis, and `ξ = e₁`; both sides then equal `-1`. -/
theorem nonvacuity_witness :
    witnessA.IsSymm ∧ witnessA.trace = 0 ∧ (-1 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 ∧
      we₁ ⬝ᵥ we₁ = 1 ∧ we₂ ⬝ᵥ we₂ = 1 ∧ we₃ ⬝ᵥ we₃ = 1 ∧
      we₁ ⬝ᵥ we₂ = 0 ∧ we₁ ⬝ᵥ we₃ = 0 ∧ we₂ ⬝ᵥ we₃ = 0 ∧
      witnessA *ᵥ we₁ = (-1 : ℝ) • we₁ ∧ witnessA *ᵥ we₂ = (0 : ℝ) • we₂ ∧
      witnessA *ᵥ we₃ = (1 : ℝ) • we₃ ∧
      (1 : ℝ)^2 + 0^2 + 0^2 = 1 ∧
      ((1 : ℝ) • we₁ + (0 : ℝ) • we₂ + (0 : ℝ) • we₃) ⬝ᵥ
          (witnessA *ᵥ ((1 : ℝ) • we₁ + (0 : ℝ) • we₂ + (0 : ℝ) • we₃)) = -1 := by
  refine ⟨Matrix.isSymm_diagonal _, ?_, by norm_num, by norm_num, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, by norm_num, ?_⟩
  · simp [witnessA, Matrix.trace, Fin.sum_univ_three]
  all_goals first
    | (simp [we₁, we₂, we₃, dotProduct, Fin.sum_univ_three]; done)
    | (funext i; fin_cases i <;> simp [witnessA, we₁, we₂, we₃, Matrix.mulVec_diagonal])
    | simp [witnessA, we₁, we₂, we₃, dotProduct, Fin.sum_univ_three, Matrix.mulVec_diagonal]

end TruthGate
