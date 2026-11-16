/-
Copyright (c) 2026 Benjamin Stanley Frohman. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Benjamin Stanley Frohman
-/

import StrainEigenvalue

/-!
# Truth Gate: semantics lock (see `TRUTH_GATE.md`)

PAPER_PATH: paper/Strain_Eigenvalue_Breakdown.tex
PAPER_SHA256: 9f1e2db28b8b73951d3068ecbf14744ea5c2849aae14ae928695e2d995a8f6e3
PAPER_SECTION: Section 1, Proposition "Intermediate-eigenvalue representation" (Proposition 1.1)

Locked paper claim, quoted verbatim:

PAPER_QUOTE_BEGIN
\begin{proposition}[Intermediate-eigenvalue representation]
\[
\boldsymbol{\xi}\cdot S\boldsymbol{\xi}
=\lambda_2+(\lambda_1-\lambda_2)\xi_1^2+(\lambda_3-\lambda_2)\xi_3^2.
\]
PAPER_QUOTE_END

Reading of the paper's terms (fixed here, once, following the paper's own Section "Lean
formalization: exact scope"):
* `S` is a real symmetric `3 × 3` matrix with zero trace (the strain at a point; `tr S = ∇·u = 0`);
* `λ₁ ≤ λ₂ ≤ λ₃` (named `l₁, l₂, l₃` below, since `λ` is a Lean keyword) are its eigenvalues in
  increasing order, `StrainEigenvalue.eigenvalues` at Lean indices `0, 1, 2`;
* `ξ` is a Euclidean unit vector (`ξ₁² + ξ₂² + ξ₃² = 1`), and `ξ₁, ξ₂, ξ₃` are its coordinates
  in the ordered orthonormal eigenbasis `e₁, e₂, e₃`, `StrainEigenvalue.eigenCoords`;
* `ξ · S ξ` is the dot product of `ξ` with `S ξ`.

`formal_claim` is the statement of `StrainEigenvalue.quadratic_form_intermediate` (over the bundled
structure `StrainTensor`). `paper_claim` quantifies over raw symmetric trace-free matrices and
names the paper's `λ₁, λ₂, λ₃` and `ξ₁, ξ₃` explicitly.

Scope: a pointwise algebraic identity. It gives no bound on `‖S‖_{L^∞}`, leaves Hypothesis B
open and makes no claim about the Clay Millennium problem.
-/

namespace TruthGate

open StrainEigenvalue
open scoped Matrix

-- TRUTH-GATE LOCK BEGIN
/-- The repository's main statement (`quadratic_form_intermediate`). -/
def formal_claim : Prop :=
  ∀ (S : StrainTensor ℝ) (ξ : Fin 3 → ℝ), ∑ i, (ξ i)^2 = 1 →
    ξ ⬝ᵥ (S.mat *ᵥ ξ) =
      eigenvalues S 1 +
      (eigenvalues S 0 - eigenvalues S 1) * (eigenCoords S ξ 0)^2 +
      (eigenvalues S 2 - eigenvalues S 1) * (eigenCoords S ξ 2)^2

/-- Paper Proposition 1.1: for a symmetric trace-free `S` and a unit `ξ`,
`ξ·Sξ = λ₂ + (λ₁ - λ₂) ξ₁² + (λ₃ - λ₂) ξ₃²`. -/
def paper_claim : Prop :=
  ∀ (A : Matrix (Fin 3) (Fin 3) ℝ) (hsymm : A.IsSymm) (htr : A.trace = 0) (ξ : Fin 3 → ℝ),
    (ξ 0)^2 + (ξ 1)^2 + (ξ 2)^2 = 1 →
      let S : StrainTensor ℝ := ⟨A, hsymm, htr⟩
      let l₁ := eigenvalues S 0
      let l₂ := eigenvalues S 1
      let l₃ := eigenvalues S 2
      let ξ₁ := eigenCoords S ξ 0
      let ξ₃ := eigenCoords S ξ 2
      ξ ⬝ᵥ (A *ᵥ ξ) = l₂ + (l₁ - l₂) * ξ₁^2 + (l₃ - l₂) * ξ₃^2

/-- The fixed correspondence between the formal statement and the paper's claim. -/
theorem intended_correspondence : formal_claim ↔ paper_claim := by
  constructor
  · intro h A hsymm htr ξ hξ
    have hs : ∑ i, (ξ i)^2 = 1 := by simpa [Fin.sum_univ_three] using hξ
    exact h ⟨A, hsymm, htr⟩ ξ hs
  · intro h S ξ hξ
    have hs : (ξ 0)^2 + (ξ 1)^2 + (ξ 2)^2 = 1 := by simpa [Fin.sum_univ_three] using hξ
    obtain ⟨A, hsymm, htr⟩ := S
    exact h A hsymm htr ξ hs
-- TRUTH-GATE LOCK END

/-- The main theorem proves `formal_claim`. -/
theorem formal_claim_holds : formal_claim :=
  fun S ξ hξ => quadratic_form_intermediate S ξ hξ

/-- The paper's claim, transported across the correspondence. -/
theorem paper_claim_holds : paper_claim :=
  intended_correspondence.mp formal_claim_holds

end TruthGate
