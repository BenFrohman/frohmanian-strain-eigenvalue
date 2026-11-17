# TRUTH GATE — the GOD gate. Read this first.

Author: Benjamin Stanley Frohman. This file is the root instruction for every person and every
automated agent (every bot) that touches this repository. Load it before any other file.

**Only truth and honest, kernel-proved theorems pass this gate. Nothing from this repository is
published, released, deposited on Zenodo, cited or claimed unless the `truth-gate` check is green
on the exact commit being cited.** That is why it is the GOD gate: it sits above every other
check, and no other green check can stand in for it.

## The issue this gate fixes

A paper states its claim in English. Lean can only prove `formal_claim ↔ paper_claim` once
`paper_claim` is itself written in Lean. If `paper_claim` were simply *defined to be*
`formal_claim` (or an alias of it, or something that unfolds to it), the theorem
`intended_correspondence` would be `Iff.rfl`: it would be empty and prove nothing about the
paper. A green certificate could then "certify" a statement different from the one the paper
makes (drift), whether by accident or by an injected instruction.

## The fix rule (binding, permanent)

1. `paper_claim` is an **independent Lean transcription of the paper's exact claim**, written in
   the paper's own terms, with every hypothesis the paper states. The verbatim English quote,
   the paper path, its sha256 and the section are recorded in the doc comment of
   `Semantics.lean` **and** in this file (below).
2. `paper_claim` must **not** be defined as, reference, or trivially alias `formal_claim`.
3. `intended_correspondence : formal_claim ↔ paper_claim` must have a **substantive proof**. It
   may not be `Iff.rfl`, `rfl`, `exact Iff.rfl` or similar, and it may not use the main theorem
   (it is a statement-level equivalence, not "both sides happen to be provable").
4. `formal_claim` is exactly the statement of the repository's main theorem, and
   `paper_claim_holds` is the main theorem transported across the correspondence.
5. Only `propext`, `Classical.choice` and `Quot.sound`. No `sorry`, `admit`, `native_decide` or
   new `axiom` anywhere outside the draft directories in `TRUTH_GATE.lock`.
6. If the paper's English claim cannot be faithfully transcribed, or is not what Lean proves,
   the gate stays **red** and the mismatch is reported. Never patch over it: never weaken
   `paper_claim`, drop a hypothesis, or redefine it to match the formal side. If the
   formalization drifted, rewrite the formalization so it transports across the lock again.
7. Open problems stay hypotheses. No Millennium Prize problem is claimed solved; the gate only
   ensures the certificate proves precisely the locked claim and nothing else.
8. The locked region of `Semantics.lean`, the quote and `TRUTH_GATE.lock` change only with the
   author's explicit sign-off, as a PR that says "new lock" in its title.
9. Commits are authored by Benjamin Stanley Frohman only, with no AI co-author trailers. No
   force-push and no history rewriting.

## What `scripts/verify-lock.sh` checks mechanically

* `lake build` succeeds, with no `sorry` warning outside the draft directories;
* no `sorry` / `admit` / `native_decide` / `axiom` token outside the draft directories
  (comments and strings excluded);
* `Semantics.lean` has `PAPER_PATH`, `PAPER_SHA256`, `PAPER_SECTION` and a verbatim
  `PAPER_QUOTE`; the hash matches the paper file and the quote occurs in it; this file carries
  the same path, hash and quote;
* the lock region hash matches `TRUTH_GATE.lock`;
* `paper_claim`'s body does not mention `formal_claim`; the correspondence is not proved by
  `Iff.rfl`/`rfl`;
* in Lean: the bodies of `formal_claim` and `paper_claim` differ, the two are not
  definitionally equal, the correspondence proof does not reach the main theorem, the main
  theorem's statement is `formal_claim`, `paper_claim_holds` goes through the correspondence,
  and `#print axioms` shows only the three standard axioms.

What it cannot check: whether the transcription is the right reading of the English. That
reading is fixed once, in writing, below and in `Semantics.lean`, and is the author's sign-off.

## Running the gate locally

```
lake exe cache get
bash scripts/verify-lock.sh
```

Reports are written to `truth-gate-report/`.

## The locked claim of this repository

* Paper: `paper/Strain_Eigenvalue_Breakdown.tex`
* sha256: `9f1e2db28b8b73951d3068ecbf14744ea5c2849aae14ae928695e2d995a8f6e3`
* Section: Section 1, Proposition "Intermediate-eigenvalue representation" (Proposition 1.1)
* Main theorem(s): `StrainEigenvalue.quadratic_form_intermediate_of_eigenbasis`
* Lock file: `TRUTH_GATE.lock`; semantics: `StrainEigenvalue/Semantics.lean`

Verbatim quote:

```
be the symmetric strain-rate tensor. Then \(\operatorname{tr}S=\nabla\cdot u=0\), so the three real eigenvalues satisfy (cf.\ Betchov~\cite{Betchov1956})
\begin{equation}\label{eq:trace}
\lambda_1\le\lambda_2\le\lambda_3,\qquad\lambda_1+\lambda_2+\lambda_3=0.
\end{equation}
At each point where \(S\) is continuous there exists an orthonormal eigenbasis \(\{e_1,e_2,e_3\}\). Writing the unit vorticity direction
\[
\boldsymbol{\xi}=\frac{\omega}{|\omega|}=\xi_1 e_1+\xi_2 e_2+\xi_3 e_3
\]
(with \(\xi_1^2+\xi_2^2+\xi_3^2=1\)) one obtains the quadratic form

\begin{proposition}[Intermediate-eigenvalue representation]
\[
\boldsymbol{\xi}\cdot S\boldsymbol{\xi}
=\lambda_2+(\lambda_1-\lambda_2)\xi_1^2+(\lambda_3-\lambda_2)\xi_3^2.
\]
```

```lean
def formal_claim : Prop :=
  ∀ (S : StrainTensor ℝ) (U : Matrix (Fin 3) (Fin 3) ℝ) (l : Fin 3 → ℝ),
    Uᵀ * U = 1 → S.mat * U = U * Matrix.diagonal l → Monotone l →
    ∀ (ξ : Fin 3 → ℝ), ∑ i, (ξ i)^2 = 1 →
      ξ ⬝ᵥ (S.mat *ᵥ ξ) =
        l 1 + (l 0 - l 1) * ((Uᵀ *ᵥ ξ) 0)^2 + (l 2 - l 1) * ((Uᵀ *ᵥ ξ) 2)^2

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
```

See the doc comment of `StrainEigenvalue/Semantics.lean` for the fixed reading of the paper's terms, the scope and the non-vacuity witness.

## Re-audit (2026-11-16): the earlier lock was NOT certifying (superseded by the re-lock below)

Status at the re-audit: **REOPENED. The gate was red on purpose.** `TRUTH_GATE.lock` carries `"certifying": false`, and
`scripts/truth_gate_check.py` fails while it does. Nothing was deleted: `Semantics.lean`, the quotes,
the hashes and the history are unchanged.

Rule applied (Benjamin Stanley Frohman, 2026-11-16):
* There are no partial locks. A lock certifies only a step on the correct path to the full theorem
  that is kernel-proved as the actual true answer, so that the next step can build on it.
* Drifted, dummy, placeholder or stand-in types, names or categories are rejected.
* Cross-ontology connections are not rejected for looking unrelated. The kernel check, and whether
  the piece genuinely helps reach the full structured proof, decide.
* `paper_claim` is an independent transcription of the verbatim paper quote, never an alias of
  `formal_claim`, and the correspondence is never `rfl`/`Iff.rfl`.

Locked claim under review: quadratic_form_intermediate (Proposition 1.1, intermediate-eigenvalue representation)

Why it is reopened:
* Not an independent transcription. `paper_claim` uses the repository's own `eigenvalues` and `eigenCoords` for the ordered eigenvalues λ₁ ≤ λ₂ ≤ λ₃ and the coordinates ξ₁, ξ₃, so the terms that carry the content are read through repository definitions.
* Otherwise the claim is the complete Proposition 1.1, it is about the real objects (symmetric trace-free 3×3 matrices), and it is kernel-checked.

What would re-certify it: Re-lock with `paper_claim` transcribed from the paper's words. For a symmetric trace-free `A`, every orthonormal eigenbasis `e₁, e₂, e₃` with eigenvalues `λ₁ ≤ λ₂ ≤ λ₃`, and every unit `ξ`: `ξ·Aξ = λ₂ + (λ₁−λ₂)(ξ·e₁)² + (λ₃−λ₂)(ξ·e₃)²`.

## Re-lock (2026-11-16): full lock, certifying

With Benjamin Stanley Frohman's approval of 2026-11-16, the lock was replaced by a full lock:
Proposition 1.1 for any orthonormal eigenbasis e₁, e₂, e₃ with λ₁ ≤ λ₂ ≤ λ₃, transcribed from the paper's own terms (raw symmetric trace-free matrix, three reals, three orthonormal eigenvectors, ξ = ξ₁e₁ + ξ₂e₂ + ξ₃e₃), with no use of the repository's `eigenvalues`/`eigenCoords`. New main theorem `quadratic_form_intermediate_of_eigenbasis` (StrainEigenvalue/Eigenbasis.lean).

Previous main theorem(s): `StrainEigenvalue.quadratic_form_intermediate`. New main theorem(s): `StrainEigenvalue.quadratic_form_intermediate_of_eigenbasis`. `TRUTH_GATE.lock` is back to `"certifying": true`; the reopen record is kept under `reaudit_history`.
All rules still apply: no `sorry`/`admit`/`native_decide`/new axioms; only `propext`, `Classical.choice`, `Quot.sound`;
`paper_claim` is an independent transcription of the verbatim quote; the correspondence is substantive (not `rfl`/`Iff.rfl`)
and does not use the main theorems; a non-vacuity witness is proved in `StrainEigenvalue/Semantics.lean`.
