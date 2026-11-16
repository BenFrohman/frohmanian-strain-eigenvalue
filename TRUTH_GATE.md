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
* Main theorem(s): `StrainEigenvalue.quadratic_form_intermediate`
* Lock file: `TRUTH_GATE.lock`; semantics: `StrainEigenvalue/Semantics.lean`

Verbatim quote:

```
\begin{proposition}[Intermediate-eigenvalue representation]
\[
\boldsymbol{\xi}\cdot S\boldsymbol{\xi}
=\lambda_2+(\lambda_1-\lambda_2)\xi_1^2+(\lambda_3-\lambda_2)\xi_3^2.
\]
```

```lean
def formal_claim : Prop :=
  ∀ (S : StrainTensor ℝ) (ξ : Fin 3 → ℝ), ∑ i, (ξ i)^2 = 1 →
    ξ ⬝ᵥ (S.mat *ᵥ ξ) =
      eigenvalues S 1 +
      (eigenvalues S 0 - eigenvalues S 1) * (eigenCoords S ξ 0)^2 +
      (eigenvalues S 2 - eigenvalues S 1) * (eigenCoords S ξ 2)^2

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
```

See the doc comment of `StrainEigenvalue/Semantics.lean` for the fixed reading of the paper's terms and the scope.
