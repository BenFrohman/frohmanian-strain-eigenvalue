# Strain-tensor eigenvalue decomposition

Author: Benjamin Stanley Frohman
Affiliation: Independent Researcher, Texas, United States
ORCID: [0009-0006-7068-3718](https://orcid.org/0009-0006-7068-3718)
Email: frohmanbenjamin@gmail.com

This private repository contains a **Lean 4 skeleton**
(`StrainEigenvalue.lean`) and a short algebraic note
(`paper/Strain_Eigenvalue_Breakdown.tex`, with a compiled PDF). The note
records the elementary eigenvalue decomposition of the symmetric,
trace-free strain-rate tensor of a divergence-free field, and the
consequences of that identity for the local vortex-stretching term.

## Honest scope

- **This is a skeleton, not a completed formalization.** One theorem is
  proved; the intermediate-alignment identity is only stated.
- **This is not a Clay Millennium Navier–Stokes proof**, and it is not a
  regularity theorem for 3D Navier–Stokes. Large-data global regularity
  remains open.
- The identities in the note are pointwise and algebraic. They do **not**
  imply integrability of \(\|S\|_{L^\infty}\) in time, and they do **not**
  prove Hypothesis B,
  \[
  \int_0^T \|S(t)\|_{L^\infty}\,dt < \infty,
  \]
  for arbitrary large smooth data. The supercritical gap between the
  energy inequality and the Beale–Kato–Majda criterion remains open.
- **A kernel check is not a geometric, analytic, or physical proof.** A
  successful `lake build` only means that the Lean file elaborates and
  that any completed proofs were accepted by the kernel.
- The paper’s discussion of Hölder conditions on the vorticity direction,
  Constantin–Fefferman desingularization, the angular-dispersion
  functional \(\mathcal{D}_{\boldsymbol{\xi}}\), and classical geometric
  criteria (Neustupa–Penel, Miller) is **not formalized** in Lean.
- Mathlib’s `IsHermitian.eigenvalues` are indexed by `Fin 3` after a
  cardinality reindexing; the Lean statement of
  `intermediate_representation` uses index `1` in the role of the paper’s
  intermediate eigenvalue \(\lambda_2\). The algebraic rearrangement does
  not require the ordering \(\lambda_1\le\lambda_2\le\lambda_3\), and Lean
  does not prove that indexing is the ordered triple used in the
  geometric interpretation.

## What Lean actually proves

In `StrainEigenvalue.lean`:

1. `eigenvalues_sum_zero` (proved): for a real `StrainTensor` (a
   symmetric \(3\times 3\) matrix with vanishing trace), the sum of the
   three eigenvalues of the associated Hermitian matrix is zero. This is
   the standard trace–eigenvalue identity plus `trace_zero`.
2. `StrainTensor.isHermitian` (proved; compile adaptation, see below): on \(\mathbb{R}\),
   a symmetric matrix is Hermitian, so the Mathlib spectral API applies.

## What uses sorry or remains a hypothesis

- `intermediate_representation` is **stated and unproved** (`sorry`).
  The intended argument is the algebraic rearrangement
  \(\xi_1^2 = 1-\xi_0^2-\xi_2^2\) written in the paper’s proposition, and
  in the Lean comment.
- The same theorem passes `∑ i, (ξ i)^2 = 1` to `stretching`, which
  expects `‖ξ‖ = 1`, by `by sorry`. That identification of the Euclidean
  squared-sum with the `Pi`/`ℓ²` norm is also unproved.
- Sorry count in the committed skeleton: **2**.

## Compile adaptations (no change to mathematical meaning)

The skeleton was originally written with `Matrix.IsHermitian.of_isSymm`
and without an import of the spectral file. Against the Mathlib pin used
in this repository (`v4.30.0-rc1`, commit
`0c154d67103f74be3a0f2c509f72ccbf5be9f2a7`, matching
`frohmanian-metriplectic-ns`):

1. Added `import Mathlib.Analysis.Matrix.Spectrum`, which is where
   `IsHermitian.eigenvalues` and `IsHermitian.trace_eq_sum_eigenvalues`
   live. The original imports did not expose those declarations.
2. Replaced `Matrix.IsHermitian.of_isSymm` (not present at this pin; it
   appears on later Mathlib as `isHermitian_iff_isSymm`) by a short lemma
   `isHermitian` that uses `IsHermitian.ext` and `star_trivial` on
   \(\mathbb{R}\). The statements of `eigenvalues` and
   `eigenvalues_sum_zero` are unchanged.
3. `lakefile.toml` originally started with a Lean-style `--` comment for
   the author header. Lake's TOML parser rejected it (`unexpected 'A';
   expected '='`). The header is now a TOML `#` comment. No package or
   pin change.
4. The compile adaptation lemma was originally named `isHermitian`. Lean
   field notation `S.isHermitian` looks up `StrainTensor.isHermitian`, so
   the CI run after the lakefile fix
   ([42919197798](https://github.com/BenFrohman/frohmanian-strain-eigenvalue/actions/runs/42919197798))
   failed with “Invalid field `isHermitian`” on the projections in
   `eigenvalues` and `eigenvalues_sum_zero`, and the trace-zero goal was
   left unsolved. The lemma was renamed to `StrainTensor.isHermitian`.
   The proof body of the conversion and the *statements* of
   `eigenvalues` and `eigenvalues_sum_zero` are unchanged.
5. After that rename, CI
   ([42919676638](https://github.com/BenFrohman/frohmanian-strain-eigenvalue/actions/runs/42919676638))
   failed because `rw [← h]` could not match Mathlib’s
   `trace = ∑ i, ↑(eigenvalues i)` against the goal
   `∑ i, eigenvalues S i = 0`. On `𝕜 = ℝ` the `↑` is a redundant
   coercion. The proof now unfolds `eigenvalues`, identifies the
   coercion, and then applies `trace_zero`. The theorem statement is
   unchanged.

No other Lean wording was changed. The two `sorry` tokens were left in
place.

## Reproducibility

- Toolchain: Lean 4.30.0-rc1, Mathlib `v4.30.0-rc1`
  (`0c154d67103f74be3a0f2c509f72ccbf5be9f2a7`), pinned in `lean-toolchain`
  and `lake-manifest.json` to the same versions as
  `frohmanian-metriplectic-ns`.
- One-command rebuild: `lake exe cache get && lake build`
- Kernel / sorry report: `./scripts/kernel_check.sh` after a successful
  build (`#print axioms` for the main theorems; sorry tokens are counted
  and reported; they fail the job only if the file contains none, in
  which case zero sorry is enforced). `admit`, `native_decide`, and new
  `axiom` declarations still fail the job.
- The committed PDF under `paper/` is the pre-existing compilation of the
  same `.tex` source, produced 9 November 2026, 6:59 AM CT
  (America/Chicago). `pdflatex` was not available on the machine that
  created this repository, so the PDF was not rebuilt here. The source
  uses `\date{\today}`.
- Commit SHA: recorded on GitHub after the initial push; rebuilds should
  name that commit.

## Related repositories

- [frohmanian-metriplectic-ns](https://github.com/BenFrohman/frohmanian-metriplectic-ns)
- [frohmanian-tether-conditional-regularity](https://github.com/BenFrohman/frohmanian-tether-conditional-regularity)
- [frohmanian-tether-sdiff](https://github.com/BenFrohman/frohmanian-tether-sdiff)
- [two-point-strain-coercivity](https://github.com/BenFrohman/two-point-strain-coercivity)
- [two-point-strain-direction-pairing-2026-11](https://github.com/BenFrohman/two-point-strain-direction-pairing-2026-11)

## License

- Code: Apache License 2.0 (`LICENSE`).
- Paper (LaTeX and PDF): CC BY 4.0 (`LICENSE-paper`).
