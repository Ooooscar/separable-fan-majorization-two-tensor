# newProject

A Lean 4 / Mathlib formalization of a chain of matrix-analysis results — partial traces,
positive-semidefiniteness, spectral decomposition, majorization, Weyl monotonicity, and Von
Neumann's trace inequality — building up to bounds on the overlap `Tr[Q(A ⊗ B)]` of a projector
`Q` with a product operator `A ⊗ B`. `NewProject.lean` imports every file below; that's the
project's entry point.

## Project structure

The project is split into two parts:

* [`NewProject/ForMathlib/`](NewProject/ForMathlib) — general-purpose matrix-analysis results (not
  specific to the overlap-bound goal below) that are, in the author's judgment, reasonable
  candidates for upstreaming to Mathlib itself.
* `NewProject/*.lean` (this project's own root) — the overlap-bound-specific chain of results built
  on top of `ForMathlib/`, culminating in the final theorem.

Files are listed in rough dependency order (later files import earlier ones).

### `NewProject/ForMathlib/`

| File | Purpose | Status |
| --- | --- | --- |
| [`Majorization.lean`](NewProject/ForMathlib/Majorization.lean) | Defines majorization (`≺`) and weak majorization (`≺w`) for tuples `Fin n → ℝ`, since it's not in Mathlib. `decreasingSort`, `topSum`, and `sum_mul_le_topSum` ("top-`k` beats any `[0,1]`-weighted average of the same total mass"), needed by `SumKroneckerMajorization.lean`'s `trace_mul_le_topSum_sortedDiagonal`. | complete |
| [`PartialTrace.lean`](NewProject/ForMathlib/PartialTrace.lean) | Partial trace `traceLeft`/`traceRight` of an operator on `𝕜^m ⊗ 𝕜^n` (indexed as `Matrix (m × n) (m × n) 𝕜`, matching `Matrix.kroneckerMap`'s convention). | complete |
| [`PosSemidef.lean`](NewProject/ForMathlib/PosSemidef.lean) | General facts about `Matrix.PosSemidef`: trace of a product of two PSD matrices is nonnegative, the quadratic-form/trace identity `star u ⬝ᵥ (N *ᵥ u) = Tr[N (u uᴴ)]`, and that a projector (`IsStarProjection`) is PSD. | complete |
| [`Projector.lean`](NewProject/ForMathlib/Projector.lean) | `IsStarProjection.trace_eq_rank`: the trace of a projector equals its rank. | complete |
| [`EigenvalueMonotonicity.lean`](NewProject/ForMathlib/EigenvalueMonotonicity.lean) | Weyl's monotonicity theorem: `B ≤ A` (Loewner order) implies `B`'s eigenvalues are weakly majorized by `A`'s (weak form), and termwise `≤` (pointwise form, not in Mathlib either). Proved via the standard Courant-Fischer subspace-intersection argument, specialized to one index. | complete |
| [`SpectralDecomposition.lean`](NewProject/ForMathlib/SpectralDecomposition.lean) | Derives the "outer product" spectral form `A = ∑ₖ αₖ (uₖ uₖ*)` (Mathlib's `spectral_theorem` only gives the unitary-conjugation form), the telescoping/Abel-summation identity `A = ∑ⱼ (λⱼ(A) - λⱼ₊₁(A)) • P_[j]` used by `OverlapBound.lean`, and the rank-`k` spectral truncation projector `topProjector`/its "self" Ky Fan equality `Tr[topProjector k · A] = topSum (eigenvalues₀) k` used by `SumKroneckerMajorization.lean`. | complete |
| [`TraceInequality.lean`](NewProject/ForMathlib/TraceInequality.lean) | Von Neumann's trace inequality: `Tr[AB] ≤ ∑ᵢ λᵢ(A) λᵢ(B)` for Hermitian `A, B`, eigenvalues sorted decreasing. Not in Mathlib. | complete |
| [`SingularValue.lean`](NewProject/ForMathlib/SingularValue.lean) | `Matrix.singularValues`: singular values of a square matrix (not necessarily Hermitian/PSD), sorted decreasing, as square roots of `(Aᴴ A)`'s eigenvalues — the `Fin (Fintype.card ι) → ℝ` shape `Majorization.lean`'s `≺w` needs, absent from Mathlib. | complete |
| [`SingularValueDecomposition.lean`](NewProject/ForMathlib/SingularValueDecomposition.lean) | The full SVD factorization `A = U * Σ * Vᴴ` of a square matrix, absent from Mathlib (which only has the singular-value sequence). Roadmap + low-risk lemmas landed; the geometric core (orthonormal-basis extension) is `sorry`'d. | roadmap / partial |
| [`KyFanNorm.lean`](NewProject/ForMathlib/KyFanNorm.lean) | `Matrix.kyFanNorm k A`: the sum of the `k` largest singular values of `A`, the standard first family of examples of a unitarily invariant norm. | complete |
| [`UnitarilyInvariantNorm.lean`](NewProject/ForMathlib/UnitarilyInvariantNorm.lean) | `Matrix.IsUnitarilyInvariantNorm`: the general notion of a norm on square matrices invariant under two-sided unitary conjugation, following Bhatia's textbook definition. | complete |

### `NewProject/` (project-specific)

| File | Purpose | Status |
| --- | --- | --- |
| [`BilinearPositivity.lean`](NewProject/BilinearPositivity.lean) | `Φ(C, A) := Tr₁[C(A ⊗ 1)]` is jointly positive: `C, A` PSD implies `Φ(C, A)` PSD. | complete |
| [`OverlapBound.lean`](NewProject/OverlapBound.lean) | Bounds `Tr[Q(A ⊗ B)]` for a projector `Q`: the special case `A = P` a rank-`r` projector (`trace_mul_kronecker_le_sum_min`), and the general PSD-`A` case (`trace_mul_kronecker_le_sum_min_diff`). | complete |
| [`SumKroneckerMajorization.lean`](NewProject/SumKroneckerMajorization.lean) | **PSD case**: `λ(∑ᵢ A⁽ⁱ⁾ ⊗ B⁽ⁱ⁾) ≺ λ(∑ᵢ A⁽ⁱ⁾↓ ⊗ B⁽ⁱ⁾↓)` for PSD families `A⁽ⁱ⁾`, `B⁽ⁱ⁾`, where `X↓` is the diagonal matrix of `X`'s sorted eigenvalues. Built from `Matrix.IsHermitian.topSum_eigenvalues₀_diagonal` (`topSum` of a diagonal Hermitian's `eigenvalues₀` is basis/enumeration-independent) and `trace_mul_le_topSum_sortedDiagonal` (assembles the weak-majorization bound `Tr[Q·∑ᵢA⁽ⁱ⁾⊗B⁽ⁱ⁾] ≤ topSum` from `OverlapBound.lean`'s per-family bound). | complete |
| [`SumKroneckerWeakMajorization.lean`](NewProject/SumKroneckerWeakMajorization.lean) | **Final theorem**: `σ(∑ᵢ A⁽ⁱ⁾ ⊗ B⁽ⁱ⁾) ≺w ∑ᵢ σ(A⁽ⁱ⁾)⊗σ(B⁽ⁱ⁾)` for general (not necessarily Hermitian/PSD) families `A⁽ⁱ⁾`, `B⁽ⁱ⁾` — generalizes `SumKroneckerMajorization.lean`'s PSD case, where singular values become eigenvalues and weak majorization strengthens to majorization. Statement only (`sorry`). | statement only |