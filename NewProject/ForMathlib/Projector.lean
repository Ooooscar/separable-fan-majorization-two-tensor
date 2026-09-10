import NewProject.ForMathlib.PosSemidef
import NewProject.ForMathlib.SortedEigenvectorBasis

/-!
# Basic facts about star projections

For a star projection (self-adjoint idempotent, `IsStarProjection`), the trace equals the rank: the
eigenvalues are `0` or `1`, and the trace is the number of `1`s, which is exactly the rank.

Mathlib does not connect `Matrix.rank`/`Matrix.trace` to `IsIdempotentElem`/`IsStarProjection`
directly, but `LinearMap.IsProj.trace` (`Mathlib.LinearAlgebra.Trace`) gives the analogous fact
for endomorphisms of a free module: `trace R M f = (finrank R p : R)` when `f` is the projection
onto `p` (`IsProj p f`), and `IsIdempotentElem.isProj_range` turns idempotency of `f` into
`IsProj (range f) f` (`Mathlib.LinearAlgebra.Projection`). We transport this through
`Matrix.mulVecLin` (whose range's rank is `Matrix.rank` by definition).

## Main results

* `IsStarProjection.posSemidef`: A projector is positive definite. Follows from
  `IsStarProjection.nonneg`, which holds in any star-ordered ring; here the Loewner order
  (`Mathlib.Analysis.Matrix.Order`, scoped `MatrixOrder`) identifies `0 ≤ P` with `P.PosSemidef`.
* `IsStarProjection.trace_eq_rank`: `P.trace = P.rank` for a star projection `P`.
* `Matrix.isStarProjection_mul_conjTranspose_of_conjTranspose_mul_self_eq_one`: an isometry
  `U : Matrix n (Fin k) 𝕜` (`Uᴴ*U = 1`) makes `U*Uᴴ` a rank-`k` star projection.
* `IsStarProjection.eigenvalues₀_eq_zero_or_one`: a star projection's `eigenvalues₀` are each `0`
  or `1`.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

omit [DecidableEq n] in
/-- A projector matrix is positive semidefinite. -/
theorem IsStarProjection.posSemidef {P : Matrix n n 𝕜} (hP : IsStarProjection P) :
    P.PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp hP.nonneg

omit [DecidableEq n] in
/-- A projector matrix's trace is equal to its rank. -/
theorem IsStarProjection.trace_eq_rank {P : Matrix n n 𝕜} (hP : IsStarProjection P) :
    P.trace = (P.rank : 𝕜) := by
  classical
  have hidem : IsIdempotentElem P.mulVecLin := by
    change P.mulVecLin ∘ₗ P.mulVecLin = P.mulVecLin
    rw [← Matrix.mulVecLin_mul, hP.isIdempotentElem]
  unfold Matrix.rank
  rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_apply']
  exact (LinearMap.IsIdempotentElem.isProj_range P.mulVecLin hidem).trace

omit [DecidableEq n] in
/-- If `U : Matrix n (Fin k) 𝕜` has orthonormal columns (`Uᴴ * U = 1`), `U * Uᴴ` is a star
projection of rank exactly `k`: the orthogonal projector onto `U`'s (`k`-dimensional) column space.
Needed to feed `KyFanMaxPrinciple.lean`'s general Ky Fan maximum principle
(`Matrix.IsHermitian.trace_mul_le_topSum_of_isStarProjection`) `U * Uᴴ` as its rank-`k`
star-projection `Q`, and (applied to the isometry pair's second leg) `Matrix.kyFanNorm_add_le`'s
roadmap (`KyFanNorm.lean`). Lives here rather than in `KyFanCauchySchwarz.lean`, where it was
originally stated, since `KyFanNorm.lean` needs it too and cannot import that file (which itself
imports `KyFanNorm.lean`).

Proof: idempotency and self-adjointness of `U * Uᴴ` are immediate from `Uᴴ * U = 1`; the rank
is `Matrix.rank_self_mul_conjTranspose` (`(U*Uᴴ).rank = U.rank`) combined with
`Matrix.rank_conjTranspose_mul_self`/`Matrix.rank_one` (`U.rank = (Uᴴ*U).rank = (1 :
Matrix (Fin k) (Fin k) 𝕜).rank = k`). -/
theorem Matrix.isStarProjection_mul_conjTranspose_of_conjTranspose_mul_self_eq_one
    {k : ℕ} {U : Matrix n (Fin k) 𝕜} (hUU : Uᴴ * U = 1) :
    IsStarProjection (U * Uᴴ) ∧ (U * Uᴴ).rank = k := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · change U * Uᴴ * (U * Uᴴ) = U * Uᴴ
    rw [show U * Uᴴ * (U * Uᴴ) = U * (Uᴴ * U) * Uᴴ from by simp only [Matrix.mul_assoc], hUU,
      Matrix.mul_one]
  · change star (U * Uᴴ) = U * Uᴴ
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  · rw [Matrix.rank_self_mul_conjTranspose, ← Matrix.rank_conjTranspose_mul_self U, hUU,
      Matrix.rank_one, Fintype.card_fin]

/-- **A star projection's eigenvalues are `0` or `1`.** For `Q` a star projection
(`IsStarProjection`, i.e. self-adjoint and idempotent), every entry of the (decreasing-sorted)
`eigenvalues₀` of `Q` (read via `hQ.posSemidef.isHermitian`, `ForMathlib/PosSemidef.lean`) is `0` or
`1`. Needed by `Matrix.kyFanNorm_add_le`'s roadmap (`KyFanNorm.lean`): a rank-`k` star projection's
`eigenvalues₀`/singular values are exactly `k` ones followed by zeros, which is what collapses the
general von Neumann trace inequality's `∑ᵢ σᵢ(A)σᵢ(W)` sum down to `A.kyFanNorm k` there.

For `hQH := hQ.posSemidef.isHermitian`, `u := hQH.sortedEigenvectorBasis i` is a unit eigenvector
(`Matrix.IsHermitian.orthonormal_sortedEigenvectorBasis`) for `lam := hQH.eigenvalues₀ i`
(`Matrix.IsHermitian.mulVec_sortedEigenvectorBasis`). Working in `Matrix.toLpLin 2 2 Q`,
idempotency of `Q` gives two computations of `Q (Q u)`: directly `lam² • u`, and via
`hQ.isIdempotentElem` also `lam • u`. Cancelling the nonzero `u` gives `lam * (lam - 1) = 0` in `𝕜`,
which is pulled back to `ℝ` via `RCLike.ofReal` injectivity. -/
theorem IsStarProjection.eigenvalues₀_eq_zero_or_one {Q : Matrix n n 𝕜} (hQ : IsStarProjection Q)
    (i : Fin (Fintype.card n)) :
    hQ.posSemidef.isHermitian.eigenvalues₀ i = 0 ∨
    hQ.posSemidef.isHermitian.eigenvalues₀ i = 1 := by
  set hQH := hQ.posSemidef.isHermitian
  set u := hQH.sortedEigenvectorBasis i
  set lam := hQH.eigenvalues₀ i with hlam_def
  have hune : u ≠ 0 := by
    have hnorm : ‖u‖ = 1 := hQH.orthonormal_sortedEigenvectorBasis.1 i
    intro h
    rw [h, norm_zero] at hnorm
    exact one_ne_zero hnorm.symm
  have hfu : Matrix.toLpLin 2 2 Q u = (lam : 𝕜) • u := by
    rw [Matrix.toLpLin_apply, hQH.mulVec_sortedEigenvectorBasis]; rfl
  have hffu : Matrix.toLpLin 2 2 Q (Matrix.toLpLin 2 2 Q u) = ((lam : 𝕜) * lam) • u := by
    rw [hfu, map_smul, hfu, smul_smul]
  have hcomp : Matrix.toLpLin 2 2 Q (Matrix.toLpLin 2 2 Q u) = (lam : 𝕜) • u := by
    rw [← LinearMap.comp_apply, ← Matrix.toLpLin_mul_same, hQ.isIdempotentElem]; exact hfu
  have hzero : (((lam : 𝕜) * lam) - lam) • u = 0 := by
    rw [sub_smul, hffu.symm.trans hcomp, sub_self]
  have hlameq : (lam : 𝕜) * lam - lam = 0 :=
    (eq_zero_or_eq_zero_of_smul_eq_zero hzero).resolve_right hune
  have hlamsq : (lam : 𝕜) * (lam - 1) = 0 := by rw [mul_sub, mul_one]; exact hlameq
  rcases mul_eq_zero.mp hlamsq with h | h
  · left; exact_mod_cast h
  · right; exact_mod_cast sub_eq_zero.mp h
