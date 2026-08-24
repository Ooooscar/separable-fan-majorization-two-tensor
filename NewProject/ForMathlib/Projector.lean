import Mathlib.Algebra.Star.StarProjection
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Trace
import Mathlib.LinearAlgebra.Projection
import Mathlib.Analysis.RCLike.Basic

/-!
# The trace of a projector is its rank

For a projector (self-adjoint idempotent, `IsStarProjection`), the trace equals the rank: the
eigenvalues are `0` or `1`, and the trace is the number of `1`s, which is exactly the rank.

Mathlib does not connect `Matrix.rank`/`Matrix.trace` to `IsIdempotentElem`/`IsStarProjection`
directly, but `LinearMap.IsProj.trace` (`Mathlib.LinearAlgebra.Trace`) gives the analogous fact
for endomorphisms of a free module: `trace R M f = (finrank R p : R)` when `f` is the projection
onto `p` (`IsProj p f`), and `IsIdempotentElem.isProj_range` turns idempotency of `f` into
`IsProj (range f) f` (`Mathlib.LinearAlgebra.Projection`). We transport this through
`Matrix.mulVecLin` (whose range's rank is `Matrix.rank` by definition).
-/

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

omit [DecidableEq n] in
theorem IsStarProjection.trace_eq_rank {P : Matrix n n 𝕜} (hP : IsStarProjection P) :
    P.trace = (P.rank : 𝕜) := by
  classical
  have hidem : IsIdempotentElem P.mulVecLin := by
    change P.mulVecLin ∘ₗ P.mulVecLin = P.mulVecLin
    rw [← Matrix.mulVecLin_mul, hP.isIdempotentElem]
  unfold Matrix.rank
  rw [← Matrix.trace_toLin'_eq, Matrix.toLin'_apply']
  exact (LinearMap.IsIdempotentElem.isProj_range P.mulVecLin hidem).trace
