import Mathlib.Analysis.Matrix.Order
import Mathlib.Algebra.Star.StarProjection

/-!
# General facts about positive semidefinite matrices

Facts about `Matrix.PosSemidef` on a single (non-tensor) space, and the trace/quadratic-form
identities used to establish it; not specific to eigenvalues or to the bipartite/tensor-product
setting.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

omit [DecidableEq n] in
/-- The trace of a product of two positive semidefinite matrices is non-negative.

Proved by writing `B = Cᴴ * C` (`CStarAlgebra.nonneg_iff_eq_star_mul_self`) and cycling the
trace to reduce to `Matrix.PosSemidef.mul_mul_conjTranspose_same`; equivalently, this is
`Tr[AB] = Tr[CACᴴ] ≥ 0`. -/
theorem Matrix.PosSemidef.trace_mul_nonneg {A B : Matrix n n 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) : 0 ≤ (A * B).trace := by
  classical
  obtain ⟨C, rfl⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.mp hB.nonneg
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc, star_eq_conjTranspose]
  exact (hA.mul_mul_conjTranspose_same C).trace_nonneg

omit [DecidableEq n] in
/-- The quadratic form `uᴴ N u` as a trace against the rank-one operator `u uᴴ`.

This needs no positivity at all: it is the `a := u`, `b := star u` case of the general identity
`(N * vecMulVec a b).trace = b ⬝ᵥ (N *ᵥ a)`, which itself follows immediately from
`Matrix.mul_vecMulVec` (`N * vecMulVec a b = vecMulVec (N *ᵥ a) b`) and `Matrix.trace_vecMulVec`
(`(vecMulVec a b).trace = a ⬝ᵥ b`). It earns its keep here because this is exactly the shape
needed to convert "`⟨u, N u⟩ ≥ 0` for all `u`" into "`Tr[N D] ≥ 0` for the PSD `D = u uᴴ`". -/
theorem Matrix.dotProduct_mulVec_eq_trace_mul_vecMulVec (N : Matrix n n 𝕜) (u : n → 𝕜) :
    star u ⬝ᵥ (N *ᵥ u) = (N * vecMulVec u (star u)).trace := by
  rw [Matrix.mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_comm]

omit [DecidableEq n] in
/-- A projector (self-adjoint idempotent, `IsStarProjection`) is positive semidefinite: its
eigenvalues are `0` or `1`. Follows from `IsStarProjection.nonneg`, which holds in any
star-ordered ring; here the Loewner order (`Mathlib.Analysis.Matrix.Order`, scoped `MatrixOrder`)
identifies `0 ≤ P` with `P.PosSemidef`. -/
theorem IsStarProjection.posSemidef {P : Matrix n n 𝕜} (hP : IsStarProjection P) :
    P.PosSemidef :=
  Matrix.nonneg_iff_posSemidef.mp hP.nonneg
