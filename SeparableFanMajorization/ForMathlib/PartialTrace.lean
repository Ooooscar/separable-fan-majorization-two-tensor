import Mathlib.Analysis.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker

/-!
# The partial trace

We model an operator on the tensor product `𝕜^m ⊗ 𝕜^n` as a matrix indexed by `m × n`
(the standard basis of the tensor product is indexed by pairs of basis vectors), i.e. as
`Matrix (m × n) (m × n) 𝕜`. This is the same indexing convention Mathlib uses for
`Matrix.kroneckerMap`.
-/

open Matrix

variable {m n 𝕜 : Type*} [Fintype m] [Fintype n] [RCLike 𝕜]

/-- Partial trace tracing out the *second* tensor factor: for `M` an operator on
`𝕜^m ⊗ 𝕜^n`, `M.traceRight` is the induced operator on `𝕜^m`. -/
def Matrix.traceRight (M : Matrix (m × n) (m × n) 𝕜) : Matrix m m 𝕜 :=
  Matrix.of fun i j => ∑ k, M (i, k) (j, k)

/-- Partial trace tracing out the *first* tensor factor: for `M` an operator on
`𝕜^m ⊗ 𝕜^n`, `M.traceLeft` is the induced operator on `𝕜^n`. -/
def Matrix.traceLeft (M : Matrix (m × n) (m × n) 𝕜) : Matrix n n 𝕜 :=
  Matrix.of fun i j => ∑ k, M (k, i) (k, j)

omit [Fintype n] in
/-- Partial trace is additive, hence (being also additive in the negation) subtractive. -/
theorem Matrix.traceLeft_sub (M N : Matrix (m × n) (m × n) 𝕜) :
    (M - N).traceLeft = M.traceLeft - N.traceLeft := by
  ext i j
  simp [Matrix.traceLeft, Finset.sum_sub_distrib]

/-- Sanity check: tracing out one factor and then taking the (full) trace of what remains
gives back the trace of the original operator. -/
theorem Matrix.trace_traceRight (M : Matrix (m × n) (m × n) 𝕜) :
    M.traceRight.trace = M.trace := by
  simp [Matrix.traceRight, Matrix.trace, Matrix.diag, Fintype.sum_prod_type]

/-- Sanity check, the `traceLeft` analogue of `Matrix.trace_traceRight`. -/
theorem Matrix.trace_traceLeft (M : Matrix (m × n) (m × n) 𝕜) :
    M.traceLeft.trace = M.trace := by
  simp [Matrix.traceLeft, Matrix.trace, Matrix.diag, Fintype.sum_prod_type_right]

omit [Fintype n] in
/-- Partial trace commutes with the conjugate transpose. -/
theorem Matrix.traceLeft_conjTranspose (M : Matrix (m × n) (m × n) 𝕜) :
    (Mᴴ).traceLeft = (M.traceLeft)ᴴ := by
  ext i j
  simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.conjTranspose_apply, star_sum]

omit [Fintype n] in
/-- Tracing out one factor of a Hermitian operator leaves a Hermitian operator on the other. -/
theorem Matrix.IsHermitian.traceLeft {M : Matrix (m × n) (m × n) 𝕜} (hM : M.IsHermitian) :
    M.traceLeft.IsHermitian :=
  (Matrix.traceLeft_conjTranspose M).symm.trans (congrArg Matrix.traceLeft hM.eq)

open scoped Kronecker

variable [DecidableEq m]

/-- The *representer property*: partial trace is "adjoint" to tensoring with the identity
on the traced-out factor. Specializes to `Matrix.trace_traceLeft` when `B = 1`. -/
theorem Matrix.trace_mul_traceLeft (M : Matrix (m × n) (m × n) 𝕜) (B : Matrix n n 𝕜) :
    (M.traceLeft * B).trace = (M * ((1 : Matrix m m 𝕜) ⊗ₖ B)).trace := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Matrix.traceLeft, Matrix.of_apply,
    kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type, Finset.sum_mul]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul]
  rw [show (∑ a : m, ∑ i : n, ∑ b : m, ∑ j : n,
        if b = a then M (a, i) (b, j) * (1 * B j i) else 0)
      = ∑ a : m, ∑ i : n, ∑ j : n, ∑ b : m,
        if b = a then M (a, i) (b, j) * (1 * B j i) else 0 from
    Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, one_mul]
  rw [show (∑ a : m, ∑ i : n, ∑ j : n, M (a, i) (a, j) * B j i)
      = ∑ i : n, ∑ a : m, ∑ j : n, M (a, i) (a, j) * B j i from
    Finset.sum_comm]
  rw [show (∑ i : n, ∑ a : m, ∑ j : n, M (a, i) (a, j) * B j i)
      = ∑ i : n, ∑ j : n, ∑ a : m, M (a, i) (a, j) * B j i from
    Finset.sum_congr rfl fun i _ => Finset.sum_comm]

variable [DecidableEq n]

omit [DecidableEq m] in
/-- Partial trace commutes past operators that act as the identity on the *kept* factor `n`
(and arbitrarily on the traced-out factor `m`): tensoring `X` with the identity on `n` lets it
be cycled through the trace freely, even though `X ⊗ₖ 1` and `M` need not commute themselves. -/
theorem Matrix.traceLeft_kronecker_one_mul_comm (X : Matrix m m 𝕜) (M : Matrix (m × n) (m × n) 𝕜) :
    ((X ⊗ₖ (1 : Matrix n n 𝕜)) * M).traceLeft = (M * (X ⊗ₖ (1 : Matrix n n 𝕜))).traceLeft := by
  ext i j
  simp only [Matrix.traceLeft, Matrix.of_apply, Matrix.mul_apply, kroneckerMap_apply,
    Matrix.one_apply, Fintype.sum_prod_type]
  simp only [mul_ite, ite_mul, mul_zero, zero_mul, mul_one]
  simp only [Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [show (∑ k : m, ∑ p : m, X k p * M (p, i) (k, j))
      = ∑ k : m, ∑ p : m, M (p, i) (k, j) * X k p from
    Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun p _ => mul_comm _ _]
  exact Finset.sum_comm

omit [Fintype n] [DecidableEq m] in
/-- Tracing out the first factor of `X ⊗ 1` just leaves `(Tr X) • 1` behind. -/
theorem Matrix.traceLeft_kronecker_one (X : Matrix m m 𝕜) :
    (X ⊗ₖ (1 : Matrix n n 𝕜)).traceLeft = X.trace • (1 : Matrix n n 𝕜) := by
  ext i j
  simp [Matrix.traceLeft, Matrix.trace, Matrix.diag, kroneckerMap_apply, Finset.sum_mul]
