import SeparableFanMajorization.ForMathlib.PartialTrace
import SeparableFanMajorization.ForMathlib.PosSemidef

/-!
# Joint positivity of `Φ(C, A) = Tr₁[C(A ⊗ 1)]`

`Phi C A := Tr₁[C(A ⊗ 1)]` is the matrix on `𝕜^dim2` obtained by "inserting" `A` into the first
tensor factor of `C` and tracing that factor out. Its role is the representer property
`Tr[Φ(C, A) B] = Tr[C(A ⊗ B)]` (`Phi_trace_mul`): it lets a trace of a Kronecker product be
rewritten as a trace of an ordinary matrix product, which is what makes the overlap-bound proofs in
`OverlapBound.lean` tractable (they apply von Neumann's trace inequality to `Φ(Q, A)` and `B`
instead of working with `Q(A ⊗ B)` directly).

Main results:

* `Phi_posSemidef`: `Φ` is jointly positive semidefinite, i.e. `C, A` positive semidefinite implies
  `Φ(C, A)` positive semidefinite.
* `Phi_sub_left`, `Phi_sub_right`: `Φ` is additive (hence subtractive) in each argument.
* `Phi_one_left`: `Φ(1, A) = (Tr A) • 1`.
* `Phi_one_right`: `Φ(C, 1) = Tr₁ C`.
* `Phi_trace_mul`: the representer property, `Tr[Φ(C, A) B] = Tr[C(A ⊗ B)]`.
-/

open Matrix
open scoped Kronecker ComplexOrder

variable {dim1 dim2 𝕜 : Type*} [Fintype dim1] [Fintype dim2] [DecidableEq dim1] [DecidableEq dim2]
  [RCLike 𝕜]

omit [DecidableEq dim1] in
/-- `Φ(C, A) := Tr₁[C (A ⊗ 1)]`. -/
def Phi (C : Matrix (dim1 × dim2) (dim1 × dim2) 𝕜) (A : Matrix dim1 dim1 𝕜) :
    Matrix dim2 dim2 𝕜 :=
  (C * (A ⊗ₖ (1 : Matrix dim2 dim2 𝕜))).traceLeft

omit [DecidableEq dim1] in
/-- **Lemma**: `Φ` is jointly positive. Assembled from the general partial-trace and
positive-semidefinite facts in `PartialTrace.lean` / `PosSemidef.lean`, via
`Matrix.PosSemidef.of_dotProduct_mulVec_nonneg`. -/
theorem Phi_posSemidef {C : Matrix (dim1 × dim2) (dim1 × dim2) 𝕜} {A : Matrix dim1 dim1 𝕜}
    (hC : C.PosSemidef) (hA : A.PosSemidef) : (Phi C A).PosSemidef := by
  classical
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun u => ?_
  · -- Step 1: Φ(C, A) is Hermitian.
    change (Phi C A)ᴴ = Phi C A
    unfold Phi
    rw [← Matrix.traceLeft_conjTranspose, conjTranspose_mul, conjTranspose_kronecker,
      hA.isHermitian, conjTranspose_one, hC.isHermitian, Matrix.traceLeft_kronecker_one_mul_comm]
  · -- Step 2: the quadratic form is non-negative.
    rw [Matrix.dotProduct_mulVec_eq_trace_mul_vecMulVec]
    unfold Phi
    rw [Matrix.trace_mul_traceLeft, Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, mul_one, one_mul]
    exact hC.trace_mul_nonneg (hA.kronecker (Matrix.posSemidef_vecMulVec_self_star u))

omit [DecidableEq dim1] in
/-- `Φ` is additive (hence subtractive) in its first argument. -/
theorem Phi_sub_left (C C' : Matrix (dim1 × dim2) (dim1 × dim2) 𝕜) (A : Matrix dim1 dim1 𝕜) :
    Phi (C - C') A = Phi C A - Phi C' A := by
  unfold Phi
  rw [sub_mul, Matrix.traceLeft_sub]

omit [DecidableEq dim1] in
/-- `Φ` is additive (hence subtractive) in its second argument. -/
theorem Phi_sub_right (C : Matrix (dim1 × dim2) (dim1 × dim2) 𝕜) (A A' : Matrix dim1 dim1 𝕜) :
    Phi C (A - A') = Phi C A - Phi C A' := by
  have hK : (A - A') ⊗ₖ (1 : Matrix dim2 dim2 𝕜) = A ⊗ₖ (1 : Matrix dim2 dim2 𝕜) - A' ⊗ₖ 1 := by
    ext ⟨i, k⟩ ⟨j, l⟩
    simp [kroneckerMap_apply, sub_mul]
  unfold Phi
  rw [hK, mul_sub, Matrix.traceLeft_sub]

/-- `Φ(1, A) = (Tr A) • 1`. -/
theorem Phi_one_left (A : Matrix dim1 dim1 𝕜) :
    Phi (1 : Matrix (dim1 × dim2) (dim1 × dim2) 𝕜) A = A.trace • (1 : Matrix dim2 dim2 𝕜) := by
  unfold Phi
  rw [one_mul, Matrix.traceLeft_kronecker_one]

/-- `Φ(C, 1) = Tr₁ C`. -/
theorem Phi_one_right (C : Matrix (dim1 × dim2) (dim1 × dim2) 𝕜) :
    Phi C (1 : Matrix dim1 dim1 𝕜) = C.traceLeft := by
  unfold Phi
  rw [Matrix.one_kronecker_one, mul_one]

omit [DecidableEq dim1] in
/-- The *representer property* for `Φ`: `Tr[Φ(C,A) B] = Tr[C(A ⊗ B)]`. -/
theorem Phi_trace_mul (C : Matrix (dim1 × dim2) (dim1 × dim2) 𝕜) (A : Matrix dim1 dim1 𝕜)
    (B : Matrix dim2 dim2 𝕜) :
    (Phi C A * B).trace = (C * (A ⊗ₖ B)).trace := by
  classical
  unfold Phi
  rw [Matrix.trace_mul_traceLeft, Matrix.mul_assoc, ← Matrix.mul_kronecker_mul, mul_one, one_mul]
