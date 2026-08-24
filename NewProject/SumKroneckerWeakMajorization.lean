import NewProject.ForMathlib.SingularValue
import NewProject.SumKroneckerMajorization

/-!
# Weak majorization for sums of Kronecker products

**General theorem**: for finite families `A⁽¹⁾, …, A⁽ᵐ⁾` of (not necessarily Hermitian or positive
semidefinite) operators on `dim1` and `B⁽¹⁾, …, B⁽ᵐ⁾` on `dim2`,
```
σ(∑ᵢ A⁽ⁱ⁾ ⊗ B⁽ⁱ⁾) ≺w ∑ᵢ σ(A⁽ⁱ⁾) ⊗ σ(B⁽ⁱ⁾)
```
where `σ` (`Matrix.singularValues`, `SingularValue.lean`) denotes singular values sorted in
decreasing order. If every `A⁽ⁱ⁾`, `B⁽ⁱ⁾` is positive semidefinite, singular values coincide with
eigenvalues and weak majorization strengthens to majorization: this is the special case proved as
`SumKroneckerMajorization.lean`'s `majorized_sum_kronecker_sortedDiagonal`.

The right-hand side `∑ᵢ σ(A⁽ⁱ⁾) ⊗ σ(B⁽ⁱ⁾)` is realized as a vector of eigenvalues, mirroring
`SumKroneckerMajorization.lean`'s `sortedDiagonal` device: `Matrix.singularValueDiagonal A⁽ⁱ⁾` is
the diagonal matrix of `A⁽ⁱ⁾`'s singular values, `∑ᵢ singularValueDiagonal A⁽ⁱ⁾ ⊗ₖ
singularValueDiagonal B⁽ⁱ⁾` is positive semidefinite (`posSemidef_sum_kronecker_singularValueDiagonal`,
a sum of Kronecker products of diagonal matrices with nonnegative entries), and its
`dim1 × dim2`-indexed eigenvalues (`Matrix.IsHermitian.eigenvalues₀`) are exactly what
`∑ᵢ σ(A⁽ⁱ⁾) ⊗ σ(B⁽ⁱ⁾)` means as a vector.

* `Matrix.singularValueDiagonal`/`Matrix.posSemidef_singularValueDiagonal`: `σ(A)` realized as a
  diagonal matrix, and its positive semidefiniteness.
* `Matrix.posSemidef_sum_kronecker_singularValueDiagonal`: `∑ᵢ σ(A⁽ⁱ⁾) ⊗ σ(B⁽ⁱ⁾)` is positive
  semidefinite, so its eigenvalues make sense.
* `weakMajorized_sum_kronecker_singularValueDiagonal`: the weak majorization theorem itself.
-/

open Matrix
open scoped Kronecker ComplexOrder MatrixOrder Majorization

variable {dim1 dim2 𝕜 : Type*} [Fintype dim1] [Fintype dim2] [DecidableEq dim1] [DecidableEq dim2]
  [RCLike 𝕜]

/-- The diagonal matrix of a square matrix `A`'s singular values: `σ(A)` realized as a matrix, so
that its Kronecker product with another such diagonal matrix makes sense. -/
noncomputable def Matrix.singularValueDiagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι 𝕜) : Matrix ι ι 𝕜 :=
  Matrix.diagonal (fun i => (A.singularValues (Fintype.equivFin ι i) : 𝕜))

/-- `singularValueDiagonal A` is positive semidefinite: it is diagonal with `A`'s (nonnegative)
singular values as its entries. -/
theorem Matrix.posSemidef_singularValueDiagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι 𝕜) : A.singularValueDiagonal.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  simp only [Pi.zero_apply]
  exact_mod_cast A.singularValues_nonneg (Fintype.equivFin ι i)

/-- A finite sum of Kronecker products of `singularValueDiagonal`s is positive semidefinite, so its
eigenvalues (`Matrix.IsHermitian.eigenvalues₀`) make sense: this realizes the right-hand side
`∑ᵢ σ(A⁽ⁱ⁾) ⊗ σ(B⁽ⁱ⁾)` of `weakMajorized_sum_kronecker_singularValueDiagonal` below as a vector. -/
theorem Matrix.posSemidef_sum_kronecker_singularValueDiagonal {m : ℕ}
    (A : Fin m → Matrix dim1 dim1 𝕜) (B : Fin m → Matrix dim2 dim2 𝕜) :
    (∑ i, (A i).singularValueDiagonal ⊗ₖ (B i).singularValueDiagonal).PosSemidef :=
  Matrix.posSemidef_sum_kronecker (fun i => Matrix.posSemidef_singularValueDiagonal (A i))
    (fun i => Matrix.posSemidef_singularValueDiagonal (B i))

/-- **General theorem**: for finite families `A⁽¹⁾, …, A⁽ᵐ⁾` of (not necessarily Hermitian or
positive semidefinite) operators on `dim1` and `B⁽¹⁾, …, B⁽ᵐ⁾` on `dim2`, the singular values of
`∑ᵢ A⁽ⁱ⁾ ⊗ B⁽ⁱ⁾` are weakly majorized by `∑ᵢ σ(A⁽ⁱ⁾) ⊗ σ(B⁽ⁱ⁾)`, realized as the eigenvalues of
`∑ᵢ singularValueDiagonal A⁽ⁱ⁾ ⊗ₖ singularValueDiagonal B⁽ⁱ⁾`. Generalizes
`SumKroneckerMajorization.lean`'s `majorized_sum_kronecker_sortedDiagonal` (the positive
semidefinite case, where weak majorization strengthens to majorization since singular values
coincide with eigenvalues there). -/
theorem weakMajorized_sum_kronecker_singularValueDiagonal {m : ℕ}
    (A : Fin m → Matrix dim1 dim1 𝕜) (B : Fin m → Matrix dim2 dim2 𝕜) :
    (∑ i, A i ⊗ₖ B i).singularValues
      ≺w (Matrix.posSemidef_sum_kronecker_singularValueDiagonal A B).isHermitian.eigenvalues₀ := by
  sorry
