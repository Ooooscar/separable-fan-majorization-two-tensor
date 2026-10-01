import SeparableFanMajorization.ForMathlib.PolarDecomposition
import SeparableFanMajorization.ForMathlib.KyFanCauchySchwarz
import SeparableFanMajorization.SumKroneckerMajorization

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
singularValueDiagonal B⁽ⁱ⁾` is positive semidefinite
(`posSemidef_sum_kronecker_singularValueDiagonal`, a sum of Kronecker products of diagonal
matrices with nonnegative entries), and its
`dim1 × dim2`-indexed eigenvalues (`Matrix.IsHermitian.eigenvalues₀`) are exactly what
`∑ᵢ σ(A⁽ⁱ⁾) ⊗ σ(B⁽ⁱ⁾)` means as a vector.

* `Matrix.singularValueDiagonal`/`Matrix.posSemidef_singularValueDiagonal`: `σ(A)` realized as a
  diagonal matrix, and its positive semidefiniteness.
* `Matrix.posSemidef_sum_kronecker_singularValueDiagonal`: `∑ᵢ σ(A⁽ⁱ⁾) ⊗ σ(B⁽ⁱ⁾)` is positive
  semidefinite, so its eigenvalues make sense.
* `weakMajorized_sum_kronecker_singularValueDiagonal`: the weak majorization theorem itself.

## Roadmap for proving `weakMajorized_sum_kronecker_singularValueDiagonal`

Follows the argument of [WZ26], which reduces the general case to the PSD case
(`majorized_sum_kronecker_sortedDiagonal`, already proved in `SumKroneckerMajorization.lean`) via
the Cauchy–Schwarz inequality for unitarily invariant norms (Bhatia, *Matrix Analysis*, `IX.5`).
Write `M l := A l ⊗ₖ B l`:

1. **PSD matrix square root**, `Matrix.PosSemidef.sqrt` (`ForMathlib/MatrixSqrt.lean`), built from
   the continuous functional calculus for Hermitian matrices
   (`Mathlib.Analysis.Matrix.HermitianFunctionalCalculus`, `Matrix.IsHermitian.cfc`), with
   `posSemidef_sqrt`/`sqrt_mul_sqrt`/`sqrt_unique`.
2. **Kronecker-multiplicativity of sqrt**: `Matrix.PosSemidef.sqrt_kronecker`
   (`ForMathlib/MatrixSqrt.lean`), `(A ⊗ₖ B).sqrt = A.sqrt ⊗ₖ B.sqrt` for PSD `A`, `B`, via
   `sqrt_unique` applied to `A.sqrt ⊗ₖ B.sqrt` (PSD by `Matrix.PosSemidef.kronecker`, squares to
   `A ⊗ₖ B` by `Matrix.mul_kronecker_mul`).
3. **Absolute value** `Matrix.abs M := (Mᴴ * M).sqrt` (`ForMathlib/MatrixAbs.lean`) for general
   square `M` (not necessarily Hermitian/PSD), with `Matrix.posSemidef_abs` (from step 1) and
   `Matrix.abs_kronecker` (`|A ⊗ₖ B| = |A| ⊗ₖ |B|`, from steps 1–2 plus
   `Matrix.conjTranspose_kronecker`/`Matrix.mul_kronecker_mul`).
4. **`|M|`'s eigenvalues are `σ(M)`**: `Matrix.abs_eigenvalues₀_eq_singularValues`
   (`ForMathlib/MatrixAbs.lean`).
5. **`σ(Mᴴ) = σ(M)`**: `Matrix.singularValues_conjTranspose` (`ForMathlib/MatrixAbs.lean`).
   *Cheap*, no polar decomposition needed — `Mᴴ * M` and `M * Mᴴ` are square same-size matrices, so
   they share a characteristic polynomial via `Matrix.charpoly_mul_comm` (already used for exactly
   this purpose in `Matrix.singularValues_unitary_conj`, `SingularValue.lean`), hence the same
   `eigenvalues₀`, hence the same square roots.
6. **Polar decomposition**: `Matrix.exists_polarDecomposition`
   (`ForMathlib/PolarDecomposition.lean`), `∃ U : unitaryGroup, M = U * |M|`. Derived from
   `SingularValueDecomposition.lean`'s full SVD factorization; see that file's module doc for the
   "extend a partial orthonormal family to a full orthonormal basis" geometric argument this rests
   on.
7. **`|Mᴴ| = U * |M| * Uᴴ`**: `Matrix.abs_conjTranspose_eq_of_polarDecomposition`
   (`ForMathlib/PolarDecomposition.lean`), given a polar decomposition from step 6.
8. **The block operators `L`, `R`**: `exists_LR_kronecker_identities` below.
   `∃ L R : Matrix ((dim1 × dim2) × Fin m) (dim1 × dim2) 𝕜`, the vertical stacks of blocks
   `|M l|.sqrt * (U l)ᴴ` resp. `|M l|.sqrt` over `l : Fin m` (`U l` from step 6 applied to `M l`),
   satisfying `Lᴴ * R = ∑ l, M l`, `Lᴴ * L = ∑ l, |(M l)ᴴ|`, `Rᴴ * R = ∑ l, |M l|`. These identities
   hold by expanding the block sum; cross terms `l ≠ l'` cancel since the `Fin m` blocks are
   orthogonal. Routine but somewhat long index bookkeeping, hence stated as an existence lemma
   rather than exposing `L`, `R` as named `def`s.
9. **Cauchy–Schwarz for Ky Fan norms**: `Matrix.kyFanNorm_conjTranspose_mul_le`
   (`ForMathlib/KyFanCauchySchwarz.lean`) — the hardest and only genuinely new piece of matrix
   analysis needed, not derivable from anything above. Reduces via an AM-GM scaling trick to the
   block-PSD Ky Fan bound `Matrix.kyFanNorm_le_max_of_fromBlocks_posSemidef`, which in turn chains
   the Douglas factorization lemma (`ForMathlib/ContractionFactorization.lean`) with the sharper
   sandwiched-contraction Ky Fan bound
   (`Matrix.kyFanNorm_sqrt_mul_contraction_mul_sqrt_le_max`, `ForMathlib/KyFanCauchySchwarz.lean`
   — a form of the Bhatia–Kittaneh inequality). That last lemma rests on
   `Matrix.exists_isometryPair_trace_eq_kyFanNorm` (`ForMathlib/KyFanNorm.lean`); see
   `KyFanCauchySchwarz.lean`'s module doc for details.
10. **Assembly**: for each `k`, apply `majorized_sum_kronecker_sortedDiagonal` (already proved) to
    `∑ l, |A l| ⊗ₖ |B l| = ∑ l, |M l|` (step 3) and to `∑ l, |(A l)ᴴ| ⊗ₖ |(B l)ᴴ| = ∑ l, |(M l)ᴴ|`,
    using step 5 (`σ(Aᴴ) = σ(A)`) to see both bound `(∑ l, |M l|).kyFanNorm k` and
    `(∑ l, |(M l)ᴴ|).kyFanNorm k` by the *same* right-hand side `topSum (∑ l, σ(A l) ⊗ σ(B l)) k`.
    Combine with step 8's identities and step 9's Cauchy–Schwarz to get
    `(∑ l, M l).kyFanNorm k ≤ topSum (∑ l, σ(A l) ⊗ σ(B l)) k` for every `k` — exactly
    `weakMajorized_sum_kronecker_singularValueDiagonal`, since `kyFanNorm k` unfolds to
    `topSum ∘ singularValues` (`KyFanNorm.lean`).

    **Bridging step 10**: `majorized_sum_kronecker_sortedDiagonal` bounds `kyFanNorm` in terms of
    `sortedDiagonal` (built from `Matrix.IsHermitian.eigenvalues`), not `singularValueDiagonal`
    (built from `Fintype.equivFin`) — bridged by
    `sortedDiagonal_abs_weakMajorized_singularValueDiagonal` below (the two turn out to be diagonal
    matrices related by a single fixed permutation, not a genuine rearrangement inequality — see
    its docstring) and combined with the PSD-eigenvalues₀-equals-singularValues bridge
    (`Matrix.PosSemidef.singularValues_eq_eigenvalues₀`, `ForMathlib/MatrixAbs.lean`) into the
    shared assembly step `kyFanNorm_sum_kronecker_abs_le` below, split into
    `eigenvalues₀_posSemidef_sum_kronecker_singularValueDiagonal_congr` and
    `topSum_abs_kronecker_le_of_le_card` so each piece stays small enough for the kernel to check.
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

omit [Fintype dim1] [Fintype dim2] in
/-- Shared computation behind `sortedDiagonal_abs_weakMajorized_singularValueDiagonal` below: a
finite sum of Kronecker products of two families of diagonal matrices (one `dim1`-indexed, one
`dim2`-indexed) is itself diagonal, with entries the corresponding sum of pointwise products
(`Matrix.diagonal_kronecker_diagonal` termwise, then a case split on the resulting
`Matrix.diagonal` index equality). The same pattern also appears in
`SumKroneckerMajorization.lean`'s `majorized_sum_kronecker_sortedDiagonal`; not merged with it here
to avoid touching an already-proved file. -/
private theorem diagonal_sum_kronecker_diagonal {m : ℕ} (f : Fin m → dim1 → ℝ)
    (g : Fin m → dim2 → ℝ) :
    (∑ l, Matrix.diagonal (fun i => (f l i : 𝕜))
        ⊗ₖ Matrix.diagonal (fun j : dim2 => (g l j : 𝕜)) : Matrix (dim1 × dim2) (dim1 × dim2) 𝕜)
      = Matrix.diagonal (fun p : dim1 × dim2 => ((∑ l, f l p.1 * g l p.2 : ℝ) : 𝕜)) := by
  have hterm : ∀ l, (Matrix.diagonal (fun i => (f l i : 𝕜))
      ⊗ₖ Matrix.diagonal (fun j : dim2 => (g l j : 𝕜)) : Matrix (dim1 × dim2) (dim1 × dim2) 𝕜)
      = Matrix.diagonal (fun p : dim1 × dim2 => (f l p.1 : 𝕜) * (g l p.2 : 𝕜)) :=
    fun l => Matrix.diagonal_kronecker_diagonal _ _
  ext p q
  simp only [Matrix.sum_apply, hterm, Matrix.diagonal_apply]
  split_ifs with h
  · rw [RCLike.ofReal_sum]
    exact Finset.sum_congr rfl fun l _ => (RCLike.ofReal_mul _ _).symm
  · simp

/-- **Former "core gap" in step 10 of the roadmap above — turns out not to be a genuine
rearrangement inequality.** The docstring this replaced assumed `sortedDiagonal(|A l|)` sorts each
`l` "independently, by that summand's own eigenvector basis," so comparing it to
`singularValueDiagonal(A l)` (every `l` sorted *consistently*, via the same global
`Fintype.equivFin`) would need a genuine rearrangement-style argument. That assumption is false:
`Matrix.PosSemidef.sortedDiagonal` is built from `Matrix.IsHermitian.eigenvalues`, which
(`Mathlib.Analysis.Matrix.Spectrum`) reindexes `eigenvalues₀ : Fin (Fintype.card ι) → ℝ` along
`Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))` — a bijection depending only on the
index *type* `ι`, **not on the matrix or its eigenvector basis**. So `sortedDiagonal(|A l|)` uses
the *same* fixed bijection for every `l`, just a *different* one than `singularValueDiagonal`'s
`Fintype.equivFin`. Both sides are therefore diagonal matrices (via
`diagonal_sum_kronecker_diagonal` above) whose diagonal-defining functions agree up to
precomposition by a single fixed permutation `σ ×ˢ τ` of `dim1 × dim2` (independent of `l`) — a
pure reindexing identity, not an inequality: their `eigenvalues₀` are literally *equal* (hence
certainly weakly majorize each other), via `Matrix.IsHermitian.topSum_eigenvalues₀_diagonal`
(`SumKroneckerMajorization.lean`) applied to both sides along the same enumeration, plus
`Majorization.topSum_comp_perm` to absorb the permutation. -/
theorem sortedDiagonal_abs_weakMajorized_singularValueDiagonal {m : ℕ}
    (A : Fin m → Matrix dim1 dim1 𝕜) (B : Fin m → Matrix dim2 dim2 𝕜) :
    (Matrix.posSemidef_sum_kronecker
        (fun l => (Matrix.posSemidef_abs (A l)).posSemidef_sortedDiagonal)
        (fun l => (Matrix.posSemidef_abs (B l)).posSemidef_sortedDiagonal)).isHermitian.eigenvalues₀
      ≺w (Matrix.posSemidef_sum_kronecker_singularValueDiagonal A B).isHermitian.eigenvalues₀ := by
  -- The diagonal-defining functions of both sides.
  set dL : dim1 × dim2 → ℝ := fun p =>
    ∑ l, (Matrix.posSemidef_abs (A l)).isHermitian.eigenvalues p.1
      * (Matrix.posSemidef_abs (B l)).isHermitian.eigenvalues p.2 with hdL_def
  set dR : dim1 × dim2 → ℝ := fun p =>
    ∑ l, (A l).singularValues (Fintype.equivFin dim1 p.1)
      * (B l).singularValues (Fintype.equivFin dim2 p.2) with hdR_def
  have hMLdiag : (∑ l, (Matrix.posSemidef_abs (A l)).sortedDiagonal
      ⊗ₖ (Matrix.posSemidef_abs (B l)).sortedDiagonal)
      = Matrix.diagonal (fun p => (dL p : 𝕜)) := by
    rw [hdL_def]
    exact diagonal_sum_kronecker_diagonal
      (fun l => (Matrix.posSemidef_abs (A l)).isHermitian.eigenvalues)
      (fun l => (Matrix.posSemidef_abs (B l)).isHermitian.eigenvalues)
  have hMRdiag : (∑ l, (A l).singularValueDiagonal ⊗ₖ (B l).singularValueDiagonal)
      = Matrix.diagonal (fun p => (dR p : 𝕜)) := by
    rw [hdR_def]
    exact diagonal_sum_kronecker_diagonal
      (fun l (i : dim1) => (A l).singularValues (Fintype.equivFin dim1 i))
      (fun l (j : dim2) => (B l).singularValues (Fintype.equivFin dim2 j))
  -- `Matrix.IsHermitian.eigenvalues` reindexes `eigenvalues₀` via a fixed (matrix-independent)
  -- bijection `dim1 ≃ Fin (Fintype.card dim1)`: `Fintype.equivOfCardEq`. Composing that bijection
  -- with `Fintype.equivFin dim1` (the *different* fixed bijection `singularValueDiagonal` uses)
  -- gives a single permutation `σ` of `dim1`, independent of `l`, making the two sides' diagonal
  -- entries line up.
  set σ : dim1 ≃ dim1 :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card dim1))).symm.trans
      (Fintype.equivFin dim1).symm with hσ_def
  set τ : dim2 ≃ dim2 :=
    (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card dim2))).symm.trans
      (Fintype.equivFin dim2).symm with hτ_def
  have hAeig : ∀ l (i : dim1), (Matrix.posSemidef_abs (A l)).isHermitian.eigenvalues i
      = (A l).singularValues (Fintype.equivFin dim1 (σ i)) := by
    intro l i
    rw [← Matrix.abs_eigenvalues₀_eq_singularValues]
    simp [Matrix.IsHermitian.eigenvalues, hσ_def]
  have hBeig : ∀ l (j : dim2), (Matrix.posSemidef_abs (B l)).isHermitian.eigenvalues j
      = (B l).singularValues (Fintype.equivFin dim2 (τ j)) := by
    intro l j
    rw [← Matrix.abs_eigenvalues₀_eq_singularValues]
    simp [Matrix.IsHermitian.eigenvalues, hτ_def]
  have hdL_eq : dL = dR ∘ (Equiv.prodCongr σ τ) := by
    funext p
    obtain ⟨i, j⟩ := p
    have hpc : (Equiv.prodCongr σ τ) (i, j) = (σ i, τ j) := rfl
    simp only [hdL_def, hdR_def, Function.comp_apply, hpc]
    exact Finset.sum_congr rfl fun l _ => by rw [hAeig l i, hBeig l j]
  have hML_PSD := Matrix.posSemidef_sum_kronecker
    (fun l => (Matrix.posSemidef_abs (A l)).posSemidef_sortedDiagonal)
    (fun l => (Matrix.posSemidef_abs (B l)).posSemidef_sortedDiagonal)
  have hMR_PSD := Matrix.posSemidef_sum_kronecker_singularValueDiagonal A B
  have hdL_herm : (Matrix.diagonal (fun p : dim1 × dim2 => (dL p : 𝕜))).IsHermitian :=
    hMLdiag ▸ hML_PSD.isHermitian
  have hdR_herm : (Matrix.diagonal (fun p : dim1 × dim2 => (dR p : 𝕜))).IsHermitian :=
    hMRdiag ▸ hMR_PSD.isHermitian
  have heigL : hML_PSD.isHermitian.eigenvalues₀ = hdL_herm.eigenvalues₀ :=
    hML_PSD.isHermitian.eigenvalues₀_eq_of_charpoly_eq hdL_herm (congrArg Matrix.charpoly hMLdiag)
  have heigR : hMR_PSD.isHermitian.eigenvalues₀ = hdR_herm.eigenvalues₀ :=
    hMR_PSD.isHermitian.eigenvalues₀_eq_of_charpoly_eq hdR_herm (congrArg Matrix.charpoly hMRdiag)
  have htopSumEq : ∀ k, Majorization.topSum hdL_herm.eigenvalues₀ k
      = Majorization.topSum hdR_herm.eigenvalues₀ k := by
    intro k
    set e : dim1 × dim2 ≃ Fin (Fintype.card (dim1 × dim2)) := Fintype.equivFin (dim1 × dim2)
    rw [Matrix.IsHermitian.topSum_eigenvalues₀_diagonal dL hdL_herm e k,
      Matrix.IsHermitian.topSum_eigenvalues₀_diagonal dR hdR_herm e k, hdL_eq]
    have hcomp : (dR ∘ (Equiv.prodCongr σ τ)) ∘ (⇑e.symm)
        = (dR ∘ (⇑e.symm)) ∘ (⇑(e.symm.trans ((Equiv.prodCongr σ τ).trans e))) := by
      funext x
      simp only [Function.comp_apply, Equiv.trans_apply, Equiv.symm_apply_apply]
    rw [hcomp]
    exact Majorization.topSum_comp_perm (dR ∘ (⇑e.symm))
      (e.symm.trans ((Equiv.prodCongr σ τ).trans e)) k
  intro k _
  rw [heigL, heigR]
  exact (htopSumEq k).le

/-- `posSemidef_sum_kronecker_singularValueDiagonal`'s eigenvalues depend on the families `A`, `B`
only through their singular values: if `X`, `Y` have the same singular values as `A`, `B`
respectively (`hXA`, `hYB`), the `singularValueDiagonal`-built matrices agree termwise
(`hSumEq`), hence so do their sums' `IsHermitian.eigenvalues₀`, via
`Matrix.IsHermitian.eigenvalues₀_eq_of_charpoly_eq` (`SingularValue.lean`, equal matrices
trivially having equal `charpoly`) — deliberately not over `(h ▸ hP).eigenvalues₀ = hP.eigenvalues₀`
by `subst`/proof-irrelevance (used elsewhere in this project for this kind of transport),
which here made the kernel time out on this declaration (this lemma is split out from
`kyFanNorm_sum_kronecker_abs_le` below to keep each piece small on its own). -/
theorem eigenvalues₀_posSemidef_sum_kronecker_singularValueDiagonal_congr {m : ℕ}
    (X A : Fin m → Matrix dim1 dim1 𝕜) (Y B : Fin m → Matrix dim2 dim2 𝕜)
    (hXA : ∀ l, (X l).singularValues = (A l).singularValues)
    (hYB : ∀ l, (Y l).singularValues = (B l).singularValues) :
    (Matrix.posSemidef_sum_kronecker_singularValueDiagonal X Y).isHermitian.eigenvalues₀
      = (Matrix.posSemidef_sum_kronecker_singularValueDiagonal A B).isHermitian.eigenvalues₀ := by
  have hXeq : ∀ l, (X l).singularValueDiagonal = (A l).singularValueDiagonal := fun l => by
    simp only [Matrix.singularValueDiagonal, hXA l]
  have hYeq : ∀ l, (Y l).singularValueDiagonal = (B l).singularValueDiagonal := fun l => by
    simp only [Matrix.singularValueDiagonal, hYB l]
  have hSumEq : (∑ l, (X l).singularValueDiagonal ⊗ₖ (Y l).singularValueDiagonal)
      = ∑ l, (A l).singularValueDiagonal ⊗ₖ (B l).singularValueDiagonal :=
    Finset.sum_congr rfl (fun l _ => by rw [hXeq l, hYeq l])
  exact (Matrix.posSemidef_sum_kronecker_singularValueDiagonal X Y).isHermitian
    |>.eigenvalues₀_eq_of_charpoly_eq
      (Matrix.posSemidef_sum_kronecker_singularValueDiagonal A B).isHermitian
      (congrArg Matrix.charpoly hSumEq)

/-- The weak-majorization bound feeding `kyFanNorm_sum_kronecker_abs_le` below, restricted to `k ≤
Fintype.card (dim1 × dim2)` (the range `Majorization.WeakMajorizedBy` quantifies over). Chains
`majorized_sum_kronecker_sortedDiagonal` (already proved, `SumKroneckerMajorization.lean`) with
`sortedDiagonal_abs_weakMajorized_singularValueDiagonal` above, bridged by
`eigenvalues₀_posSemidef_sum_kronecker_singularValueDiagonal_congr`. Split out as its own
declaration for the same kernel-size reason as that lemma. -/
theorem topSum_abs_kronecker_le_of_le_card {m : ℕ} (X A : Fin m → Matrix dim1 dim1 𝕜)
    (Y B : Fin m → Matrix dim2 dim2 𝕜) (hXA : ∀ l, (X l).singularValues = (A l).singularValues)
    (hYB : ∀ l, (Y l).singularValues = (B l).singularValues) {k : ℕ}
    (hk : k ≤ Fintype.card (dim1 × dim2)) :
    Majorization.topSum
        (Matrix.posSemidef_sum_kronecker (fun l => Matrix.posSemidef_abs (X l))
          (fun l => Matrix.posSemidef_abs (Y l))).isHermitian.eigenvalues₀ k
      ≤ Majorization.topSum
          (Matrix.posSemidef_sum_kronecker_singularValueDiagonal A B).isHermitian.eigenvalues₀
            k := by
  have h1 := (majorized_sum_kronecker_sortedDiagonal (fun l => Matrix.posSemidef_abs (X l))
    (fun l => Matrix.posSemidef_abs (Y l))).1 k hk
  have h2 := sortedDiagonal_abs_weakMajorized_singularValueDiagonal X Y k hk
  rw [eigenvalues₀_posSemidef_sum_kronecker_singularValueDiagonal_congr X A Y B hXA hYB] at h2
  exact h1.trans h2

/-- Shared bound used twice in `weakMajorized_sum_kronecker_singularValueDiagonal`'s final assembly
below: once directly (`X, Y := A, B`) and once for the conjugate-transposed family (`X, Y := fun l
=> (A l)ᴴ, fun l => (B l)ᴴ`, via `Matrix.singularValues_conjTranspose`). Given families `X`, `Y`
whose singular values agree with `A`'s, `B`'s (`hXA`, `hYB`), `∑ l, |X l| ⊗ₖ |Y l|`'s Ky Fan
`k`-norm is bounded by `weakMajorized_sum_kronecker_singularValueDiagonal`'s right-hand side.
Assembles `topSum_abs_kronecker_le_of_le_card` above (the `k ≤ n` case) with
`Majorization.topSum_eq_topSum_of_le` (`Majorization.lean`) to extend to every `k` (`topSum`
saturates once `k` exceeds `n`, on both sides at once). -/
theorem kyFanNorm_sum_kronecker_abs_le {m : ℕ} (X A : Fin m → Matrix dim1 dim1 𝕜)
    (Y B : Fin m → Matrix dim2 dim2 𝕜) (hXA : ∀ l, (X l).singularValues = (A l).singularValues)
    (hYB : ∀ l, (Y l).singularValues = (B l).singularValues) (k : ℕ) :
    (∑ l, (X l).abs ⊗ₖ (Y l).abs).kyFanNorm k
      ≤ Majorization.topSum
          (Matrix.posSemidef_sum_kronecker_singularValueDiagonal A B).isHermitian.eigenvalues₀
            k := by
  have hXY : (∑ l, (X l).abs ⊗ₖ (Y l).abs).PosSemidef :=
    Matrix.posSemidef_sum_kronecker (fun l => Matrix.posSemidef_abs (X l))
      (fun l => Matrix.posSemidef_abs (Y l))
  unfold Matrix.kyFanNorm
  rw [Matrix.PosSemidef.singularValues_eq_eigenvalues₀ hXY]
  by_cases hk : k ≤ Fintype.card (dim1 × dim2)
  · exact topSum_abs_kronecker_le_of_le_card X A Y B hXA hYB hk
  · rw [Majorization.topSum_eq_topSum_of_le hXY.isHermitian.eigenvalues₀ (not_le.mp hk).le,
      Majorization.topSum_eq_topSum_of_le
        (Matrix.posSemidef_sum_kronecker_singularValueDiagonal A B).isHermitian.eigenvalues₀
        (not_le.mp hk).le]
    exact topSum_abs_kronecker_le_of_le_card X A Y B hXA hYB le_rfl

/-- **Step 8 of the roadmap above.** The block operators `L`, `R` whose Cauchy–Schwarz inequality
(`Matrix.kyFanNorm_conjTranspose_mul_le`, `ForMathlib/KyFanCauchySchwarz.lean`) drives the reduction
to the positive semidefinite case: the vertical stacks (over `l : Fin m`) of `|A l ⊗ₖ B l|.sqrt *
(U l)ᴴ` resp. `|A l ⊗ₖ B l|.sqrt`, where `U l` is a polar-decomposition unitary for `A l ⊗ₖ B l`
(`Matrix.exists_polarDecomposition`, `ForMathlib/PolarDecomposition.lean`). Stated as an existence
lemma (rather than exposing `L`, `R` as named `def`s) since the identities hold by expanding the
block sum and cancelling cross terms `l ≠ l'` (orthogonality of the `Fin m` factor) — routine but
long index bookkeeping that the statement itself does not need to reference. -/
theorem exists_LR_kronecker_identities {m : ℕ} (A : Fin m → Matrix dim1 dim1 𝕜)
    (B : Fin m → Matrix dim2 dim2 𝕜) :
    ∃ L R : Matrix ((dim1 × dim2) × Fin m) (dim1 × dim2) 𝕜,
      Lᴴ * R = ∑ l, A l ⊗ₖ B l ∧
      Lᴴ * L = ∑ l, (A l ⊗ₖ B l)ᴴ.abs ∧
      Rᴴ * R = ∑ l, (A l ⊗ₖ B l).abs := by
  choose U hU using fun l => Matrix.exists_polarDecomposition (A l ⊗ₖ B l)
  set S : Fin m → Matrix (dim1 × dim2) (dim1 × dim2) 𝕜 :=
    fun l => (Matrix.posSemidef_abs (A l ⊗ₖ B l)).sqrt
  have hSHerm : ∀ l, (S l)ᴴ = S l :=
    fun l => (Matrix.posSemidef_abs (A l ⊗ₖ B l)).posSemidef_sqrt.isHermitian
  have hSS : ∀ l, S l * S l = (A l ⊗ₖ B l).abs :=
    fun l => (Matrix.posSemidef_abs (A l ⊗ₖ B l)).sqrt_mul_sqrt
  have hconj : ∀ l, (S l * (U l : Matrix (dim1 × dim2) (dim1 × dim2) 𝕜)ᴴ)ᴴ
      = (U l : Matrix (dim1 × dim2) (dim1 × dim2) 𝕜) * S l := fun l => by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, hSHerm l]
  -- The vertical-stack construction: for blocks `X l`, `Y l` indexed by `l`, stacking `X`/`Y`
  -- over `l` into tall matrices turns `(stack X)ᴴ * (stack Y)` into `∑ l, (X l)ᴴ * Y l` — the
  -- cross terms `l ≠ l'` never arise since rows are indexed by the disjoint union over `l`.
  have hblock : ∀ (X Y : Fin m → Matrix (dim1 × dim2) (dim1 × dim2) 𝕜),
      (Matrix.of (fun p : (dim1 × dim2) × Fin m => fun c => X p.2 p.1 c))ᴴ *
        Matrix.of (fun p : (dim1 × dim2) × Fin m => fun c => Y p.2 p.1 c) =
      ∑ l, (X l)ᴴ * Y l := by
    intro X Y
    ext c c'
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.of_apply,
      Fintype.sum_prod_type_right, Matrix.sum_apply]
  refine ⟨Matrix.of (fun p c => (S p.2 * (U p.2 : Matrix (dim1 × dim2) (dim1 × dim2) 𝕜)ᴴ) p.1 c),
    Matrix.of (fun p c => S p.2 p.1 c), ?_, ?_, ?_⟩
  · refine (hblock (fun l => S l * (U l : Matrix (dim1 × dim2) (dim1 × dim2) 𝕜)ᴴ) S).trans ?_
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hconj l, mul_assoc, hSS l, ← hU l]
  · refine (hblock (fun l => S l * (U l : Matrix (dim1 × dim2) (dim1 × dim2) 𝕜)ᴴ)
      (fun l => S l * (U l : Matrix (dim1 × dim2) (dim1 × dim2) 𝕜)ᴴ)).trans ?_
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hconj l]
    have hassoc : (U l : Matrix (dim1 × dim2) (dim1 × dim2) 𝕜) * S l *
        (S l * (U l : Matrix (dim1 × dim2) (dim1 × dim2) 𝕜)ᴴ)
        = (U l : Matrix (dim1 × dim2) (dim1 × dim2) 𝕜) * (S l * S l) *
          (U l : Matrix (dim1 × dim2) (dim1 × dim2) 𝕜)ᴴ := by noncomm_ring
    rw [hassoc, hSS l]
    exact (Matrix.abs_conjTranspose_eq_of_polarDecomposition (hU l)).symm
  · refine (hblock S S).trans ?_
    refine Finset.sum_congr rfl (fun l _ => ?_)
    rw [hSHerm l, hSS l]

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
  -- Step 3: `|A l ⊗ₖ B l| = |A l| ⊗ₖ |B l|`.
  have habs : ∀ l, (A l ⊗ₖ B l).abs = (A l).abs ⊗ₖ (B l).abs := fun l => Matrix.abs_kronecker _ _
  -- Step 4: `|A l|`, `|B l|`'s eigenvalues are `σ(A l)`, `σ(B l)`.
  have hAeig : ∀ l, (Matrix.posSemidef_abs (A l)).isHermitian.eigenvalues₀ = (A l).singularValues :=
    fun l => Matrix.abs_eigenvalues₀_eq_singularValues (A l)
  have hBeig : ∀ l, (Matrix.posSemidef_abs (B l)).isHermitian.eigenvalues₀ = (B l).singularValues :=
    fun l => Matrix.abs_eigenvalues₀_eq_singularValues (B l)
  -- Step 5: `σ((A l ⊗ₖ B l)ᴴ) = σ(A l ⊗ₖ B l)`.
  have hconj : ∀ l, (A l ⊗ₖ B l)ᴴ.singularValues = (A l ⊗ₖ B l).singularValues :=
    fun l => Matrix.singularValues_conjTranspose (A l ⊗ₖ B l)
  -- Step 6: polar decomposition of each `A l ⊗ₖ B l`.
  choose U hU using fun l => Matrix.exists_polarDecomposition (A l ⊗ₖ B l)
  -- Step 7: `|(A l ⊗ₖ B l)ᴴ| = U l * |A l ⊗ₖ B l| * (U l)ᴴ`.
  have hUabs : ∀ l, (A l ⊗ₖ B l)ᴴ.abs
      = (U l : Matrix _ _ 𝕜) * (A l ⊗ₖ B l).abs * (U l : Matrix _ _ 𝕜)ᴴ :=
    fun l => Matrix.abs_conjTranspose_eq_of_polarDecomposition (hU l)
  -- Step 8: the block operators `L`, `R`.
  obtain ⟨L, R, hLR, hLL, hRR⟩ := exists_LR_kronecker_identities A B
  -- Step 9: Cauchy–Schwarz for Ky Fan norms, applied to `L`, `R`.
  have hCS : ∀ k, (Lᴴ * R).kyFanNorm k
      ≤ Real.sqrt ((Lᴴ * L).kyFanNorm k * (Rᴴ * R).kyFanNorm k) :=
    fun k => Matrix.kyFanNorm_conjTranspose_mul_le L R k
  -- Step 10: assemble, for each `k`, via `kyFanNorm_sum_kronecker_abs_le` (applied to `A, B`
  -- directly for `Rᴴ * R`, and to the conjugate-transposed family for `Lᴴ * L`) plus `hCS`.
  intro k _
  set target := Majorization.topSum
    (Matrix.posSemidef_sum_kronecker_singularValueDiagonal A B).isHermitian.eigenvalues₀ k
    with htarget_def
  have htarget_nonneg : 0 ≤ target := by
    rw [htarget_def]
    exact Majorization.topSum_nonneg _
      (fun i => (Matrix.posSemidef_sum_kronecker_singularValueDiagonal A B).eigenvalues₀_nonneg i) k
  have hLLabs : ∀ l, (A l ⊗ₖ B l)ᴴ.abs = (A l)ᴴ.abs ⊗ₖ (B l)ᴴ.abs := fun l => by
    rw [Matrix.conjTranspose_kronecker, Matrix.abs_kronecker]
  have hLL' : Lᴴ * L = ∑ l, (A l)ᴴ.abs ⊗ₖ (B l)ᴴ.abs := by
    rw [hLL]; exact Finset.sum_congr rfl fun l _ => hLLabs l
  have hRR' : Rᴴ * R = ∑ l, (A l).abs ⊗ₖ (B l).abs := by
    rw [hRR]; exact Finset.sum_congr rfl fun l _ => habs l
  have hRbound : (Rᴴ * R).kyFanNorm k ≤ target := by
    rw [hRR']
    exact kyFanNorm_sum_kronecker_abs_le A A B B (fun _ => rfl) (fun _ => rfl) k
  have hLbound : (Lᴴ * L).kyFanNorm k ≤ target := by
    rw [hLL']
    exact kyFanNorm_sum_kronecker_abs_le (fun l => (A l)ᴴ) A (fun l => (B l)ᴴ) B
      (fun l => Matrix.singularValues_conjTranspose (A l))
      (fun l => Matrix.singularValues_conjTranspose (B l)) k
  change (∑ i, A i ⊗ₖ B i).kyFanNorm k ≤ target
  calc (∑ i, A i ⊗ₖ B i).kyFanNorm k
      = (Lᴴ * R).kyFanNorm k := by rw [hLR]
    _ ≤ Real.sqrt ((Lᴴ * L).kyFanNorm k * (Rᴴ * R).kyFanNorm k) := hCS k
    _ ≤ Real.sqrt (target * target) :=
        Real.sqrt_le_sqrt (mul_le_mul hLbound hRbound (Matrix.kyFanNorm_nonneg k _)
          htarget_nonneg)
    _ = target := Real.sqrt_mul_self htarget_nonneg
