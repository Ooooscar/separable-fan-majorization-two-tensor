import NewProject.ForMathlib.PosSemidef
import NewProject.ForMathlib.EigenvalueScaling

/-!
# Singular values of a square matrix

Mathlib has singular values for linear maps between inner product spaces
(`LinearMap.singularValues`, `Mathlib.Analysis.InnerProductSpace.SingularValues`), indexed by `ℕ`
via a `Finsupp`, but nothing at the level of `Matrix`, indexed the way
`Matrix.IsHermitian.eigenvalues₀` is (`Fin (Fintype.card ι) → ℝ`, decreasing) — the shape
`Majorization.WeakMajorizedBy`/`≺w` (`Majorization.lean`) needs. We define that version directly:
the square roots of the eigenvalues of the positive semidefinite Hermitian matrix `Aᴴ * A`
(`Matrix.posSemidef_conjTranspose_mul_self`).

## Main definitions

* `Matrix.singularValues`: `σ(A)`, the singular values of a square matrix `A`, sorted in
  decreasing order. Needed by `SumKroneckerWeakMajorization.lean`'s general (non-Hermitian, not
  necessarily positive semidefinite) majorization theorem for sums of Kronecker products.

## Main results

* `Matrix.singularValues_nonneg`, `Matrix.singularValues_antitone`: `σ(A)` is nonnegative and
  sorted in decreasing order.
* `Matrix.IsHermitian.eigenvalues₀_eq_of_charpoly_eq`: Hermitian matrices with equal characteristic
  polynomials have equal `eigenvalues₀`.
* `Matrix.singularValues_unitary_conj`: `σ(U * A * V) = σ(A)` for unitary `U`, `V`. Needed for
  `Matrix.kyFanNorm` (`KyFanNorm.lean`) to satisfy `Matrix.IsUnitarilyInvariantNorm.unitary_conj'`.
* `Matrix.isHermitian_fromBlocks_zero_conjTranspose`: the Hermitian **Jordan–Wielandt dilation**
  `Ã := fromBlocks 0 A Aᴴ 0` of a square matrix `A`. Its eigenvalues are `±σ(A)` (not proved here as
  a standalone fact, only via the two results below that use it).
* `Matrix.charpoly_fromBlocks_zero_conjTranspose`: the classical algebraic identity underlying that
  fact, `Ã.charpoly = (Aᴴ*A).charpoly.comp (X^2)`, via a Schur-complement determinant computation
  (`Matrix.det_scalar_sub_fromBlocks_zero_conjTranspose`).
* `Matrix.sum_eigenvalues₀_fromBlocks_zero_conjTranspose_mul_eq`: the pairwise-product identity
  between two dilations' full eigenvalue lists and the underlying matrices' singular values,
  `∑ᵢ λᵢ(Ã)λᵢ(B̃) = 2∑ᵢ σᵢ(A)σᵢ(B)`. Feeds the general von Neumann trace inequality
  (`TraceInequality.lean`).
-/

open Matrix
open scoped ComplexOrder

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

/-- The singular values of a square matrix `A`, sorted in decreasing order: the square roots of
the eigenvalues of the positive semidefinite Hermitian matrix `Aᴴ * A`
(`Matrix.posSemidef_conjTranspose_mul_self`), read out via `Matrix.IsHermitian.eigenvalues₀`. -/
noncomputable def Matrix.singularValues (A : Matrix ι ι 𝕜) : Fin (Fintype.card ι) → ℝ :=
  fun i => Real.sqrt ((Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀ i)

/-- `σ(A)` is nonnegative, being a square root. -/
theorem Matrix.singularValues_nonneg (A : Matrix ι ι 𝕜) (i : Fin (Fintype.card ι)) :
    0 ≤ A.singularValues i :=
  Real.sqrt_nonneg _

/-- `σ(A)` is sorted in decreasing order, since `Matrix.IsHermitian.eigenvalues₀` is
(`Matrix.IsHermitian.eigenvalues₀_antitone`) and `Real.sqrt` is monotone. -/
theorem Matrix.singularValues_antitone (A : Matrix ι ι 𝕜) : Antitone A.singularValues :=
  fun _ _ hij => Real.sqrt_le_sqrt
    ((Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀_antitone hij)

/-- Hermitian matrices with equal characteristic polynomials have equal (decreasing-sorted)
`eigenvalues₀`: both are recovered as the sorted list of `charpoly` roots
(`Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀`), so equal charpolys force equal sorted
root-lists, hence equal `eigenvalues₀` via `List.ofFn` injectivity. -/
theorem Matrix.IsHermitian.eigenvalues₀_eq_of_charpoly_eq {M N : Matrix ι ι 𝕜}
    (hM : M.IsHermitian) (hN : N.IsHermitian) (h : M.charpoly = N.charpoly) :
    hM.eigenvalues₀ = hN.eigenvalues₀ := by
  apply List.ofFn_injective
  rw [← hM.sort_roots_charpoly_eq_eigenvalues₀, ← hN.sort_roots_charpoly_eq_eigenvalues₀, h]

/-- If `A`'s and `B`'s `Aᴴ * A`-eigenvalues agree, so do their singular values: squaring undoes
the `Real.sqrt` in `Matrix.singularValues`'s definition, pointwise. Used to finish
`Matrix.singularValues_unitary_conj` below, once the eigenvalue equality itself is in hand via
`eigenvalues₀_eq_of_charpoly_eq`. -/
theorem Matrix.singularValues_eq_of_eigenvalues₀_eq {A B : Matrix ι ι 𝕜}
    (h : (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀
      = (Matrix.posSemidef_conjTranspose_mul_self B).isHermitian.eigenvalues₀) :
    A.singularValues = B.singularValues :=
  funext fun i => congrArg Real.sqrt (congrFun h i)

/-- `σ(U * A * V) = σ(A)` for unitary `U`, `V`: singular values are unchanged by two-sided unitary
conjugation. Needed for `Matrix.kyFanNorm` (`KyFanNorm.lean`) to satisfy
`Matrix.IsUnitarilyInvariantNorm.unitary_conj'`.

The proof reduces to invariance of the characteristic polynomial under similarity:
`(UAV)ᴴ(UAV) = Vᴴ(AᴴA)V` (since `UᴴU = 1`), and `charpoly (Vᴴ M V) = charpoly M` for any `M` and
unitary `V` (since `Vᴴ = V⁻¹`, via `Matrix.charpoly_mul_comm`). Equal characteristic polynomials
give equal `eigenvalues₀` (via `eigenvalues₀_eq_of_charpoly_eq` above), hence equal square roots. -/
theorem Matrix.singularValues_unitary_conj (U V : Matrix.unitaryGroup ι 𝕜) (A : Matrix ι ι 𝕜) :
    ((U : Matrix ι ι 𝕜) * A * (V : Matrix ι ι 𝕜)).singularValues = A.singularValues := by
  set Uc := (U : Matrix ι ι 𝕜)
  set Vc := (V : Matrix ι ι 𝕜)
  have hUU : Ucᴴ * Uc = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp U.2
    rwa [Matrix.star_eq_conjTranspose] at h
  have hVV : Vc * Vcᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp V.2
    rwa [Matrix.star_eq_conjTranspose] at h
  have hM : (Aᴴ * A).IsHermitian := (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian
  have hN : ((Uc * A * Vc)ᴴ * (Uc * A * Vc)).IsHermitian :=
    (Matrix.posSemidef_conjTranspose_mul_self (Uc * A * Vc)).isHermitian
  have hprod : (Uc * A * Vc)ᴴ * (Uc * A * Vc) = Vcᴴ * (Aᴴ * A) * Vc := by
    have e1 : (Uc * A * Vc)ᴴ = Vcᴴ * Aᴴ * Ucᴴ := by
      simp only [Matrix.conjTranspose_mul, mul_assoc]
    have regroup : Vcᴴ * Aᴴ * Ucᴴ * (Uc * A * Vc) = Vcᴴ * Aᴴ * (Ucᴴ * Uc) * A * Vc := by
      simp only [mul_assoc]
    rw [e1, regroup, hUU, mul_one, mul_assoc Vcᴴ Aᴴ A]
  have hcharpoly : ((Uc * A * Vc)ᴴ * (Uc * A * Vc)).charpoly = (Aᴴ * A).charpoly := by
    rw [hprod, mul_assoc Vcᴴ (Aᴴ * A) Vc, Matrix.charpoly_mul_comm Vcᴴ ((Aᴴ * A) * Vc),
      mul_assoc (Aᴴ * A) Vc Vcᴴ, hVV, mul_one]
  have heig : hN.eigenvalues₀ = hM.eigenvalues₀ := hN.eigenvalues₀_eq_of_charpoly_eq hM hcharpoly
  exact Matrix.singularValues_eq_of_eigenvalues₀_eq heig

/-- `σ(c • A) = ‖c‖ • σ(A)` for any `c : 𝕜` (singular values are always nonnegative, so a
non-positive-real or non-real `c` cannot scale them by `c` itself): needed by
`Matrix.singularValues_real_smul` below, in turn needed by `Matrix.kyFanNorm_smul`
(`KyFanNorm.lean`) and the Cauchy–Schwarz inequality for Ky Fan norms
(`KyFanCauchySchwarz.lean`).

`(c•A)ᴴ*(c•A) = ‖c‖² • (Aᴴ*A)` (`(c•A)ᴴ = conj c • Aᴴ`, and `conj c * c = ‖c‖²` — this is a *real*
nonnegative scalar even when `c` itself isn't real), so both sides' `eigenvalues₀` agree by
`eigenvalues₀_eq_of_charpoly_eq` (equal underlying matrices ⟹ equal charpoly ⟹ equal
`eigenvalues₀`) with `Matrix.IsHermitian.eigenvalues₀_smul` (`EigenvalueScaling.lean` — a general
Hermitian-matrix fact, not specific to singular values, so it lives there rather than here) applied
with the real, nonnegative `‖c‖²`, then `√(‖c‖² * x) = ‖c‖ * √x` (`‖c‖ ≥ 0`) finishes it. -/
theorem Matrix.singularValues_smul (A : Matrix ι ι 𝕜) (c : 𝕜) :
    (c • A).singularValues = ‖c‖ • A.singularValues := by
  have hM : (Aᴴ * A).IsHermitian := (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian
  have hMc : ((c • A)ᴴ * (c • A)).IsHermitian :=
    (Matrix.posSemidef_conjTranspose_mul_self (c • A)).isHermitian
  have hprod : (c • A)ᴴ * (c • A) = (‖c‖ ^ 2 : ℝ) • (Aᴴ * A) := by
    rw [Matrix.conjTranspose_smul, smul_mul_assoc, mul_smul_comm, smul_smul, RCLike.star_def,
      RCLike.conj_mul, ← RCLike.ofReal_pow, ← RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  have hcharpoly : ((c • A)ᴴ * (c • A)).charpoly = ((‖c‖ ^ 2 : ℝ) • (Aᴴ * A)).charpoly := by
    rw [hprod]
  have heigeq : hMc.eigenvalues₀ = (hM.smul (IsSelfAdjoint.all (‖c‖ ^ 2 : ℝ))).eigenvalues₀ :=
    hMc.eigenvalues₀_eq_of_charpoly_eq (hM.smul (IsSelfAdjoint.all (‖c‖ ^ 2 : ℝ))) hcharpoly
  funext i
  unfold Matrix.singularValues
  simp only [Pi.smul_apply, smul_eq_mul]
  change Real.sqrt (hMc.eigenvalues₀ i) = ‖c‖ * Real.sqrt (hM.eigenvalues₀ i)
  rw [heigeq, hM.eigenvalues₀_smul (sq_nonneg ‖c‖)]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Real.sqrt_mul (sq_nonneg ‖c‖), Real.sqrt_sq (norm_nonneg c)]

/-- `σ(c • A) = |c| • σ(A)` for a *real* `c` (the `Module ℝ (Matrix ι ι 𝕜)` scaling, as opposed to
`Matrix.singularValues_smul`'s `Module 𝕜 (Matrix ι ι 𝕜)` scaling above): a direct corollary via
`RCLike.real_smul_eq_coe_smul` (`c • A = (c : 𝕜) • A`) and `RCLike.norm_ofReal` (`‖(c : 𝕜)‖ =
|c|`). Needed by `Matrix.kyFanNorm_smul` (`KyFanNorm.lean`), in turn needed by the Cauchy–Schwarz
inequality for Ky Fan norms (`KyFanCauchySchwarz.lean`), both of which only ever scale by a real
constant. -/
theorem Matrix.singularValues_real_smul (A : Matrix ι ι 𝕜) (c : ℝ) :
    (c • A).singularValues = |c| • A.singularValues := by
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), Matrix.singularValues_smul A (c : 𝕜),
    RCLike.norm_ofReal]

omit [Fintype ι] [DecidableEq ι] in
/-- The Hermitian **Jordan–Wielandt dilation** of a square matrix: `Ã := fromBlocks 0 A Aᴴ 0` on
`ι ⊕ ι`. `IsHermitian` here is immediate from `Matrix.fromBlocks_conjTranspose`; the substance
(`Ã.eigenvalues₀ = ±σ(A)`) is exploited, but not independently stated, by
`Matrix.sum_eigenvalues₀_fromBlocks_zero_conjTranspose_mul_eq` below. -/
theorem Matrix.isHermitian_fromBlocks_zero_conjTranspose (A : Matrix ι ι 𝕜) :
    (Matrix.fromBlocks (0 : Matrix ι ι 𝕜) A Aᴴ 0).IsHermitian := by
  classical
  change (Matrix.fromBlocks (0 : Matrix ι ι 𝕜) A Aᴴ 0)ᴴ
      = Matrix.fromBlocks (0 : Matrix ι ι 𝕜) A Aᴴ 0
  rw [Matrix.fromBlocks_conjTranspose]
  simp

/-- **Schur complement determinant identity for the Jordan–Wielandt dilation.** For any nonzero
`x : 𝕜`, `det(x • 1 - Ã) = det(x² • 1 - Aᴴ * A)`, where `Ã := fromBlocks 0 A Aᴴ 0`
(`Matrix.isHermitian_fromBlocks_zero_conjTranspose`).

This is the classical determinant identity behind the standard **Jordan–Wielandt** fact that the
eigenvalues of `Ã` are `±σ(A)` (see e.g. Horn & Johnson, *Topics in Matrix Analysis*, §3.0–3.1, or
Bhatia, *Matrix Analysis*, Exercise I.2.8). Proof: `x • 1 - Ã = fromBlocks (x•1) (-A) (-Aᴴ) (x•1)`;
since `x ≠ 0`, the top-left block `x • 1` is invertible, so the Schur-complement determinant
formula (`Matrix.det_fromBlocks₁₁`) gives `det = det(x•1) * det(x•1 - (-Aᴴ)*(x•1)⁻¹*(-A))
= xⁿ * det(x•1 - x⁻¹ • (Aᴴ*A))`, and pulling the scalar `x` back inside via `Matrix.det_smul`
turns `xⁿ * det(x•1 - x⁻¹•(Aᴴ*A))` into `det(x • (x•1 - x⁻¹•(Aᴴ*A))) = det(x²•1 - Aᴴ*A)`. -/
theorem Matrix.det_scalar_sub_fromBlocks_zero_conjTranspose (A : Matrix ι ι 𝕜) {x : 𝕜}
    (hx : x ≠ 0) :
    (Matrix.scalar (ι ⊕ ι) x - Matrix.fromBlocks (0 : Matrix ι ι 𝕜) A Aᴴ 0).det
      = (Matrix.scalar ι (x ^ 2) - Aᴴ * A).det := by
  have hone : Matrix.scalar (ι ⊕ ι) x = x • (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝕜) := by
    rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul, mul_one]
  have hone' : (1 : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝕜)
      = Matrix.fromBlocks (1 : Matrix ι ι 𝕜) 0 0 1 := Matrix.fromBlocks_one.symm
  have hone2 : Matrix.scalar ι (x ^ 2) = (x ^ 2) • (1 : Matrix ι ι 𝕜) := by
    rw [Matrix.scalar_apply, Matrix.smul_eq_diagonal_mul, mul_one]
  haveI : Invertible (x • (1 : Matrix ι ι 𝕜)) :=
    ⟨x⁻¹ • (1 : Matrix ι ι 𝕜),
      by rw [smul_mul_assoc, one_mul, smul_smul, inv_mul_cancel₀ hx, one_smul],
      by rw [smul_mul_assoc, one_mul, smul_smul, mul_inv_cancel₀ hx, one_smul]⟩
  have hinv : ⅟(x • (1 : Matrix ι ι 𝕜)) = x⁻¹ • (1 : Matrix ι ι 𝕜) :=
    invOf_eq_right_inv (by rw [smul_mul_assoc, one_mul, smul_smul, mul_inv_cancel₀ hx, one_smul])
  have hxx : x⁻¹ * x ^ 2 = x := by rw [pow_two, ← mul_assoc, inv_mul_cancel₀ hx, one_mul]
  have hmid : x • (1 : Matrix ι ι 𝕜) - x⁻¹ • (Aᴴ * A)
      = x⁻¹ • (Matrix.scalar ι (x ^ 2) - Aᴴ * A) := by
    rw [smul_sub, hone2, smul_smul, hxx]
  rw [hone, hone', Matrix.fromBlocks_smul, sub_eq_add_neg, Matrix.fromBlocks_neg,
    Matrix.fromBlocks_add]
  simp only [smul_zero, neg_zero, add_zero, zero_add]
  rw [Matrix.det_fromBlocks₁₁, hinv, neg_mul, neg_mul_neg, mul_smul_comm, mul_one, smul_mul_assoc,
    hmid]
  simp only [Matrix.det_smul, Matrix.det_one, mul_one]
  rw [← mul_assoc, ← mul_pow, mul_inv_cancel₀ hx, one_pow, one_mul]

/-- **Charpoly of the Jordan–Wielandt dilation.** `Ã.charpoly = (Aᴴ*A).charpoly.comp (X^2)`, where
`Ã := fromBlocks 0 A Aᴴ 0`.

Both sides, evaluated at any `x : 𝕜`, compute `det(x•1 - Ã)` and `det(x²•1 - Aᴴ*A)` respectively
(`Matrix.eval_charpoly`, `Polynomial.eval_comp`), which agree for every `x ≠ 0` by
`det_scalar_sub_fromBlocks_zero_conjTranspose` above. Since `𝕜` (being `RCLike`) is infinite, `{x |
x ≠ 0}` is an infinite set of agreement, so the two polynomials coincide outright
(`Polynomial.eq_of_infinite_eval_eq`). -/
theorem Matrix.charpoly_fromBlocks_zero_conjTranspose (A : Matrix ι ι 𝕜) :
    (Matrix.fromBlocks (0 : Matrix ι ι 𝕜) A Aᴴ 0).charpoly
      = (Aᴴ * A).charpoly.comp (Polynomial.X ^ 2) := by
  apply Polynomial.eq_of_infinite_eval_eq
  have hsub : ({0} : Set 𝕜)ᶜ ⊆
      {x : 𝕜 | (Matrix.fromBlocks (0 : Matrix ι ι 𝕜) A Aᴴ 0).charpoly.eval x
        = ((Aᴴ * A).charpoly.comp (Polynomial.X ^ 2)).eval x} := by
    intro x hx
    rw [Set.mem_compl_iff, Set.mem_singleton_iff] at hx
    simp only [Set.mem_setOf_eq, Polynomial.eval_comp, Polynomial.eval_pow, Polynomial.eval_X,
      Matrix.eval_charpoly]
    exact Matrix.det_scalar_sub_fromBlocks_zero_conjTranspose A hx
  exact Set.Infinite.mono hsub ((Set.finite_singleton (0 : 𝕜)).infinite_compl)

/-- `σᵢ(A)² = ` the `i`-th (sorted) eigenvalue of `Aᴴ * A`: squaring undoes the `Real.sqrt` in the
definition of `Matrix.singularValues`, since that eigenvalue is nonnegative
(`Matrix.PosSemidef.eigenvalues₀_nonneg`, via `Aᴴ * A`'s positive semidefiniteness
`Matrix.posSemidef_conjTranspose_mul_self`). -/
theorem Matrix.singularValues_sq (A : Matrix ι ι 𝕜) (i : Fin (Fintype.card ι)) :
    (A.singularValues i) ^ 2
      = (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues₀ i := by
  simp only [Matrix.singularValues]
  exact Real.sq_sqrt ((Matrix.posSemidef_conjTranspose_mul_self A).eigenvalues₀_nonneg i)

/-- **Charpoly of the Jordan–Wielandt dilation, factored.** `Ã.charpoly` (`Ã := fromBlocks 0 A Aᴴ
0`) splits as the product of `∏ᵢ (X - C(σᵢ(A)))` and `∏ᵢ (X - C(-σᵢ(A)))` — the precise sense in
which `Ã`'s eigenvalues are `±σ(A)`, promised in `isHermitian_fromBlocks_zero_conjTranspose`'s
docstring.

`Aᴴ*A`'s charpoly, reindexed from `ι` to `Fin (Fintype.card ι)` via `Fintype.prod_equiv`, is
composed with `X^2` (`charpoly_fromBlocks_zero_conjTranspose` above), then each resulting factor
`X^2 - C (hM.eigenvalues₀ i : 𝕜)` is rewritten as a difference of squares via
`hM.eigenvalues₀ i = (A.singularValues i)^2` (`Matrix.singularValues_sq`) and split into
`(X - C (A.singularValues i : 𝕜)) * (X - C (-(A.singularValues i) : 𝕜))`, and the product of these
paired factors distributes into the two separate products (`Finset.prod_mul_distrib`). -/
theorem Matrix.charpoly_fromBlocks_zero_conjTranspose_eq_prod (A : Matrix ι ι 𝕜) :
    (Matrix.fromBlocks (0 : Matrix ι ι 𝕜) A Aᴴ 0).charpoly
      = (∏ i : Fin (Fintype.card ι), (Polynomial.X - Polynomial.C (A.singularValues i : 𝕜)))
        * ∏ i : Fin (Fintype.card ι),
          (Polynomial.X - Polynomial.C (-(A.singularValues i) : 𝕜)) := by
  have hM := (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian
  have hreindex : (Aᴴ * A).charpoly
      = ∏ i : Fin (Fintype.card ι), (Polynomial.X - Polynomial.C (hM.eigenvalues₀ i : 𝕜)) := by
    rw [hM.charpoly_eq]
    exact Fintype.prod_equiv (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm _ _
      (fun i => by simp only [Matrix.IsHermitian.eigenvalues])
  have hfactor : ∀ i : Fin (Fintype.card ι),
      (Polynomial.X - Polynomial.C (hM.eigenvalues₀ i : 𝕜)).comp (Polynomial.X ^ 2)
        = (Polynomial.X - Polynomial.C (A.singularValues i : 𝕜))
          * (Polynomial.X - Polynomial.C (-(A.singularValues i) : 𝕜)) := by
    intro i
    rw [Polynomial.sub_comp, Polynomial.X_comp, Polynomial.C_comp, ← Matrix.singularValues_sq A i,
      RCLike.ofReal_pow, map_pow, map_neg]
    ring
  rw [Matrix.charpoly_fromBlocks_zero_conjTranspose A, hreindex, Polynomial.prod_comp]
  simp only [hfactor]
  rw [Finset.prod_mul_distrib]

/-- **Sorted eigenvalue list of the Jordan–Wielandt dilation.** The full decreasing-sorted
eigenvalue list of `Ã` is the singular values of `A` followed by their negatives in reverse order —
`(σ₀(A), …, σₙ₋₁(A), -σₙ₋₁(A), …, -σ₀(A))` — which is indeed already sorted decreasing, since
`A.singularValues` is nonnegative and antitone (`Matrix.singularValues_nonneg`,
`Matrix.singularValues_antitone`). -/
theorem Matrix.ofFn_eigenvalues₀_fromBlocks_zero_conjTranspose (A : Matrix ι ι 𝕜) :
    List.ofFn (Matrix.isHermitian_fromBlocks_zero_conjTranspose A).eigenvalues₀
      = List.ofFn A.singularValues ++ (List.ofFn A.singularValues).reverse.map Neg.neg := by
  set hÃ := Matrix.isHermitian_fromBlocks_zero_conjTranspose A
  set sv := A.singularValues
  -- `Ã.charpoly` factors (`charpoly_fromBlocks_zero_conjTranspose_eq_prod`) as
  -- `∏ (X - C (sv i)) * ∏ (X - C (-(sv i)))`, so its roots are the union of the two root multisets.
  have hne1 : (∏ i : Fin (Fintype.card ι), (Polynomial.X - Polynomial.C (sv i : 𝕜))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.X_sub_C_ne_zero (sv i : 𝕜))
  have hne2 : (∏ i : Fin (Fintype.card ι), (Polynomial.X - Polynomial.C (-(sv i) : 𝕜))) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => Polynomial.X_sub_C_ne_zero (-(sv i) : 𝕜))
  have hroots : (Matrix.fromBlocks (0 : Matrix ι ι 𝕜) A Aᴴ 0).charpoly.roots
      = Multiset.map (RCLike.ofReal ∘ sv) Finset.univ.val
        + Multiset.map (RCLike.ofReal ∘ (-sv)) Finset.univ.val := by
    rw [Matrix.charpoly_fromBlocks_zero_conjTranspose_eq_prod, Polynomial.roots_mul
      (mul_ne_zero hne1 hne2), Polynomial.roots_prod _ _ hne1, Polynomial.roots_prod _ _ hne2]
    congr 1
    · simp
    · simp
  -- `List.ofFn (-sv)` and `(List.ofFn sv).reverse.map Neg.neg` are both
  -- `(List.ofFn sv).map Neg.neg` up to reversal, hence permutations of each other
  -- (`List.reverse_perm`, `List.Perm.map`).
  have hnegeq : List.ofFn (-sv) = (List.ofFn sv).map Neg.neg := by
    rw [List.map_ofFn]
    congr 1
  have hperm : List.Perm (List.ofFn (-sv)) ((List.ofFn sv).reverse.map Neg.neg) := by
    rw [hnegeq]
    exact ((List.ofFn sv).reverse_perm.map Neg.neg).symm
  -- Mapping `hroots` through `RCLike.re` and unfolding `Finset.univ.val.map` via
  -- `Fin.univ_val_map` turns `Ã.charpoly.roots.map RCLike.re` into the multiset
  -- `↑(List.ofFn sv) + ↑(List.ofFn (-sv))`, which is the multiset of the claimed list by `hperm`.
  have hsortEq : (Matrix.fromBlocks (0 : Matrix ι ι 𝕜) A Aᴴ 0).charpoly.roots.map RCLike.re
      = ((List.ofFn sv ++ (List.ofFn sv).reverse.map Neg.neg : List ℝ) : Multiset ℝ) := by
    rw [hroots, Multiset.map_add, Multiset.map_map, Multiset.map_map]
    simp only [Function.comp_def, RCLike.ofReal_re]
    rw [Fin.univ_val_map, Fin.univ_val_map, Multiset.coe_add, Multiset.coe_eq_coe]
    exact hperm.append_left _
  -- The claimed list is `Sorted (≥)`: the first block is decreasing and `≥ 0`, the second block is
  -- that block reversed-then-negated (hence decreasing and `≤ 0`), and every first-block entry
  -- dominates every second-block entry — so it is the unique `(≥)`-sort of its own multiset.
  rw [← hÃ.sort_roots_charpoly_eq_eigenvalues₀, hsortEq, Multiset.coe_sort]
  apply List.mergeSort_of_pairwise
  simp_rw [decide_eq_true_eq, List.pairwise_append]
  refine ⟨(Matrix.singularValues_antitone A).sortedGE_ofFn.pairwise, ?_, ?_⟩
  · -- second block (`sv` reversed then negated) is decreasing
    rw [List.pairwise_map, List.pairwise_reverse]
    exact (Matrix.singularValues_antitone A).sortedGE_ofFn.pairwise.imp (fun h => by linarith)
  · -- every entry of the first block (`≥ 0`) dominates every entry of the second block (`≤ 0`)
    intro a ha b hb
    rw [List.mem_ofFn] at ha
    obtain ⟨i, rfl⟩ := ha
    rw [List.mem_map] at hb
    obtain ⟨c, hc, rfl⟩ := hb
    rw [List.mem_reverse, List.mem_ofFn] at hc
    obtain ⟨j, rfl⟩ := hc
    have h1 : 0 ≤ sv i := Matrix.singularValues_nonneg A i
    have h2 : 0 ≤ sv j := Matrix.singularValues_nonneg A j
    linarith

/-- **Pure list-combinatorics lemma behind the Jordan–Wielandt pairwise-product identity.** If `F`'s
(resp. `G`'s) `List.ofFn` is `sv`'s (resp. `sw`'s) `List.ofFn` followed by its own reverse negated —
exactly the shape `ofFn_eigenvalues₀_fromBlocks_zero_conjTranspose` gives for a dilation's sorted
eigenvalues in terms of the underlying matrix's singular values — then the pairwise-product sum
over `F`, `G` is twice the pairwise-product sum over `sv`, `sw`. Isolated as a fact purely about
lists (no matrices involved), since it is the one part of
`sum_eigenvalues₀_fromBlocks_zero_conjTranspose_mul_eq` below not resting on Hermitian-matrix
spectral theory. -/
theorem List.sum_mul_eq_two_mul_sum_of_ofFn_eq_append_reverse_map_neg
    {n k : ℕ} {F G : Fin k → ℝ} {sv sw : Fin n → ℝ}
    (hF : List.ofFn F = List.ofFn sv ++ (List.ofFn sv).reverse.map Neg.neg)
    (hG : List.ofFn G = List.ofFn sw ++ (List.ofFn sw).reverse.map Neg.neg) :
    ∑ i, F i * G i = 2 * ∑ i, sv i * sw i := by
  have hzip : ∀ {m : ℕ} (f g : Fin m → ℝ),
      List.ofFn (fun i => f i * g i) = (List.ofFn f).zipWith (· * ·) (List.ofFn g) := by
    intro m f g
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp
  have hlen : (List.ofFn sv).length = (List.ofFn sw).length := by simp
  have hblock2 : ((List.ofFn sv).reverse.map Neg.neg).zipWith (· * ·)
        ((List.ofFn sw).reverse.map Neg.neg)
      = ((List.ofFn sv).zipWith (· * ·) (List.ofFn sw)).reverse := by
    rw [List.zipWith_map, List.reverse_zipWith hlen]
    simp only [neg_mul_neg]
  rw [← List.sum_ofFn, hzip F G, hF, hG, List.zipWith_append hlen, List.sum_append, hblock2,
    List.sum_reverse, ← hzip sv sw, List.sum_ofFn]
  ring

/-- **Jordan–Wielandt dilation: pairwise-product identity.** For any `A, B : Matrix ι ι 𝕜`, the
full (`2 * Fintype.card ι`-long) eigenvalue lists of their Hermitian dilations `Ã`, `B̃`
(`Matrix.isHermitian_fromBlocks_zero_conjTranspose`) pair up, termwise in decreasing order, to
twice the pairwise product of `A`, `B`'s singular values.

This is the "genuinely new content" needed by the general (non-Hermitian) von Neumann trace
inequality (`Matrix.trace_mul_conjTranspose_le`, `TraceInequality.lean`): feeding it and
`Matrix.IsHermitian.trace_mul_le` (`TraceInequality.lean`) applied to `Ã`, `B̃` gives that
inequality directly, since `Tr(Ã*B̃) = Tr(A*Bᴴ) + Tr(Aᴴ*B) = 2 • Re Tr(A*Bᴴ)` (block-multiply out
`Ã*B̃ = fromBlocks (A*Bᴴ) 0 0 (Aᴴ*B)`, then `Tr(Aᴴ*B) = conj (Tr(A*Bᴴ))` via `Tr(Xᴴ) = conj (Tr X)`
and cyclicity).

Immediate from feeding `ofFn_eigenvalues₀_fromBlocks_zero_conjTranspose` (applied to `A` and to `B`)
into `List.sum_mul_eq_two_mul_sum_of_ofFn_eq_append_reverse_map_neg` below. -/
theorem Matrix.sum_eigenvalues₀_fromBlocks_zero_conjTranspose_mul_eq (A B : Matrix ι ι 𝕜) :
    ∑ i : Fin (Fintype.card (ι ⊕ ι)),
        (Matrix.isHermitian_fromBlocks_zero_conjTranspose A).eigenvalues₀ i *
        (Matrix.isHermitian_fromBlocks_zero_conjTranspose B).eigenvalues₀ i
      = 2 * ∑ i : Fin (Fintype.card ι), A.singularValues i * B.singularValues i :=
  List.sum_mul_eq_two_mul_sum_of_ofFn_eq_append_reverse_map_neg
    (Matrix.ofFn_eigenvalues₀_fromBlocks_zero_conjTranspose A)
    (Matrix.ofFn_eigenvalues₀_fromBlocks_zero_conjTranspose B)
