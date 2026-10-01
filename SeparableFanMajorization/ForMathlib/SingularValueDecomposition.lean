import SeparableFanMajorization.ForMathlib.SingularValue

/-!
# Singular value decomposition of a square matrix

Not in Mathlib. `Mathlib.Analysis.InnerProductSpace.SingularValues` and this project's own
`Matrix.singularValues` (`SingularValue.lean`) only define the *sequence of singular values* — the
square roots of the eigenvalues of `Aᴴ * A`. Neither constructs the actual **factorization**
`A = U * Σ * Vᴴ` with `U`, `V` unitary and `Σ` diagonal. This file builds that factorization,
following the same overall pattern as Mathlib's Hermitian spectral theorem
(`Matrix.IsHermitian.spectral_theorem`, `Matrix.IsHermitian.eigenvectorUnitary`).

## The construction, and why it's harder than the Hermitian case

Write `hAA := (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian : (Aᴴ * A).IsHermitian`.

1. **The right factor `V`**: `hAA.eigenvectorUnitary`, already fully constructed in Mathlib.
2. **The singular values `Σ`**: `Matrix.svdValues`, the (`ι`-indexed, unsorted) square roots of
   `hAA.eigenvalues`.
3. **The left factor `U`**: the genuinely new content (in the Hermitian case `U = V`, so no
   separate construction is needed). For `i` with `svdValues A i ≠ 0`, the vector
   `uᵢ := (svdValues A i)⁻¹ • (A vᵢ)` (`svdLeftVectorPre`) is the unique choice making
   `A vᵢ = σᵢ • uᵢ`, and these are orthonormal (`orthonormal_svdLeftVectorPre`, via the inner
   product identity `inner_toLpLin_eigenvectorBasis`). For `i` with `svdValues A i = 0`,
   `vᵢ ∈ ker A` (`mulVec_eigenvectorBasis_eq_zero_of_svdValues_eq_zero`), so there is no forced
   `uᵢ` — any orthonormal completion works, since that column of `U` only ever gets multiplied
   by `0`.
   Completing a partial orthonormal family to a full basis is
   `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`
   (`Mathlib.Analysis.InnerProductSpace.PiL2`) — the one load-bearing Mathlib lemma this whole
   construction rests on (`exists_svdLeftBasis`).
4. **Reassembly**: `A * V = U * Σ` holds columnwise (`mulVec_eigenvectorBasis_eq_svdValues_smul`),
   hence `A = U * Σ * Vᴴ` since `V * Vᴴ = 1`.

## Main definitions

* `Matrix.svdValues`: the (unsorted, `ι`-indexed) singular values of `A`. Related to
  `Matrix.singularValues` (`SingularValue.lean`) by `svdValues_eq_singularValues_comp`.
* `Matrix.svdLeftVectorPre`: the forced `i`-th left singular vector wherever `svdValues A i ≠ 0`;
  junk `0` elsewhere (replaced by an arbitrary orthonormal completion in `exists_svdLeftBasis`).

## Main results

* `Matrix.mulVec_eigenvectorBasis_eq_zero_of_svdValues_eq_zero`: step 1, the kernel fact.
* `Matrix.orthonormal_svdLeftVectorPre`: step 2, orthonormality of the partial left-vector family.
* `Matrix.exists_svdLeftBasis`: step 3, the orthonormal-basis extension.
* `Matrix.mulVec_eigenvectorBasis_eq_svdValues_smul`: step 4a, `A vⱼ = σⱼ • uⱼ`.
* `Matrix.exists_svd`: step 4b, the final theorem, `∃ U V, A = U * Σ * Vᴴ`.

## Why this is worth building

`exists_svd` supplies the construction behind `Matrix.exists_isometryPair_trace_eq_kyFanNorm`
(`KyFanNorm.lean`): taking `U`, `V` to be the top-`k` (by singular value) columns of `A`'s SVD
realizes `A.kyFanNorm k` exactly as `Tr(Uᴴ * A * V)` for an isometry pair `U, V`. That lemma is the
"full SVD" variational formula shared by both genuinely new results built on top of it:
`KyFanCauchySchwarz.lean`'s sandwiched-contraction Ky Fan bound
(`Matrix.kyFanNorm_sqrt_mul_contraction_mul_sqrt_le_max`) and `KyFanNorm.lean`'s triangle inequality
(`Matrix.kyFanNorm_add_le`).
-/

open Matrix
open scoped ComplexOrder

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

/-- The (unsorted, `ι`-indexed) singular values of `A`: the square roots of the eigenvalues of the
positive semidefinite Hermitian matrix `Aᴴ * A`, read out via `Matrix.IsHermitian.eigenvalues`
rather than `.eigenvalues₀`. See `Matrix.singularValues` (`SingularValue.lean`) for the sorted
version, and `svdValues_eq_singularValues_comp` for how the two relate. -/
noncomputable def Matrix.svdValues (A : Matrix ι ι 𝕜) : ι → ℝ :=
  fun i => Real.sqrt ((Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i)

/-- `svdValues A` is nonnegative, being a square root. -/
theorem Matrix.svdValues_nonneg (A : Matrix ι ι 𝕜) (i : ι) : 0 ≤ A.svdValues i :=
  Real.sqrt_nonneg _

/-- The `Σ` factor of the SVD, `Matrix.diagonal (RCLike.ofReal ∘ A.svdValues)`, is Hermitian. -/
theorem Matrix.isHermitian_diagonal_svdValues (A : Matrix ι ι 𝕜) :
    (Matrix.diagonal (RCLike.ofReal (K := 𝕜) ∘ A.svdValues)).IsHermitian := by
  rw [Matrix.isHermitian_diagonal_iff]
  exact fun i => RCLike.conj_ofReal (A.svdValues i)

/-- The `Σ` factor of the SVD, `Matrix.diagonal (RCLike.ofReal ∘ A.svdValues)`, is positive
semidefinite. -/
theorem Matrix.posSemidef_diagonal_svdValues (A : Matrix ι ι 𝕜) :
    (Matrix.diagonal (RCLike.ofReal (K := 𝕜) ∘ A.svdValues)).PosSemidef := by
  rw [Matrix.posSemidef_diagonal_iff]
  exact fun i => RCLike.ofReal_nonneg.mpr (A.svdValues_nonneg i)

/-- `(svdValues A i) ^ 2` is the `i`-th eigenvalue of `Aᴴ * A`. -/
theorem Matrix.svdValues_sq_eq_eigenvalues (A : Matrix ι ι 𝕜) (i : ι) :
    (A.svdValues i) ^ 2
      = (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i :=
  Real.sq_sqrt (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i)

/-- `Matrix.svdValues` (unsorted, indexed by `ι`) and `Matrix.singularValues` (`SingularValue.lean`,
sorted, indexed by `Fin (Fintype.card ι)`) are the same underlying data, related by the same
reindexing equivalence `Fintype.equivOfCardEq (Fintype.card_fin _)` that Mathlib uses to relate
`Matrix.IsHermitian.eigenvalues` to `.eigenvalues₀`. -/
theorem Matrix.svdValues_eq_singularValues_comp (A : Matrix ι ι 𝕜) :
    A.svdValues = A.singularValues ∘
      (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm := by
  funext i
  simp [Matrix.svdValues, Matrix.singularValues, Matrix.IsHermitian.eigenvalues]

/-- **Step 1: the kernel fact.** If `svdValues A j = 0`, the `j`-th eigenvector of `Aᴴ * A` lies in
`ker A`, via `(Aᴴ*A) vⱼ = (svdValues A j)^2 • vⱼ = 0` and `ker (Aᴴ * A) = ker A`
(`Matrix.conjTranspose_mul_self_mulVec_eq_zero`). This is why `svdLeftVectorPre` is junk-valued
exactly where `svdValues A i = 0`: there is no forced left singular vector to recover there. -/
theorem Matrix.mulVec_eigenvectorBasis_eq_zero_of_svdValues_eq_zero (A : Matrix ι ι 𝕜) {j : ι}
    (h : A.svdValues j = 0) :
    A *ᵥ ⇑((Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvectorBasis j) = 0 := by
  set hAA := (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian
  have heig : hAA.eigenvalues j = 0 := by
    rw [← A.svdValues_sq_eq_eigenvalues j, h]; ring
  rw [← Matrix.conjTranspose_mul_self_mulVec_eq_zero A, hAA.mulVec_eigenvectorBasis, heig,
    zero_smul]

/-- **The forced left singular vector**, wherever `svdValues A i ≠ 0`: `σᵢ⁻¹ • (A vᵢ)`, where
`vᵢ := (Aᴴ*A)`'s `i`-th eigenvector. This is the unique choice making `A vᵢ = σᵢ • uᵢ`. Junk-valued
`0` when `svdValues A i = 0` — `exists_svd`'s reconstruction never depends on this junk value, since
it's always multiplied by the singular value `0`; `exists_svdLeftBasis` replaces exactly these junk
entries with an arbitrary orthonormal completion.

Uses `Matrix.toLpLin 2 2 A` rather than `A *ᵥ ⇑(...)` directly: `EuclideanSpace` (built from
`WithLp`/`PiLp`, a genuine `structure`) is not defeq to `ι → 𝕜`, so `A *ᵥ ⇑(...)` does not typecheck
as this definition's return type. -/
noncomputable def Matrix.svdLeftVectorPre (A : Matrix ι ι 𝕜) (i : ι) : EuclideanSpace 𝕜 ι :=
  (A.svdValues i)⁻¹ • Matrix.toLpLin 2 2 A
    ((Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvectorBasis i)

omit [DecidableEq ι] in
/-- The adjoint identity `⟪A x, A y⟫ = ⟪x, (Aᴴ * A) y⟫`, in raw `dotProduct` form. -/
theorem Matrix.star_mulVec_dotProduct_mulVec (A : Matrix ι ι 𝕜) (x y : ι → 𝕜) :
    star (A *ᵥ x) ⬝ᵥ (A *ᵥ y) = star x ⬝ᵥ ((Aᴴ * A) *ᵥ y) := by
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec]

/-- **Step 2.** The inner product of `A` applied to two eigenvectors of `Aᴴ * A`:
`⟪A vᵢ, A vⱼ⟫ = if i = j then λᵢ else 0`, where `λ := hAA.eigenvalues`. Combines the adjoint
identity `star_mulVec_dotProduct_mulVec` with `Aᴴ * A`'s eigenvalue equation and the orthonormality
of its eigenvector basis. -/
theorem Matrix.inner_toLpLin_eigenvectorBasis (A : Matrix ι ι 𝕜) (hAA : (Aᴴ * A).IsHermitian)
    (i j : ι) :
    inner 𝕜 (Matrix.toLpLin 2 2 A (hAA.eigenvectorBasis i))
        (Matrix.toLpLin 2 2 A (hAA.eigenvectorBasis j))
      = if i = j then ((hAA.eigenvalues i : ℝ) : 𝕜) else 0 := by
  have hstep : inner 𝕜 (Matrix.toLpLin 2 2 A (hAA.eigenvectorBasis i))
        (Matrix.toLpLin 2 2 A (hAA.eigenvectorBasis j))
      = (hAA.eigenvalues j : ℝ) •
        (star ⇑(hAA.eigenvectorBasis i) ⬝ᵥ ⇑(hAA.eigenvectorBasis j)) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [Matrix.toLpLin_apply, WithLp.ofLp_toLp]
    rw [dotProduct_comm (A *ᵥ ⇑(hAA.eigenvectorBasis j)) (star (A *ᵥ ⇑(hAA.eigenvectorBasis i))),
      A.star_mulVec_dotProduct_mulVec, hAA.mulVec_eigenvectorBasis, dotProduct_smul]
  have hconv : star ⇑(hAA.eigenvectorBasis i) ⬝ᵥ ⇑(hAA.eigenvectorBasis j)
      = inner 𝕜 (hAA.eigenvectorBasis i) (hAA.eigenvectorBasis j) := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
  rw [hstep, hconv, orthonormal_iff_ite.mp hAA.eigenvectorBasis.orthonormal i j]
  split_ifs with h
  · subst h
    rw [RCLike.real_smul_eq_coe_smul (K := 𝕜), smul_eq_mul, mul_one]
  · rw [smul_zero]

/-- **Step 2, continued.** `svdLeftVectorPre` is orthonormal on `{i | svdValues A i ≠ 0}`: for
`i, j` in this set, `⟪uᵢ, uⱼ⟫ = (σᵢσⱼ)⁻¹ ⟪A vᵢ, A vⱼ⟫ = (σᵢσⱼ)⁻¹ λⱼ δᵢⱼ`, which is `1` when `i = j`
(cancelling `σᵢ² / σᵢ²`, using `svdValues_sq_eq_eigenvalues`) and `0` otherwise. -/
theorem Matrix.orthonormal_svdLeftVectorPre (A : Matrix ι ι 𝕜) :
    Orthonormal 𝕜 ({i : ι | A.svdValues i ≠ 0}.restrict A.svdLeftVectorPre) := by
  classical
  set hAA := (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian
  rw [orthonormal_iff_ite]
  rintro ⟨i, hi⟩ ⟨j, hj⟩
  simp only [Set.restrict_apply, Matrix.svdLeftVectorPre, Subtype.mk_eq_mk]
  rw [RCLike.real_smul_eq_coe_smul (K := 𝕜) (A.svdValues i)⁻¹,
    RCLike.real_smul_eq_coe_smul (K := 𝕜) (A.svdValues j)⁻¹, inner_smul_left, inner_smul_right,
    RCLike.conj_ofReal, A.inner_toLpLin_eigenvectorBasis hAA i j]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, if_pos rfl,
      show (hAA.eigenvalues i : ℝ) = (A.svdValues i) ^ 2 from
        (A.svdValues_sq_eq_eigenvalues i).symm]
    have hne' : ((A.svdValues i : ℝ) : 𝕜) ≠ 0 := RCLike.ofReal_ne_zero.mpr hi
    push_cast
    field_simp
  · rw [if_neg hij, if_neg hij, mul_zero, mul_zero]

/-- **Step 3: extend the partial orthonormal family to a full orthonormal basis of `ι`.** This is
the one genuinely new piece beyond the Hermitian spectral theorem: applies
`Orthonormal.exists_orthonormalBasis_extension_of_card_eq` to `orthonormal_svdLeftVectorPre` to
produce a full orthonormal basis `w` of `EuclideanSpace 𝕜 ι` agreeing with `svdLeftVectorPre` on
`{i | svdValues A i ≠ 0}`. `w`'s columns become the left factor `U` of the SVD in `exists_svd`. -/
theorem Matrix.exists_svdLeftBasis (A : Matrix ι ι 𝕜) :
    ∃ w : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι),
      ∀ i : ι, A.svdValues i ≠ 0 → w i = A.svdLeftVectorPre i := by
  have hcard : Module.finrank 𝕜 (EuclideanSpace 𝕜 ι) = Fintype.card ι := finrank_euclideanSpace
  obtain ⟨w, hw⟩ :=
    A.orthonormal_svdLeftVectorPre.exists_orthonormalBasis_extension_of_card_eq hcard
  exact ⟨w, hw⟩

/-- **Step 4a.** `A vⱼ = σⱼ • uⱼ` for every `j`, where `uⱼ := w j` for any orthonormal basis `w`
extending `svdLeftVectorPre` (as produced by `exists_svdLeftBasis`). Combines the kernel fact
(step 1, the `σⱼ = 0` case) with `w`'s defining property (the `σⱼ ≠ 0` case). -/
theorem Matrix.mulVec_eigenvectorBasis_eq_svdValues_smul (A : Matrix ι ι 𝕜)
    (w : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι))
    (hw : ∀ i : ι, A.svdValues i ≠ 0 → w i = A.svdLeftVectorPre i) (j : ι) :
    A *ᵥ ⇑((Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvectorBasis j)
      = (A.svdValues j : 𝕜) • ⇑(w j) := by
  set hAA := (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian
  by_cases hj : A.svdValues j = 0
  · rw [Matrix.mulVec_eigenvectorBasis_eq_zero_of_svdValues_eq_zero A hj, hj]
    simp
  · have hwj : ⇑(w j) = ((A.svdValues j)⁻¹ : 𝕜) • (A *ᵥ ⇑(hAA.eigenvectorBasis j)) := by
      rw [hw j hj]
      simp only [Matrix.svdLeftVectorPre, RCLike.real_smul_eq_coe_smul (K := 𝕜),
        RCLike.ofReal_inv, WithLp.ofLp_smul, Matrix.toLpLin_apply]
    rw [hwj, smul_smul, mul_inv_cancel₀ (RCLike.ofReal_ne_zero.mpr hj), one_smul]

/-- **Singular value decomposition.** Every square matrix `A` factors as `A = U * Σ * Vᴴ` with `U`,
`V` unitary and `Σ` diagonal with nonnegative entries (`Matrix.svdValues A`, cast to `𝕜` via
`RCLike.ofReal`, matching `Matrix.IsHermitian.spectral_theorem`'s convention).

Construction: `V := hAA.eigenvectorUnitary`
(`hAA := (posSemidef_conjTranspose_mul_self A).isHermitian`), `U` built from the basis `w` given by
`exists_svdLeftBasis` the same way `V` is built from `hAA.eigenvectorBasis`. `A * V = U * Σ` holds
columnwise by `mulVec_eigenvectorBasis_eq_svdValues_smul` (step 4a), and `A = U * Σ * Vᴴ` follows
by right-multiplying by `Vᴴ` and using `V * Vᴴ = 1`. -/
theorem Matrix.exists_svd (A : Matrix ι ι 𝕜) :
    ∃ (U V : Matrix.unitaryGroup ι 𝕜),
      A = (U : Matrix ι ι 𝕜) * Matrix.diagonal (RCLike.ofReal ∘ A.svdValues) *
        (V : Matrix ι ι 𝕜)ᴴ := by
  classical
  set hAA := (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian with hAA_def
  obtain ⟨w, hw⟩ := A.exists_svdLeftBasis
  set V : Matrix.unitaryGroup ι 𝕜 := hAA.eigenvectorUnitary
  -- `U`, built from `w` exactly the way `V` is built from `hAA.eigenvectorBasis`
  -- (`Matrix.IsHermitian.eigenvectorUnitary`).
  set U : Matrix.unitaryGroup ι 𝕜 :=
    ⟨(EuclideanSpace.basisFun ι 𝕜).toBasis.toMatrix w.toBasis,
      (EuclideanSpace.basisFun ι 𝕜).toMatrix_orthonormalBasis_mem_unitary w⟩
  refine ⟨U, V, ?_⟩
  -- `U`'s `j`-th column is `w j`, by the same defeq that makes
  -- `Matrix.IsHermitian.eigenvectorUnitary_col_eq` an `rfl` for `hAA.eigenvectorBasis`.
  have hU_col : ∀ j : ι, Matrix.col (U : Matrix ι ι 𝕜) j = ⇑(w j) := fun _ => rfl
  have hU_mulVec : ∀ j : ι, (U : Matrix ι ι 𝕜) *ᵥ Pi.single j (1 : 𝕜) = ⇑(w j) := fun j => by
    rw [Matrix.mulVec_single_one, hU_col]
  -- `A * V = U * Σ`, shown columnwise via `mulVec_eigenvectorBasis_eq_svdValues_smul` (step 4a).
  have hcol_eq : ∀ j : ι, (A * (V : Matrix ι ι 𝕜)).col j
      = ((U : Matrix ι ι 𝕜) * Matrix.diagonal (RCLike.ofReal ∘ A.svdValues)).col j := by
    intro j
    rw [← Matrix.mulVec_single_one, ← Matrix.mulVec_single_one, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec]
    have hVcol : (V : Matrix ι ι 𝕜) *ᵥ Pi.single j (1 : 𝕜) = ⇑(hAA.eigenvectorBasis j) :=
      hAA.eigenvectorUnitary_mulVec j
    have hDiagCol : Matrix.diagonal (RCLike.ofReal ∘ A.svdValues) *ᵥ Pi.single j (1 : 𝕜)
        = (A.svdValues j : 𝕜) • Pi.single j (1 : 𝕜) := by
      rw [Matrix.diagonal_mulVec_single]
      funext i
      simp [Pi.single_apply, Function.comp_apply]
    rw [hVcol, hDiagCol, Matrix.mulVec_smul, hU_mulVec j]
    exact A.mulVec_eigenvectorBasis_eq_svdValues_smul w hw j
  have hAV : A * (V : Matrix ι ι 𝕜)
      = (U : Matrix ι ι 𝕜) * Matrix.diagonal (RCLike.ofReal ∘ A.svdValues) :=
    Matrix.ext fun i j => congrFun (hcol_eq j) i
  -- `A = U * Σ * Vᴴ` follows from `A * V = U * Σ` by right-multiplying by `Vᴴ`, using `V * Vᴴ = 1`
  -- (`Matrix.mem_unitaryGroup_iff`, as in `Matrix.singularValues_unitary_conj`,
  -- `SingularValue.lean`).
  have hVV : (V : Matrix ι ι 𝕜) * (V : Matrix ι ι 𝕜)ᴴ = 1 := by
    have h := Matrix.mem_unitaryGroup_iff.mp V.2
    rwa [Matrix.star_eq_conjTranspose] at h
  calc A = A * (V : Matrix ι ι 𝕜) * (V : Matrix ι ι 𝕜)ᴴ := by rw [mul_assoc, hVV, mul_one]
    _ = (U : Matrix ι ι 𝕜) * Matrix.diagonal (RCLike.ofReal ∘ A.svdValues) *
        (V : Matrix ι ι 𝕜)ᴴ := by rw [hAV]
