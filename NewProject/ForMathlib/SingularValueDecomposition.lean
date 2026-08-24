import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.Matrix
import Mathlib.LinearAlgebra.UnitaryGroup
import NewProject.ForMathlib.SingularValue

/-!
# Singular value decomposition of a square matrix

Not in Mathlib. `Mathlib.Analysis.InnerProductSpace.SingularValues` (`LinearMap.singularValues`)
and this project's own `Matrix.singularValues` (`SingularValue.lean`) only define the *sequence of
singular values* — the square roots of the eigenvalues of `Aᴴ * A`. Neither Mathlib file (checked
`SingularValues.lean`, `Analysis/Matrix/Spectrum.lean`, `Analysis/InnerProductSpace/Spectrum.lean`)
constructs the actual **factorization** `A = U * Σ * Vᴴ` with `U`, `V` unitary and `Σ` diagonal.
This file builds that factorization directly, following the same overall pattern Mathlib uses for
the Hermitian spectral theorem (`Matrix.IsHermitian.spectral_theorem`,
`Matrix.IsHermitian.eigenvectorUnitary`).

## The construction, and why it's harder than the Hermitian case

Write `hAA := (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian : (Aᴴ * A).IsHermitian`.

1. **The right factor `V`**: just `hAA.eigenvectorUnitary`, the unitary matrix of eigenvectors of
   `Aᴴ * A`. Already fully constructed in Mathlib — no new work needed.
2. **The singular values `Σ`**: `Matrix.svdValues` below, the (`ι`-indexed, unsorted) square roots
   of `hAA.eigenvalues`. Related to the existing (`Fin (Fintype.card ι)`-indexed, sorted)
   `Matrix.singularValues` (`SingularValue.lean`) by the same reindexing equivalence
   `Fintype.equivOfCardEq (Fintype.card_fin _)` that already relates `hAA.eigenvalues`/
   `hAA.eigenvalues₀` (`svdValues_eq_singularValues_comp`).
3. **The left factor `U`**: this is the genuinely new content, and the reason the Hermitian
   spectral theorem doesn't already give this for free (there, `U = V`, so no separate
   construction is needed). For each `i` with `svdValues A i ≠ 0`, the vector
   `uᵢ := (svdValues A i)⁻¹ • (A *ᵥ vᵢ)` (`svdLeftVectorPre`) is forced: it's the unique choice
   making `A vᵢ = σᵢ • uᵢ`, and a short computation (`⟪uᵢ, uⱼ⟫ = (σᵢσⱼ)⁻¹ ⟪A vᵢ, A vⱼ⟫ = (σᵢσⱼ)⁻¹ σⱼ²
   ⟪vᵢ, vⱼ⟫ = δᵢⱼ`, using `Aᴴ * A vⱼ = σⱼ² vⱼ`) shows these are orthonormal. But for `i` with
   `svdValues A i = 0`, `vᵢ ∈ ker A` (`mulVec_eigenvectorBasis_eq_zero_of_svdValues_eq_zero`), so
   there is *no* forced value for `uᵢ` — any orthonormal completion works, since that column of `U`
   only ever gets multiplied by the singular value `0` in the final reconstruction. Completing a
   partial orthonormal family (indexed by a *subset* of `ι`) to a full orthonormal basis of `ι` is
   exactly `Orthonormal.exists_orthonormalBasis_extension_of_card_eq`
   (`Mathlib.Analysis.InnerProductSpace.PiL2`) — the one load-bearing Mathlib lemma this whole
   construction rests on.
4. **Reassembly**: `A * V = U * Σ` holds columnwise (`A *ᵥ vⱼ = σⱼ • uⱼ`, both the `σⱼ ≠ 0` case
   from step 3's defining property and the `σⱼ = 0` case from step 1's kernel fact), hence
   `A = U * Σ * Vᴴ` since `V * Vᴴ = 1`.

## Main definitions

* `Matrix.svdValues`: the (unsorted, `ι`-indexed) singular values of `A`, i.e. the square roots of
  the eigenvalues of `Aᴴ * A` read out via `Matrix.IsHermitian.eigenvalues` rather than
  `.eigenvalues₀`. Related to `Matrix.singularValues` (`SingularValue.lean`) by
  `svdValues_eq_singularValues_comp`.
* `Matrix.svdLeftVectorPre`: the forced value of the `i`-th left singular vector wherever
  `svdValues A i ≠ 0`; junk-valued `0` elsewhere (replaced by an arbitrary orthonormal completion
  in `exists_svdLeftBasis`).

## Main results (roadmap; `sorry`d pending the geometric argument in step 3 above)

* `Matrix.mulVec_eigenvectorBasis_eq_zero_of_svdValues_eq_zero`: step 1, the kernel fact.
* `Matrix.exists_svdLeftBasis`: step 3, the orthonormal-basis extension.
* `Matrix.exists_svd`: the final theorem, `∃ U V, A = U * Σ * Vᴴ`.

## Why this is worth building

Once `exists_svd` lands, it gives the variational characterization
`Σᵢ₌₀ᵏ⁻¹ σᵢ(A) = max` over rank-`k` orthonormal frames `(u, v)` of `Σᵢ |⟨uᵢ, A vᵢ⟩|`, which is the
"full SVD" route to Ky Fan subadditivity for `Matrix.kyFanNorm` (`KyFanNorm.lean`) discussed
alongside `Matrix.singularValues_unitary_conj` (`SingularValue.lean`) — an alternative to the
Jordan-Wielandt Hermitian-dilation route, at the cost of this file's construction instead of a
dilation argument reusing the existing `Matrix.IsHermitian.topProjector` machinery
(`SpectralDecomposition.lean`).
-/

open Matrix
open scoped ComplexOrder

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

/-- The (unsorted, `ι`-indexed) singular values of `A`: the square roots of the eigenvalues of the
positive semidefinite Hermitian matrix `Aᴴ * A`, read out via `Matrix.IsHermitian.eigenvalues`
(indexed by `ι`, the matrix's own index type) rather than `.eigenvalues₀` (indexed by
`Fin (Fintype.card ι)`, sorted). See `Matrix.singularValues` (`SingularValue.lean`) for the sorted
version, and `svdValues_eq_singularValues_comp` for how the two relate. -/
noncomputable def Matrix.svdValues (A : Matrix ι ι 𝕜) : ι → ℝ :=
  fun i => Real.sqrt ((Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i)

/-- `svdValues A` is nonnegative, being a square root. -/
theorem Matrix.svdValues_nonneg (A : Matrix ι ι 𝕜) (i : ι) : 0 ≤ A.svdValues i :=
  Real.sqrt_nonneg _

/-- `(svdValues A i) ^ 2` is exactly the `i`-th eigenvalue of `Aᴴ * A`: immediate from
`Real.sq_sqrt`, using `Matrix.eigenvalues_conjTranspose_mul_self_nonneg` for nonnegativity. Used to
turn `⟪A vᵢ, A vⱼ⟫ = ⟪vᵢ, (Aᴴ*A) vⱼ⟫` computations back into `σⱼ² ⟪vᵢ, vⱼ⟫` in the orthonormality
argument for `exists_svdLeftBasis`.

Proved as a direct term, relying on `A.svdValues i` unfolding (definitionally) to
`Real.sqrt (...)`, in the same style as `svdValues_nonneg` above — *not* via `rw`, since
`Matrix.svdValues` is a plain `def` rather than an equation/`Iff` lemma, and so is not a valid `rw`
argument. -/
theorem Matrix.svdValues_sq_eq_eigenvalues (A : Matrix ι ι 𝕜) (i : ι) :
    (A.svdValues i) ^ 2
      = (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvalues i :=
  Real.sq_sqrt (Matrix.eigenvalues_conjTranspose_mul_self_nonneg A i)

/-- `Matrix.svdValues` (unsorted, indexed by `ι`) and `Matrix.singularValues` (`SingularValue.lean`,
sorted, indexed by `Fin (Fintype.card ι)`) are the same underlying data, related by the same
reindexing equivalence `Fintype.equivOfCardEq (Fintype.card_fin _)` that Mathlib uses to relate
`Matrix.IsHermitian.eigenvalues` to `.eigenvalues₀` (`Analysis/Matrix/Spectrum.lean`). Expected
proof: unfold `Matrix.IsHermitian.eigenvalues`'s definition (`eigenvalues := fun i => eigenvalues₀
(e.symm i)`) on both sides — should close by `rfl`/`unfold`, since both `Matrix.svdValues` and
`Matrix.singularValues` are built from the *same* Hermitian proof term
`(Matrix.posSemidef_conjTranspose_mul_self A).isHermitian` (equal up to `Prop` proof irrelevance).
`sorry`d only because this hasn't been compile-checked yet, not because the argument is expected to
be hard. -/
theorem Matrix.svdValues_eq_singularValues_comp (A : Matrix ι ι 𝕜) :
    A.svdValues = A.singularValues ∘
      (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))).symm := by
  sorry

/-- **Step 1: the kernel fact.** If `svdValues A j = 0`, the `j`-th eigenvector of `Aᴴ * A` lies in
the kernel of `A`. Proof idea: `‖A vⱼ‖² = ⟪vⱼ, (Aᴴ*A) vⱼ⟫ = ⟪vⱼ, (svdValues A j)^2 • vⱼ⟫ = 0` (using
`Matrix.IsHermitian.mulVec_eigenvectorBasis` on `Aᴴ * A` and `svdValues_sq_eq_eigenvalues`), so
`A vⱼ = 0` by positive-definiteness of the inner product. This is why `svdLeftVectorPre` is
junk-valued exactly where `svdValues A i = 0`: there is no forced left singular vector to recover
there, and `exists_svd`'s reconstruction doesn't need one, since those columns get multiplied by
singular value `0` anyway. -/
theorem Matrix.mulVec_eigenvectorBasis_eq_zero_of_svdValues_eq_zero (A : Matrix ι ι 𝕜) {j : ι}
    (h : A.svdValues j = 0) :
    A *ᵥ ⇑((Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvectorBasis j) = 0 := by
  sorry

/-- **The forced left singular vector**, wherever `svdValues A i ≠ 0`: `σᵢ⁻¹ • (A vᵢ)`, where
`vᵢ := (Aᴴ*A)`'s `i`-th eigenvector (`hAA.eigenvectorBasis i`). This is the unique choice making
`A vᵢ = σᵢ • uᵢ`. Junk-valued `0` (via `(0 : ℝ)⁻¹ = 0`) when `svdValues A i = 0` — `exists_svd`'s
reconstruction never depends on this junk value, since it's always multiplied by the singular
value `0`; `exists_svdLeftBasis` (step 3) replaces exactly these junk entries with an arbitrary
orthonormal completion.

`A vᵢ` is computed via `Matrix.toLpLin 2 2 A`, the `EuclideanSpace`-typed repackaging of `A *ᵥ ·`
(the same device `EigenvalueMonotonicity.lean`'s `hAv`/`hAxeq` use), rather than `A *ᵥ ⇑(...)`
directly: `WithLp`/`PiLp` (which `EuclideanSpace` is built from) is a genuine `structure`, not a
reducible type synonym, so `A *ᵥ ⇑(hAA.eigenvectorBasis i) : ι → 𝕜` is *not* defeq to
`EuclideanSpace 𝕜 ι` and does not typecheck as this definition's return value. -/
noncomputable def Matrix.svdLeftVectorPre (A : Matrix ι ι 𝕜) (i : ι) : EuclideanSpace 𝕜 ι :=
  (A.svdValues i)⁻¹ • Matrix.toLpLin 2 2 A
    ((Matrix.posSemidef_conjTranspose_mul_self A).isHermitian.eigenvectorBasis i)

/- **Step 2 (internal to step 3's proof, not stated standalone): orthonormality of the partial
left-singular-vector family.** On `s := {i | svdValues A i ≠ 0}`, `svdLeftVectorPre` is orthonormal:
for `i, j ∈ s`, `⟪uᵢ, uⱼ⟫ = (σᵢσⱼ)⁻¹ ⟪A vᵢ, A vⱼ⟫ = (σᵢσⱼ)⁻¹ ⟪vᵢ, (Aᴴ*A) vⱼ⟫ = (σᵢσⱼ)⁻¹ σⱼ² ⟪vᵢ,
vⱼ⟫ = (σᵢσⱼ)⁻¹ σⱼ² δᵢⱼ`, which is `1` when `i = j` (cancelling `σᵢ² / σᵢ²`) and `0` otherwise. Needs
an inner-product/`dotProduct` identity relating `⟪A x, A y⟫` to `⟪x, (Aᴴ*A) y⟫` (e.g. via
`EuclideanSpace.inner_eq_star_dotProduct` plus `Matrix.dotProduct_mulVec`/`star_mulVec`-style
rewriting, in the same style as `Matrix.IsHermitian.trace_mul_topProjector_self`'s orthonormality
computation in `SpectralDecomposition.lean`). -/

/-- **Step 3: extend the partial orthonormal family to a full orthonormal basis of `ι`.** This is
the one genuinely new piece beyond the Hermitian spectral theorem: applies
`Orthonormal.exists_orthonormalBasis_extension_of_card_eq` (`Mathlib.Analysis.InnerProductSpace.PiL2`)
with `v := A.svdLeftVectorPre`, `s := {i : ι | A.svdValues i ≠ 0}`, and the orthonormality fact from
step 2 above (`hv : Orthonormal 𝕜 (s.restrict v)`) to produce a full orthonormal basis `w` of
`EuclideanSpace 𝕜 ι` agreeing with `svdLeftVectorPre` on `s`. `w`'s columns (packaged as a unitary
matrix the same way `Matrix.IsHermitian.eigenvectorUnitary` packages `eigenvectorBasis`, via
`(EuclideanSpace.basisFun ι 𝕜).toBasis.toMatrix w.toBasis`) become the left factor `U` of the SVD in
`exists_svd`. -/
theorem Matrix.exists_svdLeftBasis (A : Matrix ι ι 𝕜) :
    ∃ w : OrthonormalBasis ι 𝕜 (EuclideanSpace 𝕜 ι),
      ∀ i : ι, A.svdValues i ≠ 0 → w i = A.svdLeftVectorPre i := by
  sorry

/-- **Singular value decomposition.** Every square matrix `A` factors as `A = U * Σ * Vᴴ` with `U`,
`V` unitary and `Σ` diagonal with nonnegative entries (`Matrix.svdValues A`, cast to `𝕜` via
`RCLike.ofReal`, matching `Matrix.IsHermitian.spectral_theorem`'s convention of
`diagonal (RCLike.ofReal ∘ hA.eigenvalues)`).

Construction: `V := hAA.eigenvectorUnitary` (`hAA := (posSemidef_conjTranspose_mul_self A).isHermitian`),
`U` built from the basis `w` given by `exists_svdLeftBasis` (step 3) the same way `V` is built from
`hAA.eigenvectorBasis`. Reassembly (step 4): `A * V = U * Σ` holds columnwise —
`A *ᵥ (V's j-th column) = A.svdValues j • (U's j-th column)` — by cases on whether `svdValues A j`
is zero: if so, both sides are `0` (LHS by `mulVec_eigenvectorBasis_eq_zero_of_svdValues_eq_zero`,
step 1; RHS trivially, `0 • _ = 0`); if not, this is exactly `exists_svdLeftBasis`'s defining
property after unfolding `svdLeftVectorPre` and cancelling `σⱼ • σⱼ⁻¹ = 1`. Then
`A = U * Σ * Vᴴ` follows from `A * V = U * Σ` by right-multiplying both sides by `Vᴴ` and using
`V * Vᴴ = 1` (`Matrix.mem_unitaryGroup_iff`, as in `Matrix.singularValues_unitary_conj`,
`SingularValue.lean`). -/
theorem Matrix.exists_svd (A : Matrix ι ι 𝕜) :
    ∃ (U V : Matrix.unitaryGroup ι 𝕜),
      A = (U : Matrix ι ι 𝕜) * Matrix.diagonal (RCLike.ofReal ∘ A.svdValues) *
        (V : Matrix ι ι 𝕜)ᴴ := by
  sorry
