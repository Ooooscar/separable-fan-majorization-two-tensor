import SeparableFanMajorization.ForMathlib.MatrixSqrt
import SeparableFanMajorization.ForMathlib.SingularValue

/-!
# Absolute value of a square matrix

Not in Mathlib. The absolute value `|M| := (Mᴴ * M).sqrt` (`Matrix.PosSemidef.sqrt`,
`MatrixSqrt.lean`) of a general square matrix `M` (not necessarily Hermitian/positive
semidefinite), a step towards `SumKroneckerWeakMajorization.lean`'s [WZ26] reduction
(`|A l ⊗ B l| = |A l| ⊗ |B l|`) to the positive semidefinite case already proved in
`SumKroneckerMajorization.lean`.

## Main definitions

* `Matrix.abs`: `|M|`, the absolute value of a square matrix `M`.

## Main results

* `Matrix.posSemidef_abs`: `|M|` is positive semidefinite.
* `Matrix.PosSemidef.abs_eq_self`/`Matrix.PosSemidef.singularValues_eq_eigenvalues₀`: for
  positive semidefinite `X`, `X.abs = X`, hence `X.singularValues = hX.isHermitian.eigenvalues₀`.
* `Matrix.abs_kronecker`: `|A ⊗ₖ B| = |A| ⊗ₖ |B|`, via `Matrix.PosSemidef.sqrt_kronecker`
  (`MatrixSqrt.lean`) plus the Kronecker mixed-product identity `(A ⊗ₖ B)ᴴ * (A ⊗ₖ B) = (Aᴴ * A) ⊗ₖ
  (Bᴴ * B)` (`Matrix.conjTranspose_kronecker`, `Matrix.mul_kronecker_mul`).
* `Matrix.IsHermitian.isHermitian_cfc`/`Matrix.IsHermitian.eigenvalues₀_cfc`: general
  (`Matrix.abs`-independent) facts about the Hermitian functional calculus `hA.cfc f`
  (`MatrixSqrt.lean`): it is again Hermitian, and if `f` preserves and reflects the `≥` order on
  `A`'s eigenvalues, its (decreasing-sorted) eigenvalues are `f` applied to `A`'s.
* `Matrix.abs_eigenvalues₀_eq_singularValues`: `|M|`'s (decreasing-sorted) eigenvalues are exactly
  `M.singularValues`.
* `Matrix.singularValues_conjTranspose`: `σ(Mᴴ) = σ(M)`. *Cheap*, does not need a polar
  decomposition: `Mᴴ * M` and `M * Mᴴ` are square same-size matrices, so they share a
  characteristic polynomial (`Matrix.charpoly_mul_comm`), hence the same `eigenvalues₀`
  (`Matrix.IsHermitian.eigenvalues₀_eq_of_charpoly_eq`, `SingularValue.lean`), hence the same
  square roots.
* `Matrix.PosSemidef.sqrt_singularValues`: for positive semidefinite `X`, `X.sqrt`'s singular
  values are `Real.sqrt` applied to `X`'s. Specializing to the top singular value (the operator
  norm) recovers `‖X.sqrt‖² = ‖X‖`.
-/

open Matrix
open scoped Kronecker ComplexOrder

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

/-- The absolute value `|M|` of a square matrix `M`: the positive semidefinite square root of
`Mᴴ * M`. -/
noncomputable def Matrix.abs (M : Matrix ι ι 𝕜) : Matrix ι ι 𝕜 :=
  (Matrix.posSemidef_conjTranspose_mul_self M).sqrt

/-- `|M|` is positive semidefinite, being a square root (`Matrix.PosSemidef.posSemidef_sqrt`,
`MatrixSqrt.lean`). -/
theorem Matrix.posSemidef_abs (M : Matrix ι ι 𝕜) : M.abs.PosSemidef :=
  (Matrix.posSemidef_conjTranspose_mul_self M).posSemidef_sqrt

variable {dim1 dim2 : Type*} [Fintype dim1] [Fintype dim2] [DecidableEq dim1] [DecidableEq dim2]

/-- `|A ⊗ₖ B| = |A| ⊗ₖ |B|`: the absolute value is Kronecker-multiplicative. Via
`Matrix.PosSemidef.sqrt_kronecker` (`MatrixSqrt.lean`), `|A| ⊗ₖ |B|` is itself `(hA.kronecker
hB).sqrt` for `hA`, `hB` the defining `PosSemidef` proofs of `Aᴴ * A`, `Bᴴ * B`; `sqrt_unique` then
identifies it with `|A ⊗ₖ B|`, using `Matrix.PosSemidef.sqrt_mul_sqrt` plus the Kronecker
mixed-product identity `(Aᴴ * A) ⊗ₖ (Bᴴ * B) = (A ⊗ₖ B)ᴴ * (A ⊗ₖ B)` (`Matrix.mul_kronecker_mul`,
`Matrix.conjTranspose_kronecker`). -/
theorem Matrix.abs_kronecker (A : Matrix dim1 dim1 𝕜) (B : Matrix dim2 dim2 𝕜) :
    (A ⊗ₖ B).abs = A.abs ⊗ₖ B.abs := by
  unfold Matrix.abs
  set hA := Matrix.posSemidef_conjTranspose_mul_self A
  set hB := Matrix.posSemidef_conjTranspose_mul_self B
  rw [← hA.sqrt_kronecker hB]
  exact (Matrix.posSemidef_conjTranspose_mul_self (A ⊗ₖ B)).sqrt_unique
    (hA.kronecker hB).posSemidef_sqrt <| by
      rw [(hA.kronecker hB).sqrt_mul_sqrt, mul_kronecker_mul, ← conjTranspose_kronecker]

/-- `hA.cfc f` is Hermitian for any `f : ℝ → ℝ`: it lands in the domain of the Hermitian-matrix
continuous functional calculus (`Matrix.IsHermitian.instContinuousFunctionalCalculus`,
`HermitianFunctionalCalculus.lean`), whose predicate is exactly `IsSelfAdjoint` (`cfc_predicate`,
generic CFC API) — i.e. `Matrix.IsHermitian`, via `Matrix.star_eq_conjTranspose`. -/
theorem Matrix.IsHermitian.isHermitian_cfc {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (hA.cfc f).IsHermitian := by
  have h : IsSelfAdjoint (hA.cfc f) := hA.cfc_eq f ▸ cfc_predicate f A
  rwa [isSelfAdjoint_iff, Matrix.star_eq_conjTranspose] at h

/-- For Hermitian `A` and `f : ℝ → ℝ` that both preserves and reflects the `≥` order on `A`'s
eigenvalues (`hf`), `hA.cfc f`'s (decreasing-sorted) eigenvalues are exactly `f` applied to `A`'s:
both are recovered as the sorted list of the respective matrix's `charpoly` roots
(`Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀`), and `hf` means *sorting* the (unsorted)
`f`-image of `A`'s eigenvalues agrees with applying `f` to the *already-sorted* `A.eigenvalues₀`
(`Multiset.map_sort`). -/
theorem Matrix.IsHermitian.eigenvalues₀_cfc {A : Matrix ι ι 𝕜} (hA : A.IsHermitian) {f : ℝ → ℝ}
    (hf : ∀ i j : ι,
      hA.eigenvalues i ≥ hA.eigenvalues j ↔ f (hA.eigenvalues i) ≥ f (hA.eigenvalues j)) :
    (hA.isHermitian_cfc f).eigenvalues₀ = fun i => f (hA.eigenvalues₀ i) := by
  have hmap : (hA.cfc f).charpoly.roots.map RCLike.re =
      Multiset.map (f ∘ hA.eigenvalues) Finset.univ.val := by
    rw [← hA.cfc_eq f, hA.charpoly_cfc_eq, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hsort_cfc := hmap ▸ (hA.isHermitian_cfc f).sort_roots_charpoly_eq_eigenvalues₀
  have hmap2 : A.charpoly.roots.map RCLike.re = Multiset.map hA.eigenvalues Finset.univ.val := by
    rw [hA.roots_charpoly_eq_eigenvalues, Multiset.map_map]
    simp [Function.comp_def]
  have hsort := hmap2 ▸ hA.sort_roots_charpoly_eq_eigenvalues₀
  have hmono : ∀ a ∈ Multiset.map hA.eigenvalues Finset.univ.val,
      ∀ b ∈ Multiset.map hA.eigenvalues Finset.univ.val, a ≥ b ↔ f a ≥ f b := by
    intro a ha b hb
    obtain ⟨i, -, rfl⟩ := Multiset.mem_map.mp ha
    obtain ⟨j, -, rfl⟩ := Multiset.mem_map.mp hb
    exact hf i j
  have hkey := Multiset.map_sort (f := f) (s := Multiset.map hA.eigenvalues Finset.univ.val)
    (r := (· ≥ ·)) (r' := (· ≥ ·)) hmono
  simp only [hsort, List.map_ofFn, Multiset.map_map, hsort_cfc] at hkey
  exact (List.ofFn_injective hkey).symm

/-- `|M|`'s (decreasing-sorted) eigenvalues are exactly `M.singularValues`: `M.abs = h.cfc
Real.sqrt` for `h : (Mᴴ * M).IsHermitian` (unfolding `Matrix.abs`/`Matrix.PosSemidef.sqrt`), so
this specializes `Matrix.IsHermitian.eigenvalues₀_cfc` to `f := Real.sqrt`, which is order
-reflecting on `(Mᴴ * M).PosSemidef`'s nonnegative eigenvalues (`Real.sqrt_le_sqrt_iff`). -/
theorem Matrix.abs_eigenvalues₀_eq_singularValues (M : Matrix ι ι 𝕜) :
    (Matrix.posSemidef_abs M).isHermitian.eigenvalues₀ = M.singularValues := by
  set hA := Matrix.posSemidef_conjTranspose_mul_self M
  set h := hA.isHermitian
  exact h.eigenvalues₀_cfc (f := Real.sqrt)
    (fun i j => (Real.sqrt_le_sqrt_iff (hA.eigenvalues_nonneg i)).symm)

/-- `X.abs = X` for positive semidefinite `X`: `X` is already a positive semidefinite square root
of `Xᴴ * X = X * X`, so `sqrt_unique` (`ForMathlib/MatrixSqrt.lean`) identifies it with `X.abs`. -/
theorem Matrix.PosSemidef.abs_eq_self {X : Matrix ι ι 𝕜} (hX : X.PosSemidef) : X.abs = X := by
  have h : X * X = Xᴴ * X := by rw [hX.isHermitian]
  exact (Matrix.posSemidef_conjTranspose_mul_self X).sqrt_unique hX h

/-- For positive semidefinite `X`, `X`'s singular values coincide with its (decreasing-sorted)
eigenvalues: specializes `abs_eigenvalues₀_eq_singularValues` along `X.abs = X` (`abs_eq_self`
above), transporting the `eigenvalues₀`-producing `IsHermitian` proof across that equality (proof
irrelevance identifies the result with `hX.isHermitian.eigenvalues₀` itself). -/
theorem Matrix.PosSemidef.singularValues_eq_eigenvalues₀ {X : Matrix ι ι 𝕜} (hX : X.PosSemidef) :
    X.singularValues = hX.isHermitian.eigenvalues₀ := by
  have habs : X.abs = X := hX.abs_eq_self
  have hcongr : ∀ {Y Z : Matrix ι ι 𝕜} (h : Y = Z) (hY : Y.IsHermitian),
      (h ▸ hY : Z.IsHermitian).eigenvalues₀ = hY.eigenvalues₀ := by
    intro Y Z h hY; subst h; rfl
  have h2 := hcongr habs (Matrix.posSemidef_abs X).isHermitian
  rw [show (habs ▸ (Matrix.posSemidef_abs X).isHermitian : X.IsHermitian) = hX.isHermitian from rfl]
    at h2
  rw [h2, Matrix.abs_eigenvalues₀_eq_singularValues]

/-- `σ(Mᴴ) = σ(M)`: singular values are unchanged by taking the conjugate transpose. `Mᴴ * M` and
`M * Mᴴ` are square, same-size matrices, so share a characteristic polynomial
(`Matrix.charpoly_mul_comm`), hence the same `eigenvalues₀`
(`Matrix.IsHermitian.eigenvalues₀_eq_of_charpoly_eq`, `SingularValue.lean`), hence the same square
roots. -/
theorem Matrix.singularValues_conjTranspose (M : Matrix ι ι 𝕜) :
    Mᴴ.singularValues = M.singularValues := by
  have hM : (Mᴴᴴ * Mᴴ).IsHermitian := (Matrix.posSemidef_conjTranspose_mul_self Mᴴ).isHermitian
  have hN : (Mᴴ * M).IsHermitian := (Matrix.posSemidef_conjTranspose_mul_self M).isHermitian
  have hcharpoly : (Mᴴᴴ * Mᴴ).charpoly = (Mᴴ * M).charpoly := by
    rw [Matrix.conjTranspose_conjTranspose]; exact Matrix.charpoly_mul_comm M Mᴴ
  funext i
  change Real.sqrt (hM.eigenvalues₀ i) = Real.sqrt (hN.eigenvalues₀ i)
  rw [hM.eigenvalues₀_eq_of_charpoly_eq hN hcharpoly]

/-- For positive semidefinite `X`, `X.sqrt`'s (decreasing-sorted) singular values are `Real.sqrt`
applied to `X`'s: `X.sqrt.PosSemidef` (`Matrix.PosSemidef.posSemidef_sqrt`, `MatrixSqrt.lean`)
reduces this to `singularValues_eq_eigenvalues₀` plus `eigenvalues₀_cfc` (both above), since
`X.sqrt` is definitionally `hX.isHermitian.cfc Real.sqrt` (`Matrix.PosSemidef.sqrt`,
`MatrixSqrt.lean`) and `Real.sqrt` is order-reflecting on `X`'s nonnegative eigenvalues.

Specializing at the top index (`i = 0`, the operator norm) and squaring recovers the operator-norm
identity `‖X.sqrt‖² = ‖X‖` for positive semidefinite `X` — the `k = 1` case of the sandwiched-
contraction Ky Fan bound (`Matrix.kyFanNorm_sqrt_mul_contraction_mul_sqrt_le_max`,
`KyFanCauchySchwarz.lean`). -/
theorem Matrix.PosSemidef.sqrt_singularValues {X : Matrix ι ι 𝕜} (hX : X.PosSemidef) :
    hX.sqrt.singularValues = fun i => Real.sqrt (X.singularValues i) := by
  have h2 : hX.posSemidef_sqrt.isHermitian.eigenvalues₀
      = (hX.isHermitian.isHermitian_cfc Real.sqrt).eigenvalues₀ := rfl
  have h3 : (hX.isHermitian.isHermitian_cfc Real.sqrt).eigenvalues₀
      = fun i => Real.sqrt (hX.isHermitian.eigenvalues₀ i) :=
    hX.isHermitian.eigenvalues₀_cfc
      (fun i j => (Real.sqrt_le_sqrt_iff (hX.eigenvalues_nonneg i)).symm)
  rw [hX.posSemidef_sqrt.singularValues_eq_eigenvalues₀, h2, h3, hX.singularValues_eq_eigenvalues₀]
