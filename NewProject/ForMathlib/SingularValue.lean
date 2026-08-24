import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.UnitaryGroup

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
* `Matrix.singularValues_unitary_conj`: `σ(U * A * V) = σ(A)` for unitary `U`, `V`. Needed for
  `Matrix.kyFanNorm` (`KyFanNorm.lean`) to satisfy `Matrix.IsUnitarilyInvariantNorm.unitary_conj'`.
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

/-- `σ(U * A * V) = σ(A)` for unitary `U`, `V`: singular values are unchanged by two-sided unitary
conjugation. Needed for `Matrix.kyFanNorm` (`KyFanNorm.lean`) to satisfy
`Matrix.IsUnitarilyInvariantNorm.unitary_conj'`.

The proof reduces to invariance of the characteristic polynomial under similarity:
`(UAV)ᴴ(UAV) = Vᴴ(AᴴA)V` (since `UᴴU = 1`), and `charpoly (Vᴴ M V) = charpoly M` for any `M` and
unitary `V` (since `Vᴴ = V⁻¹`, via `Matrix.charpoly_mul_comm`). Equal characteristic polynomials
give equal `eigenvalues₀` (via `Matrix.IsHermitian.sort_roots_charpoly_eq_eigenvalues₀`), hence
equal square roots. -/
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
  have heig : hN.eigenvalues₀ = hM.eigenvalues₀ := by
    apply List.ofFn_injective
    rw [← hN.sort_roots_charpoly_eq_eigenvalues₀, ← hM.sort_roots_charpoly_eq_eigenvalues₀,
      hcharpoly]
  funext i
  change Real.sqrt (hN.eigenvalues₀ i) = Real.sqrt (hM.eigenvalues₀ i)
  rw [heig]
