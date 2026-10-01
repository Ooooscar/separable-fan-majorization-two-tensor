import SeparableFanMajorization.ForMathlib.MatrixAbs
import SeparableFanMajorization.ForMathlib.SingularValueDecomposition

/-!
# Polar decomposition of a square matrix

Not in Mathlib. Every square matrix `M` factors as `M = U * |M|` with `U` unitary and `|M|`
(`Matrix.abs`, `MatrixAbs.lean`) positive semidefinite — a step towards
`SumKroneckerWeakMajorization.lean`'s [WZ26] reduction to the positive semidefinite case.

## Main results

* `Matrix.abs_eq_of_svd`: given `M = U * D * Vᴴ` (`U`, `V` unitary, `D` Hermitian PSD — an SVD's
  shape), `M.abs = V * D * Vᴴ`. The key computation behind both results below.
* `Matrix.exists_polarDecomposition`: `∃ U, M = U * |M|`, derived from the SVD factorization
  `M = U₀ * Σ * Vᴴ` (`Matrix.exists_svd`, `SingularValueDecomposition.lean`) via `abs_eq_of_svd`.
* `Matrix.abs_conjTranspose_eq_of_polarDecomposition`: given such a `U`, `|Mᴴ| = U * |M| * Uᴴ`,
  again via `abs_eq_of_svd`.
-/

open Matrix
open scoped ComplexOrder

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

/-- For `U` in the unitary group, `Uᴴ * U = 1`: `Matrix.UnitaryGroup.star_mul_self` restated via
`Matrix.star_eq_conjTranspose`. -/
theorem Matrix.UnitaryGroup.conjTranspose_mul_self (U : Matrix.unitaryGroup ι 𝕜) :
    (U : Matrix ι ι 𝕜)ᴴ * (U : Matrix ι ι 𝕜) = 1 := by
  rw [← Matrix.star_eq_conjTranspose]
  exact Matrix.UnitaryGroup.star_mul_self U

/-- If `M = U * D * Vᴴ` with `U, V` unitary and `D` Hermitian positive semidefinite, then
`M.abs = V * D * Vᴴ`: `V * D * Vᴴ` is a positive semidefinite square root of `Mᴴ * M` (using `D`
Hermitian and `Uᴴ * U = 1`), hence *is* `|M|` by `Matrix.PosSemidef.sqrt_unique`
(`MatrixSqrt.lean`). The shape `M = U * D * Vᴴ` matches an SVD (`Matrix.exists_svd`,
`SingularValueDecomposition.lean`), which is where `exists_polarDecomposition` applies this. -/
theorem Matrix.abs_eq_of_svd {M D : Matrix ι ι 𝕜} {U V : Matrix.unitaryGroup ι 𝕜}
    (hUV : M = (U : Matrix ι ι 𝕜) * D * (V : Matrix ι ι 𝕜)ᴴ) (hDHerm : D.IsHermitian)
    (hDPSD : D.PosSemidef) : M.abs = (V : Matrix ι ι 𝕜) * D * (V : Matrix ι ι 𝕜)ᴴ := by
  have hUU : (U : Matrix ι ι 𝕜)ᴴ * (U : Matrix ι ι 𝕜) = 1 :=
    Matrix.UnitaryGroup.conjTranspose_mul_self U
  have hVV : (V : Matrix ι ι 𝕜)ᴴ * (V : Matrix ι ι 𝕜) = 1 :=
    Matrix.UnitaryGroup.conjTranspose_mul_self V
  -- `Mᴴ = V * D * Uᴴ`, from `M = U * D * Vᴴ` (`D` Hermitian).
  have hMH : Mᴴ = (V : Matrix ι ι 𝕜) * D * (U : Matrix ι ι 𝕜)ᴴ := by
    rw [hUV, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, hDHerm.eq]
    noncomm_ring
  -- `Mᴴ * M = V * D² * Vᴴ`, cancelling `Uᴴ * U = 1`.
  have hMM : Mᴴ * M = (V : Matrix ι ι 𝕜) * (D * D) * (V : Matrix ι ι 𝕜)ᴴ := by
    calc Mᴴ * M = (V : Matrix ι ι 𝕜) * D * (U : Matrix ι ι 𝕜)ᴴ *
          ((U : Matrix ι ι 𝕜) * D * (V : Matrix ι ι 𝕜)ᴴ) := by rw [hMH, hUV]
      _ = (V : Matrix ι ι 𝕜) * (D * D) * (V : Matrix ι ι 𝕜)ᴴ := by
          rw [show (V : Matrix ι ι 𝕜) * D * (U : Matrix ι ι 𝕜)ᴴ *
                ((U : Matrix ι ι 𝕜) * D * (V : Matrix ι ι 𝕜)ᴴ)
              = (V : Matrix ι ι 𝕜) * D * ((U : Matrix ι ι 𝕜)ᴴ * (U : Matrix ι ι 𝕜)) * D *
                (V : Matrix ι ι 𝕜)ᴴ from by noncomm_ring,
            hUU]
          noncomm_ring
  -- `V * D * Vᴴ` is a positive semidefinite square root of `Mᴴ * M`, hence *is* `|M|`.
  have hB : ((V : Matrix ι ι 𝕜) * D * (V : Matrix ι ι 𝕜)ᴴ).PosSemidef :=
    hDPSD.mul_mul_conjTranspose_same (V : Matrix ι ι 𝕜)
  have hsq : (V : Matrix ι ι 𝕜) * D * (V : Matrix ι ι 𝕜)ᴴ *
      ((V : Matrix ι ι 𝕜) * D * (V : Matrix ι ι 𝕜)ᴴ) = Mᴴ * M := by
    rw [hMM,
      show (V : Matrix ι ι 𝕜) * D * (V : Matrix ι ι 𝕜)ᴴ *
          ((V : Matrix ι ι 𝕜) * D * (V : Matrix ι ι 𝕜)ᴴ)
        = (V : Matrix ι ι 𝕜) * D * ((V : Matrix ι ι 𝕜)ᴴ * (V : Matrix ι ι 𝕜)) * D *
          (V : Matrix ι ι 𝕜)ᴴ from by noncomm_ring,
      hVV]
    noncomm_ring
  exact (Matrix.posSemidef_conjTranspose_mul_self M).sqrt_unique hB hsq

/-- **Polar decomposition.** Every square matrix `M` factors as `M = U * |M|` with `U` unitary and
`|M|` (`Matrix.abs`) positive semidefinite. Derived from the full SVD factorization
`M = U₀ * Σ * Vᴴ` (`Matrix.exists_svd`, `SingularValueDecomposition.lean`) via `abs_eq_of_svd`,
which gives `|M| = V * Σ * Vᴴ`; then `U := U₀ * Vᴴ` is unitary with
`U * |M| = U₀ * Vᴴ * V * Σ * Vᴴ = U₀ * Σ * Vᴴ = M`. This carries the minor extra bookkeeping of the
right factor `V` (irrelevant to the polar decomposition itself), but reuses `Matrix.exists_svd`'s
harder geometric argument (`Orthonormal.exists_orthonormalBasis_extension_of_card_eq`,
`Mathlib.Analysis.InnerProductSpace.PiL2`) rather than redoing it directly. -/
theorem Matrix.exists_polarDecomposition (M : Matrix ι ι 𝕜) :
    ∃ U : Matrix.unitaryGroup ι 𝕜, M = (U : Matrix ι ι 𝕜) * M.abs := by
  classical
  obtain ⟨U₀, V, hUV⟩ := M.exists_svd
  set D := Matrix.diagonal (RCLike.ofReal (K := 𝕜) ∘ M.svdValues) with hD_def
  have habs : M.abs = (V : Matrix ι ι 𝕜) * D * (V : Matrix ι ι 𝕜)ᴴ :=
    Matrix.abs_eq_of_svd hUV M.isHermitian_diagonal_svdValues M.posSemidef_diagonal_svdValues
  have hVV : (V : Matrix ι ι 𝕜)ᴴ * (V : Matrix ι ι 𝕜) = 1 :=
    Matrix.UnitaryGroup.conjTranspose_mul_self V
  -- `U := U₀ * Vᴴ` is unitary, and `U * |M| = U₀ * Vᴴ * V * D * Vᴴ = U₀ * D * Vᴴ = M`.
  refine ⟨U₀ * star V, ?_⟩
  have hcoe : ((U₀ * star V : Matrix.unitaryGroup ι 𝕜) : Matrix ι ι 𝕜)
      = (U₀ : Matrix ι ι 𝕜) * (V : Matrix ι ι 𝕜)ᴴ := by
    rw [Submonoid.coe_mul, Unitary.coe_star, Matrix.star_eq_conjTranspose]
  calc M = (U₀ : Matrix ι ι 𝕜) * D * (V : Matrix ι ι 𝕜)ᴴ := hUV
    _ = (U₀ : Matrix ι ι 𝕜) * (V : Matrix ι ι 𝕜)ᴴ *
        ((V : Matrix ι ι 𝕜) * D * (V : Matrix ι ι 𝕜)ᴴ) := by
        rw [show (U₀ : Matrix ι ι 𝕜) * (V : Matrix ι ι 𝕜)ᴴ *
              ((V : Matrix ι ι 𝕜) * D * (V : Matrix ι ι 𝕜)ᴴ)
            = (U₀ : Matrix ι ι 𝕜) * ((V : Matrix ι ι 𝕜)ᴴ * (V : Matrix ι ι 𝕜)) * D *
              (V : Matrix ι ι 𝕜)ᴴ from by noncomm_ring,
          hVV]
        noncomm_ring
    _ = ((U₀ * star V : Matrix.unitaryGroup ι 𝕜) : Matrix ι ι 𝕜) * M.abs := by rw [hcoe, habs]

/-- Given a polar decomposition `M = U * |M|`, the absolute value of `Mᴴ` is `U * |M| * Uᴴ`.
`Mᴴ = 1 * |M| * Uᴴ` has exactly `abs_eq_of_svd`'s shape (with the identity in place of the left
unitary factor), so this is that lemma applied to `Mᴴ`. -/
theorem Matrix.abs_conjTranspose_eq_of_polarDecomposition {M : Matrix ι ι 𝕜}
    {U : Matrix.unitaryGroup ι 𝕜} (hU : M = (U : Matrix ι ι 𝕜) * M.abs) :
    Mᴴ.abs = (U : Matrix ι ι 𝕜) * M.abs * (U : Matrix ι ι 𝕜)ᴴ := by
  have hMH : Mᴴ = ((1 : Matrix.unitaryGroup ι 𝕜) : Matrix ι ι 𝕜) * M.abs * (U : Matrix ι ι 𝕜)ᴴ := by
    conv_lhs => rw [hU]
    rw [conjTranspose_mul, (Matrix.posSemidef_abs M).isHermitian.eq, Submonoid.coe_one, one_mul]
  exact Matrix.abs_eq_of_svd hMH (Matrix.posSemidef_abs M).isHermitian (Matrix.posSemidef_abs M)
