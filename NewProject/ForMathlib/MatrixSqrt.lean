import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order

/-!
# Square roots of positive semidefinite matrices

Not in Mathlib as a named `Matrix.PosSemidef.sqrt` API (Mathlib has the pieces: the continuous
functional calculus for Hermitian matrices, `Matrix.IsHermitian.cfc`,
`Mathlib.Analysis.Matrix.HermitianFunctionalCalculus`). We define `hA.sqrt` for `hA : A.PosSemidef`
directly as `hA.isHermitian.cfc Real.sqrt`, i.e. `U * diagonal (√ ∘ eigenvalues) * Uᴴ` for
`U := hA.isHermitian.eigenvectorUnitary`. Needed by `MatrixAbs.lean` (`Matrix.abs M := (Mᴴ *
M).sqrt`), a step towards `SumKroneckerWeakMajorization.lean`'s Rico–Wolf reduction to the
positive semidefinite case.

## Main definitions

* `Matrix.PosSemidef.sqrt`: the positive semidefinite square root of a positive semidefinite
  matrix.

## Main results

* `Matrix.PosSemidef.sqrt_eq`: `hA.sqrt` unfolds to its `cfc` construction.
* `Matrix.PosSemidef.posSemidef_sqrt`: `hA.sqrt` is again positive semidefinite.
* `Matrix.PosSemidef.sqrt_mul_sqrt`: `hA.sqrt * hA.sqrt = A`.
* `Matrix.PosSemidef.eq_of_mul_self_eq_mul_self`: two positive semidefinite matrices whose squares
  agree are equal (the general "commutator trick").
* `Matrix.PosSemidef.sqrt_unique`: the positive semidefinite square root is the *unique* positive
  semidefinite matrix squaring to `A` (the `eq_of_mul_self_eq_mul_self` special case).
* `Matrix.PosSemidef.sqrt_kronecker`: `(A ⊗ₖ B).sqrt = A.sqrt ⊗ₖ B.sqrt` for positive semidefinite
  `A`, `B`.
-/

open Matrix
open scoped Kronecker ComplexOrder

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

/-- The positive semidefinite square root of a positive semidefinite matrix `A`, built from the
continuous functional calculus for Hermitian matrices (`Matrix.IsHermitian.cfc`,
`Mathlib.Analysis.Matrix.HermitianFunctionalCalculus`): `hA.sqrt = U * diagonal (√ ∘ eigenvalues) *
Uᴴ` for `U := hA.isHermitian.eigenvectorUnitary`. -/
noncomputable def Matrix.PosSemidef.sqrt {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) : Matrix ι ι 𝕜 :=
  hA.isHermitian.cfc Real.sqrt

/-- `hA.sqrt` unfolds to its `cfc` construction: `U * diagonal (√ ∘ eigenvalues) * Uᴴ` for
`U := hA.isHermitian.eigenvectorUnitary`. Shared by `posSemidef_sqrt` and `sqrt_mul_sqrt` below,
which both need to unfold `hA.sqrt` this way. -/
theorem Matrix.PosSemidef.sqrt_eq {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    hA.sqrt = Unitary.conjStarAlgAut 𝕜 _ hA.isHermitian.eigenvectorUnitary
      (diagonal (RCLike.ofReal ∘ Real.sqrt ∘ hA.isHermitian.eigenvalues)) :=
  rfl

/-- `hA.sqrt` is again positive semidefinite: its eigenvalues (via `cfc`) are `Real.sqrt` applied
to `A`'s (nonnegative, since `A` is PSD) eigenvalues, hence nonnegative. -/
theorem Matrix.PosSemidef.posSemidef_sqrt {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    hA.sqrt.PosSemidef := by
  rw [hA.sqrt_eq, Unitary.conjStarAlgAut_apply,
    Matrix.IsUnit.posSemidef_star_right_conjugate_iff Unitary.isUnit_coe,
    Matrix.posSemidef_diagonal_iff]
  exact fun i ↦ RCLike.ofReal_nonneg.mpr (Real.sqrt_nonneg _)

/-- `hA.sqrt * hA.sqrt = A`: the defining property of the square root. Writing `hA.sqrt = U * D *
star U` (via `cfc`), `hA.sqrt * hA.sqrt = U * D * D * star U` since `star U * U = 1`, and
`D * D = diagonal (RCLike.ofReal ∘ eigenvalues)` since `√eᵢ * √eᵢ = eᵢ` (`Real.mul_self_sqrt`,
using `A`'s eigenvalues `eᵢ` are nonnegative as `A` is PSD); this is exactly `A` by the spectral
theorem (`IsHermitian.spectral_theorem`). -/
theorem Matrix.PosSemidef.sqrt_mul_sqrt {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    hA.sqrt * hA.sqrt = A := by
  have hD : (diagonal (RCLike.ofReal ∘ Real.sqrt ∘ hA.isHermitian.eigenvalues) : Matrix ι ι 𝕜) *
      diagonal (RCLike.ofReal ∘ Real.sqrt ∘ hA.isHermitian.eigenvalues) =
      diagonal (RCLike.ofReal ∘ hA.isHermitian.eigenvalues) := by
    rw [diagonal_mul_diagonal]
    congr 1
    funext i
    simp only [Function.comp_apply, ← RCLike.ofReal_mul,
      Real.mul_self_sqrt (hA.eigenvalues_nonneg i)]
  rw [hA.sqrt_eq, ← map_mul, hD]
  exact hA.isHermitian.spectral_theorem.symm

omit [DecidableEq ι] in
/-- If `S` is positive semidefinite and `C` is Hermitian with `C * S * C = 0`, then `S * C = 0`.
Writing `S = T * T` for `T := S`'s own PSD square root, `C * S * C = 0` becomes
`(T * C)ᴴ * (T * C) = 0`, forcing `T * C = 0` (`conjTranspose_mul_self_eq_zero`) and hence
`S * C = T * (T * C) = 0`. The key step of the "commutator trick" in `sqrt_unique` below, isolated
since it uses none of `sqrt_unique`'s hypotheses on `B`. -/
theorem Matrix.PosSemidef.mul_eq_zero_of_conj_mul_eq_zero {S C : Matrix ι ι 𝕜} (hS : S.PosSemidef)
    (hC : C.IsHermitian) (hCSC : C * S * C = 0) : S * C = 0 := by
  classical
  have hTherm : hS.sqrt.IsHermitian := hS.posSemidef_sqrt.isHermitian
  have hTT : hS.sqrt * hS.sqrt = S := hS.sqrt_mul_sqrt
  have hTCeq : (hS.sqrt * C)ᴴ * (hS.sqrt * C) = C * S * C := by
    rw [conjTranspose_mul, hTherm.eq, hC.eq,
      show C * hS.sqrt * (hS.sqrt * C) = C * (hS.sqrt * hS.sqrt) * C from by noncomm_ring, hTT]
  have hTC0 : hS.sqrt * C = 0 := conjTranspose_mul_self_eq_zero.mp (hTCeq.trans hCSC)
  rw [← hTT, mul_assoc, hTC0, mul_zero]

omit [DecidableEq ι] in
/-- **The "commutator trick"**: if `S`, `B` are positive semidefinite and `S * S = B * B`, then
`S = B`. The standard uniqueness argument for positive square roots, avoiding
eigenbasis-matching; `sqrt_unique` below is the special case `S := hA.sqrt`. With `C := S - B`
(Hermitian), `S * C + C * B = S * S - B * B = 0`, so `S * C = -(C * B)` and (adjoining)
`C * S = -(B * C)`. `C * S * C` and `C * B * C` are both positive semidefinite (conjugates of `S`,
`B` by `C`) with nonnegative trace, and their traces are negatives of each other (via
`C * S = -(B * C)` and cyclicity of trace), so `C * S * C`'s trace vanishes, hence
`C * S * C = 0`. `mul_eq_zero_of_conj_mul_eq_zero` turns this into `S * C = 0`; combined with
`S * C = -(C * B)` and one adjoint, `S * C = C * S = C * B = 0`, so `C * C = C * S - C * B = 0`.
Since `C` is Hermitian, `Cᴴ * C = C * C = 0` forces `C = 0`, i.e. `S = B`. -/
theorem Matrix.PosSemidef.eq_of_mul_self_eq_mul_self {S B : Matrix ι ι 𝕜} (hS : S.PosSemidef)
    (hB : B.PosSemidef) (h : S * S = B * B) : S = B := by
  have hSHerm : S.IsHermitian := hS.isHermitian
  have hBHerm : B.IsHermitian := hB.isHermitian
  have key : S * (S - B) + (S - B) * B = 0 := by
    have expand : S * (S - B) + (S - B) * B = S * S - B * B := by noncomm_ring
    rw [expand, h, sub_self]
  set C := S - B with hC_def
  have hC : C.IsHermitian := hSHerm.sub hBHerm
  have key1 : S * C = -(C * B) := by rw [eq_neg_iff_add_eq_zero]; exact key
  have key2 : C * S = -(B * C) := by
    have hadj := congrArg Matrix.conjTranspose key1
    simpa [conjTranspose_mul, hC.eq, hSHerm.eq, hBHerm.eq] using hadj
  have hCSC0 : C * S * C = 0 := by
    have hCSC : (C * S * C).PosSemidef := by
      have := hS.conjTranspose_mul_mul_same C
      rwa [hC.eq] at this
    have hCBC : (C * B * C).PosSemidef := by
      have := hB.conjTranspose_mul_mul_same C
      rwa [hC.eq] at this
    have e1 : C * S * C = -(B * (C * C)) := by rw [key2]; noncomm_ring
    have e2 : (C * B * C).trace = (B * (C * C)).trace := by
      rw [trace_mul_comm (C * B) C, ← mul_assoc, trace_mul_comm (C * C) B]
    have htr : (C * S * C).trace = -(C * B * C).trace := by rw [e1, trace_neg, e2]
    have hle : (C * S * C).trace ≤ 0 := by rw [htr]; exact neg_nonpos.mpr hCBC.trace_nonneg
    exact hCSC.trace_eq_zero_iff.mp (le_antisymm hle hCSC.trace_nonneg)
  have hSC0 : S * C = 0 := hS.mul_eq_zero_of_conj_mul_eq_zero hC hCSC0
  have hCB0 : C * B = 0 := by
    have h' : -(C * B) = 0 := by rw [← key1]; exact hSC0
    simpa using h'
  have hCS0 : C * S = 0 := by
    have hadj := congrArg Matrix.conjTranspose hSC0
    simpa [conjTranspose_mul, hSHerm.eq, hC.eq] using hadj
  have hCC0 : C * C = 0 := by
    nth_rewrite 2 [hC_def]
    simp [mul_sub, hCS0, hCB0]
  have hC0 : C = 0 := conjTranspose_mul_self_eq_zero.mp (by rw [hC.eq]; exact hCC0)
  exact sub_eq_zero.mp (hC_def ▸ hC0)

/-- The positive semidefinite square root is unique: if `B` is positive semidefinite and
`B * B = A`, then `B = hA.sqrt`. The `S := hA.sqrt` case of `eq_of_mul_self_eq_mul_self`. -/
theorem Matrix.PosSemidef.sqrt_unique {A B : Matrix ι ι 𝕜} (hA : A.PosSemidef) (hB : B.PosSemidef)
    (h : B * B = A) : hA.sqrt = B :=
  hA.posSemidef_sqrt.eq_of_mul_self_eq_mul_self hB (hA.sqrt_mul_sqrt.trans h.symm)

variable {dim1 dim2 : Type*} [Fintype dim1] [Fintype dim2] [DecidableEq dim1] [DecidableEq dim2]

/-- Kronecker-multiplicativity of the square root: `(A ⊗ₖ B).sqrt = A.sqrt ⊗ₖ B.sqrt` for positive
semidefinite `A`, `B`. Via `sqrt_unique`: `A.sqrt ⊗ₖ B.sqrt` is positive semidefinite
(`Matrix.PosSemidef.kronecker`) and squares to `A ⊗ₖ B` (`Matrix.mul_kronecker_mul`), so it *is*
`(A ⊗ₖ B).sqrt`. -/
theorem Matrix.PosSemidef.sqrt_kronecker {A : Matrix dim1 dim1 𝕜} {B : Matrix dim2 dim2 𝕜}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (hA.kronecker hB).sqrt = hA.sqrt ⊗ₖ hB.sqrt :=
  (hA.kronecker hB).sqrt_unique (hA.posSemidef_sqrt.kronecker hB.posSemidef_sqrt)
    (by rw [← mul_kronecker_mul, hA.sqrt_mul_sqrt, hB.sqrt_mul_sqrt])
