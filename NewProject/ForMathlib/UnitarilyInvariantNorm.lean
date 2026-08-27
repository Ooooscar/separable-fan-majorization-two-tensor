import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.RCLike.Basic

/-!
# Unitarily invariant norms on matrices

Not in Mathlib: there is no notion here of a norm on matrices that is invariant under unitary
conjugation, nor any of its standard instances (Ky Fan norms, Schatten norms, the operator norm).
We define the general notion directly, following the textbook definition (e.g. Bhatia,
*Matrix Analysis*, IV.1): a norm `N` on square matrices such that `N (U * A * V) = N A` for all
unitary `U`, `V`.

This is stated as a `class` taking the candidate function `N` as an explicit argument, mirroring
`IsAbsoluteValue` (`Mathlib.Algebra.Order.AbsoluteValue.Basic`) rather than Mathlib's `Norm`
typeclass: `Norm` ties a norm to instance resolution on a *type*, which only works when a type
carries one canonical norm, but `Matrix ι ι 𝕜` needs many unitarily invariant norms at once (each
Ky Fan k-norm, each Schatten p-norm, the operator norm, ...). Field names (`smul'`, `add_le'`)
match the corresponding fields of Mathlib's `Seminorm`/`AddGroupSeminorm`; `nonneg` is not a
primitive field for the same reason it isn't one there — it is derivable from the others.

This is the structure needed to state and prove the Cauchy-Schwarz inequality for
unitarily invariant norms, a tool towards `SumKroneckerWeakMajorization.lean`'s final theorem.

## Main definitions

* `Matrix.IsUnitarilyInvariantNorm`: `N` is a norm (definite, homogeneous, subadditive) that is
  unchanged by two-sided conjugation by unitary matrices.

## Main results

* `Matrix.IsUnitarilyInvariantNorm.nonneg`: nonnegativity, derived from `smul` and `add_le`.
* `Matrix.IsUnitarilyInvariantNorm.unitary_conj_left`/`unitary_conj_right`: one-sided special
  cases of `unitary_conj`, obtained by taking the other side to be `1`.
-/

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

/-- `N` is a *unitarily invariant norm* on `ι`-by-`ι` matrices over `𝕜` if it is a norm
(`eq_zero'`, `smul'`, `add_le'`) that is additionally unchanged under conjugation by unitary
matrices on both sides: `N (U * A * V) = N A` for all unitary `U`, `V`. Ky Fan norms
(`Majorization.topSum` of `Matrix.singularValues`) and Schatten norms are the standard examples,
since `σ(U * A * V) = σ(A)` for unitary `U`, `V`. -/
class Matrix.IsUnitarilyInvariantNorm (N : Matrix ι ι 𝕜 → ℝ) : Prop where
  /-- The norm is positive definite. -/
  eq_zero' : ∀ {A}, N A = 0 ↔ A = 0
  /-- The norm is absolutely homogeneous. -/
  smul' : ∀ (c : 𝕜) (A : Matrix ι ι 𝕜), N (c • A) = ‖c‖ * N A
  /-- The norm satisfies the triangle inequality. -/
  add_le' : ∀ A B, N (A + B) ≤ N A + N B
  /-- The norm is unchanged by two-sided unitary conjugation. -/
  unitary_conj' : ∀ (U V : Matrix.unitaryGroup ι 𝕜) (A : Matrix ι ι 𝕜),
      N ((U : Matrix ι ι 𝕜) * A * (V : Matrix ι ι 𝕜)) = N A

namespace Matrix.IsUnitarilyInvariantNorm

variable (N : Matrix ι ι 𝕜 → ℝ) [Matrix.IsUnitarilyInvariantNorm N]

theorem eq_zero {A : Matrix ι ι 𝕜} : N A = 0 ↔ A = 0 := eq_zero'

theorem smul (c : 𝕜) (A : Matrix ι ι 𝕜) : N (c • A) = ‖c‖ * N A := smul' c A

theorem add_le (A B : Matrix ι ι 𝕜) : N (A + B) ≤ N A + N B := add_le' A B

theorem unitary_conj (U V : Matrix.unitaryGroup ι 𝕜) (A : Matrix ι ι 𝕜) :
    N ((U : Matrix ι ι 𝕜) * A * (V : Matrix ι ι 𝕜)) = N A := unitary_conj' U V A

/-- One-sided left conjugation invariance, obtained from `unitary_conj` by taking `V = 1`. -/
theorem unitary_conj_left (U : Matrix.unitaryGroup ι 𝕜) (A : Matrix ι ι 𝕜) :
    N ((U : Matrix ι ι 𝕜) * A) = N A := by
  simpa using unitary_conj N U 1 A

/-- One-sided right conjugation invariance, obtained from `unitary_conj` by taking `U = 1`. -/
theorem unitary_conj_right (V : Matrix.unitaryGroup ι 𝕜) (A : Matrix ι ι 𝕜) :
    N (A * (V : Matrix ι ι 𝕜)) = N A := by
  simpa using unitary_conj N 1 V A

/-- Nonnegativity is derivable rather than a primitive axiom: `0 = N 0 ≤ N A + N (-A) = 2 * N A`,
using `smul` at `c = -1` (so `N (-A) = N A`) and the triangle inequality at `(A, -A)`. -/
theorem nonneg (A : Matrix ι ι 𝕜) : 0 ≤ N A := by
  have hzero : N 0 = 0 := (eq_zero N).mpr rfl
  have hneg : N (-A) = N A := by
    have h := smul N (-1 : 𝕜) A
    rwa [neg_one_smul, norm_neg, norm_one, one_mul] at h
  have htri : N (A + -A) ≤ N A + N (-A) := add_le N A (-A)
  rw [add_neg_cancel, hzero, hneg] at htri
  linarith

end Matrix.IsUnitarilyInvariantNorm
