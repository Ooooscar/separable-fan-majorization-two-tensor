import NewProject.ForMathlib.Majorization
import NewProject.ForMathlib.SingularValue

/-!
# Ky Fan `k`-norms

Not in Mathlib. The Ky Fan `k`-norm of a matrix `A` is the sum of its `k` largest singular values,
`Majorization.topSum A.singularValues k`. It is the standard first family of examples of a
unitarily invariant norm (`Matrix.IsUnitarilyInvariantNorm`, `UnitarilyInvariantNorm.lean`): `k = 1`
gives the operator norm and `k = Fintype.card ι` gives the trace norm.

Mathlib's standard `p`-norms on `Fin n → ℝ` (`PiLp`/`EuclideanSpace`,
`Mathlib.Analysis.Normed.Lp.PiLp`) are set up as a *type synonym* `PiLp p α` carrying a `Norm`
instance found by instance resolution. `UnitarilyInvariantNorm.lean`'s module doc explains why that
pattern is unsuitable here: `Matrix ι ι 𝕜` needs many unitarily invariant norms at once (one Ky Fan
norm per `k`, Schatten norms, the operator norm, ...), not one canonical norm per type. So, like
`Matrix.IsUnitarilyInvariantNorm` itself, `kyFanNorm` is a plain function taking `k` as an explicit
argument, in the same style as `Matrix.singularValues`/`Matrix.singularValueDiagonal`
(`SingularValue.lean`).

## Main definitions

* `Matrix.kyFanNorm`: `Matrix.kyFanNorm k A`, the sum of the `k` largest singular values of `A`.

## Main results

* `Matrix.kyFanNorm_nonneg`: `kyFanNorm k A` is nonnegative.
-/

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

/-- The Ky Fan `k`-norm of `A`: the sum of the `k` largest singular values of `A`. `k = 1` gives
the operator norm and `k = Fintype.card ι` gives the trace norm. -/
noncomputable def Matrix.kyFanNorm (k : ℕ) (A : Matrix ι ι 𝕜) : ℝ :=
  Majorization.topSum A.singularValues k

/-- `kyFanNorm k A` is nonnegative, being a sum of (nonnegative) singular values. -/
theorem Matrix.kyFanNorm_nonneg (k : ℕ) (A : Matrix ι ι 𝕜) : 0 ≤ A.kyFanNorm k :=
  Majorization.topSum_nonneg A.singularValues A.singularValues_nonneg k
