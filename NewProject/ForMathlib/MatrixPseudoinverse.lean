import Mathlib.Algebra.Star.StarProjection
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Analysis.Matrix.Order
import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Pseudoinverses of positive semidefinite matrices

Not in Mathlib. For `hA : A.PosSemidef`, `hA.pinv := hA.isHermitian.cfc (·⁻¹)`
(`Matrix.IsHermitian.cfc`, `Mathlib.Analysis.Matrix.HermitianFunctionalCalculus`), the pseudoinverse
built from the same Hermitian functional calculus `MatrixSqrt.lean` builds `sqrt` from:
`U * diagonal (eigenvalues⁻¹) * Uᴴ` for `U := hA.isHermitian.eigenvectorUnitary`, relying on `ℝ`'s
convention `(0 : ℝ)⁻¹ = 0` to make the naive `Inv.inv` already the right (zero-on-the-kernel)
pseudoinverse function, with no `if t = 0 then 0 else t⁻¹` needed.

Needed by `ContractionFactorization.lean`'s roadmap (Step 3, "Pseudoinverse via `cfc`"): applied
there to `hX.posSemidef_sqrt`/`hY.posSemidef_sqrt` (i.e. `hX.posSemidef_sqrt.pinv` is the
pseudoinverse of `X.sqrt` itself, not of `X`), to build the range-projectors `X.sqrt *
hX.posSemidef_sqrt.pinv` and `hX.posSemidef_sqrt.pinv * X.sqrt` that assemble Douglas'
factorization.

Mathlib has no general (Moore–Penrose) pseudoinverse theory to fall back on for the Penrose-style
identities below (only a documentation remark in `NonsingularInverse.lean` acknowledging the
general notion exists, without formalizing it), so they are proved directly here. Each identity
needs *two* independent copies of `A` (and/or `hA.pinv`) present in the goal at once, which is
exactly where the matrix-specific `hA.isHermitian.cfc` breaks down as a rewriting tool: its
elaborated term embeds `A` as the implicit index of the proof `hA.isHermitian`, so rewriting a bare
`A` via `hA.isHermitian.spectral_theorem` while `hA.isHermitian.cfc _` terms are also present forces
Lean to abstract that same `A` out of `hA.isHermitian`'s type too, and the resulting motive fails to
type-check.

The fix: `Matrix.IsHermitian.cfc_eq` identifies `hA.isHermitian.cfc f` with the *generic*,
proof-independent continuous functional calculus `cfc f A` from
`Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Unital` (available via
`Matrix.IsHermitian.instContinuousFunctionalCalculus : ContinuousFunctionalCalculus ℝ (Matrix n n
𝕜) IsSelfAdjoint`). Unlike `hA.isHermitian.cfc`, `cfc f a` is a plain `(ℝ → ℝ) → Matrix n n 𝕜 →
Matrix n n 𝕜`-valued function (built via a `Classical`-decidable if-then-else on `IsSelfAdjoint a ∧
ContinuousOn f (spectrum ℝ a)`, not by taking a proof as an argument), so its elaborated term never
hides a fixed hypothesis about `A` — rewriting bare `A` around `cfc`-terms is always safe. Once
`hA.pinv` and the relevant copies of `A` are both expressed as `cfc _ A`, the triple-product
identities reduce, via the generic algebra lemmas `cfc_mul`/`cfc_id`/`cfc_congr`, to *pointwise*
identities in `ℝ` on the reciprocal function — true unconditionally by `ℝ`'s `0⁻¹ = 0` convention
(`x * x⁻¹ * x = x`, `x⁻¹ * x * x⁻¹ = x⁻¹`). Commutativity (`mul_pinv_eq_pinv_mul`) needs no
real-number computation at all: `cfc_commute_cfc` gives it directly, since any two `cfc`-images of
the same `A` automatically commute (both lie in the range of the same algebra homomorphism
`cfcHom`). The `ContinuousOn f (spectrum ℝ A)` side conditions these lemmas carry discharge for
*any* `f : ℝ → ℝ`, via the same `by rw [continuousOn_iff_continuous_restrict]; fun_prop` proof
`Matrix.IsHermitian.cfc_eq` itself uses — the spectrum of a matrix is finite, so every function is
continuous on it.

## Main definitions

* `Matrix.PosSemidef.pinv`: the pseudoinverse of a positive semidefinite matrix.

## Main results

* `Matrix.PosSemidef.pinv_eq`: `hA.pinv` unfolds to its `cfc` construction.
* `Matrix.PosSemidef.posSemidef_pinv`: `hA.pinv` is again positive semidefinite.
* `Matrix.PosSemidef.mul_pinv_mul_self`, `Matrix.PosSemidef.pinv_mul_self_mul_pinv`: the defining
  pseudoinverse identities `A * hA.pinv * A = A` and `hA.pinv * A * hA.pinv = hA.pinv`, via the
  generic-`cfc` bridge described above. Both share the same "sandwich" shape
  `cfc f A * cfc g A * cfc f A = cfc f A`, factored into the private helper `cfc_sandwich_self`
  (`cfc_mul`/`cfc_congr` reducing it to the pointwise real identities `t * t⁻¹ * t = t` /
  `t⁻¹ * t * t⁻¹ = t⁻¹`).
* `Matrix.PosSemidef.mul_pinv_eq_pinv_mul`: `A` and `hA.pinv` commute, directly from
  `cfc_commute_cfc`.
* `Matrix.PosSemidef.isStarProjection_mul_pinv`, `Matrix.PosSemidef.isStarProjection_pinv_mul`:
  `A * hA.pinv` and `hA.pinv * A` are both star projections (self-adjoint idempotents,
  `IsStarProjection`) — the orthogonal projector onto `range A`. Pure algebra built on the three
  identities above: idempotency from `pinv_mul_self_mul_pinv` plus associativity, self-adjointness
  from `mul_pinv_eq_pinv_mul` plus `A`, `hA.pinv` each being Hermitian.
-/

open Matrix
open scoped ComplexOrder

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

/-- The pseudoinverse of a positive semidefinite matrix `A`, built from the continuous functional
calculus for Hermitian matrices (`Matrix.IsHermitian.cfc`,
`Mathlib.Analysis.Matrix.HermitianFunctionalCalculus`): `hA.pinv = U * diagonal (eigenvalues⁻¹) *
Uᴴ` for `U := hA.isHermitian.eigenvectorUnitary`, using `ℝ`'s `(0 : ℝ)⁻¹ = 0` convention so that
`Inv.inv` is already zero on `A`'s kernel. -/
noncomputable def Matrix.PosSemidef.pinv {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) : Matrix ι ι 𝕜 :=
  hA.isHermitian.cfc (·⁻¹)

/-- `hA.pinv` unfolds to its `cfc` construction: `U * diagonal (eigenvalues⁻¹) * Uᴴ` for
`U := hA.isHermitian.eigenvectorUnitary`. -/
theorem Matrix.PosSemidef.pinv_eq {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    hA.pinv = Unitary.conjStarAlgAut 𝕜 _ hA.isHermitian.eigenvectorUnitary
      (diagonal (RCLike.ofReal ∘ (·⁻¹) ∘ hA.isHermitian.eigenvalues)) :=
  rfl

/-- `hA.pinv` is again positive semidefinite: its eigenvalues (via `cfc`) are the reciprocals of
`A`'s (nonnegative, since `A` is PSD) eigenvalues, hence nonnegative (using `ℝ`'s `(0 : ℝ)⁻¹ = 0`
convention when an eigenvalue vanishes). -/
theorem Matrix.PosSemidef.posSemidef_pinv {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    hA.pinv.PosSemidef := by
  rw [hA.pinv_eq, Unitary.conjStarAlgAut_apply,
    Matrix.IsUnit.posSemidef_star_right_conjugate_iff Unitary.isUnit_coe,
    Matrix.posSemidef_diagonal_iff]
  exact fun i ↦ RCLike.ofReal_nonneg.mpr (inv_nonneg.mpr (hA.eigenvalues_nonneg i))

/-- `hA.pinv` as the generic `cfc`: the proof-independent counterpart of `pinv_eq`, used to rewrite
`hA.pinv` freely alongside other `cfc`-images of `A` (see the module docstring for why the
`hA.isHermitian.cfc`-based `pinv_eq` can't be used for this instead). -/
private theorem pinv_eq_cfc_inv {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    hA.pinv = cfc (·⁻¹ : ℝ → ℝ) A :=
  (hA.isHermitian.cfc_eq (·⁻¹)).symm

/-- The generic `cfc` of the identity function on `A` is just `A`. -/
private theorem cfc_id_self {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    cfc (id : ℝ → ℝ) A = A :=
  cfc_id ℝ A hA.isHermitian.isSelfAdjoint

/-- Shared shape of `mul_pinv_mul_self` and `pinv_mul_self_mul_pinv`: both are the "sandwich"
identity `cfc f A * cfc g A * cfc f A = cfc f A` for a pair `f, g` satisfying the pointwise real
identity `f x * g x * f x = f x` (`(f, g) = (id, ·⁻¹)` and `(·⁻¹, id)` respectively), folded through
`cfc_mul` into a single `cfc` and closed by `cfc_congr`. Needs no hypothesis on `A`: `cfc_mul` and
`cfc_congr` carry no `IsSelfAdjoint`/predicate side condition, only the continuity one, which
`hcont` discharges unconditionally (see the module docstring). -/
private theorem cfc_sandwich_self {A : Matrix ι ι 𝕜} (f g : ℝ → ℝ)
    (h : ∀ x, f x * g x * f x = f x) :
    cfc f A * cfc g A * cfc f A = cfc f A := by
  have hcont : ∀ f : ℝ → ℝ, ContinuousOn f (spectrum ℝ A) := fun f => by
    rw [continuousOn_iff_continuous_restrict]; fun_prop
  rw [← cfc_mul f g A (hcont _) (hcont _), ← cfc_mul (fun x => f x * g x) f A (hcont _) (hcont _)]
  exact cfc_congr fun x _ => h x

/-- **Pseudoinverse identity.** `A * hA.pinv * A = A`. Via the generic-`cfc` bridge (see the module
docstring): rewrite `hA.pinv` and (separately, via `cfc_sandwich_self`) two copies of `A` as
`cfc`-images of `A`, sandwiched around the pointwise real identity `x * x⁻¹ * x = x` (true for every
real `x`, including `0`, by `0⁻¹ = 0`). -/
theorem Matrix.PosSemidef.mul_pinv_mul_self {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    A * hA.pinv * A = A := by
  have hcfc := cfc_sandwich_self (A := A) id (·⁻¹) fun x => by
    change x * x⁻¹ * x = x
    rcases eq_or_ne x 0 with h | h
    · simp [h]
    · rw [mul_assoc, inv_mul_cancel₀ h, mul_one]
  rwa [cfc_id_self hA, ← pinv_eq_cfc_inv hA] at hcfc

/-- **Pseudoinverse identity.** `hA.pinv * A * hA.pinv = hA.pinv`. Mirrors `mul_pinv_mul_self` via
`cfc_sandwich_self`, sandwiched around the pointwise real identity `x⁻¹ * x * x⁻¹ = x⁻¹`. -/
theorem Matrix.PosSemidef.pinv_mul_self_mul_pinv {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    hA.pinv * A * hA.pinv = hA.pinv := by
  have hcfc := cfc_sandwich_self (A := A) (·⁻¹) id fun x => by
    change x⁻¹ * x * x⁻¹ = x⁻¹
    rcases eq_or_ne x 0 with h | h
    · simp [h]
    · rw [mul_assoc, mul_inv_cancel₀ h, mul_one]
  rwa [cfc_id_self hA, ← pinv_eq_cfc_inv hA] at hcfc

/-- `A` and its pseudoinverse `hA.pinv` commute: both are `cfc`-images of the same `A`, and any two
`cfc`-images of one element automatically commute (`cfc_commute_cfc`, no real-number computation
needed). -/
theorem Matrix.PosSemidef.mul_pinv_eq_pinv_mul {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    A * hA.pinv = hA.pinv * A := by
  have hcomm : cfc (id : ℝ → ℝ) A * cfc (·⁻¹ : ℝ → ℝ) A
      = cfc (·⁻¹ : ℝ → ℝ) A * cfc (id : ℝ → ℝ) A :=
    cfc_commute_cfc (id : ℝ → ℝ) (·⁻¹ : ℝ → ℝ) A
  rwa [cfc_id_self hA, ← pinv_eq_cfc_inv hA] at hcomm

/-- `A * hA.pinv` is a star projection (self-adjoint idempotent) — the orthogonal projector onto
`range A`. Idempotency is `pinv_mul_self_mul_pinv` plus associativity; self-adjointness is
`mul_pinv_eq_pinv_mul` plus `A`, `hA.pinv` each being Hermitian. -/
theorem Matrix.PosSemidef.isStarProjection_mul_pinv {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    IsStarProjection (A * hA.pinv) where
  isIdempotentElem := by
    change A * hA.pinv * (A * hA.pinv) = A * hA.pinv
    rw [mul_assoc A hA.pinv (A * hA.pinv), ← mul_assoc hA.pinv A hA.pinv,
      hA.pinv_mul_self_mul_pinv]
  isSelfAdjoint := by
    change star (A * hA.pinv) = A * hA.pinv
    have hAstar : star A = A := hA.isHermitian.isSelfAdjoint
    have hPstar : star hA.pinv = hA.pinv := hA.posSemidef_pinv.isHermitian.isSelfAdjoint
    rw [star_mul, hPstar, hAstar, ← hA.mul_pinv_eq_pinv_mul]

/-- `hA.pinv * A` is a star projection (self-adjoint idempotent) — the orthogonal projector onto
`range A`, same as `A * hA.pinv` by `mul_pinv_eq_pinv_mul`. -/
theorem Matrix.PosSemidef.isStarProjection_pinv_mul {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) :
    IsStarProjection (hA.pinv * A) :=
  hA.mul_pinv_eq_pinv_mul ▸ hA.isStarProjection_mul_pinv
