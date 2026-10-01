import SeparableFanMajorization.ForMathlib.MatrixSqrt
import SeparableFanMajorization.ForMathlib.MatrixPseudoinverse

/-!
# Douglas' factorization lemma for block positive semidefinite matrices

Not in Mathlib. The finite-dimensional matrix form of Douglas' factorization theorem
(R. G. Douglas, *On majorization, factorization, and range inclusion of operators on
Hilbert space*, Proc. Amer. Math. Soc. 17 (1966), 413–415): if `[[X, Z], [Zᴴ, Y]]` is
positive semidefinite, then `Z` factors as `Z = X.sqrt * K * Y.sqrt`
(`Matrix.PosSemidef.sqrt`, `MatrixSqrt.lean`) through a *contraction* `K`
(`Matrix.IsContraction`, i.e. `K * Kᴴ ≤ 1` in the Loewner order,
`Mathlib.Analysis.Matrix.Order`).

A step towards `KyFanCauchySchwarz.lean`'s
`Matrix.kyFanNorm_le_max_of_fromBlocks_posSemidef`: that theorem uses this
factorization to reduce the block-PSD Ky Fan bound to bounding `kyFanNorm k` of the
sandwiched contraction `X.sqrt * K * Y.sqrt`, which is where the genuine remaining
difficulty lives.

## Proof strategy

The classical argument (Douglas 1966 / generalized Schur complement, Albert 1969),
specialized to finite dimensions.

1. **Range inclusions** (`sqrt_pinv_mul_self_of_fromBlocks`). Positive semidefiniteness
   of the block matrix forces `Z` to be fixed by the orthogonal projectors onto
   `range hX.sqrt` and `range hY.sqrt`, i.e. `range Z ⊆ range hX.sqrt` and
   `range Zᴴ ⊆ range hY.sqrt`. This comes from testing the block quadratic form on
   vectors `Sum.elim 0 v` with `v ∈ ker Y`.
2. **Pseudoinverse.** Already proved in `MatrixPseudoinverse.lean`:
   `hX.posSemidef_sqrt.pinv` and `hY.posSemidef_sqrt.pinv` are the pseudoinverses of
   `X.sqrt`, `Y.sqrt` (not of `X`, `Y`), and `hA.sqrt * hA.posSemidef_sqrt.pinv` is the
   orthogonal projector onto `range hA.sqrt`.
3. **Generalized Schur complement, then assemble.** With
   `P := hX.posSemidef_sqrt.pinv`, `Q := hY.posSemidef_sqrt.pinv`, `K := P * Z * Q`,
   step 1's identities collapse `X.sqrt * K * Y.sqrt` straight to `Z`
   (`exists_isContraction_sqrt_mul_sqrt_of_fromBlocks_posSemidef`). For
   `K.IsContraction`, substituting `v := -(Q * Q *ᵥ (Zᴴ *ᵥ u))` into the block
   quadratic form `⟨(u, v), M (u, v)⟩ ≥ 0` "completes the square" and yields the
   generalized Schur complement inequality `(X - Z * (Q * Q) * Zᴴ).PosSemidef`
   (`sub_mul_sqrt_pinv_sq_mul_conjTranspose_posSemidef_of_fromBlocks`), with no
   Cauchy–Schwarz step. Sandwiching by `P` and identifying `P * X * P ≤ 1` (a
   projector) with `P * (Z * (Q * Q) * Zᴴ) * P = K * Kᴴ` gives `K * Kᴴ ≤ 1` directly
   (`isContraction_pinv_sqrt_mul_mul_pinv_sqrt_of_fromBlocks`).

## Main results

* `Matrix.IsContraction`: a matrix `K` with `K * Kᴴ ≤ 1`.
* `Matrix.PosSemidef.sqrt_pinv_mul_self_of_fromBlocks`: roadmap step 1.
* `Matrix.PosSemidef.sub_mul_sqrt_pinv_sq_mul_conjTranspose_posSemidef_of_fromBlocks`:
  the generalized Schur complement inequality from roadmap step 3.
* `Matrix.PosSemidef.isContraction_pinv_sqrt_mul_mul_pinv_sqrt_of_fromBlocks`: roadmap
  step 3's contraction bound.
* `Matrix.exists_isContraction_sqrt_mul_sqrt_of_fromBlocks_posSemidef`: the
  factorization itself.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

/-- A matrix `K` is a *contraction* if `K * Kᴴ ≤ 1` in the Loewner order
(`Mathlib.Analysis.Matrix.Order`). -/
def Matrix.IsContraction (K : Matrix ι ι 𝕜) : Prop := K * Kᴴ ≤ 1

/-- `K.IsContraction` unfolds to `K * Kᴴ ≤ 1`. -/
theorem Matrix.isContraction_iff {K : Matrix ι ι 𝕜} :
    K.IsContraction ↔ K * Kᴴ ≤ 1 := Iff.rfl

omit [DecidableEq ι] in
/-- The "adjoint swap" identity `star x ⬝ᵥ (A *ᵥ y) = star (Aᴴ *ᵥ x) ⬝ᵥ y`, used repeatedly by
the generalized Schur complement argument below. -/
private theorem Matrix.dotProduct_mulVec_eq_star_conjTranspose_mulVec_dotProduct
    {A : Matrix ι ι 𝕜} (x y : ι → 𝕜) :
    star x ⬝ᵥ (A *ᵥ y) = star (Aᴴ *ᵥ x) ⬝ᵥ y := by
  rw [dotProduct_mulVec, mulVec_conjTranspose, star_star]

omit [DecidableEq ι] in
/-- `fromBlocks_mulVec` specialized to a `Sum.elim` input, isolated since both block-quadratic-form
computations below expand a `fromBlocks` matrix applied to `Sum.elim x y`. -/
private theorem Matrix.fromBlocks_mulVec_sumElim {A C B D : Matrix ι ι 𝕜} (x y : ι → 𝕜) :
    (Matrix.fromBlocks A C B D) *ᵥ Sum.elim x y = Sum.elim (A *ᵥ x + C *ᵥ y) (B *ᵥ x + D *ᵥ y) := by
  rw [fromBlocks_mulVec]; simp

omit [DecidableEq ι] in
/-- If `C` is the off-diagonal block of a positive semidefinite `fromBlocks A C Cᴴ B` and `v` is
killed by `B`, then `v` is also killed by `C`: the kernel-inclusion half of roadmap step 1,
applied below to `fromBlocks X Z Zᴴ Y` and to its `Sum.swap`-submatrix. Proved by testing
positive semidefiniteness at `Sum.elim 0 v`, whose quadratic form reduces to
`star v ⬝ᵥ (B *ᵥ v)` and vanishes by `hv`; `Matrix.PosSemidef.dotProduct_mulVec_zero_iff` then
forces the whole block row `C *ᵥ v` to vanish too. -/
private theorem Matrix.PosSemidef.mulVec_eq_zero_of_mulVec_eq_zero_of_fromBlocks
    {A C B : Matrix ι ι 𝕜} (h : (Matrix.fromBlocks A C Cᴴ B).PosSemidef)
    {v : ι → 𝕜} (hv : B *ᵥ v = 0) : C *ᵥ v = 0 := by
  classical
  have hstar : star (Sum.elim (0 : ι → 𝕜) v) = Sum.elim (0 : ι → 𝕜) (star v) := by
    simp [Function.star_sumElim]
  have hM : (Matrix.fromBlocks A C Cᴴ B) *ᵥ Sum.elim (0 : ι → 𝕜) v =
      Sum.elim (C *ᵥ v) (B *ᵥ v) := by
    rw [fromBlocks_mulVec_sumElim]; simp
  have hzero : star (Sum.elim (0 : ι → 𝕜) v) ⬝ᵥ
      ((Matrix.fromBlocks A C Cᴴ B) *ᵥ Sum.elim (0 : ι → 𝕜) v) = 0 := by
    rw [hM, hstar, sumElim_dotProduct_sumElim, zero_dotProduct, zero_add, hv, dotProduct_zero]
  have hker := (h.dotProduct_mulVec_zero_iff (Sum.elim (0 : ι → 𝕜) v)).mp hzero
  rw [hM] at hker
  funext j
  simpa using congrFun hker (Sum.inl j)

/-- `C` is fixed by the orthogonal projector onto `range hB.sqrt` on the right: the matrix-identity
form of `mulVec_eq_zero_of_mulVec_eq_zero_of_fromBlocks` above. Proved by applying that lemma to
`w - Q *ᵥ w` for `Q := hB.sqrt * hB.posSemidef_sqrt.pinv`, which `B` kills since `Q` fixes
`hB.sqrt`. -/
private theorem Matrix.PosSemidef.mul_sqrt_mul_pinv_eq_of_fromBlocks {A C B : Matrix ι ι 𝕜}
    (hB : B.PosSemidef) (h : (Matrix.fromBlocks A C Cᴴ B).PosSemidef) :
    C * (hB.sqrt * hB.posSemidef_sqrt.pinv) = C := by
  set Q := hB.sqrt * hB.posSemidef_sqrt.pinv with hQ_def
  have hsqrtQ : hB.sqrt * Q = hB.sqrt := by
    have h1 : hB.sqrt * hB.posSemidef_sqrt.pinv * hB.sqrt = hB.sqrt :=
      hB.posSemidef_sqrt.mul_pinv_mul_self
    rw [← hQ_def] at h1
    have hQsa : star Q = Q := hB.posSemidef_sqrt.isStarProjection_mul_pinv.isSelfAdjoint
    have hSherm : star hB.sqrt = hB.sqrt := hB.posSemidef_sqrt.isHermitian.star_eq
    have hstar := congrArg star h1
    rwa [star_mul, hQsa, hSherm] at hstar
  rw [ext_iff_mulVec]
  intro w
  have hv : hB.sqrt *ᵥ (w - Q *ᵥ w) = 0 := by
    rw [mulVec_sub, mulVec_mulVec, hsqrtQ, sub_self]
  have hBv : B *ᵥ (w - Q *ᵥ w) = 0 := by
    rw [← hB.sqrt_mul_sqrt, ← mulVec_mulVec, hv, mulVec_zero]
  have hCv : C *ᵥ w - C *ᵥ (Q *ᵥ w) = 0 := by
    rw [← mulVec_sub]
    exact h.mulVec_eq_zero_of_mulVec_eq_zero_of_fromBlocks hBv
  rw [← mulVec_mulVec]
  exact (sub_eq_zero.mp hCv).symm

/-- The left-sided form of `mul_sqrt_mul_pinv_eq_of_fromBlocks`: the same right-fixed-point
identity, adjointed (the projector is self-adjoint) into `(hB.sqrt * pinv) * Cᴴ = Cᴴ`. Used twice
below (directly, and via the `Sum.swap`-submatrix) so both steps are packaged together here. -/
private theorem Matrix.PosSemidef.pinv_sqrt_mul_eq_of_fromBlocks {A C B : Matrix ι ι 𝕜}
    (hB : B.PosSemidef) (h : (Matrix.fromBlocks A C Cᴴ B).PosSemidef) :
    (hB.sqrt * hB.posSemidef_sqrt.pinv) * Cᴴ = Cᴴ := by
  have heq := hB.mul_sqrt_mul_pinv_eq_of_fromBlocks h
  have hadj := congrArg Matrix.conjTranspose heq
  rwa [conjTranspose_mul,
    hB.posSemidef_sqrt.isStarProjection_mul_pinv.isSelfAdjoint.isHermitian.eq] at hadj

/-- **Range inclusions, in projector form** (roadmap step 1). If `[[X, Z], [Zᴴ, Y]]` is positive
semidefinite, `Z` is fixed by the orthogonal projector onto `range hX.sqrt` on the left, and by
the orthogonal projector onto `range hY.sqrt` on the right — equivalently, `range Z ⊆ range
hX.sqrt` and `range Zᴴ ⊆ range hY.sqrt`.

The right-hand identity is `mul_sqrt_mul_pinv_eq_of_fromBlocks` applied to `h`; the left-hand one
is `pinv_sqrt_mul_eq_of_fromBlocks` applied to the `Sum.swap`-submatrix `fromBlocks Y Zᴴ Z X`
(positive semidefinite by `Matrix.PosSemidef.submatrix`, identified via
`fromBlocks_submatrix_sum_swap_sum_swap`). -/
theorem Matrix.PosSemidef.sqrt_pinv_mul_self_of_fromBlocks {X Y Z : Matrix ι ι 𝕜}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (h : (Matrix.fromBlocks X Z Zᴴ Y).PosSemidef) :
    (hX.sqrt * hX.posSemidef_sqrt.pinv) * Z = Z ∧
      Z * (hY.sqrt * hY.posSemidef_sqrt.pinv) = Z := by
  refine ⟨?_, hY.mul_sqrt_mul_pinv_eq_of_fromBlocks h⟩
  have hSwap : (Matrix.fromBlocks Y Zᴴ Zᴴᴴ X).PosSemidef := by
    rw [conjTranspose_conjTranspose, ← fromBlocks_submatrix_sum_swap_sum_swap]
    exact h.submatrix Sum.swap
  have hadj := hX.pinv_sqrt_mul_eq_of_fromBlocks hSwap
  rwa [conjTranspose_conjTranspose] at hadj

/-- Both forms of "the pinv sandwiches `A` down to the range-projector `hA.sqrt *
hA.posSemidef_sqrt.pinv`": needed as `A * (P * P) = hA.sqrt * P` by the Schur complement
inequality below and as `P * A * P = hA.sqrt * P` by the contraction bound after it. Proved
together since both reduce to the same idempotence fact. -/
private theorem Matrix.PosSemidef.pinv_mul_self_mul_pinv_eq_sqrt_mul_pinv {A : Matrix ι ι 𝕜}
    (hA : A.PosSemidef) :
    hA.posSemidef_sqrt.pinv * A * hA.posSemidef_sqrt.pinv = hA.sqrt * hA.posSemidef_sqrt.pinv ∧
      A * (hA.posSemidef_sqrt.pinv * hA.posSemidef_sqrt.pinv) =
        hA.sqrt * hA.posSemidef_sqrt.pinv := by
  set P := hA.posSemidef_sqrt.pinv with hP_def
  have hcomm : hA.sqrt * P = P * hA.sqrt := hA.posSemidef_sqrt.mul_pinv_eq_pinv_mul
  have hidem : (hA.sqrt * P) * (hA.sqrt * P) = hA.sqrt * P :=
    hA.posSemidef_sqrt.isStarProjection_mul_pinv.isIdempotentElem
  refine ⟨?_, ?_⟩
  · calc P * A * P = P * (hA.sqrt * hA.sqrt) * P := by rw [hA.sqrt_mul_sqrt]
      _ = (P * hA.sqrt) * (hA.sqrt * P) := by simp only [mul_assoc]
      _ = (hA.sqrt * P) * (hA.sqrt * P) := by rw [← hcomm]
      _ = hA.sqrt * P := hidem
  · calc A * (P * P) = hA.sqrt * hA.sqrt * (P * P) := by rw [hA.sqrt_mul_sqrt]
      _ = hA.sqrt * (hA.sqrt * P) * P := by simp only [mul_assoc]
      _ = hA.sqrt * (P * hA.sqrt) * P := by rw [hcomm]
      _ = (hA.sqrt * P) * (hA.sqrt * P) := by simp only [mul_assoc]
      _ = hA.sqrt * P := hidem

/-- **The generalized Schur complement inequality** (roadmap step 3). If `[[X, Z], [Zᴴ, Y]]` is
positive semidefinite, then `X - Z * (hY.posSemidef_sqrt.pinv * hY.posSemidef_sqrt.pinv) * Zᴴ`
is positive semidefinite.

Proof: `PY * PY` (`PY := hY.posSemidef_sqrt.pinv`) plays the role of a pseudoinverse of `Y`
itself, so substituting `v := -((PY * PY) *ᵥ (Zᴴ *ᵥ u))` into the block quadratic form
`0 ≤ ⟨(u, v), M (u, v)⟩` "completes the square": every cross term collapses to the single
quantity `t := star (Zᴴ *ᵥ u) ⬝ᵥ ((PY * PY) *ᵥ (Zᴴ *ᵥ u))`, leaving
`0 ≤ star u ⬝ᵥ (X *ᵥ u) - t`, exactly the wanted bound. No Cauchy–Schwarz step. -/
theorem Matrix.PosSemidef.sub_mul_sqrt_pinv_sq_mul_conjTranspose_posSemidef_of_fromBlocks
    {X Y Z : Matrix ι ι 𝕜} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (h : (Matrix.fromBlocks X Z Zᴴ Y).PosSemidef) :
    (X - Z * (hY.posSemidef_sqrt.pinv * hY.posSemidef_sqrt.pinv) * Zᴴ).PosSemidef := by
  set PY := hY.posSemidef_sqrt.pinv with hPY_def
  have hR_eq : Y * (PY * PY) = hY.sqrt * PY := hY.pinv_mul_self_mul_pinv_eq_sqrt_mul_pinv.2
  have hRZ : (hY.sqrt * PY) * Zᴴ = Zᴴ := hY.pinv_sqrt_mul_eq_of_fromBlocks h
  have hYinvZ : Y * (PY * PY) * Zᴴ = Zᴴ := by rw [hR_eq]; exact hRZ
  have hYinvHerm : (PY * PY)ᴴ = PY * PY := by
    rw [conjTranspose_mul, hY.posSemidef_sqrt.posSemidef_pinv.isHermitian.eq]
  have hHerm : (X - Z * (PY * PY) * Zᴴ).IsHermitian := by
    have hSherm : (Z * (PY * PY) * Zᴴ)ᴴ = Z * (PY * PY) * Zᴴ := by
      rw [conjTranspose_mul, conjTranspose_mul, conjTranspose_conjTranspose, hYinvHerm]
      noncomm_ring
    exact hX.isHermitian.sub hSherm
  refine PosSemidef.of_dotProduct_mulVec_nonneg hHerm fun u => ?_
  set q : ι → 𝕜 := Zᴴ *ᵥ u with hq_def
  set p : ι → 𝕜 := (PY * PY) *ᵥ q with hp_def
  set t : 𝕜 := star q ⬝ᵥ p with ht_def
  have htu : star u ⬝ᵥ (Z *ᵥ p) = t := by
    rw [ht_def, Matrix.dotProduct_mulVec_eq_star_conjTranspose_mulVec_dotProduct (A := Z),
      ← hq_def]
  have htp : star p ⬝ᵥ q = t := by
    rw [ht_def, hp_def,
      Matrix.dotProduct_mulVec_eq_star_conjTranspose_mulVec_dotProduct (A := PY * PY), hYinvHerm]
  have hYp : Y *ᵥ p = q := by
    rw [hp_def, hq_def, mulVec_mulVec, mulVec_mulVec, hYinvZ]
  have hSu : star u ⬝ᵥ ((Z * (PY * PY) * Zᴴ) *ᵥ u) = t := by
    rw [← mulVec_mulVec, ← mulVec_mulVec, ← hq_def, ← hp_def, htu]
  have hterm2 : star u ⬝ᵥ (Z *ᵥ (-p)) = -t := by
    rw [mulVec_neg, dotProduct_neg, htu]
  have hterm3 : star (-p) ⬝ᵥ (Zᴴ *ᵥ u) = -t := by
    rw [star_neg, neg_dotProduct, ← hq_def, htp]
  have hterm4 : star (-p) ⬝ᵥ (Y *ᵥ (-p)) = t := by
    rw [mulVec_neg, dotProduct_neg, hYp, star_neg, neg_dotProduct, neg_neg]
    exact htp
  have hMval : (Matrix.fromBlocks X Z Zᴴ Y) *ᵥ Sum.elim u (-p) =
      Sum.elim (X *ᵥ u + Z *ᵥ (-p)) (Zᴴ *ᵥ u + Y *ᵥ (-p)) := fromBlocks_mulVec_sumElim u (-p)
  have hstarw : star (Sum.elim u (-p)) = Sum.elim (star u) (star (-p)) :=
    Function.star_sumElim u (-p)
  have hM2 := h.dotProduct_mulVec_nonneg (Sum.elim u (-p))
  rw [hMval, hstarw, sumElim_dotProduct_sumElim, dotProduct_add, dotProduct_add, hterm2, hterm3,
    hterm4] at hM2
  have heq : star u ⬝ᵥ (X *ᵥ u) + -t + (-t + t) = star u ⬝ᵥ (X *ᵥ u) - t := by ring
  rw [heq] at hM2
  rw [sub_mulVec, dotProduct_sub, sub_nonneg, hSu]
  exact sub_nonneg.mp hM2

/-- **Contraction bound on the pinv-sandwiched block** (roadmap step 3, second half). If
`[[X, Z], [Zᴴ, Y]]` is positive semidefinite, `hX.posSemidef_sqrt.pinv * Z *
hY.posSemidef_sqrt.pinv` is a contraction — this is the `K` that
`exists_isContraction_sqrt_mul_sqrt_of_fromBlocks_posSemidef` below uses.

Proved by sandwiching `sub_mul_sqrt_pinv_sq_mul_conjTranspose_posSemidef_of_fromBlocks` by
`P := hX.posSemidef_sqrt.pinv` on both sides (congruence preserves the Loewner order): `P * X * P`
collapses to the projector `hX.sqrt * P` (`≤ 1`), while `P * (Z * (Q * Q) * Zᴴ) * P`
(`Q := hY.posSemidef_sqrt.pinv`) is exactly `K * Kᴴ`, giving `(1 - K * Kᴴ).PosSemidef`. -/
theorem Matrix.PosSemidef.isContraction_pinv_sqrt_mul_mul_pinv_sqrt_of_fromBlocks
    {X Y Z : Matrix ι ι 𝕜} (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (h : (Matrix.fromBlocks X Z Zᴴ Y).PosSemidef) :
    (hX.posSemidef_sqrt.pinv * Z * hY.posSemidef_sqrt.pinv).IsContraction := by
  set PX := hX.posSemidef_sqrt.pinv with hPX_def
  set PY := hY.posSemidef_sqrt.pinv with hPY_def
  have hPXherm : PXᴴ = PX := hX.posSemidef_sqrt.posSemidef_pinv.isHermitian.eq
  have hPYherm : PYᴴ = PY := hY.posSemidef_sqrt.posSemidef_pinv.isHermitian.eq
  have hSchur := hX.sub_mul_sqrt_pinv_sq_mul_conjTranspose_posSemidef_of_fromBlocks hY h
  have hcongr := hSchur.mul_mul_conjTranspose_same PX
  rw [hPXherm] at hcongr
  have hK : (PX * Z * PY)ᴴ = PY * Zᴴ * PX := by
    rw [conjTranspose_mul, conjTranspose_mul, hPYherm, hPXherm, mul_assoc]
  have hPXXPX : PX * X * PX = hX.sqrt * PX := hX.pinv_mul_self_mul_pinv_eq_sqrt_mul_pinv.1
  have hexpand : PX * (X - Z * (PY * PY) * Zᴴ) * PX =
      hX.sqrt * PX - (PX * Z * PY) * (PX * Z * PY)ᴴ := by
    rw [hK, mul_sub, sub_mul, hPXXPX]
    simp only [mul_assoc]
  rw [hexpand] at hcongr
  have hpiece1 : (1 - hX.sqrt * PX).PosSemidef :=
    Matrix.le_iff.mp hX.posSemidef_sqrt.isStarProjection_mul_pinv.le_one
  have hsum := hpiece1.add hcongr
  have hsumeq : (1 - hX.sqrt * PX) + (hX.sqrt * PX - (PX * Z * PY) * (PX * Z * PY)ᴴ)
      = 1 - (PX * Z * PY) * (PX * Z * PY)ᴴ := by abel
  rw [hsumeq] at hsum
  rw [isContraction_iff, le_iff]
  exact hsum

/-- **Douglas' factorization lemma.** If `[[X, Z], [Zᴴ, Y]]` is positive semidefinite, `Z` factors
as `Z = X.sqrt * K * Y.sqrt` through a contraction `K`. Assembled from the results above plus the
pseudoinverse identities from `MatrixPseudoinverse.lean`; see the module docstring for the
roadmap. -/
theorem Matrix.exists_isContraction_sqrt_mul_sqrt_of_fromBlocks_posSemidef {X Y Z : Matrix ι ι 𝕜}
    (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (h : (Matrix.fromBlocks X Z Zᴴ Y).PosSemidef) :
    ∃ K : Matrix ι ι 𝕜, K.IsContraction ∧ Z = hX.sqrt * K * hY.sqrt := by
  refine ⟨hX.posSemidef_sqrt.pinv * Z * hY.posSemidef_sqrt.pinv,
    hX.isContraction_pinv_sqrt_mul_mul_pinv_sqrt_of_fromBlocks hY h, ?_⟩
  obtain ⟨hfix1, hfix2⟩ := hX.sqrt_pinv_mul_self_of_fromBlocks hY h
  -- Associativity, then `X.sqrt`/pinv commuting, then step 1's identities collapse `K` to `Z`.
  have hassoc : hX.sqrt * (hX.posSemidef_sqrt.pinv * Z * hY.posSemidef_sqrt.pinv) * hY.sqrt
      = hX.sqrt * hX.posSemidef_sqrt.pinv * Z * (hY.posSemidef_sqrt.pinv * hY.sqrt) := by
    noncomm_ring
  rw [hassoc, ← hY.posSemidef_sqrt.mul_pinv_eq_pinv_mul, hfix1, hfix2]
