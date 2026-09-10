import Mathlib.Data.Matrix.ColumnRowPartitioned
import NewProject.ForMathlib.ContractionFactorization
import NewProject.ForMathlib.KyFanMaxPrinciple
import NewProject.ForMathlib.KyFanNorm
import NewProject.ForMathlib.MatrixAbs

/-!
# Cauchy–Schwarz inequality for Ky Fan norms

Not in Mathlib. The matrix-analysis Cauchy–Schwarz inequality for unitarily invariant norms
(Bhatia, *Matrix Analysis*, `IX.5`), specialized to Ky Fan norms (`Matrix.kyFanNorm`,
`KyFanNorm.lean`): for rectangular `L, R : Matrix κ ι 𝕜` (both mapping "out of" `ι`, so `Lᴴ * R`,
`Lᴴ * L`, `Rᴴ * R` are all square `ι`-by-`ι`),
```
(Lᴴ * R).kyFanNorm k ≤ √((Lᴴ * L).kyFanNorm k * (Rᴴ * R).kyFanNorm k).
```
The hardest and only genuinely new piece of matrix analysis needed by
`SumKroneckerWeakMajorization.lean`'s final theorem, resting on
`Matrix.exists_isometryPair_trace_eq_kyFanNorm` (`KyFanNorm.lean`), that
`kyFanNorm_sqrt_mul_contraction_mul_sqrt_le_max` below rests on.

## Proof strategy (roadmap)

The standard route is the arithmetic-geometric-mean scaling trick: `[[Lᴴ*L, Lᴴ*R], [(Lᴴ*R)ᴴ,
Rᴴ*R]] = [L R]ᴴ * [L R] ≥ 0` (`Matrix.posSemidef_conjTranspose_mul_self`, applied to the horizontal
concatenation of `L`, `R`), so for every `t > 0` the congruence by `diag(√t • 1, t⁻¹/² • 1)` gives
`[[t • (Lᴴ*L), Lᴴ*R], [(Lᴴ*R)ᴴ, t⁻¹ • (Rᴴ*R)]] ≥ 0`. Feeding this into
`kyFanNorm_le_max_of_fromBlocks_posSemidef` below (with `X := t • (Lᴴ*L)`, `Y := t⁻¹ • (Rᴴ*R)`, `Z
:= Lᴴ*R`) gives `(Lᴴ*R).kyFanNorm k ≤ max (t * (Lᴴ*L).kyFanNorm k) (t⁻¹ * (Rᴴ*R).kyFanNorm k)` for
every `t > 0`; optimizing over `t` (balancing the two terms) yields the Cauchy–Schwarz bound.

`kyFanNorm_le_max_of_fromBlocks_posSemidef` itself assembles from three pieces: it extracts `X`,
`Y`'s diagonal-block positive semidefiniteness (via `Matrix.PosSemidef.submatrix`), applies
`ContractionFactorization.lean`'s Douglas factorization lemma
(`Matrix.exists_isContraction_sqrt_mul_sqrt_of_fromBlocks_posSemidef` gives
`Z = X.sqrt * K * Y.sqrt` for a contraction `K`), and feeds the result into
`kyFanNorm_sqrt_mul_contraction_mul_sqrt_le_max` below
(bounds `kyFanNorm k` of that sandwiched contraction by `max (X.kyFanNorm k) (Y.kyFanNorm k)`, a
genuine step up in difficulty from naive submultiplicativity — a form of Bhatia–Kittaneh, *Math.
Ann.* 287 (1990); see the note above it).
`kyFanNorm_conjTranspose_mul_le` itself assembles below from the congruence and block-matrix
algebra above via `Mathlib.Data.Matrix.ColumnRowPartitioned`/`Block`'s API, the optimization over
`t` resolved by an explicit finite argument in every case (no limits), plus one extra fact —
`Matrix.kyFanNorm` scales linearly under a nonnegative real `smul` (`KyFanNorm.lean`'s
`Matrix.kyFanNorm_smul`), resting on `EigenvalueScaling.lean`'s
`Matrix.IsHermitian.eigenvalues₀_smul` (scaling of a Hermitian matrix's `eigenvalues₀` under
nonnegative real `smul`).

### The sandwiched-contraction bound: a compound-matrix-free route

`kyFanNorm_sqrt_mul_contraction_mul_sqrt_le_max` cannot be derived from
`kyFanNorm_le_max_of_fromBlocks_posSemidef` (that would be circular: the latter reduces to the
former via Douglas factorization, and conversely feeding `X, Y, K` into the congruence
`fromBlocks X (X.sqrt*K*Y.sqrt) _ Y = diag(X.sqrt,Y.sqrt) * fromBlocks 1 K Kᴴ 1 *
diag(X.sqrt,Y.sqrt)` — PSD since `fromBlocks 1 K Kᴴ 1 ≥ 0` for a contraction `K`, by the Schur
complement `1 - Kᴴ*1⁻¹*K ≥ 0` — recovers the former from the latter just as directly). It follows
the classical "Ky Fan variational formula" route instead, via three sub-results:

1. **`Matrix.exists_isometryPair_trace_eq_kyFanNorm`** (`KyFanNorm.lean`): any `Z`'s `kyFanNorm k`
   is realized exactly as `Tr(Uᴴ*Z*V)` for some isometry pair `U, V : Matrix ι (Fin k) 𝕜`
   (`Uᴴ*U = 1`, `Vᴴ*V = 1`) — take
   `U`, `V` to be the top-`k` columns (by singular value) of `Z`'s SVD (`Matrix.exists_svd`,
   `SingularValueDecomposition.lean`).
2. **`Matrix.norm_trace_conjTranspose_mul_contraction_mul_le`**: for such a pair
   `P, Q : Matrix ι (Fin k) 𝕜` and a contraction `K`, `‖Tr(Pᴴ*K*Q)‖ ≤ √(Tr(Pᴴ*P)) * √(Tr(Qᴴ*Q))` —
   Cauchy–Schwarz for the Frobenius/Hilbert–Schmidt trace pairing, via `EuclideanSpace`/`PiLp`'s
   inner product on matrix columns, composed with the operator-norm bound `‖K*Q‖ ≤ ‖Q‖` a
   contraction gives.
3. **`Matrix.isStarProjection_mul_conjTranspose_of_conjTranspose_mul_self_eq_one`**
   (`Projector.lean`): an isometry `U` (`Uᴴ*U = 1`) makes `U*Uᴴ` a rank-`k` star projection —
   routine linear algebra
   (`Matrix.rank_conjTranspose_mul_self`/`Matrix.rank_self_mul_conjTranspose`/`Matrix.rank_one`),
   needed to feed `U*Uᴴ` into `KyFanMaxPrinciple.lean`'s general Ky Fan maximum principle
   (`Matrix.IsHermitian.trace_mul_le_topSum_of_isStarProjection`).

`kyFanNorm_sqrt_mul_contraction_mul_sqrt_le_max` itself assembles below: write
`Z := X.sqrt*K*Y.sqrt`, take `U, V` realizing `Z.kyFanNorm k` via 1., set `P := X.sqrt*U`,
`Q := Y.sqrt*V` (so `Pᴴ*K*Q = Uᴴ*Z*V` and `Pᴴ*P = Uᴴ*X*U`, `Qᴴ*Q = Vᴴ*Y*V`, using
`X.sqrt`/`Y.sqrt`'s self-adjointness and `sqrt_mul_sqrt`), apply 2. to bound `Z.kyFanNorm k` by
`√(Tr(Uᴴ*X*U)) * √(Tr(Vᴴ*Y*V))`, bound each trace by `X.kyFanNorm k`/`Y.kyFanNorm k` via the
maximum principle (using 3. and `Matrix.PosSemidef.singularValues_eq_eigenvalues₀`,
`MatrixAbs.lean`, to match singular values with eigenvalues for PSD `X`, `Y`), and finish with the
elementary bound `√a * √b ≤ max a b` for `a, b ≥ 0`.

## Main results

* `Matrix.kyFanNorm_sqrt_mul_contraction_mul_sqrt_le_max`: the sandwiched-contraction Ky Fan bound,
  resting on `exists_isometryPair_trace_eq_kyFanNorm` (`KyFanNorm.lean`).
* `Matrix.kyFanNorm_le_max_of_fromBlocks_posSemidef`: the block-positive-semidefinite Ky Fan bound,
  given the sandwiched-contraction bound above and `ContractionFactorization.lean`'s Douglas
  factorization lemma.
* `Matrix.kyFanNorm_conjTranspose_mul_le`: the Cauchy–Schwarz inequality itself, given the above.
-/

open Matrix
open scoped ComplexOrder MatrixOrder

variable {ι κ 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] [RCLike 𝕜]

/-- **Cauchy–Schwarz for the trace pairing, sandwiched by a contraction.** For rectangular
`P Q : Matrix ι (Fin k) 𝕜` and a contraction `K : Matrix ι ι 𝕜` (`Matrix.IsContraction`),
`‖Tr(Pᴴ * K * Q)‖ ≤ √(Tr(Pᴴ*P)) * √(Tr(Qᴴ*Q))` (both traces on the right are real and nonnegative,
being traces of the Gram matrices `Pᴴ*P`, `Qᴴ*Q`).

Proved via Mathlib's `EuclideanSpace`/`PiLp` machinery, not any from-scratch Frobenius-norm
infrastructure: `inner_matrix_col_col` identifies `(Pᴴ*K*Q) j j` with the Euclidean inner product
`⟪(Kᴴ*P)ᵀj, Qᵀj⟫` of the matrices' `j`-th columns (using `Pᴴ*K*Q = (Kᴴ*P)ᴴ*Q`), so
`Tr(Pᴴ*K*Q) = Σⱼ ⟪(Kᴴ*P)ᵀj, Qᵀj⟫`. Per-column Cauchy–Schwarz (`norm_inner_le_norm`) plus the
triangle inequality bounds this by `Σⱼ ‖(Kᴴ*P)ᵀj‖ * ‖Qᵀj‖`, and the elementary Cauchy–Schwarz for
finite sums (`Finset.sum_mul_sq_le_sq_mul_sq`) bounds that in turn by
`√(Σⱼ‖(Kᴴ*P)ᵀj‖²) * √(Σⱼ‖Qᵀj‖²)`. The second factor is exactly `√(Tr(Qᴴ*Q))` (`inner_matrix_col_col`
again, on `Q` against itself); the first is at most `√(Tr(Pᴴ*P))` because `K.IsContraction`
(`K*Kᴴ ≤ 1`) makes `Pᴴ*P - Pᴴ*(K*Kᴴ)*P` positive semidefinite
(`Matrix.PosSemidef.mul_mul_conjTranspose_same`, congruence by `Pᴴ`), hence trace-nonnegative. -/
theorem Matrix.norm_trace_conjTranspose_mul_contraction_mul_le {k : ℕ}
    (P Q : Matrix ι (Fin k) 𝕜) {K : Matrix ι ι 𝕜} (hK : K.IsContraction) :
    ‖(Pᴴ * K * Q).trace‖ ≤
      Real.sqrt (RCLike.re (Pᴴ * P).trace) * Real.sqrt (RCLike.re (Qᴴ * Q).trace) := by
  set a : Fin k → ℝ := fun j => ‖(WithLp.toLp 2 ((Kᴴ * P)ᵀ j) : EuclideanSpace 𝕜 ι)‖ with ha_def
  set b : Fin k → ℝ := fun j => ‖(WithLp.toLp 2 (Qᵀ j) : EuclideanSpace 𝕜 ι)‖ with hb_def
  have hPKQ : Pᴴ * K * Q = (Kᴴ * P)ᴴ * Q := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  have hentry : ∀ j, (Pᴴ * K * Q) j j
      = (inner 𝕜 (WithLp.toLp 2 ((Kᴴ * P)ᵀ j) : EuclideanSpace 𝕜 ι)
          (WithLp.toLp 2 (Qᵀ j) : EuclideanSpace 𝕜 ι) : 𝕜) := by
    intro j; rw [hPKQ]; exact (inner_matrix_col_col (Kᴴ * P) Q j j).symm
  -- Per-column Cauchy–Schwarz, then the triangle inequality over columns.
  have hstep : ∀ j, ‖(Pᴴ * K * Q) j j‖ ≤ a j * b j := by
    intro j; rw [hentry j]; exact norm_inner_le_norm _ _
  have htrace : (Pᴴ * K * Q).trace = ∑ j, (Pᴴ * K * Q) j j := by
    simp [Matrix.trace, Matrix.diag]
  have htri : ‖(Pᴴ * K * Q).trace‖ ≤ ∑ j, a j * b j := by
    calc ‖(Pᴴ * K * Q).trace‖ = ‖∑ j, (Pᴴ * K * Q) j j‖ := by rw [htrace]
      _ ≤ ∑ j, ‖(Pᴴ * K * Q) j j‖ := norm_sum_le _ _
      _ ≤ ∑ j, a j * b j := Finset.sum_le_sum fun j _ => hstep j
  -- The elementary (outer) Cauchy–Schwarz for the finite sum over columns.
  have hCSsq : (∑ j, a j * b j) ^ 2 ≤ (∑ j, a j ^ 2) * ∑ j, b j ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b
  have hsum_nonneg : 0 ≤ ∑ j, a j * b j :=
    Finset.sum_nonneg fun j _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have houter : ∑ j, a j * b j ≤ Real.sqrt ((∑ j, a j ^ 2) * ∑ j, b j ^ 2) := by
    rw [← Real.sqrt_sq hsum_nonneg]; exact Real.sqrt_le_sqrt hCSsq
  -- `∑ⱼ b j ^ 2 = Tr(Qᴴ*Q)` exactly; `∑ⱼ a j ^ 2 ≤ Tr(Pᴴ*P)` using `K.IsContraction`.
  have hre_sum : ∀ f : Fin k → 𝕜, RCLike.re (∑ j, f j) = ∑ j, RCLike.re (f j) :=
    fun f => map_sum RCLike.reLm f Finset.univ
  -- For any `M : Matrix ι (Fin k) 𝕜`, `∑ⱼ ‖Mᵀj‖² = Tr(Mᴴ*M)`; instantiate at `Q` and at `Kᴴ*P`.
  have hcol_sq_sum : ∀ M : Matrix ι (Fin k) 𝕜,
      ∑ j, ‖(WithLp.toLp 2 (Mᵀ j) : EuclideanSpace 𝕜 ι)‖ ^ 2 = RCLike.re (Mᴴ * M).trace := by
    intro M
    have h1 : (Mᴴ * M).trace = ∑ j, (Mᴴ * M) j j := by simp [Matrix.trace, Matrix.diag]
    rw [h1, hre_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← inner_self_eq_norm_sq (𝕜 := 𝕜) (WithLp.toLp 2 (Mᵀ j) : EuclideanSpace 𝕜 ι)]
    exact congrArg RCLike.re (inner_matrix_col_col M M j j)
  have hbsum : ∑ j, b j ^ 2 = RCLike.re (Qᴴ * Q).trace := hcol_sq_sum Q
  have hasum : ∑ j, a j ^ 2 = RCLike.re ((Kᴴ * P)ᴴ * (Kᴴ * P)).trace := hcol_sq_sum (Kᴴ * P)
  have hcontr : RCLike.re ((Kᴴ * P)ᴴ * (Kᴴ * P)).trace ≤ RCLike.re (Pᴴ * P).trace := by
    have hKKcc : (Kᴴ * P)ᴴ * (Kᴴ * P) = Pᴴ * (K * Kᴴ) * P := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
      simp only [Matrix.mul_assoc]
    rw [hKKcc]
    have hPSDdiff : (Pᴴ * P - Pᴴ * (K * Kᴴ) * P).PosSemidef := by
      have hsub : (1 - K * Kᴴ).PosSemidef := Matrix.le_iff.mp hK
      have hcong := hsub.mul_mul_conjTranspose_same (Pᴴ)
      rw [Matrix.conjTranspose_conjTranspose] at hcong
      rwa [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul] at hcong
    have hnn := hPSDdiff.trace_nonneg
    rw [Matrix.trace_sub, sub_nonneg] at hnn
    exact RCLike.re_monotone hnn
  have haSum_le : ∑ j, a j ^ 2 ≤ RCLike.re (Pᴴ * P).trace := by rw [hasum]; exact hcontr
  have hbSq_nonneg : 0 ≤ ∑ j, b j ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  have hfinal : (∑ j, a j ^ 2) * ∑ j, b j ^ 2
      ≤ RCLike.re (Pᴴ * P).trace * RCLike.re (Qᴴ * Q).trace := by
    calc (∑ j, a j ^ 2) * ∑ j, b j ^ 2
        ≤ RCLike.re (Pᴴ * P).trace * ∑ j, b j ^ 2 :=
          mul_le_mul_of_nonneg_right haSum_le hbSq_nonneg
      _ = RCLike.re (Pᴴ * P).trace * RCLike.re (Qᴴ * Q).trace := by rw [hbsum]
  have haPP_nonneg : 0 ≤ RCLike.re (Pᴴ * P).trace :=
    le_trans (Finset.sum_nonneg fun j _ => sq_nonneg (a j)) haSum_le
  calc ‖(Pᴴ * K * Q).trace‖
      ≤ ∑ j, a j * b j := htri
    _ ≤ Real.sqrt ((∑ j, a j ^ 2) * ∑ j, b j ^ 2) := houter
    _ ≤ Real.sqrt (RCLike.re (Pᴴ * P).trace * RCLike.re (Qᴴ * Q).trace) := Real.sqrt_le_sqrt hfinal
    _ = Real.sqrt (RCLike.re (Pᴴ * P).trace) * Real.sqrt (RCLike.re (Qᴴ * Q).trace) :=
        Real.sqrt_mul haPP_nonneg _

/-- **Sandwiched-contraction Ky Fan bound.** For `X, Y` positive semidefinite and `K` a contraction
(`Matrix.IsContraction`, i.e. `K * Kᴴ ≤ 1`), the Ky Fan `k`-norm of `X.sqrt * K * Y.sqrt` is at
most the larger of `X`, `Y`'s Ky Fan `k`-norms — the genuinely hard step that
`kyFanNorm_le_max_of_fromBlocks_posSemidef` below reduces to, via `ContractionFactorization.lean`'s
Douglas factorization lemma.

Not implied by submultiplicativity of `kyFanNorm` under a contraction: the naive bound that gives,
`(X.sqrt * K * Y.sqrt).kyFanNorm k ≤ ‖X.sqrt‖ * ‖Y.sqrt‖ * k` (bounding `K`'s contribution by its
operator norm `≤ 1` and each `kyFanNorm k` factor trivially by `k` times the operator norm), bounds
the target via `X`, `Y`'s *operator* norms (times `k`), not their Ky Fan `k`-norms, and so does not
close this inequality. (Contrast with the `k = 1` case, i.e. the operator norm itself, which needs
none of this: `‖X.sqrt * K * Y.sqrt‖ ≤ max(‖X‖,‖Y‖)` follows immediately from `‖K‖ ≤ 1` and
`‖X.sqrt‖² = ‖X‖`, `‖Y.sqrt‖² = ‖Y‖` — the general-`k` case is a real step up in difficulty, not a
routine generalization.)

Assembled from the three sub-results above (see the module docstring's "compound-matrix-free route"
section for the full roadmap): fully proved here, resting on
`exists_isometryPair_trace_eq_kyFanNorm` (`KyFanNorm.lean`) as this file's one remaining external
black box. -/
theorem Matrix.kyFanNorm_sqrt_mul_contraction_mul_sqrt_le_max {X Y K : Matrix ι ι 𝕜}
    (hX : X.PosSemidef) (hY : Y.PosSemidef) (hK : K.IsContraction) (k : ℕ) :
    (hX.sqrt * K * hY.sqrt).kyFanNorm k ≤ max (X.kyFanNorm k) (Y.kyFanNorm k) := by
  have hcore : ∀ k' ≤ Fintype.card ι,
      (hX.sqrt * K * hY.sqrt).kyFanNorm k' ≤ max (X.kyFanNorm k') (Y.kyFanNorm k') := by
    intro k' hk'
    set Z := hX.sqrt * K * hY.sqrt with hZ_def
    obtain ⟨U, V, hUU, hVV, hUZV⟩ := Z.exists_isometryPair_trace_eq_kyFanNorm hk'
    set P := hX.sqrt * U with hP_def
    set Q := hY.sqrt * V with hQ_def
    have hPQ : Pᴴ * K * Q = Uᴴ * Z * V := by
      rw [hP_def, hQ_def, hZ_def, Matrix.conjTranspose_mul, hX.posSemidef_sqrt.isHermitian.eq]
      simp only [Matrix.mul_assoc]
    have hPP : Pᴴ * P = Uᴴ * X * U := by
      rw [hP_def, Matrix.conjTranspose_mul, hX.posSemidef_sqrt.isHermitian.eq,
        show Uᴴ * hX.sqrt * (hX.sqrt * U) = Uᴴ * (hX.sqrt * hX.sqrt) * U from by
          simp only [Matrix.mul_assoc],
        hX.sqrt_mul_sqrt]
    have hQQ : Qᴴ * Q = Vᴴ * Y * V := by
      rw [hQ_def, Matrix.conjTranspose_mul, hY.posSemidef_sqrt.isHermitian.eq,
        show Vᴴ * hY.sqrt * (hY.sqrt * V) = Vᴴ * (hY.sqrt * hY.sqrt) * V from by
          simp only [Matrix.mul_assoc],
        hY.sqrt_mul_sqrt]
    have hnormeq : ‖((Z.kyFanNorm k' : ℝ) : 𝕜)‖ = Z.kyFanNorm k' := by
      rw [RCLike.norm_ofReal, abs_of_nonneg (Matrix.kyFanNorm_nonneg k' Z)]
    have hcs := Matrix.norm_trace_conjTranspose_mul_contraction_mul_le P Q hK
    rw [hPQ, hUZV, hnormeq, hPP, hQQ] at hcs
    -- Shared shape: for `M` PSD and an isometry `W`, `Tr(Wᴴ*M*W) ≤ M.kyFanNorm k'`.
    have hbound : ∀ {M : Matrix ι ι 𝕜} (_ : M.PosSemidef) {W : Matrix ι (Fin k') 𝕜},
        Wᴴ * W = 1 → RCLike.re (Wᴴ * M * W).trace ≤ M.kyFanNorm k' := by
      intro M hM W hWW
      rw [Matrix.trace_mul_cycle Wᴴ M W]
      obtain ⟨hproj, hrank⟩ :=
        Matrix.isStarProjection_mul_conjTranspose_of_conjTranspose_mul_self_eq_one hWW
      unfold Matrix.kyFanNorm
      rw [hM.singularValues_eq_eigenvalues₀]
      exact hM.isHermitian.trace_mul_le_topSum_of_isStarProjection hproj k' hrank
    have hXbound : RCLike.re (Uᴴ * X * U).trace ≤ X.kyFanNorm k' := hbound hX hUU
    have hYbound : RCLike.re (Vᴴ * Y * V).trace ≤ Y.kyFanNorm k' := hbound hY hVV
    have hamgm : Real.sqrt (X.kyFanNorm k') * Real.sqrt (Y.kyFanNorm k') ≤
        max (X.kyFanNorm k') (Y.kyFanNorm k') := by
      have ha := Matrix.kyFanNorm_nonneg k' X
      have hb := Matrix.kyFanNorm_nonneg k' Y
      have hmax : (0 : ℝ) ≤ max (X.kyFanNorm k') (Y.kyFanNorm k') := le_trans ha (le_max_left _ _)
      rw [← Real.sqrt_mul ha, ← Real.sqrt_sq hmax]
      apply Real.sqrt_le_sqrt
      calc X.kyFanNorm k' * Y.kyFanNorm k'
          ≤ max (X.kyFanNorm k') (Y.kyFanNorm k') * max (X.kyFanNorm k') (Y.kyFanNorm k') :=
            mul_le_mul (le_max_left _ _) (le_max_right _ _) hb hmax
        _ = max (X.kyFanNorm k') (Y.kyFanNorm k') ^ 2 := by ring
    exact hcs.trans ((mul_le_mul (Real.sqrt_le_sqrt hXbound) (Real.sqrt_le_sqrt hYbound)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)).trans hamgm)
  by_cases hk : k ≤ Fintype.card ι
  · exact hcore k hk
  · push Not at hk
    have hsatZ : (hX.sqrt * K * hY.sqrt).kyFanNorm k
        = (hX.sqrt * K * hY.sqrt).kyFanNorm (Fintype.card ι) := by
      unfold Matrix.kyFanNorm; exact Majorization.topSum_eq_topSum_of_le _ hk.le
    have hsatX : X.kyFanNorm k = X.kyFanNorm (Fintype.card ι) := by
      unfold Matrix.kyFanNorm; exact Majorization.topSum_eq_topSum_of_le _ hk.le
    have hsatY : Y.kyFanNorm k = Y.kyFanNorm (Fintype.card ι) := by
      unfold Matrix.kyFanNorm; exact Majorization.topSum_eq_topSum_of_le _ hk.le
    rw [hsatZ, hsatX, hsatY]
    exact hcore (Fintype.card ι) le_rfl

/-- If `[[X, Z], [Zᴴ, Y]]` is positive semidefinite, the Ky Fan `k`-norm of the off-diagonal block
`Z` is at most the larger of the two diagonal blocks' Ky Fan `k`-norms. -/
theorem Matrix.kyFanNorm_le_max_of_fromBlocks_posSemidef {X Y Z : Matrix ι ι 𝕜}
    (h : (Matrix.fromBlocks X Z Zᴴ Y).PosSemidef) (k : ℕ) :
    Z.kyFanNorm k ≤ max (X.kyFanNorm k) (Y.kyFanNorm k) := by
  have hX : X.PosSemidef := by
    have hsub := h.submatrix (Sum.inl : ι → ι ⊕ ι)
    rwa [show (Matrix.fromBlocks X Z Zᴴ Y).submatrix Sum.inl Sum.inl = X from by
      funext i j; simp] at hsub
  have hY : Y.PosSemidef := by
    have hsub := h.submatrix (Sum.inr : ι → ι ⊕ ι)
    rwa [show (Matrix.fromBlocks X Z Zᴴ Y).submatrix Sum.inr Sum.inr = Y from by
      funext i j; simp] at hsub
  obtain ⟨K, hK, hZ⟩ :=
    Matrix.exists_isContraction_sqrt_mul_sqrt_of_fromBlocks_posSemidef hX hY h
  rw [hZ]
  exact Matrix.kyFanNorm_sqrt_mul_contraction_mul_sqrt_le_max hX hY hK k

omit [DecidableEq κ] in
/-- **Cauchy–Schwarz inequality for Ky Fan norms.** For rectangular `L, R : Matrix κ ι 𝕜`, the Ky
Fan `k`-norm of `Lᴴ * R` is at most the geometric mean of the Ky Fan `k`-norms of `Lᴴ * L` and
`Rᴴ * R`. -/
theorem Matrix.kyFanNorm_conjTranspose_mul_le (L R : Matrix κ ι 𝕜) (k : ℕ) :
    (Lᴴ * R).kyFanNorm k ≤ Real.sqrt ((Lᴴ * L).kyFanNorm k * (Rᴴ * R).kyFanNorm k) := by
  set Xk := (Lᴴ * L).kyFanNorm k
  set Yk := (Rᴴ * R).kyFanNorm k
  set Zk := (Lᴴ * R).kyFanNorm k
  have hXk0 : 0 ≤ Xk := Matrix.kyFanNorm_nonneg k _
  have hYk0 : 0 ≤ Yk := Matrix.kyFanNorm_nonneg k _
  -- The AM-GM scaling trick (module docstring above), for every `t > 0` at once.
  have step1 : ∀ t : ℝ, 0 < t → Zk ≤ max (t * Xk) (t⁻¹ * Yk) := by
    intro t ht
    have hMPSD : (Matrix.fromBlocks (Lᴴ * L) (Lᴴ * R) (Rᴴ * L) (Rᴴ * R)).PosSemidef := by
      have h1 : (Matrix.fromCols L R)ᴴ * Matrix.fromCols L R
          = Matrix.fromBlocks (Lᴴ * L) (Lᴴ * R) (Rᴴ * L) (Rᴴ * R) := by
        rw [Matrix.conjTranspose_fromCols_eq_fromRows_conjTranspose, Matrix.fromRows_mul_fromCols]
      rw [← h1]
      exact Matrix.posSemidef_conjTranspose_mul_self _
    set s := Real.sqrt t with hs_def
    have hspos : 0 < s := Real.sqrt_pos.mpr ht
    have hssq : s * s = t := Real.mul_self_sqrt ht.le
    set C : Matrix (ι ⊕ ι) (ι ⊕ ι) 𝕜 :=
      Matrix.fromBlocks (s • (1 : Matrix ι ι 𝕜)) 0 0 (s⁻¹ • (1 : Matrix ι ι 𝕜)) with hC_def
    have hCH : Cᴴ = C := by
      rw [hC_def]
      simp only [Matrix.fromBlocks_conjTranspose, Matrix.conjTranspose_zero,
        Matrix.conjTranspose_smul, Matrix.conjTranspose_one, star_trivial]
    have hs_inv_mul : s⁻¹ * s = 1 := inv_mul_cancel₀ hspos.ne'
    have hs_mul_inv : s * s⁻¹ = 1 := mul_inv_cancel₀ hspos.ne'
    have hsinv_sq : s⁻¹ * s⁻¹ = t⁻¹ := by rw [← hssq, _root_.mul_inv_rev]
    have hZeq : (Lᴴ * R)ᴴ = Rᴴ * L := by
      rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    -- Congruence by `C` turns the PSD block matrix into `fromBlocks (t•(Lᴴ*L)) (Lᴴ*R) (Rᴴ*L)
    -- (t⁻¹•(Rᴴ*R))`, since `C` is Hermitian and `s*s = t`, `s*s⁻¹ = s⁻¹*s = 1`, `s⁻¹*s⁻¹ = t⁻¹`.
    have hCcomp : C * Matrix.fromBlocks (Lᴴ * L) (Lᴴ * R) (Rᴴ * L) (Rᴴ * R) * Cᴴ
        = Matrix.fromBlocks (t • (Lᴴ * L)) (Lᴴ * R) (Lᴴ * R)ᴴ (t⁻¹ • (Rᴴ * R)) := by
      rw [hZeq, hCH, hC_def]
      simp only [Matrix.fromBlocks_multiply, zero_mul, mul_zero, add_zero, zero_add,
        smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
      rw [hssq, hs_mul_inv, hs_inv_mul, hsinv_sq, one_smul, one_smul]
    have hCPSD := hMPSD.mul_mul_conjTranspose_same C
    rw [hCcomp] at hCPSD
    have hbound := Matrix.kyFanNorm_le_max_of_fromBlocks_posSemidef hCPSD k
    rw [Matrix.kyFanNorm_real_smul t k, Matrix.kyFanNorm_real_smul t⁻¹ k, abs_of_pos ht,
      abs_of_pos (inv_pos.mpr ht)] at hbound
    exact hbound
  -- Optimize over `t > 0`: split on whether `Xk`/`Yk` vanish.
  rcases eq_or_lt_of_le hXk0 with hXk0' | hXk
  · -- `Xk = 0`: force `Zk = 0` by a single well-chosen `t`, no limit needed.
    by_contra hcon
    push Not at hcon
    have hZkpos : 0 < Zk := lt_of_le_of_lt (Real.sqrt_nonneg _) hcon
    set t := Yk / Zk + 1 with ht_def
    have htpos : 0 < t := by
      have : 0 ≤ Yk / Zk := div_nonneg hYk0 hZkpos.le
      rw [ht_def]; linarith
    have hstep := step1 t htpos
    rw [← hXk0', mul_zero] at hstep
    have heqtZk : t * Zk = Yk + Zk := by
      rw [ht_def, add_mul, div_mul_cancel₀ Yk hZkpos.ne', one_mul]
    have hlt : Yk < t * Zk := by rw [heqtZk]; linarith
    have hlt2 : t⁻¹ * Yk < Zk := by
      have h1 : t⁻¹ * Yk < t⁻¹ * (t * Zk) := mul_lt_mul_of_pos_left hlt (inv_pos.mpr htpos)
      rwa [← mul_assoc, inv_mul_cancel₀ htpos.ne', one_mul] at h1
    exact absurd hstep (not_le.mpr (max_lt hZkpos hlt2))
  · rcases eq_or_lt_of_le hYk0 with hYk0' | hYk
    · -- `Xk > 0`, `Yk = 0`: symmetric finite argument.
      by_contra hcon
      push Not at hcon
      have hZkpos : 0 < Zk := lt_of_le_of_lt (Real.sqrt_nonneg _) hcon
      set t := Zk / (Xk + 1) with ht_def
      have hXk1pos : 0 < Xk + 1 := by linarith
      have htpos : 0 < t := div_pos hZkpos hXk1pos
      have hstep := step1 t htpos
      rw [← hYk0', mul_zero] at hstep
      have heq : t * Xk = Zk * Xk / (Xk + 1) := by rw [ht_def, div_mul_eq_mul_div]
      have hlt : t * Xk < Zk := by
        rw [heq, div_lt_iff₀ hXk1pos]
        nlinarith [hZkpos]
      exact absurd hstep (not_le.mpr (max_lt hlt hZkpos))
    · -- `Xk > 0` and `Yk > 0`: the genuine AM-GM optimum, `t := √(Yk / Xk)`.
      set t := Real.sqrt (Yk / Xk) with ht_def
      have htpos : 0 < t := Real.sqrt_pos.mpr (div_pos hYk hXk)
      have ht2 : t ^ 2 * Xk = Yk := by
        rw [ht_def, Real.sq_sqrt (div_nonneg hYk.le hXk.le), div_mul_cancel₀ Yk hXk.ne']
      have hinv : t⁻¹ = Real.sqrt (Xk / Yk) := by
        rw [ht_def, ← Real.sqrt_inv, inv_div]
      have ht2' : t⁻¹ ^ 2 * Yk = Xk := by
        rw [hinv, Real.sq_sqrt (div_nonneg hXk.le hYk.le), div_mul_cancel₀ Xk hYk.ne']
      have hsq1 : (t * Xk) ^ 2 = Xk * Yk := by linear_combination Xk * ht2
      have hsq2 : (t⁻¹ * Yk) ^ 2 = Xk * Yk := by linear_combination Yk * ht2'
      have heq1 : t * Xk = Real.sqrt (Xk * Yk) := by
        rw [← Real.sqrt_sq (mul_nonneg htpos.le hXk.le), hsq1]
      have heq2 : t⁻¹ * Yk = Real.sqrt (Xk * Yk) := by
        rw [← Real.sqrt_sq (mul_nonneg (inv_nonneg.mpr htpos.le) hYk.le), hsq2]
      have hstep := step1 t htpos
      rwa [heq1, heq2, max_self] at hstep
