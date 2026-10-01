import SeparableFanMajorization.ForMathlib.EigenvalueMonotonicity
import SeparableFanMajorization.ForMathlib.TraceInequality
import SeparableFanMajorization.BilinearPositivity

/-!
# Overlap bounds: `Tr[Q(A ⊗ B)] ≤ ∑ⱼ ∑ₖ λⱼ(A) λₖ(B) (min{j+1,μₖ} - min{j,μₖ})`

Two bounds on the overlap of a projector `Q` on `𝕜^dim1 ⊗ 𝕜^dim2` with a product `A ⊗ B`, where
`μ := λ(Tr₁ Q)`:

* `trace_mul_kronecker_le_sum_min`: the special case where `A = P` is itself a projector of rank
  `r`, giving the simpler bound `Tr[Q(P⊗B)] ≤ ∑ₖ min{r,μₖ} λₖ(B)`.
* `trace_mul_kronecker_le_sum_min_diff`: the general case where `A` is merely positive
  semidefinite, giving the double-sum bound `Tr[Q(A⊗B)] ≤ ∑ⱼ ∑ₖ λⱼ(A) λₖ(B) (min{j+1,μₖ} -
  min{j,μₖ})`.

We use `IsStarProjection` (a self-adjoint idempotent, `Mathlib.Algebra.Star.StarProjection`) for
"projector": for a matrix, `IsSelfAdjoint` is definitionally `Matrix.IsHermitian`
(`isHermitian_iff_isSelfAdjoint`), so `IsStarProjection Q` unfolds to `Q * Q = Q ∧ Qᴴ = Q`,
exactly the physicist's Hermitian-idempotent projector. No project-specific projector definition
is needed.
-/

open Matrix
open scoped Kronecker ComplexOrder MatrixOrder

variable {dim1 dim2 𝕜 : Type*} [Fintype dim1] [Fintype dim2] [DecidableEq dim1] [DecidableEq dim2]
  [RCLike 𝕜]

omit [DecidableEq dim1] in
/-- **Lemma**: for a projector `Q` on `𝕜^dim1 ⊗ 𝕜^dim2`, a projector `P` on `𝕜^dim1` of rank `r`,
and a positive `B` on `𝕜^dim2`,
`Tr[Q(P ⊗ B)] ≤ ∑ₖ min{r, λₖ(Tr₁ Q)} λₖ(B)`, where the eigenvalues are sorted in decreasing order
(`Matrix.IsHermitian.eigenvalues₀`).

Proof: `Φ(Q, P)`, `Φ(1-Q, P) = Φ(1,P) - Φ(Q,P)` and `Φ(Q, 1-P) = Φ(Q,1) - Φ(Q,P)` are all
positive semidefinite (since `Q`, `P`, `1-Q`, `1-P` are all projectors, hence positive), giving
the two upper bounds `Φ(Q,P) ≤ Φ(1,P) = (Tr P) • 1 = r • 1` and `Φ(Q,P) ≤ Φ(Q,1) = Tr₁ Q`. Weyl
monotonicity turns these into the pointwise eigenvalue bound
`λₖ(Φ(Q,P)) ≤ min{r, λₖ(Tr₁ Q)}`, and von Neumann's trace inequality
(`Matrix.IsHermitian.trace_mul_le`) applied to `Φ(Q,P)` and `B`, combined with the representer
property `Tr[Q(P⊗B)] = Tr[Φ(Q,P) B]` (`Phi_trace_mul`), gives the claim. -/
theorem trace_mul_kronecker_le_sum_min {Q : Matrix (dim1 × dim2) (dim1 × dim2) 𝕜}
    {P : Matrix dim1 dim1 𝕜} {B : Matrix dim2 dim2 𝕜} {r : ℕ} (hQ : IsStarProjection Q)
    (hP : IsStarProjection P) (hPr : P.rank = r) (hB : B.PosSemidef) :
    (Q * (P ⊗ₖ B)).trace
      ≤ (↑(∑ k : Fin (Fintype.card dim2),
          min (r : ℝ) (hQ.isSelfAdjoint.isHermitian.traceLeft.eigenvalues₀ k)
            * hB.isHermitian.eigenvalues₀ k) : 𝕜) := by
  classical
  have hQ' := hQ.posSemidef
  have hP' := hP.posSemidef
  have hΦQP := Phi_posSemidef hQ' hP'
  have hΦQP_herm := hΦQP.isHermitian
  -- Upper bound 1: `Φ(Q, P) ≤ (r : 𝕜) • 1`, from `Φ(1 - Q, P) ≥ 0`.
  have hle1 : Phi Q P ≤ ((r : ℝ) : 𝕜) • (1 : Matrix dim2 dim2 𝕜) := by
    have h := Phi_posSemidef hQ.one_sub.posSemidef hP'
    have hnn := Matrix.nonneg_iff_posSemidef.mpr h
    rw [Phi_sub_left, Phi_one_left, hP.trace_eq_rank, hPr, ← RCLike.ofReal_natCast r] at hnn
    exact sub_nonneg.mp hnn
  -- Upper bound 2: `Φ(Q, P) ≤ Tr₁ Q`, from `Φ(Q, 1 - P) ≥ 0`.
  have hle2 : Phi Q P ≤ Q.traceLeft := by
    have h := Phi_posSemidef hQ' hP.one_sub.posSemidef
    have hnn := Matrix.nonneg_iff_posSemidef.mpr h
    rw [Phi_sub_right, Phi_one_right] at hnn
    exact sub_nonneg.mp hnn
  -- Weyl monotonicity: combine the two upper bounds into the eigenvalue bound.
  have hbound : ∀ k, hΦQP_herm.eigenvalues₀ k
      ≤ min (r : ℝ) (hQ.isSelfAdjoint.isHermitian.traceLeft.eigenvalues₀ k) := fun k =>
    le_min (hΦQP_herm.eigenvalues₀_le_of_le_smul_one hle1 k)
      (hQ.isSelfAdjoint.isHermitian.traceLeft.eigenvalues₀_mono hΦQP_herm hle2 k)
  -- Von Neumann's trace inequality, plus the representer property.
  calc (Q * (P ⊗ₖ B)).trace
      = (Phi Q P * B).trace := (Phi_trace_mul Q P B).symm
    _ ≤ (↑(∑ k, hΦQP_herm.eigenvalues₀ k * hB.isHermitian.eigenvalues₀ k) : 𝕜) :=
        hΦQP_herm.trace_mul_le hB.isHermitian
    _ ≤ (↑(∑ k : Fin (Fintype.card dim2),
          min (r : ℝ) (hQ.isSelfAdjoint.isHermitian.traceLeft.eigenvalues₀ k)
            * hB.isHermitian.eigenvalues₀ k) : 𝕜) := by
        apply RCLike.ofReal_le_ofReal.mpr
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_right (hbound k) (hB.eigenvalues₀_nonneg k)

/-- The prefix `P_[j] := ∑_{k≤j} uₖuₖ*` of a (sorted, decreasing) orthonormal eigenbasis of a
Hermitian `A` is itself a projector. This is the "cumulative top-`k` eigenspace projector" fact
flagged as missing from Mathlib in `SpectralDecomposition.lean`'s module docstring (checked
`Mathlib.Analysis.Matrix.Spectrum`, `Mathlib.Analysis.InnerProductSpace.Spectrum`: only
*per-eigenvalue* eigenspace projectors are available there, not a ranked prefix sum).

Proof: idempotency follows by distributing the product over the double sum
(`Finset.sum_mul_sum`) and collapsing each inner sum to its `l = k` term via
`Matrix.IsHermitian.sortedRankOneProjector_mul` (`SpectralDecomposition.lean`, the shared
orthogonality fact behind both this lemma and `Matrix.IsHermitian.isStarProjection_topProjector`).
Self-adjointness is immediate since each `uₖuₖ*` is Hermitian (`Matrix.conjTranspose_vecMulVec`).
Needed by `trace_mul_kronecker_le_sum_min_diff` to apply `trace_mul_kronecker_le_sum_min` to each
`P_[j]`. -/
theorem Matrix.IsHermitian.isStarProjection_sum_Iic_vecMulVec {A : Matrix dim1 dim1 𝕜}
    (hA : A.IsHermitian) (j : Fin (Fintype.card dim1)) :
    IsStarProjection (∑ k ∈ Finset.Iic j, hA.sortedRankOneProjector k) := by
  have hidem : (∑ k ∈ Finset.Iic j, hA.sortedRankOneProjector k)
      * (∑ k ∈ Finset.Iic j, hA.sortedRankOneProjector k)
      = ∑ k ∈ Finset.Iic j, hA.sortedRankOneProjector k := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [Finset.sum_congr rfl fun l _ => hA.sortedRankOneProjector_mul k l]
    simp [hk]
  have hselfadj : star (∑ k ∈ Finset.Iic j, hA.sortedRankOneProjector k)
      = ∑ k ∈ Finset.Iic j, hA.sortedRankOneProjector k := by
    rw [star_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [Matrix.IsHermitian.sortedRankOneProjector]
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_vecMulVec, star_star]
  exact ⟨hidem, hselfadj⟩

/-- The spectral-truncation projector `P_[j]` (see
`Matrix.IsHermitian.isStarProjection_sum_Iic_vecMulVec`) has rank `j.val + 1`, the number of
eigenvectors summed over. Rather than exhibiting the rank directly (which would need linear
independence of the orthonormal eigenvectors `u₀, …, u_j`), we go via
`IsStarProjection.trace_eq_rank` (`Projector.lean`): `P_[j]`'s trace is `j.val + 1` termwise, each
`uᵢuᵢ*` contributing `1` (`Matrix.IsHermitian.trace_sortedRankOneProjector`,
`SpectralDecomposition.lean`), and equals its rank since `P_[j]` is a projector. -/
theorem Matrix.IsHermitian.rank_sum_Iic_vecMulVec {A : Matrix dim1 dim1 𝕜}
    (hA : A.IsHermitian) (j : Fin (Fintype.card dim1)) :
    (∑ k ∈ Finset.Iic j, hA.sortedRankOneProjector k).rank = (j : ℕ) + 1 := by
  -- The trace of the sum is exactly the number of terms, `j.val + 1`.
  have htrace : (∑ k ∈ Finset.Iic j, hA.sortedRankOneProjector k).trace
      = (((j : ℕ) + 1 : ℕ) : 𝕜) := by
    rw [Matrix.trace_sum, Finset.sum_congr rfl fun k _ => hA.trace_sortedRankOneProjector k,
      Finset.sum_const, Fin.card_Iic, nsmul_eq_mul, mul_one]
  -- Combine with `htrace` and cancel the (injective, char-zero) `ℕ → 𝕜` cast.
  have heq : ((∑ k ∈ Finset.Iic j, hA.sortedRankOneProjector k).rank : 𝕜)
      = (((j : ℕ) + 1 : ℕ) : 𝕜) := by
    rw [← (hA.isStarProjection_sum_Iic_vecMulVec j).trace_eq_rank]
    exact htrace
  exact_mod_cast heq

/-- Finite Abel-summation (summation-by-parts) identity for scalars: the "index-side" telescoping
counterpart to `Matrix.IsHermitian.sum_eigenvalue₀_diff_smul_sum_vecMulVec`'s "matrix-side"
telescoping (`SpectralDecomposition.lean`), needed to assemble the term-by-term bounds obtained by
applying `trace_mul_kronecker_le_sum_min` to each spectral-truncation projector `P_[j]` into the
final `min{j+1,μₖ} - min{j,μₖ}` shape. Given the boundary condition `f d = 0` (the paper's
`α_{d1+1} := 0` convention), rewrites `∑ᵢ (f i - f (i + 1)) * c i` as `∑ᵢ f i * (c i - c(i-1))`,
with `c(-1) := 0` written as `if i = 0 then 0 else c (i - 1)`. Proved by applying
`Finset.sum_range_by_parts` to `f` and `g i := c i - (if i = 0 then 0 else c (i - 1))` (whose
partial sums telescope back to `c`), mirroring the analogous matrix-level derivation in
`SpectralDecomposition.lean`. -/
theorem sum_range_sub_mul_eq_sum_mul_sub {f c : ℕ → ℝ} {d : ℕ} (hf : f d = 0) :
    ∑ i ∈ Finset.range d, (f i - f (i + 1)) * c i =
      ∑ i ∈ Finset.range d, f i * (c i - if i = 0 then 0 else c (i - 1)) := by
  have hGshift : ∀ i : ℕ, ∑ i' ∈ Finset.range (i + 1),
      (c i' - if i' = 0 then (0 : ℝ) else c (i' - 1)) = c i := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Finset.sum_range_succ, ih, if_neg (show i + 1 ≠ 0 by omega)]
      have hsub : i + 1 - 1 = i := by omega
      rw [hsub]; ring
  cases d with
  | zero => simp
  | succ e =>
    have hby := Finset.sum_range_by_parts f
      (fun i => c i - if i = 0 then (0 : ℝ) else c (i - 1)) (e + 1)
    simp only [smul_eq_mul] at hby
    have he1 : e + 1 - 1 = e := by omega
    rw [he1] at hby
    rw [show (∑ i ∈ Finset.range e, (f (i + 1) - f i)
          * ∑ i' ∈ Finset.range (i + 1), (c i' - if i' = 0 then (0 : ℝ) else c (i' - 1)))
        = ∑ i ∈ Finset.range e, (f (i + 1) - f i) * c i from
      Finset.sum_congr rfl fun i _ => by rw [hGshift]] at hby
    rw [hGshift e] at hby
    rw [Finset.sum_range_succ, hf, sub_zero]
    have hneg : ∑ i ∈ Finset.range e, (f (i + 1) - f i) * c i
        = -∑ i ∈ Finset.range e, (f i - f (i + 1)) * c i := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hneg] at hby
    linarith [hby]

/-- Assembles the term-by-term bounds on each spectral-truncation projector `P_[j]` (one
`∑ₖ min{j+1,μₖ}βₖ` bound per `j`, weighted by the nonneg coefficient `αⱼ - αⱼ₊₁` from
`Matrix.IsHermitian.sum_eigenvalue₀_diff_smul_sum_vecMulVec`) into the final double-sum bound, via
one application of `sum_range_sub_mul_eq_sum_mul_sub` (with `c i := ∑ₖ min{i+1,μₖ}βₖ`) plus
linearity of the `k`-sum. The `μₖ ≥ 0` hypothesis is exactly what is needed to match the `j = 0`
boundary term `c(-1) := 0` against `∑ₖ βₖ min{0,μₖ}` (`= 0` termwise, since `min{0,μₖ} = 0` when
`μₖ ≥ 0`). -/
theorem sum_coeff_mul_sum_min_eq_sum_sum_alpha_beta_min_sub {d1 d2 : ℕ} (α : Fin d1 → ℝ)
    (β μ : Fin d2 → ℝ) (hμ : ∀ k, 0 ≤ μ k) :
    ∑ j : Fin d1, (α j - if h : (j : ℕ) + 1 < d1 then α ⟨(j : ℕ) + 1, h⟩ else 0)
        * ∑ k : Fin d2, min ((j : ℝ) + 1) (μ k) * β k
      = ∑ j : Fin d1, ∑ k : Fin d2,
          α j * β k * (min ((j : ℝ) + 1) (μ k) - min (j : ℝ) (μ k)) := by
  set f : ℕ → ℝ := fun i => if h : i < d1 then α ⟨i, h⟩ else 0 with hf_def
  set c : ℕ → ℝ := fun i => ∑ k : Fin d2, min ((i : ℝ) + 1) (μ k) * β k with hc_def
  have hf : ∀ j : Fin d1, f (j : ℕ) = α j := fun j => by simp [hf_def]
  have hf_d1 : f d1 = 0 := by simp [hf_def]
  have step1 : ∑ j : Fin d1, (α j - if h : (j : ℕ) + 1 < d1 then α ⟨(j : ℕ) + 1, h⟩ else 0)
      * ∑ k : Fin d2, min ((j : ℝ) + 1) (μ k) * β k
      = ∑ i ∈ Finset.range d1, (f i - f (i + 1)) * c i := by
    rw [← Fin.sum_univ_eq_sum_range (fun i => (f i - f (i + 1)) * c i) d1]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    rw [hf j]
  have step2 : ∀ j : Fin d1, c (j : ℕ) - (if (j : ℕ) = 0 then 0 else c ((j : ℕ) - 1))
      = ∑ k : Fin d2, β k * (min ((j : ℝ) + 1) (μ k) - min (j : ℝ) (μ k)) := by
    intro j
    rcases Nat.eq_zero_or_pos (j : ℕ) with hj0 | hj0
    · rw [hj0]
      rw [if_pos rfl, sub_zero]
      simp only [hc_def, Nat.cast_zero, zero_add]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [min_eq_left (hμ k)]
      ring
    · have hjne : (j : ℕ) ≠ 0 := Nat.pos_iff_ne_zero.mp hj0
      rw [if_neg hjne]
      simp only [hc_def]
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      have hcast : (((j : ℕ) - 1 : ℕ) : ℝ) + 1 = (j : ℝ) := by
        have hnat : (j : ℕ) - 1 + 1 = (j : ℕ) := by omega
        exact_mod_cast hnat
      rw [hcast]
      ring
  calc ∑ j : Fin d1, (α j - if h : (j : ℕ) + 1 < d1 then α ⟨(j : ℕ) + 1, h⟩ else 0)
        * ∑ k : Fin d2, min ((j : ℝ) + 1) (μ k) * β k
      = ∑ i ∈ Finset.range d1, (f i - f (i + 1)) * c i := step1
    _ = ∑ i ∈ Finset.range d1, f i * (c i - if i = 0 then 0 else c (i - 1)) :=
        sum_range_sub_mul_eq_sum_mul_sub hf_d1
    _ = ∑ j : Fin d1, f (j : ℕ) * (c (j : ℕ) - if (j : ℕ) = 0 then 0 else c ((j : ℕ) - 1)) :=
        (Fin.sum_univ_eq_sum_range
          (fun i => f i * (c i - if i = 0 then 0 else c (i - 1))) d1).symm
    _ = ∑ j : Fin d1, α j * (c (j : ℕ) - if (j : ℕ) = 0 then 0 else c ((j : ℕ) - 1)) :=
        Finset.sum_congr rfl fun j _ => by rw [hf j]
    _ = ∑ j : Fin d1, α j * ∑ k : Fin d2, β k * (min ((j : ℝ) + 1) (μ k) - min (j : ℝ) (μ k)) :=
        Finset.sum_congr rfl fun j _ => by rw [step2 j]
    _ = ∑ j : Fin d1, ∑ k : Fin d2, α j * β k * (min ((j : ℝ) + 1) (μ k) - min (j : ℝ) (μ k)) :=
        Finset.sum_congr rfl fun j _ => by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun k _ => by ring

/-- **Lemma**: for a projector `Q` on `𝕜^dim1 ⊗ 𝕜^dim2` and positive `A` on `𝕜^dim1`, `B` on
`𝕜^dim2`,
`Tr[Q(A⊗B)] ≤ ∑ⱼ ∑ₖ λⱼ(A) λₖ(B) (min{j+1, λₖ(Tr₁ Q)} - min{j, λₖ(Tr₁ Q)})`,
where `j` ranges over `Fin (Fintype.card dim1)` and `k` over `Fin (Fintype.card dim2)` (so `j+1`
plays the role of the paper's 1-indexed `j`, and `j` the role of the paper's `j-1`), and all
eigenvalues are sorted in decreasing order (`Matrix.IsHermitian.eigenvalues₀`).

Generalizes `trace_mul_kronecker_le_sum_min` (which is the special case `A = P` a rank-`r`
projector, where the weight `min{j+1,μₖ} - min{j,μₖ}` collapses to `μₖ ≤ r` for `j = 0` and to `0`
otherwise, leaving just the single term `min{r,μₖ}`). -/
theorem trace_mul_kronecker_le_sum_min_diff {Q : Matrix (dim1 × dim2) (dim1 × dim2) 𝕜}
    {A : Matrix dim1 dim1 𝕜} {B : Matrix dim2 dim2 𝕜} (hQ : IsStarProjection Q)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Q * (A ⊗ₖ B)).trace
      ≤ (↑(∑ j : Fin (Fintype.card dim1), ∑ k : Fin (Fintype.card dim2),
          hA.isHermitian.eigenvalues₀ j * hB.isHermitian.eigenvalues₀ k
            * (min ((j : ℝ) + 1) (hQ.isSelfAdjoint.isHermitian.traceLeft.eigenvalues₀ k)
                - min (j : ℝ) (hQ.isSelfAdjoint.isHermitian.traceLeft.eigenvalues₀ k))) : 𝕜) := by
  set hAh := hA.isHermitian
  set d1 := Fintype.card dim1
  set α := hAh.eigenvalues₀
  set μ := hQ.isSelfAdjoint.isHermitian.traceLeft.eigenvalues₀
  set β := hB.isHermitian.eigenvalues₀
  -- `μ ≥ 0`: `Tr₁ Q` is a partial trace of the PSD projector `Q`, hence itself PSD.
  have hQtraceLeft_posSemidef : Q.traceLeft.PosSemidef := by
    rw [← Phi_one_right]
    exact Phi_posSemidef hQ.posSemidef (IsStarProjection.one (Matrix dim1 dim1 𝕜)).posSemidef
  have hμ_nonneg : ∀ k, 0 ≤ μ k := fun k => hQtraceLeft_posSemidef.eigenvalues₀_nonneg k
  -- The spectral-truncation projectors `P_[j]`, their projector property, and their rank.
  set P : Fin d1 → Matrix dim1 dim1 𝕜 := fun j => ∑ k ∈ Finset.Iic j, hAh.sortedRankOneProjector k
  have hPproj : ∀ j : Fin d1, IsStarProjection (P j) :=
    fun j => hAh.isStarProjection_sum_Iic_vecMulVec j
  have hPrank : ∀ j : Fin d1, (P j).rank = (j : ℕ) + 1 :=
    fun j => hAh.rank_sum_Iic_vecMulVec j
  -- The nonneg coefficient `αⱼ - αⱼ₊₁` (`α_{d1} := 0`) in the telescoping decomposition of `A`,
  -- both as a real number (`coeff`) and cast termwise into `𝕜` (`coeffK`, matching the exact cast
  -- structure produced by `sum_eigenvalue₀_diff_smul_sum_vecMulVec`).
  set coeffK : Fin d1 → 𝕜 :=
    fun j => (α j : 𝕜) - if h : (j : ℕ) + 1 < d1 then (α ⟨(j : ℕ) + 1, h⟩ : 𝕜) else 0
    with hcoeffK_def
  set coeff : Fin d1 → ℝ :=
    fun j => α j - if h : (j : ℕ) + 1 < d1 then α ⟨(j : ℕ) + 1, h⟩ else 0 with hcoeff_def
  have hcoeffK_eq : ∀ j : Fin d1, coeffK j = (coeff j : 𝕜) := by
    intro j
    simp only [hcoeffK_def, hcoeff_def]
    by_cases h : (j : ℕ) + 1 < d1 <;> simp only [h] <;> push_cast <;> ring
  have hcoeff_nonneg : ∀ j : Fin d1, 0 ≤ coeff j := by
    intro j
    simp only [hcoeff_def]
    by_cases h : (j : ℕ) + 1 < d1
    · rw [dif_pos h]
      have hmono : α (⟨(j : ℕ) + 1, h⟩ : Fin d1) ≤ α j :=
        hAh.eigenvalues₀_antitone (by simp only [Fin.le_def]; omega)
      linarith
    · rw [dif_neg h, sub_zero]
      exact hA.eigenvalues₀_nonneg j
  have hAdecomp : A = ∑ j : Fin d1, coeffK j • P j :=
    hAh.sum_eigenvalue₀_diff_smul_sum_vecMulVec
  -- Term-by-term bound, from `trace_mul_kronecker_le_sum_min` applied to each `P j`. The rank
  -- `(P j).rank = (j:ℕ)+1` casts as `(((j:ℕ)+1:ℕ):ℝ)`, needing a `push_cast` bridge to match the
  -- `(j:ℝ)+1` shape used throughout this proof.
  have hterm : ∀ j : Fin d1, (Q * (P j ⊗ₖ B)).trace
      ≤ (↑(∑ k : Fin (Fintype.card dim2), min ((j : ℝ) + 1) (μ k) * β k) : 𝕜) := by
    intro j
    have h0 := trace_mul_kronecker_le_sum_min hQ (hPproj j) (hPrank j) hB
    have hcast : (((j : ℕ) + 1 : ℕ) : ℝ) = (j : ℝ) + 1 := by push_cast; ring
    rwa [hcast] at h0
  -- `(∑ⱼ cⱼ • Pⱼ) ⊗ₖ B = ∑ⱼ cⱼ • (Pⱼ ⊗ₖ B)`: sum-kronecker distributivity combined with
  -- smul-kronecker commutativity (`add_kronecker`/`zero_kronecker`/`smul_kronecker`).
  have hsum_smul_kronecker : ∀ s : Finset (Fin d1),
      (∑ j ∈ s, coeffK j • P j) ⊗ₖ B = ∑ j ∈ s, coeffK j • (P j ⊗ₖ B) := by
    intro s
    induction s using Finset.induction with
    | empty => simp
    | insert a s hnotmem ih =>
        rw [Finset.sum_insert hnotmem, Finset.sum_insert hnotmem, add_kronecker, smul_kronecker, ih]
  calc (Q * (A ⊗ₖ B)).trace
      = (Q * (∑ j : Fin d1, coeffK j • (P j ⊗ₖ B))).trace := by
        rw [hAdecomp, hsum_smul_kronecker]
    _ = ∑ j : Fin d1, coeffK j * (Q * (P j ⊗ₖ B)).trace := by
        rw [Finset.mul_sum, Matrix.trace_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_smul_comm, Matrix.trace_smul, smul_eq_mul]
    _ ≤ ∑ j : Fin d1, coeffK j
          * (↑(∑ k : Fin (Fintype.card dim2), min ((j : ℝ) + 1) (μ k) * β k) : 𝕜) := by
        refine Finset.sum_le_sum fun j _ => ?_
        refine mul_le_mul_of_nonneg_left (hterm j) ?_
        rw [hcoeffK_eq j]
        exact_mod_cast hcoeff_nonneg j
    _ = (↑(∑ j : Fin d1, coeff j
          * ∑ k : Fin (Fintype.card dim2), min ((j : ℝ) + 1) (μ k) * β k) : 𝕜) := by
        rw [RCLike.ofReal_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hcoeffK_eq j, RCLike.ofReal_mul]
    _ = (↑(∑ j : Fin d1, ∑ k : Fin (Fintype.card dim2),
          α j * β k * (min ((j : ℝ) + 1) (μ k) - min (j : ℝ) (μ k))) : 𝕜) := by
        congr 1
        exact sum_coeff_mul_sum_min_eq_sum_sum_alpha_beta_min_sub α β μ hμ_nonneg
