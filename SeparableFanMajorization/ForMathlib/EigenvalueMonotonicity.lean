import SeparableFanMajorization.ForMathlib.PosSemidef
import SeparableFanMajorization.ForMathlib.SortedEigenvectorBasis
import SeparableFanMajorization.ForMathlib.Majorization

/-!
# Weyl's monotonicity theorem

If `B ≤ A` in the Loewner order (`Mathlib.Analysis.Matrix.Order`, scoped `MatrixOrder`), the
eigenvalues of `B` are weakly majorized by the eigenvalues of `A`. Mathlib does not appear to
relate `Matrix.IsHermitian.eigenvalues₀` to the Loewner order at all (no
Weyl/Courant-Fischer/min-max results were found), so we prove the facts we need here.

## Proof roadmap

The standard proof is the Courant–Fischer subspace-intersection argument, specialized to a single
index `k` (we don't need the full min-max *characterization*, only its proof technique):

1. `U` := span of `B`'s top `k+1` (sorted) eigenvectors. `dim U = k+1`, and on `U`,
   `⟨Bx,x⟩ ≥ eigenvalues₀ B k · ‖x‖²` (every eigenvalue occurring in `U` is `≥ eigenvalues₀ B k`).
2. `V` := span of `A`'s bottom `d-k` (sorted) eigenvectors (`d := Fintype.card n`). `dim V = d-k`,
   and on `V`, `⟨Ax,x⟩ ≤ eigenvalues₀ A k · ‖x‖²`.
3. `dim U + dim V = d+1 > d`, so `U ⊓ V ≠ ⊥`; pick nonzero `x` there.
4. Chain: `eigenvalues₀ B k · ‖x‖² ≤ ⟨Bx,x⟩ ≤ ⟨Ax,x⟩ ≤ eigenvalues₀ A k · ‖x‖²` (the middle step is
   exactly `B ≤ A`), then divide by `‖x‖² > 0`.

This file builds that argument as a chain of lemmas, culminating in `eigenvalues₀_mono` (the
pointwise form) and `eigenvalues₀_weakMajorizedBy` (the weak-majorization form). The two lemmas
that carry the actual mathematical content are `exists_coeff_sum_and_quadraticForm_eq` (the
eigen-expansion computation underlying steps 1-2) and `finrank_span_sortedEigenvectorBasis_image`
(the dimension count for steps 1-2); everything else, including `eigenvalues₀_mono` itself, is
bookkeeping given those two.
-/

open scoped Majorization ComplexOrder MatrixOrder Matrix

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- Local shorthand for the `EuclideanSpace 𝕜 n` inner product (Mathlib only declares `⟪·,·⟫` as
`local notation`, never globally, so files that want it must redeclare it). -/
local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

section SpanDimension

/-- The span of the sorted eigenvectors indexed by a finite set `S` has dimension `S.card`.
Proved via `finrank_span_eq_card` applied to the linearly independent sub-family
`hA.sortedEigenvectorBasis ∘ Subtype.val : S → EuclideanSpace 𝕜 n` (a subfamily of an orthonormal
family, hence orthonormal via `Orthonormal.comp`, hence linearly independent), after rewriting the
image `hA.sortedEigenvectorBasis '' S` as the range of that subfamily via `Set.image_eq_range`. -/
theorem Matrix.IsHermitian.finrank_span_sortedEigenvectorBasis_image {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (S : Finset (Fin (Fintype.card n))) :
    Module.finrank 𝕜 (Submodule.span 𝕜 (hA.sortedEigenvectorBasis '' S)) = S.card := by
  have hli : LinearIndependent 𝕜 (fun i : S => hA.sortedEigenvectorBasis i) :=
    (hA.orthonormal_sortedEigenvectorBasis.comp
      (Subtype.val : S → Fin (Fintype.card n)) Subtype.val_injective).linearIndependent
  rw [show hA.sortedEigenvectorBasis '' (S : Set (Fin (Fintype.card n))) =
      Set.range (fun i : S => hA.sortedEigenvectorBasis i) from
      Set.image_eq_range hA.sortedEigenvectorBasis (S : Set (Fin (Fintype.card n))),
    finrank_span_eq_card hli, Fintype.card_coe]

end SpanDimension

section QuadraticFormExpansion

/-- The mathematical core of the roadmap above. Expand `x`, a member of the span of a finite
sub-collection `S` of `A`'s sorted eigenvectors, in that sub-basis, and read off the quadratic form
`⟨Ax,x⟩` and `‖x‖²` in terms of the coefficients: `⟨Ax,x⟩ = ∑ᵢ λᵢ|cᵢ|²` for `x = ∑ᵢ cᵢ uᵢ`, using
`mulVec_sortedEigenvectorBasis` and orthonormality of the `uᵢ`. Everything downstream
(`eigenvalues₀_mul_sq_norm_le_of_mem_span_Iic`,
`quadraticForm_le_eigenvalues₀_mul_sq_norm_of_mem_span_Ici`) is a one-line corollary of this. -/
theorem Matrix.IsHermitian.exists_coeff_sum_and_quadraticForm_eq {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) (S : Finset (Fin (Fintype.card n))) {x : EuclideanSpace 𝕜 n}
    (hx : x ∈ Submodule.span 𝕜 (hA.sortedEigenvectorBasis '' S)) :
    ∃ c : Fin (Fintype.card n) → 𝕜, x = ∑ i ∈ S, c i • hA.sortedEigenvectorBasis i ∧
      RCLike.re (star ⇑x ⬝ᵥ A *ᵥ ⇑x) = ∑ i ∈ S, hA.eigenvalues₀ i * ‖c i‖ ^ 2 ∧
      ‖x‖ ^ 2 = ∑ i ∈ S, ‖c i‖ ^ 2 := by
  classical
  -- Extract the coefficients `c = l` from `x`'s membership in the span, as a `Finsupp` supported
  -- on (a subset of) `S`, via the general `Finsupp` span-membership API.
  obtain ⟨l, hl, hlx⟩ := (Finsupp.mem_span_image_iff_linearCombination (R := 𝕜)).mp hx
  have hsub : l.support ⊆ S := Finset.coe_subset.mp ((Finsupp.mem_supported (R := 𝕜) l).mp hl)
  have heqx : x = ∑ i ∈ S, l i • hA.sortedEigenvectorBasis i := by
    rw [← hlx, Finsupp.linearCombination_apply, Finsupp.sum]
    refine Finset.sum_subset hsub fun i _ hi => ?_
    have hzero : l i = 0 := not_not.mp fun h => hi (Finsupp.mem_support_iff.mpr h)
    rw [hzero, zero_smul]
  -- `conj z * z` as a real square, in the cast-outside form needed below.
  have hconjsq : ∀ z : 𝕜, (starRingEnd 𝕜) z * z = ((‖z‖ ^ 2 : ℝ) : 𝕜) := fun z => by
    rw [RCLike.conj_mul]; push_cast; ring
  -- Repackage `A *ᵥ ·` as a linear map `EuclideanSpace 𝕜 n →ₗ[𝕜] EuclideanSpace 𝕜 n` (Mathlib's
  -- `Matrix.toLpLin`), so `map_sum`/`map_smul` push it through the expansion of `x` above without
  -- any manual `WithLp`-coercion bookkeeping.
  have hAv : ∀ i, Matrix.toLpLin 2 2 A (hA.sortedEigenvectorBasis i) =
      (hA.eigenvalues₀ i : 𝕜) • hA.sortedEigenvectorBasis i := fun i => by
    rw [Matrix.toLpLin_apply, hA.mulVec_sortedEigenvectorBasis]; rfl
  have hAxeq : Matrix.toLpLin 2 2 A x =
      ∑ i ∈ S, ((hA.eigenvalues₀ i : 𝕜) * l i) • hA.sortedEigenvectorBasis i := by
    rw [heqx, map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hAv, smul_smul, mul_comm]
  have hAxfun : ⇑(Matrix.toLpLin 2 2 A x) = A *ᵥ ⇑x := by rw [Matrix.toLpLin_apply]
  have hquad : star ⇑x ⬝ᵥ A *ᵥ ⇑x = (⟪x, Matrix.toLpLin 2 2 A x⟫ : 𝕜) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, hAxfun, dotProduct_comm]
  refine ⟨l, heqx, ?_, ?_⟩
  · have hinner : (⟪x, Matrix.toLpLin 2 2 A x⟫ : 𝕜) =
        ∑ i ∈ S, (starRingEnd 𝕜) (l i) * ((hA.eigenvalues₀ i : 𝕜) * l i) := by
      conv_lhs => rw [hAxeq, heqx]
      exact hA.orthonormal_sortedEigenvectorBasis.inner_sum l
        (fun i => (hA.eigenvalues₀ i : 𝕜) * l i) S
    have hcast : star ⇑x ⬝ᵥ A *ᵥ ⇑x = ((∑ i ∈ S, hA.eigenvalues₀ i * ‖l i‖ ^ 2 : ℝ) : 𝕜) := by
      rw [hquad, hinner, RCLike.ofReal_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [show (starRingEnd 𝕜) (l i) * ((hA.eigenvalues₀ i : 𝕜) * l i) =
          (hA.eigenvalues₀ i : 𝕜) * ((starRingEnd 𝕜) (l i) * l i) from by ring, hconjsq]
      push_cast; ring
    rw [hcast, RCLike.ofReal_re]
  · have hinner : (⟪x, x⟫ : 𝕜) = ∑ i ∈ S, (starRingEnd 𝕜) (l i) * l i := by
      conv_lhs => rw [heqx]
      exact hA.orthonormal_sortedEigenvectorBasis.inner_sum l l S
    have hcast : (⟪x, x⟫ : 𝕜) = ((∑ i ∈ S, ‖l i‖ ^ 2 : ℝ) : 𝕜) := by
      rw [hinner, RCLike.ofReal_sum]
      exact Finset.sum_congr rfl fun i _ => hconjsq (l i)
    have hself : ((‖x‖ ^ 2 : ℝ) : 𝕜) = ((∑ i ∈ S, ‖l i‖ ^ 2 : ℝ) : 𝕜) := by
      rw [RCLike.ofReal_pow, ← inner_self_eq_norm_sq_to_K]; exact hcast
    exact RCLike.ofReal_injective hself

/-- On the span of `B`'s top `k+1` sorted eigenvectors, the quadratic form `⟨Bx,x⟩` is bounded
below by `eigenvalues₀ B k · ‖x‖²`: termwise, every eigenvalue occurring is `≥ eigenvalues₀ B k`
by `eigenvalues₀_antitone`. Step 1 of the roadmap above. -/
theorem Matrix.IsHermitian.eigenvalues₀_mul_sq_norm_le_of_mem_span_Iic {B : Matrix n n 𝕜}
    (hB : B.IsHermitian) (k : Fin (Fintype.card n)) {x : EuclideanSpace 𝕜 n}
    (hx : x ∈ Submodule.span 𝕜 (hB.sortedEigenvectorBasis '' Finset.Iic k)) :
    (hB.eigenvalues₀ k : ℝ) * ‖x‖ ^ 2 ≤ RCLike.re (star ⇑x ⬝ᵥ B *ᵥ ⇑x) := by
  obtain ⟨c, -, heq, hnorm⟩ := hB.exists_coeff_sum_and_quadraticForm_eq _ hx
  rw [heq, hnorm, Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi =>
    mul_le_mul_of_nonneg_right (hB.eigenvalues₀_antitone (Finset.mem_Iic.mp hi)) (sq_nonneg _)

/-- On the span of `A`'s bottom `d-k` sorted eigenvectors, the quadratic form `⟨Ax,x⟩` is bounded
above by `eigenvalues₀ A k · ‖x‖²`: termwise, every eigenvalue occurring is `≤ eigenvalues₀ A k` by
`eigenvalues₀_antitone`. Step 2 of the roadmap above. -/
theorem Matrix.IsHermitian.quadraticForm_le_eigenvalues₀_mul_sq_norm_of_mem_span_Ici
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (k : Fin (Fintype.card n)) {x : EuclideanSpace 𝕜 n}
    (hx : x ∈ Submodule.span 𝕜 (hA.sortedEigenvectorBasis '' Finset.Ici k)) :
    RCLike.re (star ⇑x ⬝ᵥ A *ᵥ ⇑x) ≤ (hA.eigenvalues₀ k : ℝ) * ‖x‖ ^ 2 := by
  obtain ⟨c, -, heq, hnorm⟩ := hA.exists_coeff_sum_and_quadraticForm_eq _ hx
  rw [heq, hnorm, Finset.mul_sum]
  exact Finset.sum_le_sum fun i hi =>
    mul_le_mul_of_nonneg_right (hA.eigenvalues₀_antitone (Finset.mem_Ici.mp hi)) (sq_nonneg _)

end QuadraticFormExpansion

section Intersection

/-- **Step 3 of the roadmap**: the dimension count. `B`'s top-`(k+1)` eigenspace and `A`'s
bottom-`(d-k)` eigenspace have dimensions summing to `d+1 > d`, so they intersect nontrivially. -/
theorem Matrix.IsHermitian.exists_ne_zero_mem_span_inter {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (k : Fin (Fintype.card n)) :
    ∃ x : EuclideanSpace 𝕜 n, x ≠ 0 ∧
      x ∈ Submodule.span 𝕜 (hB.sortedEigenvectorBasis '' Finset.Iic k) ∧
      x ∈ Submodule.span 𝕜 (hA.sortedEigenvectorBasis '' Finset.Ici k) := by
  set U := Submodule.span 𝕜 (hB.sortedEigenvectorBasis '' Finset.Iic k) with hU_def
  set V := Submodule.span 𝕜 (hA.sortedEigenvectorBasis '' Finset.Ici k) with hV_def
  have hU : Module.finrank 𝕜 U = (k : ℕ) + 1 := by
    rw [hU_def, hB.finrank_span_sortedEigenvectorBasis_image]; exact Fin.card_Iic k
  have hV : Module.finrank 𝕜 V = Fintype.card n - (k : ℕ) := by
    rw [hV_def, hA.finrank_span_sortedEigenvectorBasis_image]; exact Fin.card_Ici k
  have hk : (k : ℕ) < Fintype.card n := k.isLt
  have hdim : Module.finrank 𝕜 (EuclideanSpace 𝕜 n) < Module.finrank 𝕜 U + Module.finrank 𝕜 V := by
    rw [hU, hV, finrank_euclideanSpace]; omega
  have hdisj : ¬ Disjoint U V := fun hd =>
    absurd (Submodule.finrank_add_finrank_le_of_disjoint hd) (not_le.mpr hdim)
  rw [Submodule.disjoint_def] at hdisj
  push Not at hdisj
  obtain ⟨x, hxU, hxV, hx0⟩ := hdisj
  exact ⟨x, hx0, hxU, hxV⟩

end Intersection

/-- **Weyl's monotonicity theorem** (pointwise form): if `B ≤ A` in the Loewner order, then
`B`'s `k`-th (sorted, decreasing) eigenvalue is at most `A`'s, for every `k`. Stronger than
`eigenvalues₀_weakMajorizedBy` (which follows termwise from this), and what we actually need for
the overlap-bound lemma.

Step 4 of the roadmap above: assembled from `exists_ne_zero_mem_span_inter` (steps 1-3) plus the
pointwise Loewner-order inequality `⟨Bx,x⟩ ≤ ⟨Ax,x⟩` (from `B ≤ A` via
`PosSemidef.dotProduct_mulVec_nonneg`, the same fact already used in
`eigenvalues₀_le_of_le_smul_one` below). -/
theorem Matrix.IsHermitian.eigenvalues₀_mono {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hBA : B ≤ A) (k : Fin (Fintype.card n)) :
    hB.eigenvalues₀ k ≤ hA.eigenvalues₀ k := by
  obtain ⟨x, hx0, hxB, hxA⟩ := hA.exists_ne_zero_mem_span_inter hB k
  have hlow : (hB.eigenvalues₀ k : ℝ) * ‖x‖ ^ 2 ≤ RCLike.re (star ⇑x ⬝ᵥ B *ᵥ ⇑x) :=
    hB.eigenvalues₀_mul_sq_norm_le_of_mem_span_Iic k hxB
  have hhigh : RCLike.re (star ⇑x ⬝ᵥ A *ᵥ ⇑x) ≤ (hA.eigenvalues₀ k : ℝ) * ‖x‖ ^ 2 :=
    hA.quadraticForm_le_eigenvalues₀_mul_sq_norm_of_mem_span_Ici k hxA
  have hmid : RCLike.re (star ⇑x ⬝ᵥ B *ᵥ ⇑x) ≤ RCLike.re (star ⇑x ⬝ᵥ A *ᵥ ⇑x) := by
    have hM : (A - B).PosSemidef := hBA
    have hv := RCLike.nonneg_iff.mp (hM.dotProduct_mulVec_nonneg ⇑x) |>.1
    have hsplit : star ⇑x ⬝ᵥ (A - B) *ᵥ ⇑x = star ⇑x ⬝ᵥ A *ᵥ ⇑x - star ⇑x ⬝ᵥ B *ᵥ ⇑x := by
      rw [sub_mulVec, dotProduct_sub]
    rw [hsplit, map_sub] at hv
    linarith
  have hxnorm : (0 : ℝ) < ‖x‖ ^ 2 := by positivity
  nlinarith [hlow, hhigh, hmid]

/-- **Weyl's monotonicity theorem** (weak form): if `B ≤ A` in the Loewner order, the eigenvalues
of `B` are weakly majorized by the eigenvalues of `A`. Immediate termwise consequence of
`eigenvalues₀_mono` (via `decreasingSort_of_antitone` to unfold `topSum`). -/
theorem Matrix.IsHermitian.eigenvalues₀_weakMajorizedBy {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (hBA : B ≤ A) :
    hB.eigenvalues₀ ≺w hA.eigenvalues₀ := by
  intro k _
  simp only [Majorization.topSum, Majorization.decreasingSort_of_antitone hB.eigenvalues₀_antitone,
    Majorization.decreasingSort_of_antitone hA.eigenvalues₀_antitone]
  exact Finset.sum_le_sum fun i _ => hA.eigenvalues₀_mono hB hBA i

/-- The eigenvalues of a real scalar multiple of the identity are all that scalar. Special case
of `eigenvalues₀_mono` needed to turn `A ≤ (c : 𝕜) • 1` into a bound on `A`'s eigenvalues. -/
theorem Matrix.IsHermitian.eigenvalues₀_le_of_le_smul_one {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    {c : ℝ} (hAc : A ≤ (c : 𝕜) • (1 : Matrix n n 𝕜)) (k : Fin (Fintype.card n)) :
    hA.eigenvalues₀ k ≤ c := by
  classical
  suffices h : ∀ i : n, hA.eigenvalues i ≤ c by
    simpa [Matrix.IsHermitian.eigenvalues] using h ((Fintype.equivOfCardEq (Fintype.card_fin _)) k)
  intro i
  have hM : ((c : 𝕜) • (1 : Matrix n n 𝕜) - A).PosSemidef := hAc
  have hnorm : star ⇑(hA.eigenvectorBasis i) ⬝ᵥ ⇑(hA.eigenvectorBasis i) = (1 : 𝕜) := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K,
      hA.eigenvectorBasis.orthonormal.1 i]
    simp
  have hMv : ((c : 𝕜) • (1 : Matrix n n 𝕜) - A) *ᵥ ⇑(hA.eigenvectorBasis i)
      = ((c - hA.eigenvalues i : ℝ) : 𝕜) • ⇑(hA.eigenvectorBasis i) := by
    rw [sub_mulVec, smul_mulVec, one_mulVec, hA.mulVec_eigenvectorBasis,
      RCLike.real_smul_eq_coe_smul (K := 𝕜), ← sub_smul, ← RCLike.ofReal_sub]
  have hv := hM.dotProduct_mulVec_nonneg ⇑(hA.eigenvectorBasis i)
  rw [hMv, dotProduct_smul, hnorm, smul_eq_mul, mul_one, RCLike.ofReal_nonneg] at hv
  linarith
