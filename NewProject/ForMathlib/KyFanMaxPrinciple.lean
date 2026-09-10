import NewProject.ForMathlib.SpectralDecomposition

/-!
# The general Ky Fan maximum principle

Not in Mathlib. For a Hermitian `A` and **any** rank-`k` star-projection `Q` (not just `A`'s own
`hA.topProjector k`), `Tr[Q·A] ≤ topSum A.eigenvalues₀ k` — needed by
`KyFanCauchySchwarz.lean`'s `kyFanNorm_le_max_of_fromBlocks_posSemidef`.

The proof reduces to `Majorization.sum_mul_le_topSum` (`Majorization.lean`): the
scalar fact that a `[0,1]`-weighted, mass-`k` average of a tuple `w` is beaten by `w`'s own top-`k`
sum. Once `Tr[Q·A]` is rewritten as such a weighted average — weights `hA.eigenvalues₀`, mass the
"diagonal entries" `⟨uₗ,Quₗ⟩` of `Q` against `A`'s eigenbasis — that lemma applies directly; what
remains is the linear-algebra bridge from "`Q` is a rank-`k` star-projection" to its hypotheses.

## Proof roadmap

Write `A`'s (sorted, decreasing) eigendecomposition as `A = ∑ₗ λₗ • uₗuₗ*` (`uₗ :=
hA.sortedEigenvectorBasis l`, `SortedEigenvectorBasis.lean`), and set `cₗ := ⟨uₗ, Q uₗ⟩`.

1. **Trace expansion** (`trace_mul_eq_sum_eigenvalues₀_mul_dotProduct_mulVec`, no projector
   hypothesis needed): `Tr[Q·A] = ∑ₗ λₗ · ⟨uₗ,Quₗ⟩`, by expanding `A` in its own eigenbasis and
   using `Matrix.dotProduct_mulVec_eq_trace_mul_vecMulVec` (`ForMathlib/PosSemidef.lean`) termwise
   — the same computation `SpectralDecomposition.lean`'s `trace_mul_topProjector_self` already
   does, just for a general `Q` instead of `hA.topProjector k`.
2. **Diagonal entries land in `[0,1]`** (`IsStarProjection.re_dotProduct_mulVec_mem_Icc`): `Q`
   itself is positive semidefinite via `IsStarProjection.posSemidef` (`ForMathlib/PosSemidef.lean`),
   and so is `1 - Q` (`IsStarProjection.one_sub`, Mathlib); the two
   `PosSemidef.dotProduct_mulVec_nonneg` quadratic-form bounds this gives, for a unit vector `u`,
   are exactly `0 ≤ ⟨u,Qu⟩` and `⟨u,Qu⟩ ≤ 1` — the same `PosSemidef → quadratic form inequality`
   step `EigenvalueMonotonicity.lean`'s `hmid` uses, just with `1 - Q` in place of `A - B`.
3. **The diagonal sums to `Q`'s rank**
   (`IsStarProjection.sum_re_dotProduct_mulVec_sortedEigenvectorBasis_eq_rank`): `∑ₗ ⟨uₗ,Quₗ⟩ =
   Tr[Q]` (trace is basis-independent — same orthonormal-expansion argument as
   `SpectralDecomposition.lean`'s `sum_eigenvalue₀_vecMulVec_eq_one`, applied to `Q` against the
   *fixed* orthonormal family `{uₗ}` rather than expanding `Q` itself), and `Tr[Q] = Q.rank` is
   exactly `IsStarProjection.trace_eq_rank` (`Projector.lean`).
4. **Assemble** (`Matrix.IsHermitian.trace_mul_le_topSum_of_isStarProjection`, the main theorem):
   feed `w := hA.eigenvalues₀` and `c := fun l => RCLike.re ⟨uₗ,Quₗ⟩` (steps 1-3 supply exactly
   `Majorization.sum_mul_le_topSum`'s hypotheses `0 ≤ c`, `c ≤ 1`, `∑ c = k`) into that lemma.

## Main results

* `Matrix.IsHermitian.trace_mul_le_topSum_of_isStarProjection`: the general Ky Fan maximum
  principle itself.
* `Matrix.IsHermitian.topSum_eigenvalues₀_add_le`: **Ky Fan's subadditivity theorem** for Hermitian
  matrices, `topSum (A+B).eigenvalues₀ k ≤ topSum A.eigenvalues₀ k + topSum B.eigenvalues₀ k` — the
  triangle inequality for the "Hermitian Ky Fan norms". A direct corollary of the maximum principle
  above, needed as the Hermitian building block for `Matrix.kyFanNorm_add_le`
  (`KyFanNorm.lean`).
-/

open Matrix
open scoped ComplexOrder MatrixOrder

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

section DiagonalBounds

omit [DecidableEq n] in
/-- **Step 2 of the roadmap.** For a star-projection `Q` and a unit vector `u`, the diagonal
entry `⟨u,Qu⟩` (real, since `Q` is Hermitian) lies in `[0,1]`: nonnegativity comes from `Q`
itself being positive semidefinite (`IsStarProjection.posSemidef`, `ForMathlib/PosSemidef.lean`),
and the upper bound comes from `1 - Q` being positive semidefinite too (`IsStarProjection.one_sub`,
Mathlib), applied to the quadratic form `⟨u,(1-Q)u⟩ = ⟨u,u⟩ - ⟨u,Qu⟩ = 1 - ⟨u,Qu⟩ ≥ 0` (`⟨u,u⟩ = 1`
since `u` is a unit vector). Same pattern as `EigenvalueMonotonicity.lean`'s `hmid` step, with
`1 - Q` playing the role of `A - B`. -/
theorem IsStarProjection.re_dotProduct_mulVec_mem_Icc {Q : Matrix n n 𝕜}
    (hQ : IsStarProjection Q) {u : EuclideanSpace 𝕜 n} (hu : ‖u‖ = 1) :
    RCLike.re (star ⇑u ⬝ᵥ Q *ᵥ ⇑u) ∈ Set.Icc (0 : ℝ) 1 := by
  classical
  have hnorm : star ⇑u ⬝ᵥ ⇑u = (1 : 𝕜) := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct, inner_self_eq_norm_sq_to_K, hu]
    simp
  refine ⟨(RCLike.nonneg_iff.mp (hQ.posSemidef.dotProduct_mulVec_nonneg ⇑u)).1, ?_⟩
  have hv := RCLike.nonneg_iff.mp (hQ.one_sub.posSemidef.dotProduct_mulVec_nonneg ⇑u) |>.1
  rw [sub_mulVec, one_mulVec, dotProduct_sub, hnorm, map_sub, RCLike.one_re] at hv
  linarith

end DiagonalBounds

section TraceExpansion

/-- **Step 1 of the roadmap.** Expanding `A` in its own (sorted, decreasing) eigenbasis
`hA.sortedEigenvectorBasis` (`SortedEigenvectorBasis.lean`) turns `Tr[Q·A]` into a weighted sum of
the "diagonal entries" `⟨uₗ,Quₗ⟩` of `Q` against that eigenbasis, weighted by the eigenvalues. Pure
algebra: no hypothesis on `Q` is needed (unlike `trace_mul_topProjector_self`, which needs `Q` to
literally *be* `hA.topProjector k`, this holds for arbitrary `Q`). Proved the same way as that
lemma's `hstep`, via `Matrix.dotProduct_mulVec_eq_trace_mul_vecMulVec`
(`ForMathlib/PosSemidef.lean`) termwise instead of `Matrix.vecMulVec_mul_vecMulVec`. -/
theorem Matrix.IsHermitian.trace_mul_eq_sum_eigenvalues₀_mul_dotProduct_mulVec
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) (Q : Matrix n n 𝕜) :
    (Q * A).trace = ∑ l : Fin (Fintype.card n), (hA.eigenvalues₀ l : 𝕜) *
      (star ⇑(hA.sortedEigenvectorBasis l) ⬝ᵥ Q *ᵥ ⇑(hA.sortedEigenvectorBasis l)) := by
  simp only [Matrix.IsHermitian.sortedEigenvectorBasis]
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
  have hAdecomp : A = ∑ l : Fin (Fintype.card n), (hA.eigenvalues₀ l : 𝕜) •
      Matrix.vecMulVec (hA.eigenvectorBasis (e l)) (star (hA.eigenvectorBasis (e l))) :=
    hA.sum_eigenvalue₀_smul_vecMulVec
  have hQA : Q * A = Q * ∑ l : Fin (Fintype.card n), (hA.eigenvalues₀ l : 𝕜) •
      Matrix.vecMulVec (hA.eigenvectorBasis (e l)) (star (hA.eigenvectorBasis (e l))) :=
    congrArg (fun M => Q * M) hAdecomp
  rw [hQA, Finset.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [mul_smul_comm, Matrix.trace_smul, smul_eq_mul,
    ← Matrix.dotProduct_mulVec_eq_trace_mul_vecMulVec]

end TraceExpansion

section DiagonalSum

/-- **Step 3 of the roadmap.** The diagonal entries of a star-projection `Q`, read off against
*any* orthonormal basis of `EuclideanSpace 𝕜 n` (here, `A`'s sorted eigenbasis), sum to `Q`'s rank:
`∑ₗ ⟨uₗ,Quₗ⟩ = Tr[Q] = Q.rank`. The first equality is trace's basis-independence (same
orthonormal-expansion computation as `SpectralDecomposition.lean`'s
`sum_eigenvalue₀_vecMulVec_eq_one` — the `Fin (Fintype.card n)`-reindexed resolution of identity,
matching `sortedEigenvectorBasis`'s own indexing — applied to `Q` against the fixed family `{uₗ}`
rather than expanding `Q` itself in it); the second is `IsStarProjection.trace_eq_rank`
(`Projector.lean`). -/
theorem IsStarProjection.sum_re_dotProduct_mulVec_sortedEigenvectorBasis_eq_rank
    {A Q : Matrix n n 𝕜} (hA : A.IsHermitian) (hQ : IsStarProjection Q) :
    ∑ l : Fin (Fintype.card n),
      RCLike.re (star ⇑(hA.sortedEigenvectorBasis l) ⬝ᵥ Q *ᵥ ⇑(hA.sortedEigenvectorBasis l))
      = (Q.rank : ℝ) := by
  simp only [Matrix.IsHermitian.sortedEigenvectorBasis]
  set e := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n))
  have hQdecomp : Q = Q * ∑ l : Fin (Fintype.card n),
      Matrix.vecMulVec (hA.eigenvectorBasis (e l)) (star (hA.eigenvectorBasis (e l))) := by
    conv_lhs => rw [← Matrix.mul_one Q]
    exact congrArg (fun M => Q * M) hA.sum_eigenvalue₀_vecMulVec_eq_one
  have htrace : Q.trace = ∑ l : Fin (Fintype.card n),
      (star ⇑(hA.eigenvectorBasis (e l)) ⬝ᵥ Q *ᵥ ⇑(hA.eigenvectorBasis (e l))) := by
    conv_lhs => rw [hQdecomp]
    rw [Finset.mul_sum, Matrix.trace_sum]
    exact Finset.sum_congr rfl fun l _ =>
      (Matrix.dotProduct_mulVec_eq_trace_mul_vecMulVec Q _).symm
  rw [← map_sum, ← htrace, hQ.trace_eq_rank, RCLike.natCast_re]

end DiagonalSum

/-- **The general Ky Fan maximum principle.** For a Hermitian `A` and any rank-`k`
star-projection `Q` (not just `A`'s own `hA.topProjector k`, cf.
`Matrix.IsHermitian.trace_mul_topProjector_self` in `SpectralDecomposition.lean`), `Tr[Q·A]` is at
most the sum of `A`'s `k` largest eigenvalues.

Assembled from the roadmap above: rewrite `Tr[Q·A]` via
`trace_mul_eq_sum_eigenvalues₀_mul_dotProduct_mulVec` (step 1), note each term's coefficient is
real and in `[0,1]` via `re_dotProduct_mulVec_mem_Icc` (step 2), note the coefficients sum to `k`
via `sum_re_dotProduct_mulVec_sortedEigenvectorBasis_eq_rank` and `hk` (step 3), then apply
`Majorization.sum_mul_le_topSum` (step 4) with `w := hA.eigenvalues₀`. -/
theorem Matrix.IsHermitian.trace_mul_le_topSum_of_isStarProjection {A Q : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hQ : IsStarProjection Q) (k : ℕ) (hk : Q.rank = k) :
    RCLike.re (Q * A).trace ≤ Majorization.topSum hA.eigenvalues₀ k := by
  have hk_le : k ≤ Fintype.card n := by rw [← hk]; exact Q.rank_le_card_width
  set c : Fin (Fintype.card n) → ℝ :=
    fun l => RCLike.re (star ⇑(hA.sortedEigenvectorBasis l) ⬝ᵥ Q *ᵥ ⇑(hA.sortedEigenvectorBasis l))
  have hIcc : ∀ l, c l ∈ Set.Icc (0 : ℝ) 1 := fun l =>
    hQ.re_dotProduct_mulVec_mem_Icc (hA.orthonormal_sortedEigenvectorBasis.1 l)
  have hcsum : ∑ l, c l = (k : ℝ) := by
    rw [← hk]
    exact hQ.sum_re_dotProduct_mulVec_sortedEigenvectorBasis_eq_rank hA
  have hre : RCLike.re (Q * A).trace = ∑ l : Fin (Fintype.card n), hA.eigenvalues₀ l * c l := by
    rw [hA.trace_mul_eq_sum_eigenvalues₀_mul_dotProduct_mulVec Q, map_sum]
    exact Finset.sum_congr rfl fun l _ => RCLike.re_ofReal_mul _ _
  rw [hre]
  exact Majorization.sum_mul_le_topSum hA.eigenvalues₀ c k hk_le (fun l => (hIcc l).1)
    (fun l => (hIcc l).2) hcsum

/-- **Ky Fan's subadditivity theorem, Hermitian case.** For Hermitian `A`, `B`, the sum of the `k`
largest eigenvalues of `A + B` is at most the sum of the `k` largest eigenvalues of `A` plus that of
`B` — the triangle inequality for the "Hermitian Ky Fan norm" `topSum ·.eigenvalues₀ k`.

Proof: let `Q := (hA.add hB).topProjector k` (truncated to `k' := min k (Fintype.card n)`, since
`topProjector`/`rank_topProjector` need `k' ≤ Fintype.card n`; the general `k` case then follows
from `Majorization.topSum_eq_topSum_of_le`, since `topSum` saturates once `k ≥ Fintype.card n`).
`Q` achieves equality against `A + B` itself (`trace_mul_topProjector_self`), and `Tr[Q·(A+B)] =
Tr[Q·A] + Tr[Q·B]` splits linearly; the maximum principle above then bounds each summand,
`Tr[Q·A] ≤ topSum A.eigenvalues₀ k'` and `Tr[Q·B] ≤ topSum B.eigenvalues₀ k'`, since `Q` is a
rank-`k'` star-projection (`isStarProjection_topProjector`/`rank_topProjector`) — not necessarily
`A`'s or `B`'s *own* top-`k'` projector, which is exactly why the general (not just `Q :=
hA.topProjector k`) maximum principle above is what makes this work. -/
theorem Matrix.IsHermitian.topSum_eigenvalues₀_add_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (k : ℕ) :
    Majorization.topSum (hA.add hB).eigenvalues₀ k ≤
      Majorization.topSum hA.eigenvalues₀ k + Majorization.topSum hB.eigenvalues₀ k := by
  have hcore : ∀ k' ≤ Fintype.card n, Majorization.topSum (hA.add hB).eigenvalues₀ k' ≤
      Majorization.topSum hA.eigenvalues₀ k' + Majorization.topSum hB.eigenvalues₀ k' := by
    intro k' hk'
    set Q := (hA.add hB).topProjector k' with hQ_def
    have hQproj : IsStarProjection Q := (hA.add hB).isStarProjection_topProjector k'
    have hQrank : Q.rank = k' := (hA.add hB).rank_topProjector k' hk'
    have heq : (Q * (A + B)).trace = ((Majorization.topSum (hA.add hB).eigenvalues₀ k' : ℝ) : 𝕜) :=
      (hA.add hB).trace_mul_topProjector_self k'
    have hsplit : (Q * (A + B)).trace = (Q * A).trace + (Q * B).trace := by
      rw [Matrix.mul_add, Matrix.trace_add]
    have hre : RCLike.re (Q * A).trace + RCLike.re (Q * B).trace
        = Majorization.topSum (hA.add hB).eigenvalues₀ k' := by
      rw [← map_add, ← hsplit, heq, RCLike.ofReal_re]
    have hbA : RCLike.re (Q * A).trace ≤ Majorization.topSum hA.eigenvalues₀ k' :=
      hA.trace_mul_le_topSum_of_isStarProjection hQproj k' hQrank
    have hbB : RCLike.re (Q * B).trace ≤ Majorization.topSum hB.eigenvalues₀ k' :=
      hB.trace_mul_le_topSum_of_isStarProjection hQproj k' hQrank
    linarith [hre, hbA, hbB]
  by_cases hk : k ≤ Fintype.card n
  · exact hcore k hk
  · push Not at hk
    rw [Majorization.topSum_eq_topSum_of_le _ hk.le, Majorization.topSum_eq_topSum_of_le _ hk.le,
      Majorization.topSum_eq_topSum_of_le _ hk.le]
    exact hcore (Fintype.card n) le_rfl
