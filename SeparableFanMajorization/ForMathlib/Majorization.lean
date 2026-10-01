import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Majorization of vectors

Majorization is not yet in Mathlib: `Mathlib.Analysis.Convex.Birkhoff` only mentions it in a
`TODO` ("Show that for `x y : n → R`, `x` is majorized by `y` if and only if there is a doubly
stochastic matrix `M` such that `M *ᵥ y = x`"), with no accompanying definition anywhere in the
library.

We define majorization for tuples `Fin n → ℝ`, the shape produced by
`Matrix.IsHermitian.eigenvalues₀`, which is where we need it.

## Main definitions

* `Majorization.decreasingSort f`: the entries of `f` rearranged into decreasing order.
* `Majorization.topSum f k`: the sum of the `k` largest entries of `f`.
* `Majorization.WeakMajorizedBy`/`x ≺w y`: `x` is weakly majorized by `y`, i.e.
  `topSum x k ≤ topSum y k` for every `k`.
* `Majorization.MajorizedBy`/`x ≺ y`: `x` is majorized by `y`, i.e. weakly majorized by `y` with
  equal total sums.

## Main results

* `Majorization.decreasingSort_of_antitone`: `decreasingSort` is the identity on an already-
  `Antitone` tuple. Needed to turn `topSum`'s `decreasingSort` (which re-sorts) back into a plain
  sum over an already-sorted tuple, e.g. `hA.eigenvalues₀` (`EigenvalueMonotonicity.lean`,
  `SpectralDecomposition.lean`, `KyFanNorm.lean`).
* `Majorization.sum_mul_le_topSum`: weighting `w` by a `[0,1]`-valued `c` summing to `k` cannot
  beat `topSum w k`, the sum of `w`'s `k` largest entries. Assembled from `exists_top_finset`
  (constructs the top-`k` index set) and `sum_mul_le_sum_of_threshold` (the abstract averaging
  bound for any such threshold set).
* `Majorization.topSum_nonneg`: `topSum f k` is nonnegative when `f` is entrywise nonnegative.
  Needed by `Matrix.kyFanNorm_nonneg` (`KyFanNorm.lean`).
* `Majorization.forall_eq_zero_of_topSum_eq_zero`: a nonnegative `f` with a vanishing top-`k` sum
  (`k ≥ 1`) vanishes entirely. Needed by `Matrix.kyFanNorm_eq_zero_iff` (`KyFanNorm.lean`), the
  definiteness half of exhibiting `kyFanNorm k` as a genuine norm.
-/

namespace Majorization

variable {n : ℕ}

/-- The entries of `f`, rearranged into decreasing order. -/
noncomputable def decreasingSort (f : Fin n → ℝ) : Fin n → ℝ :=
  f ∘ Tuple.sort (-f)

theorem antitone_decreasingSort (f : Fin n → ℝ) : Antitone (decreasingSort f) := fun i j hij => by
  have h := Tuple.monotone_sort (-f) hij
  simpa [decreasingSort] using h

/-- `decreasingSort` is the identity on an already-`Antitone` tuple. Needed to turn `topSum`'s
`decreasingSort` (which re-sorts) back into a plain sum over an already-sorted tuple, e.g.
`hA.eigenvalues₀` via `Matrix.IsHermitian.eigenvalues₀_antitone`
(`EigenvalueMonotonicity.lean`/`SpectralDecomposition.lean`/`KyFanNorm.lean`). -/
theorem decreasingSort_of_antitone {f : Fin n → ℝ} (hf : Antitone f) : decreasingSort f = f := by
  have h1 : Antitone (f ∘ Tuple.sort (-f)) := antitone_decreasingSort f
  have h2 : Antitone (f ∘ Equiv.refl (Fin n)) := hf
  simpa [decreasingSort] using Tuple.unique_antitone h1 h2

/-- Precomposing `f` with a permutation of its index type does not change its `decreasingSort`:
`f` and `f ∘ σ` have the same multiset of values, just reindexed, so sorting them into decreasing
order produces the same result. Needed by `topSum_comp_perm` below, and by
`Matrix.IsHermitian.topSum_eigenvalues₀_diagonal` (`SumKroneckerMajorization.lean`) to identify a
diagonal Hermitian matrix's `eigenvalues₀` with its (unsorted) diagonal-defining function read out
along any bijection. -/
theorem decreasingSort_comp_perm (f : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) :
    decreasingSort (f ∘ σ) = decreasingSort f := by
  have heq : (-f) ∘ σ = -(f ∘ σ) := by funext x; simp
  have h := Tuple.comp_perm_comp_sort_eq_comp_sort (f := -f) (σ := σ)
  rw [heq] at h
  funext i
  have hi := congrFun h i
  simp only [Function.comp_apply, Pi.neg_apply] at hi
  unfold decreasingSort
  simp only [Function.comp_apply]
  linarith [hi]

/-- If `f` is entrywise nonnegative, so is `decreasingSort f`: its values are `f`'s values, just
reindexed. -/
theorem decreasingSort_nonneg (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) (i : Fin n) :
    0 ≤ decreasingSort f i := by
  unfold decreasingSort
  exact hf _

/-- The sum of the `k` largest entries of `f`. -/
noncomputable def topSum (f : Fin n → ℝ) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.univ.filter (fun i : Fin n => (i : ℕ) < k), decreasingSort f i

/-- `topSum f k` is nonnegative when `f` is entrywise nonnegative: it is a sum of (nonnegative)
values of `decreasingSort f`. -/
theorem topSum_nonneg (f : Fin n → ℝ) (hf : ∀ i, 0 ≤ f i) (k : ℕ) : 0 ≤ topSum f k :=
  Finset.sum_nonneg (fun i _ => decreasingSort_nonneg f hf i)

/-- Precomposing `f` with a permutation of its index type does not change `topSum`: `topSum` only
depends on `f` through `decreasingSort f` (`decreasingSort_comp_perm`). -/
theorem topSum_comp_perm (f : Fin n → ℝ) (σ : Equiv.Perm (Fin n)) (k : ℕ) :
    topSum (f ∘ σ) k = topSum f k := by
  unfold topSum
  rw [decreasingSort_comp_perm]

/-- Scaling `f` by a nonnegative constant `c` scales `decreasingSort f` by the same constant:
`c = 0` is immediate (both sides are the zero function), and for `c > 0`, `Tuple.sort` of `-(c•f)`
and of `-f` agree because `Tuple.comp_sort_eq_comp_iff_monotone` characterizes `Tuple.sort g` as
*the* permutation making `g ∘ σ` monotone, and monotonicity is unaffected by scaling by a positive
constant. Needed by `topSum_smul` below. -/
theorem decreasingSort_smul {f : Fin n → ℝ} {c : ℝ} (hc : 0 ≤ c) :
    decreasingSort (c • f) = c • decreasingSort f := by
  rcases hc.eq_or_lt with hc0 | hc0
  · funext i
    rw [← hc0]
    unfold decreasingSort
    simp
  · have hmono : Monotone ((-f) ∘ Tuple.sort (-(c • f))) := by
      intro i j hij
      have h := Tuple.monotone_sort (-(c • f)) hij
      simp only [Function.comp_apply, Pi.neg_apply, Pi.smul_apply, smul_eq_mul] at h ⊢
      nlinarith [h]
    have hkey : (-f) ∘ Tuple.sort (-(c • f)) = (-f) ∘ Tuple.sort (-f) :=
      Tuple.comp_sort_eq_comp_iff_monotone.mpr hmono
    have hi : ∀ i, f (Tuple.sort (-(c • f)) i) = f (Tuple.sort (-f) i) := fun i => by
      have h := congrFun hkey i
      simpa using h
    funext i
    unfold decreasingSort
    simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
    rw [hi i]

/-- Scaling `f` by a nonnegative constant `c` scales `topSum f k` by the same constant: immediate
from `decreasingSort_smul`. Needed by `Matrix.kyFanNorm_smul` (`KyFanNorm.lean`), in turn needed by
the Cauchy–Schwarz inequality for Ky Fan norms (`KyFanCauchySchwarz.lean`). -/
theorem topSum_smul {f : Fin n → ℝ} {c : ℝ} (hc : 0 ≤ c) (k : ℕ) :
    topSum (c • f) k = c * topSum f k := by
  unfold topSum
  rw [decreasingSort_smul hc, Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by simp

/-- `topSum f k` saturates at `k = n`: once `k ≥ n`, the filter defining `topSum` already covers
every index of `Fin n`, so `topSum f k` equals `topSum f n` (the sum of *all* of `decreasingSort
f`'s entries). Needed to extend a weak-majorization bound established only for `k ≤ n` (the range
`WeakMajorizedBy` quantifies over) to every `k : ℕ`. -/
theorem topSum_eq_topSum_of_le (f : Fin n → ℝ) {k : ℕ} (hk : n ≤ k) :
    topSum f k = topSum f n := by
  unfold topSum
  rw [Finset.filter_true_of_mem (fun i _ => lt_of_lt_of_le i.2 hk),
    Finset.filter_true_of_mem (fun i (_ : i ∈ Finset.univ) => i.2)]

/-- `x` is *weakly majorized* by `y` if, for every `k`, the sum of the `k` largest entries of `x`
is at most the sum of the `k` largest entries of `y`. -/
def WeakMajorizedBy (x y : Fin n → ℝ) : Prop :=
  ∀ k ≤ n, topSum x k ≤ topSum y k

@[inherit_doc]
scoped infix:50 " ≺w " => WeakMajorizedBy

/-- `x` is *majorized* by `y` if `x` is weakly majorized by `y` and they have the same total
sum. -/
def MajorizedBy (x y : Fin n → ℝ) : Prop :=
  WeakMajorizedBy x y ∧ ∑ i, x i = ∑ i, y i

@[inherit_doc]
scoped infix:50 " ≺ " => MajorizedBy

/-- The top-`k` index set of `w`: the `Finset` of size `k` obtained by taking the first `k`
indices of `Tuple.sort (-w)` (which lists `Fin n` in decreasing order of `w`). Its entries sum to
`topSum w k`, and every entry inside it dominates every entry outside it. This packages the
sorting machinery used by `sum_mul_le_topSum`, separately from the purely combinatorial averaging
argument in `sum_mul_le_sum_of_threshold`. -/
theorem exists_top_finset (w : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) :
    ∃ T : Finset (Fin n), T.card = k ∧ ∑ i ∈ T, w i = topSum w k ∧
      ∀ i ∈ T, ∀ j ∉ T, w j ≤ w i := by
  set σ : Equiv.Perm (Fin n) := Tuple.sort (-w) with hσ_def
  have hanti : Antitone (fun i => w (σ i)) := by
    intro a b hab
    rw [hσ_def]
    simpa using Tuple.monotone_sort (-w) hab
  set F : Finset (Fin n) := Finset.univ.filter (fun i : Fin n => (i : ℕ) < k) with hF_def
  set T : Finset (Fin n) := F.image σ with hT_def
  have hdecomp : ∀ i, decreasingSort w i = w (σ i) := by
    intro i
    simp [decreasingSort, ← hσ_def]
  have hFcard : F.card = k := by
    have hFeq : F = (Finset.range k).attachFin
        (fun m hm => lt_of_lt_of_le (Finset.mem_range.mp hm) hk) := by
      ext i
      simp [hF_def, Finset.mem_filter, Finset.mem_attachFin, Finset.mem_range]
    rw [hFeq, Finset.card_attachFin, Finset.card_range]
  have hTcard : T.card = k := by
    rw [hT_def, Finset.card_image_of_injective _ σ.injective, hFcard]
  have hTsum : topSum w k = ∑ i ∈ T, w i := by
    unfold topSum
    rw [hT_def, Finset.sum_image (fun x _ y _ h => σ.injective h), hF_def]
    exact Finset.sum_congr rfl (fun i _ => hdecomp i)
  have hTmem : ∀ i, i ∈ T ↔ (σ.symm i : ℕ) < k := by
    intro i
    rw [hT_def, Finset.mem_image]
    constructor
    · rintro ⟨a, ha, rfl⟩
      rw [hF_def, Finset.mem_filter] at ha
      simpa using ha.2
    · intro h
      refine ⟨σ.symm i, ?_, by simp⟩
      rw [hF_def, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, h⟩
  refine ⟨T, hTcard, hTsum.symm, fun i hi j hj => ?_⟩
  rw [hTmem] at hi
  rw [hTmem] at hj
  have hj' : k ≤ (σ.symm j : ℕ) := not_lt.mp hj
  have hab : σ.symm i ≤ σ.symm j := by
    rw [Fin.le_def]
    exact (lt_of_lt_of_le hi hj').le
  simpa using hanti hab

/-- A nonnegative `f` with a vanishing top-`k` sum (`1 ≤ k ≤ n`) vanishes entirely: the top-`k`
finset (`exists_top_finset`) is nonempty and dominates every other index, so if even its
(nonnegative) entries sum to zero they must each be zero, and domination then forces every other
entry to be squeezed between that zero ceiling and nonnegativity. -/
theorem forall_eq_zero_of_topSum_eq_zero {f : Fin n → ℝ} (hf : ∀ i, 0 ≤ f i) {k : ℕ} (hk : 1 ≤ k)
    (hkn : k ≤ n) (h : topSum f k = 0) : ∀ i, f i = 0 := by
  obtain ⟨T, hTcard, hTsum, hdom⟩ := exists_top_finset f k hkn
  have hTne : T.Nonempty := Finset.card_pos.mp (by rw [hTcard]; omega)
  have hTzero : ∀ i ∈ T, f i = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hf i)).mp (hTsum.trans h)
  intro i
  by_cases hi : i ∈ T
  · exact hTzero i hi
  · obtain ⟨j, hj⟩ := hTne
    have hle : f i ≤ f j := hdom j hj i hi
    rw [hTzero j hj] at hle
    exact le_antisymm hle (hf i)

/-- If `T` is a size-`k` subset of `Fin n` such that every `w`-entry inside `T` dominates every
`w`-entry outside `T`, then weighting `w` by any `[0,1]`-valued `c` summing to `k` cannot beat the
sum of `w` over `T` — the "top-`k` beats any `[0,1]`-weighted average of the same total mass"
fact, stated for an abstract threshold set rather than concretely the top-`k` set.

Proof: handle `k = 0`/`k = T.card = n` degenerately (`c` is forced to be all-`0`/all-`1`);
otherwise split `∑ i, w i * c i` against `T`, `Tᶜ` and bound using `T.inf' w ≥ Tᶜ.sup' w` together
with the shared "mass" `∑_{i∈T} (1 - c i) = ∑_{i∉T} c i` forced by `∑ i, c i = k`. -/
theorem sum_mul_le_sum_of_threshold {T : Finset (Fin n)} {w c : Fin n → ℝ} {k : ℕ}
    (hTcard : T.card = k) (hk : k ≤ n) (hc0 : ∀ i, 0 ≤ c i) (hc1 : ∀ i, c i ≤ 1)
    (hsum : ∑ i, c i = (k : ℝ)) (hkey : ∀ i ∈ T, ∀ j ∉ T, w j ≤ w i) :
    ∑ i, w i * c i ≤ ∑ i ∈ T, w i := by
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · -- k = 0: hsum forces c ≡ 0
    have hsum0 : ∑ i, c i = 0 := by rw [hsum, hk0]; norm_num
    have hz := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => hc0 i)).mp hsum0
    have hzero : ∑ i, w i * c i = 0 :=
      Finset.sum_eq_zero (fun i _ => by rw [hz i (Finset.mem_univ i), mul_zero])
    have hTempty : T = ∅ := Finset.card_eq_zero.mp (by rw [hTcard, hk0])
    rw [hzero, hTempty]
    simp
  · rcases hk.eq_or_lt with hkn | hkltn
    · -- k = n: hsum forces c ≡ 1
      have hTuniv : T = Finset.univ := by
        apply Finset.eq_univ_of_card
        rw [hTcard, hkn, Fintype.card_fin]
      have hc_one : ∀ i, c i = 1 := by
        have hexp : ∑ i, (1 - c i) = (Fintype.card (Fin n) : ℝ) - ∑ i, c i := by
          rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]
        have hsum' : ∑ i, (1 - c i) = 0 := by rw [hexp, hsum, Fintype.card_fin, hkn]; ring
        have hz := (Finset.sum_eq_zero_iff_of_nonneg
          (fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => sub_nonneg.mpr (hc1 i))).mp hsum'
        exact fun i => by linarith [hz i (Finset.mem_univ i)]
      have hfinal : ∑ i, w i * c i = ∑ i ∈ T, w i := by
        rw [hTuniv]
        exact Finset.sum_congr rfl (fun i _ => by rw [hc_one i, mul_one])
      exact hfinal.le
    · -- 0 < k < n: the genuine threshold-set argument
      have hTne : T.Nonempty := Finset.card_pos.mp (by rw [hTcard]; exact hkpos)
      have hTcne : Tᶜ.Nonempty := by
        rw [← Finset.card_pos, Finset.card_compl, hTcard, Fintype.card_fin]
        omega
      set m1 := T.inf' hTne w
      set m2 := Tᶜ.sup' hTcne w
      have hm1_le : ∀ i ∈ T, m1 ≤ w i := fun i hi => Finset.inf'_le w hi
      have hm2_ge : ∀ j ∈ Tᶜ, w j ≤ m2 := fun j hj => Finset.le_sup' w hj
      have hm21 : m2 ≤ m1 := by
        refine Finset.sup'_le hTcne w (fun j hj => Finset.le_inf' hTne w (fun i hi => ?_))
        exact hkey i hi j (Finset.mem_compl.mp hj)
      set S := ∑ i ∈ T, (1 - c i) with hS_def
      have hSnonneg : 0 ≤ S :=
        Finset.sum_nonneg (fun i _ => by linarith [hc1 i])
      have hSTc : S = ∑ i ∈ Tᶜ, c i := by
        have hadd := Finset.sum_add_sum_compl T c
        rw [hsum] at hadd
        have hS' : S = (T.card : ℝ) - ∑ i ∈ T, c i := by
          rw [hS_def, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
        rw [hS', hTcard]
        linarith [hadd]
      -- Weighting `T` by `c` loses at least `m1 * S` compared to weighting it by `1`.
      have hineq1 : ∑ i ∈ T, w i * c i ≤ ∑ i ∈ T, w i - m1 * S := by
        have hb : m1 * S ≤ ∑ i ∈ T, w i * (1 - c i) := by
          rw [hS_def, Finset.mul_sum]
          exact Finset.sum_le_sum
            (fun i hi => mul_le_mul_of_nonneg_right (hm1_le i hi) (by linarith [hc1 i]))
        have heq2 : ∑ i ∈ T, w i * (1 - c i) = ∑ i ∈ T, w i - ∑ i ∈ T, w i * c i := by
          rw [← Finset.sum_sub_distrib]
          exact Finset.sum_congr rfl (fun i _ => by ring)
        linarith [hb, heq2]
      -- Weighting `Tᶜ` by `c` gains at most `m2 * S`, the same mass `S` lost from `T`.
      have hineq2 : ∑ i ∈ Tᶜ, w i * c i ≤ m2 * S := by
        rw [hSTc, Finset.mul_sum]
        exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_right (hm2_ge i hi) (hc0 i))
      have hprod : 0 ≤ (m1 - m2) * S := mul_nonneg (by linarith [hm21]) hSnonneg
      have hsplit : ∑ i, w i * c i = ∑ i ∈ T, w i * c i + ∑ i ∈ Tᶜ, w i * c i :=
        (Finset.sum_add_sum_compl T (fun i => w i * c i)).symm
      rw [hsplit]
      nlinarith [hineq1, hineq2, hprod]

/-- If `c` takes values in `[0,1]` and sums to `k`, then weighting `w` by `c` cannot beat the sum
of `w`'s `k` largest entries — the "top-`k` beats any `[0,1]`-weighted average of the same total
mass" fact. Needed by `majorized_sum_kronecker_sortedDiagonal` (`SumKroneckerMajorization.lean`) to
turn the `min{j+1,μₖ}-min{j,μₖ}` coefficients from `trace_mul_kronecker_le_sum_min_diff`
(`OverlapBound.lean`) into a `topSum` bound.

Combines the top-`k` index set of `exists_top_finset` with the abstract averaging bound of
`sum_mul_le_sum_of_threshold`. -/
theorem sum_mul_le_topSum (w c : Fin n → ℝ) (k : ℕ) (hk : k ≤ n) (hc0 : ∀ i, 0 ≤ c i)
    (hc1 : ∀ i, c i ≤ 1) (hsum : ∑ i, c i = (k : ℝ)) : ∑ i, w i * c i ≤ topSum w k := by
  obtain ⟨T, hTcard, hTsum, hkey⟩ := exists_top_finset w k hk
  rw [← hTsum]
  exact sum_mul_le_sum_of_threshold hTcard hk hc0 hc1 hsum hkey

end Majorization
