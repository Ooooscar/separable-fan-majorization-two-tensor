import SeparableFanMajorization.OverlapBound

/-!
# Majorization for sums of Kronecker products of positive semidefinite operators

The positive semidefinite case of the separable Ky Fan majorization for two tensor factors: for
finite families `A⁽¹⁾, …, A⁽ᵐ⁾` on `𝕜^dim1` and `B⁽¹⁾, …, B⁽ᵐ⁾` on `𝕜^dim2`, all positive
semidefinite,
```
λ(∑ᵢ A⁽ⁱ⁾ ⊗ B⁽ⁱ⁾) ≺ ∑ᵢ λ(A⁽ⁱ⁾) ⊗ λ(B⁽ⁱ⁾)
```
where `λ` (`Matrix.IsHermitian.eigenvalues₀`) denotes eigenvalues sorted in decreasing order.

The right-hand side `∑ᵢ λ(A⁽ⁱ⁾) ⊗ λ(B⁽ⁱ⁾)` is realized as a vector of eigenvalues:
`Matrix.PosSemidef.sortedDiagonal A⁽ⁱ⁾` is the diagonal matrix of `A⁽ⁱ⁾`'s eigenvalues (one per
matrix index, order irrelevant), `∑ᵢ sortedDiagonal A⁽ⁱ⁾ ⊗ₖ sortedDiagonal B⁽ⁱ⁾` is positive
semidefinite, and its eigenvalues are exactly what `∑ᵢ λ(A⁽ⁱ⁾) ⊗ λ(B⁽ⁱ⁾)` means as a vector.

* `Matrix.PosSemidef.sortedDiagonal`/`Matrix.PosSemidef.posSemidef_sortedDiagonal`: `λ(A)`
  realized as a diagonal matrix, and its positive semidefiniteness.
* `Matrix.posSemidef_sum_kronecker`: `∑ᵢ A⁽ⁱ⁾ ⊗ B⁽ⁱ⁾` is positive semidefinite (so that its
  eigenvalues, via `.isHermitian.eigenvalues₀`, make sense), from `PosSemidef.kronecker` and
  closure of the PSD cone under sums.
* `Matrix.IsHermitian.topSum_eigenvalues₀_diagonal`: `topSum` of a diagonal Hermitian matrix's
  `eigenvalues₀` agrees with `topSum` of its (unsorted) diagonal-defining function, read out along
  any bijection with `Fin (Fintype.card ι)`.
* `trace_mul_le_topSum_sortedDiagonal`: the weak-majorization half of the capstone theorem, for a
  single rank-`k` projector `Q`, built on `trace_mul_kronecker_le_sum_min_diff`
  (`OverlapBound.lean`).
* `majorized_sum_kronecker_sortedDiagonal`: the majorization theorem itself.
-/

open Matrix
open scoped Kronecker ComplexOrder MatrixOrder Majorization

variable {dim1 dim2 𝕜 : Type*} [Fintype dim1] [Fintype dim2] [DecidableEq dim1] [DecidableEq dim2]
  [RCLike 𝕜]

/-- The diagonal matrix of a positive semidefinite `A`'s eigenvalues: this realizes `λ(A)` in
`majorized_sum_kronecker_sortedDiagonal` below. Built from `hA.isHermitian.eigenvalues : ι → ℝ`
(Mathlib's *matrix-indexed* eigenvalues), deliberately not `.eigenvalues₀ ∘ Fintype.equivFin ι` —
this lines up directly with the `.eigenvectorBasis`-built machinery reused from
`SpectralDecomposition.lean`/`OverlapBound.lean` (in particular `Matrix.IsHermitian.topProjector`),
rather than introducing a second, unrelated choice of enumeration. `.eigenvalues` need not be
sorted as a sequence over `ι` (`ι` may not even be ordered) — but its multiset of values is the
same as the sorted `.eigenvalues₀`'s, which is all a purely eigenvalue-based statement can see. -/
noncomputable def Matrix.PosSemidef.sortedDiagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) : Matrix ι ι 𝕜 :=
  Matrix.diagonal (fun i => (hA.isHermitian.eigenvalues i : 𝕜))

/-- `sortedDiagonal` is again positive semidefinite: it is diagonal with `A`'s (nonnegative, since
`A` is PSD) eigenvalues as its entries. -/
theorem Matrix.PosSemidef.posSemidef_sortedDiagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    {A : Matrix ι ι 𝕜} (hA : A.PosSemidef) : hA.sortedDiagonal.PosSemidef := by
  apply Matrix.PosSemidef.diagonal
  intro i
  simp only [Pi.zero_apply]
  exact_mod_cast hA.eigenvalues_nonneg i

omit [Fintype dim1] [Fintype dim2] [DecidableEq dim1] [DecidableEq dim2] in
/-- A finite sum of Kronecker products of positive semidefinite matrices is itself positive
semidefinite: each summand is PSD by `PosSemidef.kronecker`, and the PSD cone is closed under
sums since it is exactly the nonnegative cone of the Loewner order (`MatrixOrder`). -/
theorem Matrix.posSemidef_sum_kronecker [Finite dim1] [Finite dim2] {m : ℕ}
    {A : Fin m → Matrix dim1 dim1 𝕜} {B : Fin m → Matrix dim2 dim2 𝕜}
    (hA : ∀ i, (A i).PosSemidef) (hB : ∀ i, (B i).PosSemidef) :
    (∑ i, A i ⊗ₖ B i).PosSemidef := by
  classical
  exact Matrix.nonneg_iff_posSemidef.mp <|
    Finset.sum_nonneg fun i _ => Matrix.nonneg_iff_posSemidef.mpr ((hA i).kronecker (hB i))

/-- `topSum` of a diagonal Hermitian matrix's `eigenvalues₀` agrees, at every `k`, with `topSum` of
its diagonal-defining function `d`, read out along *any* bijection `e : ι ≃ Fin (Fintype.card ι)`
— eigenvalues are basis-independent up to permutation, and `topSum` only sees the multiset of
values, so the choice of `e` cannot matter.

Proof, in two stages:

1. *Same multiset.* `Matrix.charpoly_diagonal` gives `charpoly (diagonal d) = ∏ i, (X - d i)`, so
   its roots are the multiset `{d i}` (`Polynomial.roots_prod`), while
   `Matrix.IsHermitian.roots_charpoly_eq_eigenvalues₀` identifies the same roots with
   `{eigenvalues₀ j}` (mirroring `LinearMap.IsSymmetric.sort_roots_charpoly_eq_eigenvalues`,
   `Mathlib.Analysis.InnerProductSpace.Spectrum`). Descending from `𝕜` to `ℝ` (`RCLike.re`) and
   reindexing the `ι`-side along `e` gives: `d ∘ e.symm` and `eigenvalues₀` have equal multisets of
   values, i.e. `List.ofFn (d ∘ e.symm) ~ List.ofFn eigenvalues₀` (`List.Perm`, via
   `Fin.univ_val_map`/`Multiset.coe_eq_coe`).
2. *Same sorted order ⟹ same function.* `eigenvalues₀` is antitone
   (`Matrix.IsHermitian.eigenvalues₀_antitone`), and so is `Majorization.decreasingSort (d ∘
   e.symm)`, which is *also* `List.Perm`-related to `d ∘ e.symm` (`Equiv.Perm.ofFn_comp_perm`) hence
   to `eigenvalues₀`. Two antitone rearrangements of the same multiset coincide
   (`List.Perm.eq_of_sortedGE` + `List.ofFn_injective`), so `decreasingSort (d ∘ e.symm) =
   eigenvalues₀`. Since `decreasingSort (d ∘ e.symm)` is literally `(d ∘ e.symm)` precomposed with a
   permutation, `Majorization.topSum_comp_perm` (`Majorization.lean`) finishes.

Needed by `trace_mul_le_topSum_sortedDiagonal` below. -/
theorem Matrix.IsHermitian.topSum_eigenvalues₀_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι]
    (d : ι → ℝ) (hd : (Matrix.diagonal (fun i => (d i : 𝕜))).IsHermitian)
    (e : ι ≃ Fin (Fintype.card ι)) (k : ℕ) :
    Majorization.topSum hd.eigenvalues₀ k = Majorization.topSum (d ∘ e.symm) k := by
  -- The multiset of `charpoly` roots of the diagonal matrix is, on one hand, `{d i}` (from
  -- `Matrix.charpoly_diagonal`), and on the other, `{hd.eigenvalues₀ j}` (from
  -- `Matrix.IsHermitian.roots_charpoly_eq_eigenvalues₀`).
  have hroots1 : (Matrix.diagonal (fun i => (d i : 𝕜))).charpoly.roots
      = Multiset.map (fun i => (d i : 𝕜)) (Finset.univ : Finset ι).val := by
    rw [Matrix.charpoly_diagonal, Polynomial.roots_prod]
    · simp
    · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]
  have hMeq : Multiset.map (fun i => (d i : 𝕜)) (Finset.univ : Finset ι).val
      = Multiset.map (RCLike.ofReal ∘ hd.eigenvalues₀)
          (Finset.univ : Finset (Fin (Fintype.card ι))).val :=
    hroots1.symm.trans hd.roots_charpoly_eq_eigenvalues₀
  -- Descend from `𝕜` to `ℝ` by applying `RCLike.re` to both sides.
  have hMeq2 : Multiset.map d (Finset.univ : Finset ι).val
      = Multiset.map hd.eigenvalues₀ (Finset.univ : Finset (Fin (Fintype.card ι))).val := by
    have hre := congrArg (Multiset.map (RCLike.re : 𝕜 → ℝ)) hMeq
    simpa [Multiset.map_map, Function.comp_def, RCLike.ofReal_re] using hre
  -- Reindex the `ι`-side along `e` to land on the same index type `Fin (Fintype.card ι)`.
  have hreindex0 : Multiset.map (⇑e.symm) (Finset.univ : Finset (Fin (Fintype.card ι))).val
      = (Finset.univ : Finset ι).val := by
    have h := congrArg Finset.val (Finset.map_univ_equiv e.symm)
    simp only [Finset.map_val, Equiv.coe_toEmbedding] at h
    exact h
  have hreindex : Multiset.map (d ∘ e.symm) (Finset.univ : Finset (Fin (Fintype.card ι))).val
      = Multiset.map d (Finset.univ : Finset ι).val := by
    rw [← Multiset.map_map, hreindex0]
  have hMeq3 : Multiset.map (d ∘ e.symm) (Finset.univ : Finset (Fin (Fintype.card ι))).val
      = Multiset.map hd.eigenvalues₀ (Finset.univ : Finset (Fin (Fintype.card ι))).val := by
    rw [hreindex, hMeq2]
  -- Equal multisets of a `Fin n`-indexed family are exactly `List.ofFn`s related by `List.Perm`.
  have hperm : List.Perm (List.ofFn (d ∘ e.symm)) (List.ofFn hd.eigenvalues₀) := by
    have h1 := Fin.univ_val_map (d ∘ e.symm)
    have h2 := Fin.univ_val_map hd.eigenvalues₀
    rw [h1, h2] at hMeq3
    exact Multiset.coe_eq_coe.mp hMeq3
  -- `decreasingSort (d ∘ e.symm)` is *a* permutation of `d ∘ e.symm`, hence of `hd.eigenvalues₀`
  -- too; being antitone like `hd.eigenvalues₀`, uniqueness of the antitone rearrangement of a
  -- fixed multiset (`List.Perm.eq_of_sortedGE`) identifies the two.
  have hpermSort :
      List.Perm (List.ofFn (Majorization.decreasingSort (d ∘ e.symm))) (List.ofFn (d ∘ e.symm)) :=
    Equiv.Perm.ofFn_comp_perm (Tuple.sort (-(d ∘ e.symm))) (d ∘ e.symm)
  have hlistEq : List.ofFn (Majorization.decreasingSort (d ∘ e.symm)) = List.ofFn hd.eigenvalues₀ :=
    List.Perm.eq_of_sortedGE (Majorization.antitone_decreasingSort (d ∘ e.symm)).sortedGE_ofFn
      hd.eigenvalues₀_antitone.sortedGE_ofFn (hpermSort.trans hperm)
  have hfinal : Majorization.decreasingSort (d ∘ e.symm) = hd.eigenvalues₀ :=
    List.ofFn_injective hlistEq
  rw [← hfinal]
  exact Majorization.topSum_comp_perm (d ∘ e.symm) (Tuple.sort (-(d ∘ e.symm))) k

/-- Bundles the remaining assembly of `majorized_sum_kronecker_sortedDiagonal`'s weak-majorization
half (roadmap steps 2c–2g in that theorem's docstring): given a rank-`k` projector `Q` on
`dim1 × dim2`, `Tr[Q · ∑ᵢ A⁽ⁱ⁾⊗B⁽ⁱ⁾] ≤ topSum` of the sorted-diagonal side's eigenvalues.

Proof, in six steps (`μ := ` the eigenvalues of `Q`'s left partial trace):

1. (`hstep1`–`hcheckpoint`) Sum `trace_mul_kronecker_le_sum_min_diff hQ (hA i) (hB i)`
   (`OverlapBound.lean`) over `i`, swap the resulting triple sum so the `i`-sum is innermost, and
   reindex the outer `(j,l) : Fin (Fintype.card dim1) × Fin (Fintype.card dim2)` double sum along
   `E := ((equivOfCardEq ..).prodCongr (equivOfCardEq ..)).trans (Fintype.equivFin (dim1 × dim2))`
   to land on `Tr[Q · ∑ᵢ A⁽ⁱ⁾⊗B⁽ⁱ⁾] ≤ ∑ q, w q * c q`, for `w := ` the `(j,l)`-summand's
   `∑ᵢ λⱼ(A⁽ⁱ⁾)λₗ(B⁽ⁱ⁾)` factor and `c := ` the `min{j+1,μₗ}-min{j,μₗ}` factor (both reindexed
   along `E`).
2. (`hc0`, `hc1`) `0 ≤ c ≤ 1`, the general fact `0 ≤ min(x+1,y) - min(x,y) ≤ 1` specialized.
3. (`hsum_c`) `∑ c = k`: `0 ≤ Q ≤ 1` gives `0 ≤ μ ≤ Fintype.card dim1` (via `Q`'s partial trace),
   making each `j`-sum (fixed `l`) a telescoping sum collapsing to `μ l`, and
   `∑ₗ μ l = Tr[Q.traceLeft] = Tr[Q] = k`.
4. (`hw_eq`, `hMdiag_eq`) Identify `w` with the diagonal entries of
   `∑ᵢ sortedDiagonal A⁽ⁱ⁾ ⊗ₖ sortedDiagonal B⁽ⁱ⁾` (a diagonal matrix, as a sum of Kronecker
   products of diagonals, via `Matrix.diagonal_kronecker_diagonal`),
   reindexed along `e0 : dim1 × dim2 ≃ Fin (Fintype.card (dim1 × dim2))`.
5. (`htopSum_eq`) `Matrix.IsHermitian.topSum_eigenvalues₀_diagonal` above turns this into
   `topSum w k = topSum` of the sorted-diagonal side's `eigenvalues₀`.
6. `Majorization.sum_mul_le_topSum` (`Majorization.lean`), fed steps 2–3, bounds
   `∑ q, w q * c q ≤ topSum w k`, closing the goal via step 5. -/
theorem trace_mul_le_topSum_sortedDiagonal {m : ℕ} {A : Fin m → Matrix dim1 dim1 𝕜}
    {B : Fin m → Matrix dim2 dim2 𝕜} (hA : ∀ i, (A i).PosSemidef) (hB : ∀ i, (B i).PosSemidef)
    {Q : Matrix (dim1 × dim2) (dim1 × dim2) 𝕜} (hQ : IsStarProjection Q) (k : ℕ)
    (hQrank : Q.rank = k) :
    (Q * ∑ i, A i ⊗ₖ B i).trace
      ≤ ((Majorization.topSum
          (Matrix.posSemidef_sum_kronecker (fun i => (hA i).posSemidef_sortedDiagonal)
            (fun i => (hB i).posSemidef_sortedDiagonal)).isHermitian.eigenvalues₀ k : ℝ) : 𝕜) := by
  set μ := hQ.isSelfAdjoint.isHermitian.traceLeft.eigenvalues₀
  -- Reindexing equivalence carrying the `(j, l) : Fin (Fintype.card dim1) × Fin (Fintype.card
  -- dim2)` double index onto a single `Fin (Fintype.card (dim1 × dim2))` index, via `dim1 × dim2`.
  set E : Fin (Fintype.card dim1) × Fin (Fintype.card dim2) ≃ Fin (Fintype.card (dim1 × dim2)) :=
    ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card dim1))).prodCongr
        (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card dim2)))).trans
      (Fintype.equivFin (dim1 × dim2)) with hE_def
  -- The weight `w` (the `(j,l)`-summand's `∑ᵢ λⱼ(A⁽ⁱ⁾)λₗ(B⁽ⁱ⁾)` factor) and coefficient `c`
  -- (the `min{j+1,μₗ}-min{j,μₗ}` factor), both reindexed along `E`.
  set w : Fin (Fintype.card (dim1 × dim2)) → ℝ :=
    fun q => ∑ i, (hA i).isHermitian.eigenvalues₀ (E.symm q).1
      * (hB i).isHermitian.eigenvalues₀ (E.symm q).2 with hw_def
  set c : Fin (Fintype.card (dim1 × dim2)) → ℝ :=
    fun q => min (((E.symm q).1 : ℝ) + 1) (μ (E.symm q).2) - min ((E.symm q).1 : ℝ) (μ (E.symm q).2)
    with hc_def
  -- Step 1: sum the per-`i` bound `trace_mul_kronecker_le_sum_min_diff` over `i`.
  have hstep1 : (Q * ∑ i, A i ⊗ₖ B i).trace
      ≤ (↑(∑ i, ∑ j : Fin (Fintype.card dim1), ∑ l : Fin (Fintype.card dim2),
          (hA i).isHermitian.eigenvalues₀ j * (hB i).isHermitian.eigenvalues₀ l
            * (min ((j : ℝ) + 1) (μ l) - min (j : ℝ) (μ l))) : 𝕜) := by
    have heq : (Q * ∑ i, A i ⊗ₖ B i).trace = ∑ i, (Q * (A i ⊗ₖ B i)).trace := by
      rw [Finset.mul_sum, Matrix.trace_sum]
    rw [heq, RCLike.ofReal_sum]
    exact Finset.sum_le_sum (fun i _ => trace_mul_kronecker_le_sum_min_diff hQ (hA i) (hB i))
  -- Step 2: swap the order of summation so the `i`-sum is innermost (it is the only factor
  -- depending on `i`), and factor it out.
  have hstep2 : ∑ i, ∑ j : Fin (Fintype.card dim1), ∑ l : Fin (Fintype.card dim2),
      (hA i).isHermitian.eigenvalues₀ j * (hB i).isHermitian.eigenvalues₀ l
        * (min ((j : ℝ) + 1) (μ l) - min (j : ℝ) (μ l))
      = ∑ j : Fin (Fintype.card dim1), ∑ l : Fin (Fintype.card dim2),
          (∑ i, (hA i).isHermitian.eigenvalues₀ j * (hB i).isHermitian.eigenvalues₀ l)
            * (min ((j : ℝ) + 1) (μ l) - min (j : ℝ) (μ l)) := by
    calc ∑ i, ∑ j : Fin (Fintype.card dim1), ∑ l : Fin (Fintype.card dim2),
        (hA i).isHermitian.eigenvalues₀ j * (hB i).isHermitian.eigenvalues₀ l
          * (min ((j : ℝ) + 1) (μ l) - min (j : ℝ) (μ l))
        = ∑ j : Fin (Fintype.card dim1), ∑ i, ∑ l : Fin (Fintype.card dim2),
            (hA i).isHermitian.eigenvalues₀ j * (hB i).isHermitian.eigenvalues₀ l
              * (min ((j : ℝ) + 1) (μ l) - min (j : ℝ) (μ l)) := Finset.sum_comm
      _ = ∑ j : Fin (Fintype.card dim1), ∑ l : Fin (Fintype.card dim2), ∑ i,
            (hA i).isHermitian.eigenvalues₀ j * (hB i).isHermitian.eigenvalues₀ l
              * (min ((j : ℝ) + 1) (μ l) - min (j : ℝ) (μ l)) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_comm
      _ = ∑ j : Fin (Fintype.card dim1), ∑ l : Fin (Fintype.card dim2),
          (∑ i, (hA i).isHermitian.eigenvalues₀ j * (hB i).isHermitian.eigenvalues₀ l)
            * (min ((j : ℝ) + 1) (μ l) - min (j : ℝ) (μ l)) :=
          Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => (Finset.sum_mul ..).symm
  -- Step 3: flatten and reindex the double sum over `Fin (Fintype.card dim1) × Fin (Fintype.card
  -- dim2)` along `E` into a single sum over `Fin (Fintype.card (dim1 × dim2))`, landing on
  -- `∑ q, w q * c q`.
  have hstep3 : ∑ j : Fin (Fintype.card dim1), ∑ l : Fin (Fintype.card dim2),
      (∑ i, (hA i).isHermitian.eigenvalues₀ j * (hB i).isHermitian.eigenvalues₀ l)
        * (min ((j : ℝ) + 1) (μ l) - min (j : ℝ) (μ l))
      = ∑ q : Fin (Fintype.card (dim1 × dim2)), w q * c q := by
    rw [← Fintype.sum_prod_type']
    exact (Equiv.sum_comp E.symm (fun p =>
      (∑ i, (hA i).isHermitian.eigenvalues₀ p.1 * (hB i).isHermitian.eigenvalues₀ p.2)
        * (min ((p.1 : ℝ) + 1) (μ p.2) - min (p.1 : ℝ) (μ p.2)))).symm
  have hcombine : (∑ i, ∑ j : Fin (Fintype.card dim1), ∑ l : Fin (Fintype.card dim2),
      (hA i).isHermitian.eigenvalues₀ j * (hB i).isHermitian.eigenvalues₀ l
        * (min ((j : ℝ) + 1) (μ l) - min (j : ℝ) (μ l)))
      = ∑ q : Fin (Fintype.card (dim1 × dim2)), w q * c q := hstep2.trans hstep3
  have hcheckpoint : (Q * ∑ i, A i ⊗ₖ B i).trace ≤ (↑(∑ q, w q * c q) : 𝕜) := by
    rw [← hcombine]; exact hstep1
  refine le_trans hcheckpoint ?_
  -- Step 4: each `c q ∈ [0,1]`. `c q` specializes the general fact that
  -- `min(x+1,y) - min(x,y) ∈ [0,1]` for any reals `x, y`: the difference is `≥ 0` since
  -- `t ↦ min(t,y)` is monotone, and `≤ 1` by splitting on whether `x ≤ y` or `y ≤ x`.
  have hmin_bound : ∀ x y : ℝ, 0 ≤ min (x + 1) y - min x y ∧ min (x + 1) y - min x y ≤ 1 := by
    intro x y
    refine ⟨?_, ?_⟩
    · have h : min x y ≤ min (x + 1) y := min_le_min (by linarith) le_rfl
      linarith
    · rcases le_total x y with hxy | hxy
      · rw [min_eq_left hxy]
        linarith [min_le_left (x + 1) y]
      · rw [min_eq_right hxy]
        linarith [min_le_right (x + 1) y]
  have hc0 : ∀ q, 0 ≤ c q := fun q => by simp only [hc_def]; exact (hmin_bound _ _).1
  have hc1 : ∀ q, c q ≤ 1 := fun q => by simp only [hc_def]; exact (hmin_bound _ _).2
  -- Step 5: `∑ q, c q = k`. `μ`'s partial-trace origin gives `0 ≤ μ l ≤ Fintype.card dim1` for
  -- every `l` (from `Q.traceLeft` being PSD and `≤ (Fintype.card dim1) • 1`, both consequences of
  -- `0 ≤ Q ≤ 1`); this makes each `j`-sum (for fixed `l`) a telescoping sum collapsing to
  -- `min(Fintype.card dim1, μ l) - min(0, μ l) = μ l`, and summing over `l` gives
  -- `Tr[Q.traceLeft] = Tr[Q] = Q.rank = k`.
  have hQtraceLeft_posSemidef : Q.traceLeft.PosSemidef := by
    rw [← Phi_one_right]
    exact Phi_posSemidef hQ.posSemidef (IsStarProjection.one (Matrix dim1 dim1 𝕜)).posSemidef
  have hμ_nonneg : ∀ l, 0 ≤ μ l := fun l => hQtraceLeft_posSemidef.eigenvalues₀_nonneg l
  have hQtraceLeft_le : Q.traceLeft ≤ ((Fintype.card dim1 : ℝ) : 𝕜) • (1 : Matrix dim2 dim2 𝕜) := by
    have h := Phi_posSemidef hQ.one_sub.posSemidef
      (IsStarProjection.one (Matrix dim1 dim1 𝕜)).posSemidef
    have hnn := Matrix.nonneg_iff_posSemidef.mpr h
    rw [Phi_sub_left, Phi_one_left, Phi_one_right, Matrix.trace_one,
      ← RCLike.ofReal_natCast (Fintype.card dim1)] at hnn
    exact sub_nonneg.mp hnn
  have hμ_le : ∀ l, μ l ≤ Fintype.card dim1 := fun l =>
    hQ.isSelfAdjoint.isHermitian.traceLeft.eigenvalues₀_le_of_le_smul_one hQtraceLeft_le l
  have htelescope : ∀ l : Fin (Fintype.card dim2),
      ∑ j : Fin (Fintype.card dim1), (min ((j : ℝ) + 1) (μ l) - min (j : ℝ) (μ l)) = μ l := by
    intro l
    set f : ℕ → ℝ := fun x => min (x : ℝ) (μ l) with hf_def
    have hsummand : ∀ j : Fin (Fintype.card dim1),
        min ((j : ℝ) + 1) (μ l) - min (j : ℝ) (μ l) = f ((j : ℕ) + 1) - f (j : ℕ) := by
      intro j
      simp only [hf_def]
      push_cast
      ring_nf
    simp_rw [hsummand]
    rw [(Finset.sum_range (fun i => f (i + 1) - f i)).symm, Finset.sum_range_sub f]
    have h0 : f 0 = 0 := by simp [hf_def, hμ_nonneg l]
    have hn : f (Fintype.card dim1) = μ l := by
      simp only [hf_def]
      exact min_eq_right (hμ_le l)
    rw [h0, hn, sub_zero]
  have hsum_mu : ∑ l, μ l = (k : ℝ) := by
    have hcast : ((∑ l, μ l : ℝ) : 𝕜) = (k : 𝕜) := by
      rw [RCLike.ofReal_sum, hQ.isSelfAdjoint.isHermitian.traceLeft.sum_eigenvalues₀_eq_trace,
        Matrix.trace_traceLeft, hQ.trace_eq_rank, hQrank]
    exact_mod_cast hcast
  have hc_sum : ∑ q : Fin (Fintype.card (dim1 × dim2)), c q
      = ∑ j : Fin (Fintype.card dim1), ∑ l : Fin (Fintype.card dim2),
          (min ((j : ℝ) + 1) (μ l) - min (j : ℝ) (μ l)) := by
    rw [← Fintype.sum_prod_type']
    exact Equiv.sum_comp E.symm
      (fun p => min ((p.1 : ℝ) + 1) (μ p.2) - min ((p.1 : ℝ)) (μ p.2))
  have hsum_c : ∑ q, c q = (k : ℝ) := by
    rw [hc_sum]
    calc ∑ j : Fin (Fintype.card dim1), ∑ l : Fin (Fintype.card dim2),
          (min ((j : ℝ) + 1) (μ l) - min (j : ℝ) (μ l))
        = ∑ l : Fin (Fintype.card dim2), ∑ j : Fin (Fintype.card dim1),
            (min ((j : ℝ) + 1) (μ l) - min (j : ℝ) (μ l)) := Finset.sum_comm
      _ = ∑ l : Fin (Fintype.card dim2), μ l := Finset.sum_congr rfl (fun l _ => htelescope l)
      _ = (k : ℝ) := hsum_mu
  -- Step 6: identify `w` with the diagonal entries of
  -- `M' := ∑ᵢ sortedDiagonal A⁽ⁱ⁾ ⊗ₖ sortedDiagonal B⁽ⁱ⁾`, reindexed along
  -- `e0 : dim1 × dim2 ≃ Fin (Fintype.card (dim1 × dim2))`: `M'` is diagonal (Kronecker
  -- of diagonals, summed) with diagonal-defining function `d mn := ∑ᵢ eigenvalues(A⁽ⁱ⁾) mn.1 *
  -- eigenvalues(B⁽ⁱ⁾) mn.2`, and unwinding `E = (e_A.prodCongr e_B).trans e0` together with
  -- `eigenvalues = eigenvalues₀ ∘ e_A.symm` (`Matrix.IsHermitian.eigenvalues`'s definition) shows
  -- `w = d ∘ e0.symm`. Then `Matrix.IsHermitian.topSum_eigenvalues₀_diagonal` identifies
  -- `topSum w k` with `topSum` of the sorted-diagonal side's `eigenvalues₀`, and
  -- `Majorization.sum_mul_le_topSum` (fed `hc0`, `hc1`, `hsum_c`) finishes.
  set e0 : dim1 × dim2 ≃ Fin (Fintype.card (dim1 × dim2)) := Fintype.equivFin (dim1 × dim2)
  set d : dim1 × dim2 → ℝ :=
    fun mn => ∑ i, (hA i).isHermitian.eigenvalues mn.1 * (hB i).isHermitian.eigenvalues mn.2
    with hd_def
  have hEsymm : E.symm = ((Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card dim1))).prodCongr
      (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card dim2)))).symm ∘ e0.symm := by
    funext q
    rw [hE_def]
    exact Equiv.symm_trans_apply _ e0 q
  have hw_eq : w = d ∘ e0.symm := by
    funext q
    simp [hw_def, hd_def, hEsymm, Matrix.IsHermitian.eigenvalues]
  have hterm : ∀ i, (hA i).sortedDiagonal ⊗ₖ (hB i).sortedDiagonal
      = Matrix.diagonal (fun mn : dim1 × dim2 =>
          ((hA i).isHermitian.eigenvalues mn.1 : 𝕜) * ((hB i).isHermitian.eigenvalues mn.2 : 𝕜)) :=
    fun i => Matrix.diagonal_kronecker_diagonal _ _
  have hMdiag_eq : (∑ i, (hA i).sortedDiagonal ⊗ₖ (hB i).sortedDiagonal)
      = Matrix.diagonal (fun mn => (d mn : 𝕜)) := by
    ext p q
    simp only [Matrix.sum_apply, hterm, Matrix.diagonal_apply]
    split_ifs with h
    · simp only [hd_def, RCLike.ofReal_sum]
      exact Finset.sum_congr rfl fun i _ => (RCLike.ofReal_mul _ _).symm
    · simp
  have heigen_congr : ∀ {X Y : Matrix (dim1 × dim2) (dim1 × dim2) 𝕜} (h : X = Y)
      (hX : X.IsHermitian), (h ▸ hX : Y.IsHermitian).eigenvalues₀ = hX.eigenvalues₀ := by
    intro X Y h hX
    subst h
    rfl
  have hM'_posSemidef : (∑ i, (hA i).sortedDiagonal ⊗ₖ (hB i).sortedDiagonal).PosSemidef :=
    Matrix.posSemidef_sum_kronecker (fun i => (hA i).posSemidef_sortedDiagonal)
      (fun i => (hB i).posSemidef_sortedDiagonal)
  have hd_herm : (Matrix.diagonal (fun mn => (d mn : 𝕜))).IsHermitian :=
    hMdiag_eq ▸ hM'_posSemidef.isHermitian
  have htopSum_eq : Majorization.topSum hM'_posSemidef.isHermitian.eigenvalues₀ k
      = Majorization.topSum w k := by
    rw [← heigen_congr hMdiag_eq hM'_posSemidef.isHermitian, hw_eq]
    exact Matrix.IsHermitian.topSum_eigenvalues₀_diagonal d hd_herm e0 k
  have hk : k ≤ Fintype.card (dim1 × dim2) := by rw [← hQrank]; exact Q.rank_le_card_width
  change (↑(∑ q, w q * c q) : 𝕜) ≤ ((Majorization.topSum hM'_posSemidef.isHermitian.eigenvalues₀ k
    : ℝ) : 𝕜)
  rw [htopSum_eq]
  exact RCLike.ofReal_le_ofReal.mpr (Majorization.sum_mul_le_topSum w c k hk hc0 hc1 hsum_c)

/-- **Separable Ky Fan majorization, PSD case**: for finite families `A⁽¹⁾, …, A⁽ᵐ⁾` of positive
semidefinite operators on `dim1` and `B⁽¹⁾, …, B⁽ᵐ⁾` of positive semidefinite operators on `dim2`,
`λ(∑ᵢ A⁽ⁱ⁾ ⊗ B⁽ⁱ⁾) ≺ ∑ᵢ λ(A⁽ⁱ⁾) ⊗ λ(B⁽ⁱ⁾)`, the right-hand side realized as the eigenvalues of
`M' := ∑ᵢ sortedDiagonal A⁽ⁱ⁾ ⊗ₖ sortedDiagonal B⁽ⁱ⁾` (`Matrix.PosSemidef.sortedDiagonal`).

`MajorizedBy` unfolds to `WeakMajorizedBy` + equal totals:

* *Equal totals*: `Tr[M] = Tr[M']` termwise (`Matrix.trace_kronecker` +
  `Matrix.IsHermitian.trace_eq_sum_eigenvalues`, `sortedDiagonal` being diagonal), then
  `Matrix.IsHermitian.sum_eigenvalues₀_eq_trace` (`SpectralDecomposition.lean`) turns trace
  equality into `eigenvalues₀`-sum equality.
* *Weak majorization*, for each `k`: `Q_k := M.isHermitian.topProjector k`
  (`SpectralDecomposition.lean`) is a rank-`k` projector with
  `topSum (M.isHermitian.eigenvalues₀) k = Tr[Q_k · M]`
  (`Matrix.IsHermitian.trace_mul_topProjector_self`, the "self" Ky Fan equality — no need for the
  full variational sup over all rank-`k` projectors, only this specific `Q_k`), and
  `trace_mul_le_topSum_sortedDiagonal` above bounds `Tr[Q_k · M]` by
  `topSum (M'.eigenvalues₀) k`. -/
theorem majorized_sum_kronecker_sortedDiagonal {m : ℕ} {A : Fin m → Matrix dim1 dim1 𝕜}
    {B : Fin m → Matrix dim2 dim2 𝕜} (hA : ∀ i, (A i).PosSemidef) (hB : ∀ i, (B i).PosSemidef) :
    (Matrix.posSemidef_sum_kronecker hA hB).isHermitian.eigenvalues₀
      ≺ (Matrix.posSemidef_sum_kronecker (fun i => (hA i).posSemidef_sortedDiagonal)
          (fun i => (hB i).posSemidef_sortedDiagonal)).isHermitian.eigenvalues₀ := by
  have hM := Matrix.posSemidef_sum_kronecker hA hB
  have hM' := Matrix.posSemidef_sum_kronecker (fun i => (hA i).posSemidef_sortedDiagonal)
    (fun i => (hB i).posSemidef_sortedDiagonal)
  refine ⟨fun k hk => ?_, ?_⟩
  · -- Weak majorization: bound `topSum` via `M`'s own rank-`k` spectral truncation projector.
    have hQproj : IsStarProjection (hM.isHermitian.topProjector k) :=
      hM.isHermitian.isStarProjection_topProjector k
    have hQrank : (hM.isHermitian.topProjector k).rank = k :=
      hM.isHermitian.rank_topProjector k hk
    have hQtrace : (hM.isHermitian.topProjector k * ∑ i, A i ⊗ₖ B i).trace
        = ((Majorization.topSum hM.isHermitian.eigenvalues₀ k : ℝ) : 𝕜) :=
      hM.isHermitian.trace_mul_topProjector_self k
    have hbound := trace_mul_le_topSum_sortedDiagonal hA hB hQproj k hQrank
    rw [hQtrace] at hbound
    exact_mod_cast hbound
  · -- Equal totals: both sides' eigenvalues sum to `Tr[M] = Tr[M']`.
    have hAitrace : ∀ i, (A i).trace = (hA i).sortedDiagonal.trace := fun i => by
      simp only [Matrix.PosSemidef.sortedDiagonal, Matrix.trace_diagonal]
      exact (hA i).isHermitian.trace_eq_sum_eigenvalues
    have hBitrace : ∀ i, (B i).trace = (hB i).sortedDiagonal.trace := fun i => by
      simp only [Matrix.PosSemidef.sortedDiagonal, Matrix.trace_diagonal]
      exact (hB i).isHermitian.trace_eq_sum_eigenvalues
    have hMtrace : (∑ i, A i ⊗ₖ B i).trace
        = (∑ i, (hA i).sortedDiagonal ⊗ₖ (hB i).sortedDiagonal).trace := by
      rw [Matrix.trace_sum, Matrix.trace_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.trace_kronecker, Matrix.trace_kronecker, hAitrace i, hBitrace i]
    have hcast : (∑ j, (hM.isHermitian.eigenvalues₀ j : 𝕜))
        = (∑ j, (hM'.isHermitian.eigenvalues₀ j : 𝕜)) := by
      rw [hM.isHermitian.sum_eigenvalues₀_eq_trace, hM'.isHermitian.sum_eigenvalues₀_eq_trace]
      exact hMtrace
    exact_mod_cast hcast
