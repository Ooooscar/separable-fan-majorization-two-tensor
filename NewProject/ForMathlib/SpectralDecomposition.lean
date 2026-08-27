import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Star.UnitaryStarAlgAut
import Mathlib.Algebra.Star.StarProjection
import NewProject.ForMathlib.Majorization
import NewProject.ForMathlib.Projector
import NewProject.ForMathlib.EigenvalueMonotonicity

/-!
# Spectral decomposition as a sum of rank-one projectors

Mathlib's `Matrix.IsHermitian.spectral_theorem` expresses a Hermitian matrix `A` as a unitary
conjugation `A = U · diagonal α · U*` of a diagonal matrix of eigenvalues, rather than as the more
familiar "outer product" sum `A = ∑ₖ αₖ (uₖ uₖ*)`. Mathlib does not state the latter form
anywhere (checked `Mathlib.Analysis.Matrix.Spectrum`, `Mathlib.Analysis.Matrix.PosDef`,
`Mathlib.Analysis.Matrix.HermitianFunctionalCalculus` — every use of `spectral_theorem` rewrites
with it and then works with `conjStarAlgAut`/`diagonal` directly), so we derive it here.

We write `uₖ uₖ* = Matrix.vecMulVec uₖ (star uₖ)`, the rank-one matrix `(i,j) ↦ uₖ i * star (uₖ
j)` (already used in `PosSemidef.lean`/`BilinearPositivity.lean` via
`Matrix.posSemidef_vecMulVec_self_star`).

Note on non-uniqueness: when `A` has repeated eigenvalues, the orthonormal eigenbasis is not
unique, so the individual `uₖ` are not canonical. This does not affect the theorems below: they
hold for *whichever* orthonormal eigenbasis is used, and Mathlib's `eigenvectorBasis` simply fixes
one particular (noncomputable, unspecified) choice. What *is* basis-independent is each
eigenspace's orthogonal projector, i.e. the sum of `uₖ uₖ*` over all `k` sharing one eigenvalue —
consistent with the sum decomposition below being provably true regardless of which eigenbasis is
picked.

## The Abel-summation trick

`sum_eigenvalue₀_diff_smul_sum_vecMulVec` below is the telescoping identity
`A = ∑ⱼ (λⱼ(A) - λⱼ₊₁(A)) • P_[j]` used in the overlap-bound proof (`OverlapBound.lean`), with
`P_[j] := ∑_{k ≤ j} (uₖ uₖ*)` written out inline as `∑ k ∈ Finset.Iic j, ...` — no separate
definition for `P_[j]` is needed, it is just notation from the paper, exactly as with `α`/`β`/`μ`
elsewhere in this project.

The proof turns on `Fin.sum_Iic_eq_sum_range_succ`, a purely index-bookkeeping bridging lemma
(matching `Fin (Fintype.card n)`/`Finset.Iic`, the paper's natural language, against
`ℕ`/`Finset.range`, the language `Finset.sum_range_by_parts` speaks) — nothing eigenvalue-specific
about it. The strategy, in order:

1. **Extend to `ℕ`.** `eigenvalues₀ : Fin d → ℝ` and the sorted rank-one term `k ↦ uₖ uₖ*` (with
   `d := Fintype.card n`) only make sense for indices `< d`. Define `f : ℕ → 𝕜`, `g : ℕ → Matrix n
   n 𝕜` by `dite (· < d)` (returning `0` outside `[0, d)`), so that for `k : Fin d`, `f k.val =
   (eigenvalues₀ k : 𝕜)` and `g k.val = uₖ uₖ*` (lemmas `hf`, `hg`) — and so that "beyond the top
   eigenvalue" is literally `f d = 0` (`hf_d`), which is exactly the paper's `α_{d+1} := 0`
   convention. The target's `if h : j+1 < d then ... else 0` boundary-truncated eigenvalue is then
   just `f (j.val + 1)` uniformly, whether or not `j.val + 1 < d` (`hβ`) — this is what lets a
   single, boundary-case-free formula in `f` stand in for the paper's two-case definition.
2. **Move to `range`-sums.** Using step 1's agreement, `Fin.sum_univ_eq_sum_range` turns
   `sum_eigenvalue₀_smul_vecMulVec` and `sum_eigenvalue₀_vecMulVec_eq_one` into `A = ∑ i ∈ range d,
   f i • g i` (`step1`) and `1 = ∑ i ∈ range d, g i` (`step2`) — genuine equalities in `f`/`g`'s own
   native language, ready for `Finset.sum_range_by_parts`.
3. **Bridge `range`-prefixes and `Finset.Iic`.** `Fin.sum_Iic_eq_sum_range_succ` converts the
   *target*'s `∑ k ∈ Finset.Iic j, uₖ uₖ*` into the matching `range`-prefix sum `∑ i ∈ range (j.val
   + 1), g i` (`step3`).
4. **Apply `Finset.sum_range_by_parts f g d`** (`Mathlib.Algebra.BigOperators.Module`) to `step1`'s
   sum. Its boundary term `f (d-1) • (∑ i ∈ range d, g i)` collapses to `f (d-1) • 1` via `step2`;
   after splitting `range d` back into `range (d-1) ∪ {d-1}` (`Finset.sum_range_succ`) and using
   `f d = 0` to kill the extra piece this introduces, the two boundary contributions cancel exactly
   (a `-x + x`, closed by `abel` after negating one sum via `Finset.sum_neg_distrib`), leaving the
   telescoping identity `∑ i ∈ range d, (f i - f (i+1)) • (∑ i' ∈ range (i+1), g i') = A` (`key`).
   The `d = 0` case (`n` empty) is handled separately: then `Matrix n n 𝕜` is a subsingleton, so
   `A = 0` follows from `isEmptyElim`.
5. **Convert back.** `Fin.sum_univ_eq_sum_range` turns `key` into a `Fin d`-indexed sum, and
   `step3` (from step 3) rewrites each `∑ i' ∈ range (j.val+1), g i'` back into `∑ k ∈ Finset.Iic j,
   uₖ uₖ*`, landing on the target statement.
-/

open Unitary

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- **Spectral decomposition**, outer-product form: a Hermitian matrix is the sum, over its
(some choice of orthonormal) eigenbasis, of `eigenvalue • (eigenvector eigenvector*)`. Indexed by
`n` (the matrix's own index type) via `hA.eigenvalues`/`hA.eigenvectorBasis`; see
`sum_eigenvalue₀_smul_vecMulVec` for the version indexed by `Fin (Fintype.card n)` with
eigenvalues sorted in decreasing order. -/
theorem Matrix.IsHermitian.sum_eigenvalue_smul_vecMulVec {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A = ∑ k, (hA.eigenvalues k : 𝕜) •
      Matrix.vecMulVec (hA.eigenvectorBasis k) (star (hA.eigenvectorBasis k)) := by
  ext i j
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
  conv_lhs => rw [hA.spectral_theorem, conjStarAlgAut_apply]
  simp [Matrix.mul_apply, Matrix.diagonal_apply, Matrix.star_apply, eigenvectorUnitary_apply,
    mul_comm, mul_left_comm, mul_assoc]

/-- **Spectral decomposition**, outer-product form, indexed by `Fin (Fintype.card n)` with
eigenvalues sorted in decreasing order (`eigenvalues₀`). This is the form needed for the
spectral-truncation/Abel-summation trick (see the roadmap above). -/
theorem Matrix.IsHermitian.sum_eigenvalue₀_smul_vecMulVec {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A = ∑ k : Fin (Fintype.card n), (hA.eigenvalues₀ k : 𝕜) •
      Matrix.vecMulVec (hA.sortedEigenvectorBasis k) (star (hA.sortedEigenvectorBasis k)) := by
  calc A = ∑ i, (hA.eigenvalues i : 𝕜) •
        Matrix.vecMulVec (hA.eigenvectorBasis i) (star (hA.eigenvectorBasis i)) :=
      hA.sum_eigenvalue_smul_vecMulVec
    _ = ∑ k : Fin (Fintype.card n), (hA.eigenvalues₀ k : 𝕜) •
        Matrix.vecMulVec (hA.sortedEigenvectorBasis k) (star (hA.sortedEigenvectorBasis k)) := by
      rw [← Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _))
        (fun i => (hA.eigenvalues i : 𝕜) •
          Matrix.vecMulVec (hA.eigenvectorBasis i) (star (hA.eigenvectorBasis i)))]
      simp [Matrix.IsHermitian.eigenvalues, Matrix.IsHermitian.sortedEigenvectorBasis]

/-- **Resolution of identity**: a full orthonormal eigenbasis' rank-one projectors sum to the
identity. Needed for the boundary term in the Abel-summation trick
(`sum_eigenvalue₀_diff_smul_sum_vecMulVec`): follows the same proof pattern as
`sum_eigenvalue_smul_vecMulVec`, using that `hA.eigenvectorUnitary` is unitary
(`Unitary.mul_star_self`) instead of `hA.spectral_theorem`. -/
theorem Matrix.IsHermitian.sum_vecMulVec_eq_one {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (1 : Matrix n n 𝕜) =
      ∑ k, Matrix.vecMulVec (hA.eigenvectorBasis k) (star (hA.eigenvectorBasis k)) := by
  rw [← Unitary.coe_mul_star_self hA.eigenvectorUnitary]
  ext i j
  simp only [Matrix.sum_apply, Matrix.vecMulVec_apply]
  simp [Matrix.mul_apply, Matrix.star_apply, eigenvectorUnitary_apply]

/-- **Resolution of identity**, indexed by `Fin (Fintype.card n)` with the same sorted-eigenvector
reindexing as `sum_eigenvalue₀_smul_vecMulVec`. This is the form that plugs directly into the
boundary term of `Finset.sum_range_by_parts` with no further reindexing, unlike
`sum_vecMulVec_eq_one`. -/
theorem Matrix.IsHermitian.sum_eigenvalue₀_vecMulVec_eq_one {A : Matrix n n 𝕜}
    (hA : A.IsHermitian) :
    (1 : Matrix n n 𝕜) = ∑ k : Fin (Fintype.card n),
      Matrix.vecMulVec (hA.sortedEigenvectorBasis k) (star (hA.sortedEigenvectorBasis k)) :=
  hA.sum_vecMulVec_eq_one.trans
    (Equiv.sum_comp (Fintype.equivOfCardEq (Fintype.card_fin _))
      (fun i => Matrix.vecMulVec (hA.eigenvectorBasis i) (star (hA.eigenvectorBasis i)))).symm

/-- **Bridging lemma** between `Finset.range`-prefix sums (the language of
`Finset.sum_range_by_parts`) and `Finset.Iic`-sums over a `Fin d` (the language of the
spectral-truncation projector `P_[j] = ∑ k ∈ Finset.Iic j, uₖ uₖ*`). Purely a fact about `Finset`
and `Fin`, with nothing eigenvalue-specific about it: if `g : ℕ → M` agrees with `G : Fin d → M`
on `{0, ..., d-1}`, then a `range`-prefix sum of `g` up to (and including) `k.val` equals the
`Finset.Iic`-sum of `G` up to `k`. -/
theorem Fin.sum_Iic_eq_sum_range_succ {M : Type*} [AddCommMonoid M] {d : ℕ} (G : Fin d → M)
    (g : ℕ → M) (hg : ∀ i (h : i < d), g i = G ⟨i, h⟩) (k : Fin d) :
    ∑ j ∈ Finset.Iic k, G j = ∑ i ∈ Finset.range (k.val + 1), g i := by
  rw [Nat.range_succ_eq_Iic, ← Fin.map_valEmbedding_Iic, Finset.sum_map]
  exact Finset.sum_congr rfl fun j _ => (hg j.val j.isLt).symm

/-- **The Abel-summation trick**: a Hermitian matrix, written via its *sorted* (decreasing)
eigenvalues `λ := hA.eigenvalues₀` and eigenvectors `u`, decomposes as
`A = ∑ⱼ (λⱼ - λⱼ₊₁) • (∑_{k ≤ j} uₖ uₖ*)`, with the convention `λ_{d} := 0` for `d := Fintype.card
n` (so the top term, `j = d - 1`, contributes `λ_{d-1} • 1`). This is exactly the "well-known
trick" `A = ∑ⱼ (αⱼ - αⱼ₊₁) P_[j]` from the overlap-bound proof, with `P_[j]` written out inline as
`∑ k ∈ Finset.Iic j, uₖ uₖ*` rather than introduced as a separate definition. See the roadmap
above for the proof strategy. -/
theorem Matrix.IsHermitian.sum_eigenvalue₀_diff_smul_sum_vecMulVec
    {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    A = ∑ j : Fin (Fintype.card n),
        ((hA.eigenvalues₀ j : 𝕜) -
            (if h : (j : ℕ) + 1 < Fintype.card n then (hA.eigenvalues₀ ⟨(j : ℕ) + 1, h⟩ : 𝕜)
              else 0)) •
          ∑ k ∈ Finset.Iic j,
            Matrix.vecMulVec (hA.sortedEigenvectorBasis k)
              (star (hA.sortedEigenvectorBasis k)) := by
  set d := Fintype.card n with hd_def
  set e := Fintype.equivOfCardEq (Fintype.card_fin d)
  set G : Fin d → Matrix n n 𝕜 :=
    fun k => Matrix.vecMulVec (hA.eigenvectorBasis (e k)) (star (hA.eigenvectorBasis (e k)))
    with hG_def
  set f : ℕ → 𝕜 := fun i => if h : i < d then (hA.eigenvalues₀ ⟨i, h⟩ : 𝕜) else 0 with hf_def
  set g : ℕ → Matrix n n 𝕜 := fun i => if h : i < d then G ⟨i, h⟩ else 0 with hg_def
  have hf : ∀ k : Fin d, f (k : ℕ) = (hA.eigenvalues₀ k : 𝕜) := fun k => by
    simp [hf_def, k.isLt]
  have hg : ∀ k : Fin d, g (k : ℕ) = G k := fun k => by
    simp [hg_def, k.isLt]
  have hf_d : f d = 0 := by simp [hf_def]
  have hβ : ∀ j : Fin d,
      (if h : (j : ℕ) + 1 < d then (hA.eigenvalues₀ ⟨(j : ℕ) + 1, h⟩ : 𝕜) else 0)
        = f ((j : ℕ) + 1) := fun j => by
    simp [hf_def]
  -- Step 1: `A` as a `range`-indexed sum of `f i • g i`.
  have step1 : A = ∑ i ∈ Finset.range d, f i • g i := by
    rw [hA.sum_eigenvalue₀_smul_vecMulVec, ← Fin.sum_univ_eq_sum_range (fun i => f i • g i) d]
    exact Finset.sum_congr rfl fun k _ => by rw [hf k, hg k]; rfl
  -- Step 2: resolution of identity as a `range`-indexed sum.
  have step2 : (1 : Matrix n n 𝕜) = ∑ i ∈ Finset.range d, g i := by
    rw [hA.sum_eigenvalue₀_vecMulVec_eq_one, ← Fin.sum_univ_eq_sum_range g d]
    exact Finset.sum_congr rfl fun k _ => (hg k).symm
  -- Step 3: match `Finset.Iic`-sums to `range`-prefix sums.
  have step3 : ∀ j : Fin d, ∑ k ∈ Finset.Iic j, G k = ∑ i ∈ Finset.range ((j : ℕ) + 1), g i :=
    fun j => Fin.sum_Iic_eq_sum_range_succ G g (fun i h => by simp [hg_def, h]) j
  -- Now assemble via `Finset.sum_range_by_parts`, matching the two sides of the telescoping sum.
  have key : ∑ i ∈ Finset.range d, (f i - f (i + 1)) • ∑ i' ∈ Finset.range (i + 1), g i' = A := by
    rcases Nat.eq_zero_or_pos d with hd0 | hd0
    · haveI : IsEmpty n := Fintype.card_eq_zero_iff.mp (hd_def.symm.trans hd0)
      simp only [hd0, Finset.range_zero, Finset.sum_empty]
      ext i j
      exact isEmptyElim i
    · have hby := Finset.sum_range_by_parts f g d
      rw [← step1, ← step2] at hby
      have hd_eq : d = (d - 1) + 1 := (Nat.succ_pred_eq_of_pos hd0).symm
      rw [hd_eq, Finset.sum_range_succ, ← hd_eq, hf_d, sub_zero, ← step2, hby]
      have hZ : ∑ i ∈ Finset.range (d - 1), (f (i + 1) - f i) • ∑ i' ∈ Finset.range (i + 1), g i'
          = -∑ i ∈ Finset.range (d - 1), (f i - f (i + 1)) • ∑ i' ∈ Finset.range (i + 1), g i' := by
        rw [← Finset.sum_neg_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← neg_smul]
        congr 1
        ring
      rw [hZ]
      abel
  calc A = ∑ j : Fin d,
        (f (j : ℕ) - f ((j : ℕ) + 1)) • ∑ i' ∈ Finset.range ((j : ℕ) + 1), g i' := by
        rw [← key, Fin.sum_univ_eq_sum_range
          (fun i => (f i - f (i + 1)) • ∑ i' ∈ Finset.range (i + 1), g i') d]
    _ = ∑ j : Fin d, ((hA.eigenvalues₀ j : 𝕜) -
          (if h : (j : ℕ) + 1 < d then (hA.eigenvalues₀ ⟨(j : ℕ) + 1, h⟩ : 𝕜) else 0)) •
            ∑ k ∈ Finset.Iic j, G k :=
        Finset.sum_congr rfl fun j _ => by rw [hf j, hβ j, step3 j]

/-! ## The rank-`k` spectral truncation projector

`P_[j] := ∑_{k ≤ j} uₖuₖ*` (`OverlapBound.lean`'s `isStarProjection_sum_Iic_vecMulVec`/
`rank_sum_Iic_vecMulVec`) is only indexed by `j : Fin (Fintype.card n)`, i.e. only gives ranks
`j.val + 1 ∈ {1, …, Fintype.card n}`. `topProjector` below is the same construction generalized to
an arbitrary rank `k : ℕ` (including `k = 0`, the zero projector), which is what's needed to state
the Ky Fan equality `Tr[(topProjector k) * A] = topSum (eigenvalues₀) k` used by
`majorized_sum_kronecker_sortedDiagonal` (`SumKroneckerMajorization.lean`).

The two facts below about the summand `uₗuₗ*` — mutual orthogonality/idempotency
(`sortedRankOneProjector_mul`) and unit trace (`trace_sortedRankOneProjector`) — are each the one
piece of real content needed by *both* `isStarProjection_topProjector`/`rank_topProjector` here
*and* `OverlapBound.lean`'s `isStarProjection_sum_Iic_vecMulVec`/`rank_sum_Iic_vecMulVec` (`P_[j]`
being the same summand over a different index set), so they are named and proved once here rather
than re-derived at each of the four call sites. -/

/-- The rank-one summand of `topProjector`/`P_[j]`: the projector `uₗuₗ*` onto `A`'s `l`-th sorted
eigenvector. Naming this makes `sortedRankOneProjector_mul`/`trace_sortedRankOneProjector` below
directly reusable, instead of each consuming proof re-deriving them against an ad-hoc local `set`.
-/
noncomputable def Matrix.IsHermitian.sortedRankOneProjector {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (l : Fin (Fintype.card n)) : Matrix n n 𝕜 :=
  Matrix.vecMulVec (hA.sortedEigenvectorBasis l) (star (hA.sortedEigenvectorBasis l))

/-- The sorted rank-one projectors are mutually orthogonal idempotents:
`(uₖuₖ*)(uₗuₗ*) = δₖₗ (uₖuₖ*)`. From orthonormality of `hA.eigenvectorBasis`
(`orthonormal_iff_ite`) via `Matrix.vecMulVec_mul_vecMulVec`. -/
theorem Matrix.IsHermitian.sortedRankOneProjector_mul {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k l : Fin (Fintype.card n)) :
    hA.sortedRankOneProjector k * hA.sortedRankOneProjector l =
      if k = l then hA.sortedRankOneProjector k else 0 := by
  simp only [Matrix.IsHermitian.sortedRankOneProjector]
  rw [Matrix.vecMulVec_mul_vecMulVec]
  have hdp : star ⇑(hA.sortedEigenvectorBasis k) ⬝ᵥ ⇑(hA.sortedEigenvectorBasis l)
      = if k = l then (1 : 𝕜) else 0 := by
    rw [dotProduct_comm, ← EuclideanSpace.inner_eq_star_dotProduct]
    exact orthonormal_iff_ite.mp
      (hA.eigenvectorBasis.orthonormal.comp (Fintype.equivOfCardEq (Fintype.card_fin _))
        (Fintype.equivOfCardEq (Fintype.card_fin _)).injective) k l
  rw [hdp]
  by_cases h : k = l <;> simp [h]

/-- Each sorted rank-one projector has trace `1`: `Tr[uₗuₗ*] = ⟪uₗ,uₗ⟫ = ‖uₗ‖² = 1`, by
orthonormality of `hA.eigenvectorBasis`. -/
theorem Matrix.IsHermitian.trace_sortedRankOneProjector {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (l : Fin (Fintype.card n)) : (hA.sortedRankOneProjector l).trace = (1 : 𝕜) := by
  simp only [Matrix.IsHermitian.sortedRankOneProjector, Matrix.IsHermitian.sortedEigenvectorBasis]
  rw [Matrix.trace_vecMulVec, ← EuclideanSpace.inner_eq_star_dotProduct,
    inner_self_eq_norm_sq_to_K, hA.eigenvectorBasis.orthonormal.1]
  simp

/-- The rank-`k` spectral truncation projector of a Hermitian `A`: the sum of the rank-one
projectors onto `A`'s `k` top (sorted-eigenvalue) eigenvectors. Generalizes `P_[j]`
(`OverlapBound.lean`'s `isStarProjection_sum_Iic_vecMulVec`) from `j.val + 1` to an arbitrary
`k : ℕ`. -/
noncomputable def Matrix.IsHermitian.topProjector {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : ℕ) : Matrix n n 𝕜 :=
  ∑ l ∈ Finset.univ.filter (fun l : Fin (Fintype.card n) => (l : ℕ) < k),
    hA.sortedRankOneProjector l

/-- `hA.topProjector k` is a projector: idempotency follows by distributing the product over the
double sum (`Finset.sum_mul_sum`) and collapsing each inner sum to its `l = k` term via
`sortedRankOneProjector_mul`; self-adjointness is immediate since each `uₗuₗ*` is Hermitian
(`Matrix.conjTranspose_vecMulVec`). Generalizes
`Matrix.IsHermitian.isStarProjection_sum_Iic_vecMulVec` (`OverlapBound.lean`, the `k = j.val + 1`
case) to an arbitrary rank `k`, including `k = 0` (the zero projector). -/
theorem Matrix.IsHermitian.isStarProjection_topProjector {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : ℕ) : IsStarProjection (hA.topProjector k) := by
  unfold Matrix.IsHermitian.topProjector
  set S := Finset.univ.filter (fun l : Fin (Fintype.card n) => (l : ℕ) < k)
  have hidem : (∑ l ∈ S, hA.sortedRankOneProjector l) * (∑ l ∈ S, hA.sortedRankOneProjector l)
      = ∑ l ∈ S, hA.sortedRankOneProjector l := by
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun l hl => ?_
    rw [Finset.sum_congr rfl fun l2 _ => hA.sortedRankOneProjector_mul l l2]
    simp [hl]
  have hselfadj : star (∑ l ∈ S, hA.sortedRankOneProjector l) = ∑ l ∈ S, hA.sortedRankOneProjector l
      := by
    rw [star_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    simp only [Matrix.IsHermitian.sortedRankOneProjector]
    rw [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_vecMulVec, star_star]
  exact ⟨hidem, hselfadj⟩

/-- `hA.topProjector k` has rank exactly `k` (for `k ≤ Fintype.card n`): its trace is exactly the
number of terms, `k` (`trace_sortedRankOneProjector`), and the trace of a projector equals its rank
(`IsStarProjection.trace_eq_rank`, `Projector.lean`). Generalizes
`Matrix.IsHermitian.rank_sum_Iic_vecMulVec` (`OverlapBound.lean`) to an arbitrary rank `k`. -/
theorem Matrix.IsHermitian.rank_topProjector {A : Matrix n n 𝕜} (hA : A.IsHermitian) (k : ℕ)
    (hk : k ≤ Fintype.card n) : (hA.topProjector k).rank = k := by
  -- The filter set indexing `topProjector k` has exactly `k` elements, since `k ≤ Fintype.card n`.
  have hcard : (Finset.univ.filter (fun l : Fin (Fintype.card n) => (l : ℕ) < k)).card = k := by
    rw [Fin.card_filter_val_lt, min_eq_right hk]
  have htrace : (hA.topProjector k).trace = (k : 𝕜) := by
    unfold Matrix.IsHermitian.topProjector
    rw [Matrix.trace_sum, Finset.sum_congr rfl fun l _ => hA.trace_sortedRankOneProjector l,
      Finset.sum_const, hcard, nsmul_eq_mul, mul_one]
  -- Combine with `htrace` and cancel the (injective, char-zero) `ℕ → 𝕜` cast.
  have heq : ((hA.topProjector k).rank : 𝕜) = (k : 𝕜) := by
    rw [← (hA.isStarProjection_topProjector k).trace_eq_rank]
    exact htrace
  exact_mod_cast heq

/-- The "self" Ky Fan equality: pairing `A` with its own rank-`k` spectral truncation projector
recovers the sum of its `k` largest eigenvalues. Expand both `hA.topProjector k` and `A` in the
same eigenbasis (`sum_eigenvalue₀_smul_vecMulVec`) — the cross terms collapse via
`sortedRankOneProjector_mul`/`trace_sortedRankOneProjector`, and since `eigenvalues₀` is antitone,
the resulting prefix sum literally is `topSum`. Needed (applied to `A := ∑ᵢ A⁽ⁱ⁾⊗B⁽ⁱ⁾`) for the
weak-majorization half of `majorized_sum_kronecker_sortedDiagonal`
(`SumKroneckerMajorization.lean`). -/
theorem Matrix.IsHermitian.trace_mul_topProjector_self {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (k : ℕ) :
    (hA.topProjector k * A).trace = ((Majorization.topSum hA.eigenvalues₀ k : ℝ) : 𝕜) := by
  classical
  set P := hA.sortedRankOneProjector with hP_def
  -- Expand `A` in the same eigenbasis used by `topProjector k`.
  have hAdecomp : A = ∑ l : Fin (Fintype.card n), (hA.eigenvalues₀ l : 𝕜) • P l :=
    hA.sum_eigenvalue₀_smul_vecMulVec
  have htopProjector_eq :
      hA.topProjector k = ∑ l ∈ Finset.univ.filter (fun l : Fin (Fintype.card n) => (l : ℕ) < k),
        P l := rfl
  have hPmul : ∀ l l' : Fin (Fintype.card n), P l * P l' = if l = l' then P l else 0 := fun l l' =>
    hA.sortedRankOneProjector_mul l l'
  have hPtrace : ∀ l : Fin (Fintype.card n), (P l).trace = (1 : 𝕜) := fun l =>
    hA.trace_sortedRankOneProjector l
  -- Trace of the product, expanded termwise via linearity and `hPmul`.
  have hstep : (hA.topProjector k * A).trace
      = ∑ l ∈ Finset.univ.filter (fun l : Fin (Fintype.card n) => (l : ℕ) < k),
          ∑ l' : Fin (Fintype.card n), (hA.eigenvalues₀ l' : 𝕜) * (P l * P l').trace := by
    -- `congrArg`, not `rw`, to substitute `A`: `rw [hAdecomp]` would try to abstract the bare
    -- term `A`, which also appears (as an implicit argument) inside `hA`-dependent subterms like
    -- `hA.eigenvalues₀`, producing an ill-typed motive.
    have hprodA : hA.topProjector k * A
        = hA.topProjector k * ∑ l' : Fin (Fintype.card n), (hA.eigenvalues₀ l' : 𝕜) • P l' :=
      congrArg (fun M => hA.topProjector k * M) hAdecomp
    rw [hprodA, htopProjector_eq, Finset.sum_mul, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun l' _ => ?_
    rw [mul_smul_comm, Matrix.trace_smul, smul_eq_mul]
  rw [hstep]
  -- Cross terms collapse via `hPmul`/`hPtrace`, leaving just the diagonal `eigenvalues₀ l`.
  have hcollapse : ∀ l ∈ Finset.univ.filter (fun l : Fin (Fintype.card n) => (l : ℕ) < k),
      ∑ l' : Fin (Fintype.card n), (hA.eigenvalues₀ l' : 𝕜) * (P l * P l').trace
        = (hA.eigenvalues₀ l : 𝕜) := by
    intro l _
    have hswap : ∀ l' : Fin (Fintype.card n),
        (hA.eigenvalues₀ l' : 𝕜) * (P l * P l').trace
          = if l = l' then (hA.eigenvalues₀ l : 𝕜) else 0 := by
      intro l'
      rw [hPmul l l']
      by_cases h : l = l'
      · simp [h, hPtrace]
      · simp [h]
    rw [Finset.sum_congr rfl fun l' _ => hswap l']
    simp
  rw [Finset.sum_congr rfl hcollapse]
  -- Since `eigenvalues₀` is already sorted decreasing, its `topSum` is just the prefix sum.
  have htopSum_eq : Majorization.topSum hA.eigenvalues₀ k
      = ∑ l ∈ Finset.univ.filter (fun l : Fin (Fintype.card n) => (l : ℕ) < k),
          hA.eigenvalues₀ l := by
    unfold Majorization.topSum
    rw [Majorization.decreasingSort_of_antitone hA.eigenvalues₀_antitone]
  rw [htopSum_eq, RCLike.ofReal_sum]

/-- The full sum of a Hermitian matrix's (sorted) eigenvalues is its trace — the `eigenvalues₀`
counterpart of Mathlib's `Matrix.IsHermitian.trace_eq_sum_eigenvalues` (which sums the
matrix-indexed `.eigenvalues` instead). Reindexes along `Fintype.equivOfCardEq (Fintype.card_fin
_) : Fin (Fintype.card n) ≃ n`, the same equiv `.eigenvalues` is defined through. Needed for the
"equal totals" half of `majorized_sum_kronecker_sortedDiagonal` (`SumKroneckerMajorization.lean`).
-/
theorem Matrix.IsHermitian.sum_eigenvalues₀_eq_trace {A : Matrix n n 𝕜} (hA : A.IsHermitian) :
    (∑ j, (hA.eigenvalues₀ j : 𝕜)) = A.trace := by
  rw [hA.trace_eq_sum_eigenvalues]
  exact Fintype.sum_equiv (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card n)))
    (fun j => (hA.eigenvalues₀ j : 𝕜)) (fun i => (hA.eigenvalues i : 𝕜))
    (fun j => by simp [Matrix.IsHermitian.eigenvalues])
