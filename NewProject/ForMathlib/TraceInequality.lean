import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.Analysis.Convex.Birkhoff
import Mathlib.LinearAlgebra.Matrix.Permutation
import Mathlib.Algebra.Order.Rearrangement
import NewProject.ForMathlib.SpectralDecomposition

/-!
# Von Neumann's trace inequality

For Hermitian matrices `A, B` on the same space, `Tr[AB] ≤ ∑ᵢ λᵢ(A) λᵢ(B)`, where `λ(A)` and
`λ(B)` are the eigenvalues of `A` and `B` sorted in decreasing order
(`Matrix.IsHermitian.eigenvalues₀`).

This does not currently appear to be in Mathlib: there is no "von Neumann"/`KyFan`-named trace
lemma, and the `Matrix.IsHermitian.eigenvalues₀`/`singularValues` APIs are not yet connected to
any trace bound.

## Roadmap

The classical proof (e.g. Bhatia, *Matrix Analysis*, Ch. IX) turns out to be the most approachable
one given the current Mathlib landscape, because both of its non-trivial ingredients — **Birkhoff's
theorem** (`Mathlib.Analysis.Convex.Birkhoff`) and the **rearrangement inequality**
(`Mathlib.Algebra.Order.Rearrangement`) — are already in the library, even though nothing connects
them to eigenvalues/traces yet.

Write `A`, `B` in outer-product spectral form, `A = ∑ᵢ αᵢ uᵢ uᵢᴴ`, `B = ∑ⱼ βⱼ vⱼ vⱼᴴ`
(`Matrix.IsHermitian.sum_eigenvalue₀_smul_vecMulVec`, `SpectralDecomposition.lean`), with
`α := eigenvalues₀ A`, `β := eigenvalues₀ B` both sorted decreasing and `uᵢ`, `vⱼ` the corresponding
sorted eigenvectors. Distributing the product and taking the trace termwise gives

`Tr[AB] = ∑ᵢⱼ αᵢ βⱼ |⟨uᵢ, vⱼ⟩|² = ∑ᵢⱼ αᵢ βⱼ |Wᵢⱼ|²`, where `W := Uₐᴴ U_b` is unitary
(`Uₐ := hA.eigenvectorUnitary`, `U_b := hB.eigenvectorUnitary`) — equivalently, this is what
cyclicity of the trace would give from the matrix form `Tr[AB] = Tr[Dα W Dβ Wᴴ]`, but the
outer-product route above is what's actually formalized below.

The matrix `S := (|Wᵢⱼ|²)` is *doubly stochastic* (its rows/columns are the squared moduli of the
rows/columns of a unitary matrix, hence sum to `1`). By **Birkhoff's theorem**
(`exists_eq_sum_perm_of_mem_doublyStochastic`), `S = ∑_σ w_σ • σ.permMatrix ℝ` is a convex
combination of permutation matrices (`w_σ ≥ 0`, `∑ w_σ = 1`), so

`Tr[AB] = ∑_σ w_σ (∑ᵢ αᵢ β(σ i))`.

Since `α` and `β` are both decreasing, they **monovary** (`Antitone.monovary`), so the
**rearrangement inequality** (`Monovary.sum_smul_comp_perm_le_sum_smul`) gives
`∑ᵢ αᵢ β(σ i) ≤ ∑ᵢ αᵢ βᵢ` for *every* permutation `σ`; averaging over the convex weights `w_σ`
(which sum to `1`) preserves the bound and yields `Tr[AB] ≤ ∑ᵢ αᵢ βᵢ`.

No Weyl monotonicity (`EigenvalueMonotonicity.lean`) or majorization (`Majorization.lean`) is
needed for this proof; those are used downstream in `OverlapBound.lean` instead.

### Helper lemma steps

1. `Matrix.mem_doublyStochastic_normSq_of_mem_unitaryGroup`: for *any* unitary `W`, the matrix of
   squared moduli of its entries is doubly stochastic. Purely a fact about unitary matrices, no
   eigenvalues involved; proved by reading off `W * Wᴴ = 1` / `Wᴴ * W = 1` entrywise on the
   diagonal (the same `Unitary.coe_mul_star_self`/`coe_star_mul_self` facts already used in
   `SpectralDecomposition.lean`).
2. `overlapMatrix`: the `Fin (Fintype.card n)`-indexed (i.e. `eigenvalues₀`-sorted) matrix
   `S k l := |Wₖₗ|²`, `W := Uₐᴴ U_b`, with the same `Fintype.equivOfCardEq`-reindexing already used
   throughout `SpectralDecomposition.lean` to go from the unsorted `n`-indexed
   `eigenvectorUnitary`/`eigenvalues` to the sorted `Fin (Fintype.card n)`-indexed `eigenvalues₀`.
3. `Matrix.IsHermitian.doublyStochastic_overlapMatrix`: `overlapMatrix hA hB` is doubly stochastic.
   Follows from step 1 applied to `W := star hA.eigenvectorUnitary * hB.eigenvectorUnitary`
   (a product of unitaries is unitary), transported along the reindexing via
   `reindex_mem_doublyStochastic`.
4. `Matrix.IsHermitian.trace_mul_eq_sum_eigenvalues₀_mul_overlapMatrix`: the trace identity
   `Tr[AB] = ∑ₖ ∑ₗ αₖ βₗ Sₖₗ`. The purely computational core: write `A`, `B` as sums of outer
   products via `Matrix.IsHermitian.sum_eigenvalue₀_smul_vecMulVec` (`SpectralDecomposition.lean`),
   distribute the product over both sums, and take the trace termwise using
   `Tr[(uₖ uₖᴴ)(vₗ vₗᴴ)] = |⟨uₖ, vₗ⟩|² = Sₖₗ` (via `vecMulVec_mul_vecMulVec`/`trace_vecMulVec`/
   `RCLike.mul_conj`).
5. `Matrix.IsHermitian.sum_eigenvalues₀_mul_comp_perm_le`: the rearrangement-inequality step,
   `∑ₖ αₖ β(σ k) ≤ ∑ₖ αₖ βₖ` for every permutation `σ` of `Fin (Fintype.card n)`. Follows directly
   from `(hA.eigenvalues₀_antitone.monovary hB.eigenvalues₀_antitone
   ).sum_smul_comp_perm_le_sum_smul`, since antitone functions on the same index type always
   monovary.

The main theorem then assembles 3–5: rewrite `Tr[AB]` via step 4, replace `overlapMatrix hA hB`
using Birkhoff's `exists_eq_sum_perm_of_mem_doublyStochastic` (fed by step 3), swap the `∑_σ`/`∑ₖₗ`
sums to turn `∑ₗ Sₖₗ βₗ` into `β(σ k)`, bound each permutation term by step 5, and average using
`∑_σ w_σ = 1`.
-/

open Matrix
open scoped ComplexOrder

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

/-- **Helper lemma 1**: for a unitary matrix `W`, the matrix of squared moduli of its entries is
doubly stochastic. A purely unitary-matrix fact, with no reference to eigenvalues. -/
theorem Matrix.mem_doublyStochastic_normSq_of_mem_unitaryGroup {m : Type*} [Fintype m]
    [DecidableEq m] (W : Matrix.unitaryGroup m 𝕜) :
    Matrix.of (fun i j => ‖(W : Matrix m m 𝕜) i j‖ ^ 2) ∈ doublyStochastic ℝ m := by
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun _ _ => sq_nonneg _, fun i => ?_, fun j => ?_⟩
  · have h : ∑ k, (W : Matrix m m 𝕜) i k * star ((W : Matrix m m 𝕜) i k) = 1 := by
      have := congrFun (congrFun (Unitary.coe_mul_star_self W) i) i
      simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] using this
    have h2 : ((∑ k, ‖(W : Matrix m m 𝕜) i k‖ ^ 2 : ℝ) : 𝕜) = 1 := by
      simpa [RCLike.star_def, RCLike.mul_conj] using h
    simpa [Matrix.of_apply] using (show ∑ k, ‖(W : Matrix m m 𝕜) i k‖ ^ 2 = (1 : ℝ) by
      exact_mod_cast h2)
  · have h : ∑ k, star ((W : Matrix m m 𝕜) k j) * (W : Matrix m m 𝕜) k j = 1 := by
      have := congrFun (congrFun (Unitary.coe_star_mul_self W) j) j
      simpa [Matrix.mul_apply, Matrix.star_apply, Matrix.one_apply_eq] using this
    have h2 : ((∑ k, ‖(W : Matrix m m 𝕜) k j‖ ^ 2 : ℝ) : 𝕜) = 1 := by
      simpa [RCLike.star_def, RCLike.conj_mul] using h
    simpa [Matrix.of_apply] using (show ∑ k, ‖(W : Matrix m m 𝕜) k j‖ ^ 2 = (1 : ℝ) by
      exact_mod_cast h2)

/-- **Helper lemma 2**: the `eigenvalues₀`-sorted "overlap matrix" between the eigenbases of `A`
and `B`, `Sₖₗ := |⟨(k-th sorted eigenvector of A), (l-th sorted eigenvector of B)⟩|²`, built as the
squared moduli of `W := Uₐᴴ U_b` (`Uₐ := hA.eigenvectorUnitary`, `U_b := hB.eigenvectorUnitary`),
reindexed from `n` to `Fin (Fintype.card n)` via the same `Fintype.equivOfCardEq` used throughout
`SpectralDecomposition.lean`. -/
noncomputable def overlapMatrix {A B : Matrix n n 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    Matrix (Fin (Fintype.card n)) (Fin (Fintype.card n)) ℝ :=
  fun k l =>
    let e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _)
    ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) * (hB.eigenvectorUnitary : Matrix n n 𝕜))
        (e k) (e l)‖ ^ 2

/-- **Helper lemma 3**: `overlapMatrix hA hB` is doubly stochastic. Follows from helper lemma 1
applied to the unitary `star hA.eigenvectorUnitary * hB.eigenvectorUnitary`, transported along the
`Fintype.equivOfCardEq` reindexing via `reindex_mem_doublyStochastic`. -/
theorem Matrix.IsHermitian.doublyStochastic_overlapMatrix {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    overlapMatrix hA hB ∈ doublyStochastic ℝ (Fin (Fintype.card n)) := by
  set e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _) with hedef
  have hWmem :
      star (hA.eigenvectorUnitary : Matrix n n 𝕜) * (hB.eigenvectorUnitary : Matrix n n 𝕜)
        ∈ Matrix.unitaryGroup n 𝕜 :=
    Submonoid.mul_mem _ (Unitary.star_mem hA.eigenvectorUnitary.2) hB.eigenvectorUnitary.2
  have hbase := Matrix.mem_doublyStochastic_normSq_of_mem_unitaryGroup
    (⟨_, hWmem⟩ : Matrix.unitaryGroup n 𝕜)
  have hreindex := reindex_mem_doublyStochastic (e₁ := e.symm) (e₂ := e.symm) hbase
  have hEq : overlapMatrix hA hB =
      (Matrix.of (fun i j : n =>
          ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) *
              (hB.eigenvectorUnitary : Matrix n n 𝕜)) i j‖ ^ 2) : Matrix n n ℝ).reindex
        e.symm e.symm := by
    ext k l
    simp [overlapMatrix, hedef]
  rw [hEq]
  exact hreindex

/-- **Helper lemma 4**: `Tr[AB] = ∑ₖ ∑ₗ αₖ βₗ Sₖₗ`, where `α := hA.eigenvalues₀`,
`β := hB.eigenvalues₀`, and `S := overlapMatrix hA hB`. The computational core of the proof: write
`A = ∑ₖ αₖ • uₖ uₖᴴ` and `B = ∑ₗ βₗ • vₗ vₗᴴ` via the outer-product spectral decomposition
(`Matrix.IsHermitian.sum_eigenvalue₀_smul_vecMulVec`, `SpectralDecomposition.lean`), distribute the
product over both sums, and take the trace termwise using
`Tr[(uₖ uₖᴴ)(vₗ vₗᴴ)] = ‖⟨uₖ, vₗ⟩‖² = Sₖₗ` (via `vecMulVec_mul_vecMulVec`/`trace_vecMulVec`/
`RCLike.mul_conj`). -/
theorem Matrix.IsHermitian.trace_mul_eq_sum_eigenvalues₀_mul_overlapMatrix {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * B).trace
      = (↑(∑ k : Fin (Fintype.card n), ∑ l : Fin (Fintype.card n),
          hA.eigenvalues₀ k * hB.eigenvalues₀ l * overlapMatrix hA hB k l) : 𝕜) := by
  set e : Fin (Fintype.card n) ≃ n := Fintype.equivOfCardEq (Fintype.card_fin _) with hedef
  set u : Fin (Fintype.card n) → n → 𝕜 := fun k => hA.eigenvectorBasis (e k) with hu_def
  set v : Fin (Fintype.card n) → n → 𝕜 := fun l => hB.eigenvectorBasis (e l) with hv_def
  have hA' : A = ∑ k, (hA.eigenvalues₀ k : 𝕜) • Matrix.vecMulVec (u k) (star (u k)) :=
    hA.sum_eigenvalue₀_smul_vecMulVec
  have hB' : B = ∑ l, (hB.eigenvalues₀ l : 𝕜) • Matrix.vecMulVec (v l) (star (v l)) :=
    hB.sum_eigenvalue₀_smul_vecMulVec
  -- `overlapMatrix hA hB k l` is the squared modulus of `⟨uₖ, vₗ⟩ = star (u k) ⬝ᵥ v l`.
  have hoverlap : ∀ k l, overlapMatrix hA hB k l = ‖star (u k) ⬝ᵥ v l‖ ^ 2 := by
    intro k l
    simp [overlapMatrix, hedef, hu_def, hv_def, Matrix.mul_apply, Matrix.star_apply,
      Matrix.IsHermitian.eigenvectorUnitary_apply, dotProduct, mul_comm]
  -- `⟨vₗ, uₖ⟩ = conj ⟨uₖ, vₗ⟩`, as expected of an inner product.
  have hconj : ∀ k l, u k ⬝ᵥ star (v l) = star (star (u k) ⬝ᵥ v l) := by
    intro k l
    simp only [dotProduct, star_sum, Pi.star_apply, star_mul', star_star]
  -- `Tr[(uₖ uₖ*)(vₗ vₗ*)] = ⟨uₖ, vₗ⟩ ⟨vₗ, uₖ⟩ = |⟨uₖ, vₗ⟩|² = Sₖₗ`.
  have htrace : ∀ k l,
      (Matrix.vecMulVec (u k) (star (u k)) * Matrix.vecMulVec (v l) (star (v l))).trace
        = (overlapMatrix hA hB k l : 𝕜) := by
    intro k l
    rw [Matrix.vecMulVec_mul_vecMulVec, Matrix.trace_vecMulVec, dotProduct_smul, smul_eq_mul,
      hconj k l, hoverlap k l]
    rw [RCLike.star_def, RCLike.mul_conj]
    norm_cast
  -- Assemble: expand `A`, `B` as sums, distribute the product, and take the trace termwise.
  have main : (A * B).trace
      = ∑ k, ∑ l,
          (hA.eigenvalues₀ k : 𝕜) * (hB.eigenvalues₀ l : 𝕜) * (overlapMatrix hA hB k l : 𝕜) := by
    conv_lhs => rw [hA', hB']
    rw [Fintype.sum_mul_sum, Matrix.trace_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Matrix.trace_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_mul_smul_comm, Matrix.trace_smul, smul_eq_mul, htrace k l]
  rw [main]
  push_cast
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  ring

/-- **Helper lemma 5**: the rearrangement-inequality step. `α := hA.eigenvalues₀` and
`β := hB.eigenvalues₀` are both (weakly) decreasing (`eigenvalues₀_antitone`), hence *monovary*
(`Antitone.monovary`), so the rearrangement inequality
(`Monovary.sum_smul_comp_perm_le_sum_smul`) bounds any permuted pairing of `α` against `β` by the
identically-ordered pairing. -/
theorem Matrix.IsHermitian.sum_eigenvalues₀_mul_comp_perm_le {A B : Matrix n n 𝕜}
    (hA : A.IsHermitian) (hB : B.IsHermitian) (σ : Equiv.Perm (Fin (Fintype.card n))) :
    ∑ k, hA.eigenvalues₀ k * hB.eigenvalues₀ (σ k)
      ≤ ∑ k, hA.eigenvalues₀ k * hB.eigenvalues₀ k := by
  have hmv : Monovary hA.eigenvalues₀ hB.eigenvalues₀ :=
    hA.eigenvalues₀_antitone.monovary hB.eigenvalues₀_antitone
  simpa using hmv.sum_smul_comp_perm_le_sum_smul (σ := σ)

/-- **Von Neumann's trace inequality**.

Proof strategy: rewrite `Tr[AB]` via `trace_mul_eq_sum_eigenvalues₀_mul_overlapMatrix`; apply
Birkhoff's theorem (`exists_eq_sum_perm_of_mem_doublyStochastic`, fed by
`doublyStochastic_overlapMatrix`) to write `overlapMatrix hA hB = ∑ σ, w σ • σ.permMatrix ℝ` as a
convex combination of permutation matrices; swap the resulting `∑ σ`/`∑ k, ∑ l` sums, collapsing
`∑ l, (σ.permMatrix ℝ) k l * hB.eigenvalues₀ l` to `hB.eigenvalues₀ (σ k)` by unfolding the
permutation matrix; bound each permutation's term via `sum_eigenvalues₀_mul_comp_perm_le`; average
using `∑ σ, w σ = 1`. -/
theorem Matrix.IsHermitian.trace_mul_le {A B : Matrix n n 𝕜} (hA : A.IsHermitian)
    (hB : B.IsHermitian) :
    (A * B).trace
      ≤ (↑(∑ i : Fin (Fintype.card n), hA.eigenvalues₀ i * hB.eigenvalues₀ i) : 𝕜) := by
  rw [hA.trace_mul_eq_sum_eigenvalues₀_mul_overlapMatrix hB]
  set S := overlapMatrix hA hB with hSdef
  set α := hA.eigenvalues₀
  set β := hB.eigenvalues₀
  obtain ⟨w, hw0, hw1, hw2⟩ :=
    exists_eq_sum_perm_of_mem_doublyStochastic (hA.doublyStochastic_overlapMatrix hB)
  -- The `k`-th row of `S = ∑ σ, w σ • σ.permMatrix ℝ`, dotted with `β`, is `∑ σ, w σ * β (σ k)`.
  have hSmulVec : ∀ k, ∑ l, S k l * β l = ∑ σ, w σ * β (σ k) := by
    intro k
    have hSk : ∀ l, S k l = ∑ σ, w σ * (σ.permMatrix ℝ) k l := by
      intro l
      rw [hSdef, ← hw2, Matrix.sum_apply]
      simp only [Matrix.smul_apply, smul_eq_mul]
    simp_rw [hSk, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun σ _ => ?_
    have e : ∑ l, (w σ * (σ.permMatrix ℝ) k l) * β l
        = w σ * ∑ l, (σ.permMatrix ℝ) k l * β l := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [e]
    congr 1
    simp
  -- Fold the double sum into `∑ σ, w σ * (∑ k, α k * β (σ k))`.
  have h1 : ∀ k, ∑ l, α k * β l * S k l = ∑ σ, w σ * (α k * β (σ k)) := by
    intro k
    have e1 : ∑ l, α k * β l * S k l = α k * ∑ l, S k l * β l := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by ring
    rw [e1, hSmulVec k, Finset.mul_sum]
    exact Finset.sum_congr rfl fun σ _ => by ring
  have heq : ∑ k, ∑ l, α k * β l * S k l = ∑ σ, w σ * ∑ k, α k * β (σ k) := by
    simp_rw [h1]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun σ _ => by rw [← Finset.mul_sum]
  -- Bound each permutation's contribution using the rearrangement inequality (helper lemma 5),
  -- then average against the convex weights `w σ` (which are nonnegative and sum to `1`).
  have key : ∑ k, ∑ l, α k * β l * S k l ≤ ∑ i, α i * β i := by
    rw [heq]
    calc ∑ σ, w σ * ∑ k, α k * β (σ k)
        ≤ ∑ σ, w σ * ∑ k, α k * β k := by
          refine Finset.sum_le_sum fun σ _ => ?_
          exact mul_le_mul_of_nonneg_left (hA.sum_eigenvalues₀_mul_comp_perm_le hB σ) (hw0 σ)
      _ = (∑ σ, w σ) * ∑ k, α k * β k := by rw [Finset.sum_mul]
      _ = ∑ k, α k * β k := by rw [hw1, one_mul]
  exact_mod_cast key
