import Mathlib.Analysis.Matrix.Spectrum

/-!
# Scaling a Hermitian matrix's eigenvalues

Scaling a Hermitian matrix by a nonnegative real scales its `eigenvalues₀` by the same constant.

## Main results

* `Matrix.IsHermitian.eigenvalues₀_smul`: `(c • A).eigenvalues₀ = c • A.eigenvalues₀` for a
  nonnegative real `c`.

## Proof roadmap

Mathlib has no `charpoly`-under-`smul` lemma to build this from directly (checked
`Mathlib.LinearAlgebra.Matrix.Charpoly.Basic/Coeff`, `Mathlib.LinearAlgebra.Charpoly.Basic`), so
`charpoly_smul` below rebuilds the fact by mimicking the proof of Mathlib's own
`Matrix.IsHermitian.charpoly_eq` (`Mathlib.Analysis.Matrix.Spectrum`): `A`'s own eigenbasis
diagonalizes `c • A` too (with each eigenvalue scaled by `c`), so re-diagonalizing along the same
unitary conjugation as `A`'s `spectral_theorem`, with the diagonal rescaled by `c` beforehand,
computes `(c • A).charpoly` directly. `eigenvalues₀_smul` then transports this from the
unsorted/`n`-indexed `charpoly_smul` to the sorted/`Fin (Fintype.card n)`-indexed `eigenvalues₀` by
showing that decreasingly-sorting a `c`-scaled list (`c ≥ 0`) is the same as `c`-scaling the already
decreasingly-sorted list (`Multiset.map_sort`), then matching this against `c • A`'s own canonical
sorted list via `List.ofFn_injective`.
-/

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

open Polynomial in
/-- `charpoly` counterpart of scaling by `c`, mirroring Mathlib's own
`Matrix.IsHermitian.charpoly_eq`. -/
theorem Matrix.IsHermitian.charpoly_smul {A : Matrix n n 𝕜} (hA : A.IsHermitian) (c : ℝ) :
    (c • A).charpoly = ∏ i, (X - C ((c * hA.eigenvalues i : ℝ) : 𝕜)) := by
  have hD : c • Matrix.diagonal (RCLike.ofReal (K := 𝕜) ∘ hA.eigenvalues) =
      Matrix.diagonal (RCLike.ofReal (K := 𝕜) ∘ fun i => c * hA.eigenvalues i) := by
    rw [← Matrix.diagonal_smul]
    congr 1
    funext i
    simp [RCLike.real_smul_eq_coe_smul (K := 𝕜)]
  have hcA : c • A = Unitary.conjStarAlgAut 𝕜 _ hA.eigenvectorUnitary
      (Matrix.diagonal (RCLike.ofReal ∘ fun i => c * hA.eigenvalues i)) := by
    conv_lhs => rw [hA.spectral_theorem]
    rw [Unitary.conjStarAlgAut_apply, Unitary.conjStarAlgAut_apply, ← hD, ← smul_mul_assoc,
      ← mul_smul_comm]
  rw [hcA, Unitary.conjStarAlgAut_apply, Matrix.charpoly_mul_comm, ← mul_assoc]
  simp [Matrix.charpoly_diagonal]

/-- `roots`-multiset counterpart of `charpoly_smul`, mirroring Mathlib's own
`Matrix.IsHermitian.roots_charpoly_eq_eigenvalues`. -/
theorem Matrix.IsHermitian.roots_charpoly_smul {A : Matrix n n 𝕜} (hA : A.IsHermitian) (c : ℝ) :
    (c • A).charpoly.roots =
      Multiset.map (RCLike.ofReal ∘ fun i => c * hA.eigenvalues i) Finset.univ.val := by
  rw [hA.charpoly_smul, Polynomial.roots_prod]
  · simp only [Polynomial.roots_X_sub_C, Multiset.bind_singleton, Function.comp_apply]
  · simp only [Finset.prod_ne_zero_iff, Finset.mem_univ, forall_true_left]
    exact fun i => Polynomial.X_sub_C_ne_zero _

/-- **Scaling a Hermitian matrix by a nonnegative real scales its `eigenvalues₀` by the same
constant.** See the module doc above for the proof roadmap. -/
theorem Matrix.IsHermitian.eigenvalues₀_smul {A : Matrix n n 𝕜} (hA : A.IsHermitian) {c : ℝ}
    (hc : 0 ≤ c) :
    (hA.smul (IsSelfAdjoint.all c)).eigenvalues₀ = c • hA.eigenvalues₀ := by
  rcases hc.eq_or_lt with hc0 | hc0
  · subst hc0
    funext k
    have h0 := (hA.smul (IsSelfAdjoint.all (0 : ℝ))).eigenvalues_eq_zero_iff.mpr (zero_smul ℝ A)
    simpa [Matrix.IsHermitian.eigenvalues] using
      congrFun h0 ((Fintype.equivOfCardEq (Fintype.card_fin _)) k)
  · have hre : (c • A).charpoly.roots.map RCLike.re
        = Multiset.map (c * ·) (A.charpoly.roots.map RCLike.re) := by
      rw [hA.roots_charpoly_smul, hA.roots_charpoly_eq_eigenvalues, Multiset.map_map,
        Multiset.map_map]
      simp [Function.comp, RCLike.ofReal_re]
    have hsort : ((c • A).charpoly.roots.map RCLike.re).sort (· ≥ ·)
        = ((A.charpoly.roots.map RCLike.re).sort (· ≥ ·)).map (c * ·) := by
      rw [hre]
      exact (Multiset.map_sort (f := fun x => c * x) (s := A.charpoly.roots.map RCLike.re)
        (r := (· ≥ ·)) (r' := (· ≥ ·))
        (fun a _ b _ => (mul_le_mul_iff_of_pos_left hc0).symm)).symm
    rw [(hA.smul (IsSelfAdjoint.all c)).sort_roots_charpoly_eq_eigenvalues₀,
      hA.sort_roots_charpoly_eq_eigenvalues₀, List.map_ofFn] at hsort
    have heq := List.ofFn_injective hsort
    funext k
    simpa using congrFun heq k
