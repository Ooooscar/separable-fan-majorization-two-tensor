import Mathlib.Analysis.Matrix.PosDef

/-!
# Sorted eigenvector basis

`Matrix.IsHermitian.eigenvectorBasis` (`Mathlib.Analysis.Matrix.Spectrum`) is indexed by the
matrix's own index type `n`, in no particular order. This file reindexes it by
`Fin (Fintype.card n)` so that `sortedEigenvectorBasis hA k` is a unit eigenvector for the `k`-th
sorted (decreasing) eigenvalue `hA.eigenvalues₀ k` — needed wherever eigenvectors must line up
with `eigenvalues₀`, in particular by `EigenvalueMonotonicity.lean`'s Courant–Fischer argument, but
also directly by `SpectralDecomposition.lean`, `Projector.lean`, and `KyFanMaxPrinciple.lean`,
rather than each site re-deriving this same reindexing inline.

## Main definitions

* `Matrix.IsHermitian.sortedEigenvectorBasis`

## Main results

* `Matrix.IsHermitian.mulVec_sortedEigenvectorBasis`,
  `Matrix.IsHermitian.orthonormal_sortedEigenvectorBasis`.
* `Matrix.PosSemidef.eigenvalues₀_nonneg`: the `eigenvalues₀`-indexed version of Mathlib's
  `Matrix.PosSemidef.eigenvalues_nonneg`, via the same reindexing equiv.
-/

open scoped Matrix ComplexOrder

variable {n 𝕜 : Type*} [Fintype n] [DecidableEq n] [RCLike 𝕜]

section SortedEigenvectors

variable {A : Matrix n n 𝕜} (hA : A.IsHermitian)

/-- `A`'s orthonormal eigenvectors, reindexed by `Fin (Fintype.card n)` so that
`sortedEigenvectorBasis hA k` is a unit eigenvector for the `k`-th sorted (decreasing) eigenvalue
`hA.eigenvalues₀ k`. -/
noncomputable def Matrix.IsHermitian.sortedEigenvectorBasis :
    Fin (Fintype.card n) → EuclideanSpace 𝕜 n :=
  fun k => hA.eigenvectorBasis (Fintype.equivOfCardEq (Fintype.card_fin _) k)

theorem Matrix.IsHermitian.mulVec_sortedEigenvectorBasis (k : Fin (Fintype.card n)) :
    A *ᵥ ⇑(hA.sortedEigenvectorBasis k) =
      (hA.eigenvalues₀ k : 𝕜) • ⇑(hA.sortedEigenvectorBasis k) := by
  simp [Matrix.IsHermitian.sortedEigenvectorBasis, mulVec_eigenvectorBasis,
    Matrix.IsHermitian.eigenvalues]

theorem Matrix.IsHermitian.orthonormal_sortedEigenvectorBasis :
    Orthonormal 𝕜 hA.sortedEigenvectorBasis :=
  hA.eigenvectorBasis.orthonormal.comp _
    (Fintype.equivOfCardEq (Fintype.card_fin _)).injective

end SortedEigenvectors
