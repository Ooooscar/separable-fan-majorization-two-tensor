import SeparableFanMajorization.ForMathlib.SingularValueDecomposition
import SeparableFanMajorization.ForMathlib.TraceInequality

/-!
# Ky Fan `k`-norms

Not in Mathlib. The Ky Fan `k`-norm of a matrix `A` is the sum of its `k` largest singular values,
`Majorization.topSum A.singularValues k`. It is unitarily invariant
(`Matrix.singularValues_unitary_conj`, `SingularValue.lean`) and, being definite, homogeneous, and
subadditive (`kyFanNorm_eq_zero_iff`, `kyFanNorm_smul`, `kyFanNorm_add_le` below), a genuine norm:
`k = 1` gives the operator norm and `k = Fintype.card ι` gives the trace norm.

Mathlib's standard `p`-norms on `Fin n → ℝ` (`PiLp`/`EuclideanSpace`,
`Mathlib.Analysis.Normed.Lp.PiLp`) are set up as a *type synonym* `PiLp p α` carrying a `Norm`
instance found by instance resolution. That pattern is unsuitable here: `Matrix ι ι 𝕜` needs many
unitarily invariant norms at once (one Ky Fan norm per `k`, Schatten norms, the operator norm, ...),
not one canonical norm per type. So `kyFanNorm` is a plain function taking `k` as an explicit
argument, in the same style as `Matrix.singularValues`/`Matrix.singularValueDiagonal`
(`SingularValue.lean`).

## Main definitions

* `Matrix.kyFanNorm`: `Matrix.kyFanNorm k A`, the sum of the `k` largest singular values of `A`.

## Main results

* `Matrix.kyFanNorm_nonneg`: `kyFanNorm k A` is nonnegative.
* `Matrix.kyFanNorm_eq_zero_iff`: `kyFanNorm k A = 0 ↔ A = 0`, for `1 ≤ k` — definiteness.
* `Matrix.kyFanNorm_add_le`: the triangle inequality, `kyFanNorm k (A+B) ≤ kyFanNorm k A +
  kyFanNorm k B`, via the general von Neumann trace inequality (`Matrix.trace_mul_conjTranspose_le`,
  `TraceInequality.lean`) and a star projection's eigenvalues being `0`/`1`
  (`IsStarProjection.eigenvalues₀_eq_zero_or_one`, `Projector.lean`).
-/

open Matrix
open scoped ComplexOrder

variable {ι 𝕜 : Type*} [Fintype ι] [DecidableEq ι] [RCLike 𝕜]

/-- The Ky Fan `k`-norm of `A`: the sum of the `k` largest singular values of `A`. `k = 1` gives
the operator norm and `k = Fintype.card ι` gives the trace norm. -/
noncomputable def Matrix.kyFanNorm (k : ℕ) (A : Matrix ι ι 𝕜) : ℝ :=
  Majorization.topSum A.singularValues k

/-- `kyFanNorm k A` is nonnegative, being a sum of (nonnegative) singular values. -/
theorem Matrix.kyFanNorm_nonneg (k : ℕ) (A : Matrix ι ι 𝕜) : 0 ≤ A.kyFanNorm k :=
  Majorization.topSum_nonneg A.singularValues A.singularValues_nonneg k

/-- `kyFanNorm k (c • A) = ‖c‖ * kyFanNorm k A` for any `c : 𝕜`: immediate from
`Matrix.singularValues_smul` (which already produces the nonnegative coefficient `‖c‖`, since
singular values are always nonnegative) and `Majorization.topSum_smul`. Needed by
`Matrix.kyFanNorm_real_smul` below. -/
theorem Matrix.kyFanNorm_smul (c : 𝕜) (k : ℕ) (A : Matrix ι ι 𝕜) :
    (c • A).kyFanNorm k = ‖c‖ * A.kyFanNorm k := by
  unfold Matrix.kyFanNorm
  rw [Matrix.singularValues_smul A c, Majorization.topSum_smul (norm_nonneg c)]

/-- `kyFanNorm k (c • A) = |c| * kyFanNorm k A` for a *real* `c` (the `Module ℝ (Matrix ι ι 𝕜)`
scaling, as opposed to `Matrix.kyFanNorm_smul`'s `Module 𝕜 (Matrix ι ι 𝕜)` scaling above): a direct
corollary via `Matrix.singularValues_real_smul` and `Majorization.topSum_smul`. Needed by the
Cauchy–Schwarz inequality for Ky Fan norms (`KyFanCauchySchwarz.lean`), which only ever scales by a
real constant. -/
theorem Matrix.kyFanNorm_real_smul (c : ℝ) (k : ℕ) (A : Matrix ι ι 𝕜) :
    (c • A).kyFanNorm k = |c| * A.kyFanNorm k := by
  unfold Matrix.kyFanNorm
  rw [Matrix.singularValues_real_smul A c, Majorization.topSum_smul (abs_nonneg c)]

/-- `(0 : Matrix ι ι 𝕜).kyFanNorm k = 0`, for every `k`: immediate from `kyFanNorm_smul` at
`c = 0`, since `(0 : 𝕜) • A = 0` for any `A`. Needed by `kyFanNorm_eq_zero_iff` below. -/
theorem Matrix.kyFanNorm_zero (k : ℕ) : (0 : Matrix ι ι 𝕜).kyFanNorm k = 0 := by
  have h := Matrix.kyFanNorm_smul (0 : 𝕜) k (0 : Matrix ι ι 𝕜)
  simpa using h

/-- **Definiteness of the Ky Fan `k`-norm**, for `1 ≤ k`: `kyFanNorm k A = 0 ↔ A = 0`. (`k = 0` is
excluded since `topSum f 0` is the empty sum, always `0`, regardless of `f`.)

`(←)` is `kyFanNorm_zero`. `(→)`: if `ι` is empty, `A = 0` trivially by `Subsingleton`. Otherwise
`Majorization.forall_eq_zero_of_topSum_eq_zero` applies directly when `k ≤ Fintype.card ι`; past
that point, `Majorization.topSum_eq_topSum_of_le` first collapses `kyFanNorm k A` down to
`kyFanNorm (Fintype.card ι) A`. Either way this gives `A.singularValues ≡ 0`, i.e. every eigenvalue
of `Aᴴ * A` (`Matrix.posSemidef_conjTranspose_mul_self`) is `0` (`Real.sq_sqrt`-style squaring),
hence `(Aᴴ * A).trace = 0` (`Matrix.IsHermitian.sum_eigenvalues₀_eq_trace`), hence `A = 0`
(`Matrix.trace_conjTranspose_mul_self_eq_zero_iff`). -/
theorem Matrix.kyFanNorm_eq_zero_iff {k : ℕ} (hk : 1 ≤ k) (A : Matrix ι ι 𝕜) :
    A.kyFanNorm k = 0 ↔ A = 0 := by
  refine ⟨fun h => ?_, fun h => h ▸ Matrix.kyFanNorm_zero k⟩
  rcases Nat.eq_zero_or_pos (Fintype.card ι) with hn0 | hnpos
  · haveI : IsEmpty ι := Fintype.card_eq_zero_iff.mp hn0
    exact Subsingleton.elim A 0
  · unfold Matrix.kyFanNorm at h
    have hsingzero : ∀ i, A.singularValues i = 0 := by
      by_cases hkle : k ≤ Fintype.card ι
      · exact Majorization.forall_eq_zero_of_topSum_eq_zero A.singularValues_nonneg hk hkle h
      · push Not at hkle
        rw [Majorization.topSum_eq_topSum_of_le _ hkle.le] at h
        exact Majorization.forall_eq_zero_of_topSum_eq_zero
          A.singularValues_nonneg (by omega) le_rfl h
    have hM : (Matrix.conjTranspose A * A).IsHermitian :=
      (Matrix.posSemidef_conjTranspose_mul_self A).isHermitian
    have heigzero : ∀ i, hM.eigenvalues₀ i = 0 := fun i => by
      have hnn : 0 ≤ hM.eigenvalues₀ i :=
        (Matrix.posSemidef_conjTranspose_mul_self A).eigenvalues₀_nonneg i
      have hsq : hM.eigenvalues₀ i = Real.sqrt (hM.eigenvalues₀ i) ^ 2 := (Real.sq_sqrt hnn).symm
      have hsqrt0 : Real.sqrt (hM.eigenvalues₀ i) = 0 := hsingzero i
      rw [hsqrt0] at hsq
      simpa using hsq
    have htrace : (Matrix.conjTranspose A * A).trace = 0 := by
      rw [← hM.sum_eigenvalues₀_eq_trace]
      simp [heigzero]
    exact Matrix.trace_conjTranspose_mul_self_eq_zero_iff.mp htrace

/-- When `f` is already sorted in decreasing order, its top-`k` sum (`Majorization.topSum`,
`SeparableFanMajorization/ForMathlib/Majorization.lean`) is literally the sum of its first `k` entries, read off
along `Fin.castLE hk : Fin k → Fin n` — no sorting permutation needed, unlike the general top-`k`
finset of `Majorization.exists_top_finset` (`Majorization.lean`). Needed by
`Matrix.exists_isometryPair_trace_eq_kyFanNorm` below, to identify the trace of the constructed
isometry pair (a sum over `Fin k`) with `Matrix.kyFanNorm`'s defining `topSum`. -/
theorem Majorization.topSum_eq_sum_castLE_of_antitone {n k : ℕ} {w : Fin n → ℝ} (hw : Antitone w)
    (hk : k ≤ n) :
    ∑ l : Fin k, w (Fin.castLE hk l) = Majorization.topSum w k := by
  unfold Majorization.topSum
  rw [Majorization.decreasingSort_of_antitone hw]
  refine Finset.sum_bij' (fun a _ => Fin.castLE hk a)
    (fun a ha => (⟨(a : ℕ), (Finset.mem_filter.mp ha).2⟩ : Fin k)) ?_ ?_ ?_ ?_ ?_
  · intro a _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castLE]
    exact a.isLt
  · exact fun a ha => Finset.mem_univ _
  · intro a _
    apply Fin.ext
    simp [Fin.val_castLE]
  · intro a _
    apply Fin.ext
    simp
  · exact fun a _ => rfl

/-- Restricting a matrix with orthonormal columns to an injectively-indexed subset of its columns
keeps them orthonormal: if `Wᴴ * W = 1`, `f` is injective, and `M`'s columns are `W`'s columns at
the positions `f` picks out, then `Mᴴ * M = 1`. The `(l, l')` entry of `Mᴴ * M` is the `(f l, f l')`
entry of `Wᴴ * W`, i.e. `1` iff `f l = f l'`, i.e. (by injectivity) iff `l = l'`.
Used twice by `Matrix.exists_isometryPair_trace_eq_kyFanNorm` below, once for `U₀` and once for
`V₀`. -/
private lemma Matrix.conjTranspose_mul_self_of_apply_eq_comp {ι 𝕜 : Type*} [Fintype ι]
    [DecidableEq ι] [RCLike 𝕜] {W : Matrix ι ι 𝕜} (hW : Wᴴ * W = 1) {k : ℕ}
    {M : Matrix ι (Fin k) 𝕜} (f : Fin k → ι) (hf : Function.Injective f)
    (hM : ∀ i l, M i l = W i (f l)) :
    Mᴴ * M = (1 : Matrix (Fin k) (Fin k) 𝕜) := by
  apply Matrix.ext
  intro l l'
  have hstep : (Mᴴ * M) l l' = (Wᴴ * W) (f l) (f l') := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hM]
  rw [hstep, hW, Matrix.one_apply, Matrix.one_apply]
  simp [hf.eq_iff]

/-- **Trace-realization of the Ky Fan `k`-norm via an isometry pair.** For any square matrix `Z`
and `k ≤ Fintype.card ι`, there exist `U V : Matrix ι (Fin k) 𝕜` with orthonormal columns
(`Uᴴ * U = 1`, `Vᴴ * V = 1`) such that `Tr(Uᴴ * Z * V)` is exactly `Z.kyFanNorm k` (cast into `𝕜`).

Construction: take `Z`'s SVD `Z = U₀ * Σ * V₀ᴴ` (`Matrix.exists_svd`,
`SingularValueDecomposition.lean`), let `e : Fin (Fintype.card ι) ≃ ι` be the reindexing equivalence
relating `Z.svdValues` (unsorted, `ι`-indexed) to `Z.singularValues` (sorted, `Fin (Fintype.card
ι)`-indexed) via `Matrix.svdValues_eq_singularValues_comp`, and let `f := e ∘ Fin.castLE hk : Fin k
→ ι` pick out `U₀`, `V₀`'s columns at the top `k` positions of that order. Then `U`, `V` (`U₀`, `V₀`
restricted to the columns indexed by `f`) are still orthonormal (`f` is injective), and `Uᴴ * Z * V`
is exactly the `k × k` diagonal matrix of the `k` largest singular values (`Z.singularValues ∘
Fin.castLE hk`, via `topSum_eq_sum_castLE_of_antitone` above and `Z.singularValues_antitone`), whose
trace is `Z.kyFanNorm k` by definition (`Majorization.topSum`).

Used by `KyFanCauchySchwarz.lean`'s `Matrix.kyFanNorm_sqrt_mul_contraction_mul_sqrt_le_max` and, in
this file, by `kyFanNorm_add_le`'s roadmap below. -/
theorem Matrix.exists_isometryPair_trace_eq_kyFanNorm (Z : Matrix ι ι 𝕜) {k : ℕ}
    (hk : k ≤ Fintype.card ι) :
    ∃ U V : Matrix ι (Fin k) 𝕜, Uᴴ * U = 1 ∧ Vᴴ * V = 1 ∧
      (Uᴴ * Z * V).trace = ((Z.kyFanNorm k : ℝ) : 𝕜) := by
  classical
  obtain ⟨U₀, V₀, hZsvd⟩ := Z.exists_svd
  have hU0 : (U₀ : Matrix ι ι 𝕜)ᴴ * (U₀ : Matrix ι ι 𝕜) = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp U₀.2
    rwa [Matrix.star_eq_conjTranspose] at h
  have hV0 : (V₀ : Matrix ι ι 𝕜)ᴴ * (V₀ : Matrix ι ι 𝕜) = 1 := by
    have h := Matrix.mem_unitaryGroup_iff'.mp V₀.2
    rwa [Matrix.star_eq_conjTranspose] at h
  -- `e` reindexes the sorted, `Fin (Fintype.card ι)`-indexed singular values back to `ι`, so `f`
  -- (its restriction to the first `k`) points at `U₀`, `V₀`'s columns for the `k` largest
  -- singular values, in decreasing order.
  set e : Fin (Fintype.card ι) ≃ ι := Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card ι))
    with he_def
  set f : Fin k → ι := fun l => e (Fin.castLE hk l) with hf_def
  have hf_inj : Function.Injective f := fun a b hab => Fin.castLE_injective hk (e.injective hab)
  -- U, V: U₀, V₀ restricted to the columns `f` picks out.
  set U : Matrix ι (Fin k) 𝕜 := fun i l => (U₀ : Matrix ι ι 𝕜) i (f l) with hU_def
  set V : Matrix ι (Fin k) 𝕜 := fun i l => (V₀ : Matrix ι ι 𝕜) i (f l) with hV_def
  have hU_apply : ∀ i l, U i l = (U₀ : Matrix ι ι 𝕜) i (f l) := fun _ _ => rfl
  have hV_apply : ∀ i l, V i l = (V₀ : Matrix ι ι 𝕜) i (f l) := fun _ _ => rfl
  -- `f` injective ⇒ restricting `U₀`, `V₀` to the columns it picks out preserves orthonormality.
  have hUU : Uᴴ * U = (1 : Matrix (Fin k) (Fin k) 𝕜) :=
    Matrix.conjTranspose_mul_self_of_apply_eq_comp hU0 f hf_inj hU_apply
  have hVV : Vᴴ * V = (1 : Matrix (Fin k) (Fin k) 𝕜) :=
    Matrix.conjTranspose_mul_self_of_apply_eq_comp hV0 f hf_inj hV_apply
  refine ⟨U, V, hUU, hVV, ?_⟩
  -- P := Uᴴ * U₀ and Q := V₀ᴴ * V bridge `U`, `V`'s restricted columns back to the full `U₀`,
  -- `V₀`, so that `Uᴴ * Z * V` can be rewritten via `Z`'s SVD as `P * Σ * Q` below.
  set P : Matrix (Fin k) ι 𝕜 := Uᴴ * (U₀ : Matrix ι ι 𝕜) with hP_def
  set Q : Matrix ι (Fin k) 𝕜 := (V₀ : Matrix ι ι 𝕜)ᴴ * V with hQ_def
  have hP : ∀ l i, P l i = if f l = i then (1 : 𝕜) else 0 := by
    intro l i
    have hstep : P l i = ((U₀ : Matrix ι ι 𝕜)ᴴ * (U₀ : Matrix ι ι 𝕜)) (f l) i := by
      simp only [hP_def, Matrix.mul_apply, Matrix.conjTranspose_apply, hU_apply]
    rw [hstep, hU0, Matrix.one_apply]
  have hQ : ∀ i l, Q i l = if i = f l then (1 : 𝕜) else 0 := by
    intro i l
    have hstep : Q i l = ((V₀ : Matrix ι ι 𝕜)ᴴ * (V₀ : Matrix ι ι 𝕜)) i (f l) := by
      simp only [hQ_def, Matrix.mul_apply, Matrix.conjTranspose_apply, hV_apply]
    rw [hstep, hV0, Matrix.one_apply]
  -- Substitute `Z`'s SVD and re-associate so `U₀`, `V₀` cancel against `P`, `Q`, leaving `P*Σ*Q`.
  have hassoc : Uᴴ * Z * V = P * Matrix.diagonal (RCLike.ofReal ∘ Z.svdValues) * Q := by
    rw [hP_def, hQ_def]
    conv_lhs => rw [hZsvd]
    simp only [Matrix.mul_assoc]
  -- `P * Σ * Q` is diagonal: its off-diagonal (`l ≠ l'`) entries vanish since `f` is injective.
  have hPSigmaQ : ∀ l l' : Fin k,
      (P * Matrix.diagonal (RCLike.ofReal ∘ Z.svdValues) * Q : Matrix (Fin k) (Fin k) 𝕜) l l'
        = if l = l' then (Z.svdValues (f l) : 𝕜) else 0 := by
    intro l l'
    have hstep1 : ∀ i, (P * Matrix.diagonal (RCLike.ofReal ∘ Z.svdValues) : Matrix (Fin k) ι 𝕜) l i
        = if f l = i then (Z.svdValues i : 𝕜) else 0 := by
      intro i
      rw [Matrix.mul_diagonal, hP l i]
      split_ifs <;> simp [Function.comp_apply]
    rw [Matrix.mul_apply]
    simp only [hstep1, ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true, hQ]
    simp [hf_inj.eq_iff, mul_ite, mul_one, mul_zero]
  have hUZV : Uᴴ * Z * V = Matrix.diagonal (fun l : Fin k => (Z.svdValues (f l) : 𝕜)) := by
    rw [hassoc]
    apply Matrix.ext
    intro l l'
    rw [hPSigmaQ l l', Matrix.diagonal_apply]
  -- The sorted `k` largest singular values sum to `kyFanNorm k` by definition
  -- (`Majorization.topSum`).
  have hSumEq : ∑ l : Fin k, Z.singularValues (Fin.castLE hk l) = Z.kyFanNorm k := by
    unfold Matrix.kyFanNorm
    exact Majorization.topSum_eq_sum_castLE_of_antitone Z.singularValues_antitone hk
  -- The unsorted `svdValues` at `f l = e (castLE l)` match the sorted `singularValues` at `l`,
  -- by construction of `e` (`Matrix.svdValues_eq_singularValues_comp`).
  have hsvdf : ∀ l : Fin k, Z.svdValues (f l) = Z.singularValues (Fin.castLE hk l) := by
    intro l
    rw [Matrix.svdValues_eq_singularValues_comp, ← he_def]
    simp only [hf_def, Function.comp_apply, Equiv.symm_apply_apply]
  rw [hUZV, Matrix.trace_diagonal]
  simp only [hsvdf]
  rw [← RCLike.ofReal_sum, hSumEq]

/-- **The general von Neumann trace inequality, sandwiched between an isometry pair.** For any `M`
and any `U, V : Matrix ι (Fin k) 𝕜` with orthonormal columns (`Uᴴ*U = 1`, `Vᴴ*V = 1`),
`Re Tr(Uᴴ*M*V) ≤ M.kyFanNorm k`.

Proof: cyclicity turns `Tr(Uᴴ*M*V)` into `Tr(M*Wᴴ)` for `W := U*Vᴴ`, to which the general von
Neumann trace inequality (`Matrix.trace_mul_conjTranspose_le`, `TraceInequality.lean`) applies:
`Re Tr(M*Wᴴ) ≤ ∑ᵢ σᵢ(M)σᵢ(W)`. Since `U`, `V` are isometries, `W = U*Vᴴ`
satisfies `WᴴW = V*Uᴴ*U*Vᴴ = V*Vᴴ`, a rank-`k` star projection
(`Matrix.isStarProjection_mul_conjTranspose_of_conjTranspose_mul_self_eq_one`, `Projector.lean`)
whose `eigenvalues₀` are each `0` or `1` (`IsStarProjection.eigenvalues₀_eq_zero_or_one`,
`Projector.lean`) and sum to its rank `k` (`IsStarProjection.trace_eq_rank`).
Since `Real.sqrt` fixes `0` and `1`, `W`'s singular values are exactly that same `{0,1}`-valued,
sum-`k` sequence, and `Majorization.sum_mul_le_topSum` then collapses `∑ᵢ σᵢ(M)σᵢ(W) ≤
M.kyFanNorm k`.

*Not* the star-projection max principle `KyFanCauchySchwarz.lean`'s sandwiched-contraction bound
uses: that principle only bounds `Tr(Wᴴ*M*W)` for a *Hermitian* `M` sandwiched by the *same*
isometry `W` on both sides, via cyclicity to a single star projection `W*Wᴴ`. Here `M` is a general
(non-Hermitian) matrix sandwiched by *two different* isometries `U ≠ V`, so cyclicity instead gives
`Tr((V*Uᴴ)*M)` with `V*Uᴴ` not self-adjoint and `M` not Hermitian, which that principle does not
apply to.

Applied twice by `kyFanNorm_add_le` below, once for each summand of `A + B`. -/
theorem Matrix.re_trace_le_kyFanNorm_of_isometryPair {k : ℕ} (M : Matrix ι ι 𝕜)
    (U V : Matrix ι (Fin k) 𝕜) (hk : k ≤ Fintype.card ι) (hUU : Uᴴ * U = 1) (hVV : Vᴴ * V = 1) :
    RCLike.re (Uᴴ * M * V).trace ≤ M.kyFanNorm k := by
  have hWH : (U * Vᴴ)ᴴ = V * Uᴴ := by
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
  have hWHW : (U * Vᴴ)ᴴ * (U * Vᴴ) = V * Vᴴ := by
    rw [hWH, show V * Uᴴ * (U * Vᴴ) = V * (Uᴴ * U) * Vᴴ from by
      simp only [Matrix.mul_assoc], hUU, Matrix.mul_one]
  have htr : (M * (U * Vᴴ)ᴴ).trace = (Uᴴ * M * V).trace := by
    rw [hWH, ← Matrix.mul_assoc, Matrix.trace_mul_cycle M V Uᴴ]
  have hvN := Matrix.trace_mul_conjTranspose_le M (U * Vᴴ)
  rw [htr] at hvN
  obtain ⟨hQproj, hQrank⟩ :=
    Matrix.isStarProjection_mul_conjTranspose_of_conjTranspose_mul_self_eq_one hVV
  have hQherm := hQproj.posSemidef.isHermitian
  have hWHWherm : ((U * Vᴴ)ᴴ * (U * Vᴴ)).IsHermitian :=
    (Matrix.posSemidef_conjTranspose_mul_self (U * Vᴴ)).isHermitian
  have hcharpoly : ((U * Vᴴ)ᴴ * (U * Vᴴ)).charpoly = (V * Vᴴ).charpoly := by rw [hWHW]
  have heigeq : hWHWherm.eigenvalues₀ = hQherm.eigenvalues₀ :=
    hWHWherm.eigenvalues₀_eq_of_charpoly_eq hQherm hcharpoly
  -- `W = U*Vᴴ`'s singular values coincide with `V*Vᴴ`'s `{0,1}`-valued `eigenvalues₀`.
  have hWsingeq : (U * Vᴴ).singularValues = hQherm.eigenvalues₀ := by
    funext i
    unfold Matrix.singularValues
    rw [heigeq]
    rcases hQproj.eigenvalues₀_eq_zero_or_one i with h | h <;> rw [h] <;> simp
  have hc0 : ∀ i, 0 ≤ (U * Vᴴ).singularValues i := by
    intro i; rw [hWsingeq]
    rcases hQproj.eigenvalues₀_eq_zero_or_one i with h | h <;> rw [h] ; norm_num
  have hc1 : ∀ i, (U * Vᴴ).singularValues i ≤ 1 := by
    intro i; rw [hWsingeq]
    rcases hQproj.eigenvalues₀_eq_zero_or_one i with h | h <;> rw [h] ; norm_num
  have hcsum : ∑ i, (U * Vᴴ).singularValues i = (k : ℝ) := by
    rw [hWsingeq]
    have h1 : (∑ i, (hQherm.eigenvalues₀ i : 𝕜)) = (k : 𝕜) := by
      rw [hQherm.sum_eigenvalues₀_eq_trace, hQproj.trace_eq_rank, hQrank]
    exact_mod_cast h1
  have hfinal : ∑ i, M.singularValues i * (U * Vᴴ).singularValues i ≤ M.kyFanNorm k := by
    unfold Matrix.kyFanNorm
    exact Majorization.sum_mul_le_topSum M.singularValues (U * Vᴴ).singularValues k hk hc0
      hc1 hcsum
  exact hvN.trans hfinal

/-- **The triangle inequality for Ky Fan norms**: `(A + B).kyFanNorm k ≤ A.kyFanNorm k +
B.kyFanNorm k`. Together with `kyFanNorm_eq_zero_iff`/`kyFanNorm_smul` (definiteness, homogeneity)
and unitary invariance (`Matrix.singularValues_unitary_conj`, `SingularValue.lean`), this makes
`fun A => A.kyFanNorm k` (`1 ≤ k`) a unitarily invariant norm.

Proof (Ky Fan variational-formula route): take an isometry pair `U, V : Matrix ι (Fin k') 𝕜`
realizing `(A+B).kyFanNorm k'` exactly via `Matrix.exists_isometryPair_trace_eq_kyFanNorm` above,
so `Tr(Uᴴ*(A+B)*V) = Tr(Uᴴ*A*V) + Tr(Uᴴ*B*V)`. Each summand is bounded by
`re_trace_le_kyFanNorm_of_isometryPair` above, giving `Re Tr(Uᴴ*A*V) ≤ A.kyFanNorm k'` and
`Re Tr(Uᴴ*B*V) ≤ B.kyFanNorm k'`; summing these gives the claim for `k' ≤ Fintype.card ι`, and the
general `k` case follows by `Majorization.topSum_eq_topSum_of_le` saturation, as elsewhere in this
file. -/
theorem Matrix.kyFanNorm_add_le (k : ℕ) (A B : Matrix ι ι 𝕜) :
    (A + B).kyFanNorm k ≤ A.kyFanNorm k + B.kyFanNorm k := by
  have hcore : ∀ k' ≤ Fintype.card ι,
      (A + B).kyFanNorm k' ≤ A.kyFanNorm k' + B.kyFanNorm k' := by
    intro k' hk'
    obtain ⟨U, V, hUU, hVV, hUV⟩ := Matrix.exists_isometryPair_trace_eq_kyFanNorm (A + B) hk'
    have hsplit : (Uᴴ * (A + B) * V).trace = (Uᴴ * A * V).trace + (Uᴴ * B * V).trace := by
      rw [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add]
    have hre : RCLike.re (Uᴴ * A * V).trace + RCLike.re (Uᴴ * B * V).trace
        = (A + B).kyFanNorm k' := by
      rw [← map_add, ← hsplit, hUV, RCLike.ofReal_re]
    linarith [hre, Matrix.re_trace_le_kyFanNorm_of_isometryPair A U V hk' hUU hVV,
      Matrix.re_trace_le_kyFanNorm_of_isometryPair B U V hk' hUU hVV]
  by_cases hk : k ≤ Fintype.card ι
  · exact hcore k hk
  · push Not at hk
    have hsatAB : (A + B).kyFanNorm k = (A + B).kyFanNorm (Fintype.card ι) := by
      unfold Matrix.kyFanNorm; exact Majorization.topSum_eq_topSum_of_le _ hk.le
    have hsatA : A.kyFanNorm k = A.kyFanNorm (Fintype.card ι) := by
      unfold Matrix.kyFanNorm; exact Majorization.topSum_eq_topSum_of_le _ hk.le
    have hsatB : B.kyFanNorm k = B.kyFanNorm (Fintype.card ι) := by
      unfold Matrix.kyFanNorm; exact Majorization.topSum_eq_topSum_of_le _ hk.le
    rw [hsatAB, hsatA, hsatB]
    exact hcore (Fintype.card ι) le_rfl
