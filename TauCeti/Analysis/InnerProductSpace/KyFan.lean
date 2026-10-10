/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.CourantFischer
public import TauCeti.Analysis.InnerProductSpace.SingularValues
import TauCeti.Algebra.Order.BigOperators.Sum.ByParts

/-!
# Ky Fan sums of singular values

For a linear map `A : E →ₗ[𝕜] F` between finite-dimensional inner product spaces, the Ky Fan
`k`-sum `A.kyFanSum k = ∑_{i < k} σᵢ(A)` is the sum of its `k` largest singular values. This file
proves Ky Fan's maximum principle: for orthonormal families `(uᵢ)` in `F` and `(vᵢ)` in `E` with
`k` members,

  `‖∑ᵢ ⟪uᵢ, A vᵢ⟫‖ ≤ σ₀(A) + ⋯ + σₖ₋₁(A)`,

with equality attained by the leading singular pairs. The resulting variational characterization
`LinearMap.kyFanSum_le_iff` exhibits each Ky Fan sum as a supremum of the seminorms
`A ↦ ‖∑ᵢ ⟪uᵢ, A vᵢ⟫‖`, so the Ky Fan sums inherit the triangle inequality, homogeneity, and
invariance under isometric changes of coordinates, with no comparison of individual singular
values. The same weight argument gives Ky Fan's trace inequality for a symmetric operator: over an
orthonormal family with `k` members, the diagonal entries `re ⟪T wᵢ, wᵢ⟫` sum to at most the sum
of the `k` largest eigenvalues of `T`.

The bound expands `A` in its singular system `A x = ∑ⱼ σⱼ ⟪vⱼ', x⟫ uⱼ'`. The total weight that the
two families place on the `j`-th singular pair is at most `1` by Bessel's inequality, and the
weights add up to at most `k` by Parseval's identity; such weights against the antitone sequence
of singular values give at most the sum of its first `k` terms
(`LinearMap.sum_singularValues_mul_le_kyFanSum`).

## Main declarations

* `LinearMap.kyFanSum`: the Ky Fan `k`-sum of singular values.
* `LinearMap.norm_sum_inner_le_kyFanSum`: Ky Fan's maximum principle, the upper bound.
* `LinearMap.exists_orthonormal_sum_inner_eq_kyFanSum`: the leading singular pairs attain it.
* `LinearMap.kyFanSum_le_iff`: the variational characterization.
* `LinearMap.kyFanSum_add_le`: the Ky Fan triangle inequality.
* `LinearMap.kyFanSum_smul`, `LinearMap.kyFanSum_adjoint`,
  `LinearMap.kyFanSum_linearIsometryEquiv_comp`, `LinearMap.kyFanSum_comp_linearIsometryEquiv`:
  homogeneity, and invariance under adjoints and isometric changes of coordinates.
* `LinearMap.IsSymmetric.sum_re_inner_apply_self_le_sum_eigenvalues`: Ky Fan's trace inequality.

## References

* K. Fan, *Maximum properties and inequalities for the eigenvalues of completely continuous
  operators*, Proc. Nat. Acad. Sci. U.S.A. **37** (1951), 760–766.
* R. A. Horn and C. R. Johnson, *Matrix Analysis*, second edition, Cambridge University Press,
  2013, Section 3.4.
* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997, Section IV.2.
-/

public section

open Module Finset

namespace LinearMap

variable {𝕜 E F E' F' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [FiniteDimensional 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 F]
  [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [FiniteDimensional 𝕜 E']
  [NormedAddCommGroup F'] [InnerProductSpace 𝕜 F'] [FiniteDimensional 𝕜 F']

local notation "⟪" x ", " y "⟫" => inner 𝕜 x y

/-- The **Ky Fan `k`-sum** of `A`: the sum `σ₀(A) + ⋯ + σₖ₋₁(A)` of its `k` largest singular
values. -/
noncomputable def kyFanSum (A : E →ₗ[𝕜] F) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, A.singularValues i

theorem kyFanSum_def (A : E →ₗ[𝕜] F) (k : ℕ) :
    A.kyFanSum k = ∑ i ∈ Finset.range k, A.singularValues i :=
  (rfl)

@[simp]
theorem kyFanSum_zero_right (A : E →ₗ[𝕜] F) : A.kyFanSum 0 = 0 := by
  simp [kyFanSum_def]

@[simp]
theorem kyFanSum_succ (A : E →ₗ[𝕜] F) (k : ℕ) :
    A.kyFanSum (k + 1) = A.kyFanSum k + A.singularValues k := by
  simp [kyFanSum_def, sum_range_succ]

@[simp]
theorem kyFanSum_zero_left (k : ℕ) : (0 : E →ₗ[𝕜] F).kyFanSum k = 0 := by
  simp [kyFanSum_def]

theorem kyFanSum_nonneg (A : E →ₗ[𝕜] F) (k : ℕ) : 0 ≤ A.kyFanSum k :=
  sum_nonneg fun i _ ↦ A.singularValues_nonneg i

theorem kyFanSum_mono (A : E →ₗ[𝕜] F) : Monotone A.kyFanSum := fun _ _ h ↦
  sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr h) fun i _ _ ↦
    A.singularValues_nonneg i

/-- Only the first `rank A` singular values can be nonzero, so the Ky Fan sums stop growing at the
rank. -/
@[simp]
theorem kyFanSum_min_finrank_range (A : E →ₗ[𝕜] F) (k : ℕ) :
    A.kyFanSum (min k (finrank 𝕜 (range A))) = A.kyFanSum k := by
  refine sum_subset (Finset.range_subset_range.mpr (min_le_left _ _)) fun i hik hi ↦ ?_
  simp only [Finset.mem_range, lt_min_iff, not_and, not_lt] at hik hi
  exact A.singularValues_eq_zero_iff_le_finrank_range.mpr (hi hik)

/-- Taking the adjoint preserves every Ky Fan sum, since `A` and `adjoint A` have the same
singular values. -/
@[simp]
theorem kyFanSum_adjoint (A : E →ₗ[𝕜] F) (k : ℕ) : (adjoint A).kyFanSum k = A.kyFanSum k := by
  simp [kyFanSum_def]

/-- Weights `cⱼ ∈ [0, 1]` of total mass at most `k` on the singular values of `A` give at most the
Ky Fan `k`-sum: `∑ⱼ σⱼ cⱼ ≤ σ₀ + ⋯ + σₖ₋₁`. -/
theorem sum_singularValues_mul_le_kyFanSum (A : E →ₗ[𝕜] F) {k : ℕ} {c : Fin (finrank 𝕜 E) → ℝ}
    (hc0 : ∀ j, 0 ≤ c j) (hc1 : ∀ j, c j ≤ 1) (hck : ∑ j, c j ≤ k) :
    ∑ j : Fin (finrank 𝕜 E), A.singularValues j * c j ≤ A.kyFanSum k := by
  -- Extend the weights by zero to `ℕ` and compare with the antitone sequence of singular values,
  -- up to `min k (finrank 𝕜 E)` since there are only `finrank 𝕜 E` weights.
  have hsum (f : ℕ → ℝ) : ∑ j : Fin (finrank 𝕜 E), f j * c j =
      ∑ j ∈ Finset.range (finrank 𝕜 E), f j * if h : j < finrank 𝕜 E then c ⟨j, h⟩ else 0 := by
    rw [sum_fin_eq_sum_range]
    exact sum_congr rfl fun j hj ↦ by simp [Finset.mem_range.mp hj]
  have hcard : ∑ j, c j ≤ finrank 𝕜 E :=
    (sum_le_sum fun j _ ↦ hc1 j).trans (by simp)
  rw [hsum]
  refine le_trans ?_ ((kyFanSum_def A _).symm.trans_le
    (A.kyFanSum_mono (min_le_left k (finrank 𝕜 E))))
  refine TauCeti.sum_range_mul_le_sum_range_of_sum_le (min_le_right _ _) (fun j hj ↦ ?_)
    (fun j hj ↦ ?_) ?_ (fun i _ ↦ A.singularValues_antitone (Nat.le_succ i))
    (A.singularValues_nonneg _)
  · simpa [hj] using hc0 ⟨j, hj⟩
  · simpa [hj] using hc1 ⟨j, hj⟩
  · have h1 := hsum fun _ ↦ 1
    simp only [one_mul] at h1
    rw [← h1, Nat.cast_min]
    exact le_min hck hcard

/-- **Ky Fan's maximum principle**, the upper bound: for orthonormal families `(uᵢ)` in `F` and
`(vᵢ)` in `E` with `k` members, `‖∑ᵢ ⟪uᵢ, A vᵢ⟫‖` is at most the Ky Fan `k`-sum of `A`. -/
theorem norm_sum_inner_le_kyFanSum {ι : Type*} [Fintype ι] (A : E →ₗ[𝕜] F) {u : ι → F}
    {v : ι → E} (hu : Orthonormal 𝕜 u) (hv : Orthonormal 𝕜 v) :
    ‖∑ i, ⟪u i, A (v i)⟫‖ ≤ A.kyFanSum (Fintype.card ι) := by
  -- The weights the families `v` and `u` place on the `j`-th right and left singular vectors.
  obtain ⟨a, ha⟩ : ∃ a : Fin (finrank 𝕜 E) → ℝ,
      a = fun j ↦ ∑ i, ‖⟪A.rightSingularBasis j, v i⟫‖ ^ 2 := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : Fin (finrank 𝕜 E) → ℝ,
      b = fun j ↦ ∑ i, ‖⟪A.leftSingularVector j, u i⟫‖ ^ 2 := ⟨_, rfl⟩
  -- Bessel's inequality bounds each weight by one.
  have ha1 (j) : a j ≤ 1 := by
    simpa [ha, norm_inner_symm] using hv.sum_inner_products_le (s := univ) (A.rightSingularBasis j)
  have hb1 (j) : b j ≤ 1 := by
    have := hu.sum_inner_products_le (s := univ) (A.leftSingularVector j)
    simp only [norm_inner_symm (u _)] at this
    rw [hb]
    exact this.trans (pow_le_one₀ (norm_nonneg _) (A.norm_leftSingularVector_le_one j))
  -- Parseval's identity and Bessel's inequality bound the total weights by `card ι`.
  have hasum : ∑ j, a j = Fintype.card ι := by
    rw [ha, sum_comm]
    simp [A.rightSingularBasis.sum_sq_norm_inner_right, hv.1]
  have hbsum : ∑ j, b j ≤ Fintype.card ι := by
    rw [hb, sum_comm]
    calc ∑ i, ∑ j, ‖⟪A.leftSingularVector j, u i⟫‖ ^ 2 ≤ ∑ _i : ι, (1 : ℝ) :=
          sum_le_sum fun i _ ↦ by
            simpa [hu.1] using A.sum_norm_inner_leftSingularVector_sq_le (u i)
      _ = Fintype.card ι := by simp
  refine le_trans ?_ (A.sum_singularValues_mul_le_kyFanSum (c := fun j ↦ (a j + b j) / 2)
    (fun j ↦ by rw [ha, hb]; positivity) (fun j ↦ by linarith [ha1 j, hb1 j])
    (by rw [← sum_div, sum_add_distrib]; linarith))
  -- Expand `A` in its singular system and bound each coefficient by AM-GM.
  calc ‖∑ i, ⟪u i, A (v i)⟫‖
      = ‖∑ j : Fin (finrank 𝕜 E), (A.singularValues j : 𝕜) *
          ∑ i, ⟪A.rightSingularBasis j, v i⟫ * ⟪u i, A.leftSingularVector j⟫‖ := by
        simp_rw [A.apply_eq_sum_singularValues_smul, inner_sum, inner_smul_right, mul_sum]
        rw [sum_comm]
    _ ≤ ∑ j : Fin (finrank 𝕜 E), A.singularValues j * ((a j + b j) / 2) := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun j _ ↦ ?_)
        rw [norm_mul, RCLike.norm_ofReal, abs_of_nonneg (A.singularValues_nonneg _)]
        refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans ?_) (A.singularValues_nonneg _)
        simp only [ha, hb, ← sum_add_distrib, sum_div]
        refine sum_le_sum fun i _ ↦ ?_
        rw [norm_mul, norm_inner_symm (u i)]
        nlinarith [two_mul_le_add_sq ‖⟪A.rightSingularBasis j, v i⟫‖
          ‖⟪A.leftSingularVector j, u i⟫‖]

/-- **Ky Fan's maximum principle**, attainment: the first `k` right singular vectors and the
corresponding unit left singular vectors, completed where the singular value vanishes, are
orthonormal families with `∑ᵢ ⟪uᵢ, A vᵢ⟫ = σ₀(A) + ⋯ + σₖ₋₁(A)`. -/
theorem exists_orthonormal_sum_inner_eq_kyFanSum (A : E →ₗ[𝕜] F) {k : ℕ}
    (hkE : k ≤ finrank 𝕜 E) (hkF : k ≤ finrank 𝕜 F) :
    ∃ (u : Fin k → F) (v : Fin k → E), Orthonormal 𝕜 u ∧ Orthonormal 𝕜 v ∧
      ∑ i, ⟪u i, A (v i)⟫ = (A.kyFanSum k : 𝕜) := by
  obtain ⟨w, hw⟩ := A.exists_orthonormalBasis_apply_eq_leftSingularVector
  refine ⟨fun i ↦ w (Fin.castLE hkF i), fun i ↦ A.rightSingularBasis (Fin.castLE hkE i),
    w.orthonormal.comp _ (Fin.castLE_injective _),
    A.rightSingularBasis.orthonormal.comp _ (Fin.castLE_injective _), ?_⟩
  rw [kyFanSum_def, ← Fin.sum_univ_eq_sum_range, RCLike.ofReal_sum]
  refine sum_congr rfl fun i _ ↦ ?_
  rw [apply_rightSingularBasis, inner_smul_right]
  by_cases hσ : A.singularValues i = 0
  · simp [hσ]
  · beta_reduce
    rw [hw (Fin.castLE hkE i) (Fin.castLE hkF i) (by simp) (by simpa using hσ),
      inner_leftSingularVector]
    simp [hσ]

/-- The **variational characterization** of the Ky Fan sums: `A.kyFanSum k ≤ c` exactly when
`‖∑ᵢ ⟪uᵢ, A vᵢ⟫‖ ≤ c` for all orthonormal families `(uᵢ)` in `F` and `(vᵢ)` in `E` with at most
`k` members. -/
theorem kyFanSum_le_iff (A : E →ₗ[𝕜] F) {k : ℕ} {c : ℝ} :
    A.kyFanSum k ≤ c ↔ ∀ m ≤ k, ∀ (u : Fin m → F) (v : Fin m → E), Orthonormal 𝕜 u →
      Orthonormal 𝕜 v → ‖∑ i, ⟪u i, A (v i)⟫‖ ≤ c := by
  refine ⟨fun h m hm u v hu hv ↦ ?_, fun h ↦ ?_⟩
  · have := A.norm_sum_inner_le_kyFanSum hu hv
    rw [Fintype.card_fin] at this
    exact this.trans ((A.kyFanSum_mono hm).trans h)
  · set m := min k (finrank 𝕜 (range A))
    obtain ⟨u, v, hu, hv, huv⟩ := A.exists_orthonormal_sum_inner_eq_kyFanSum (k := m)
      ((min_le_right _ _).trans A.finrank_range_le)
      ((min_le_right _ _).trans (Submodule.finrank_le _))
    have := h m (min_le_left _ _) u v hu hv
    rwa [huv, RCLike.norm_ofReal, abs_of_nonneg (A.kyFanSum_nonneg m),
      kyFanSum_min_finrank_range] at this

/-- The **Ky Fan triangle inequality**: `Kₖ(A + B) ≤ Kₖ(A) + Kₖ(B)` for every `k`. -/
theorem kyFanSum_add_le (A B : E →ₗ[𝕜] F) (k : ℕ) :
    (A + B).kyFanSum k ≤ A.kyFanSum k + B.kyFanSum k := by
  refine (kyFanSum_le_iff _).mpr fun m hm u v hu hv ↦ ?_
  have hA := A.norm_sum_inner_le_kyFanSum hu hv
  have hB := B.norm_sum_inner_le_kyFanSum hu hv
  rw [Fintype.card_fin] at hA hB
  simp only [add_apply, inner_add_right, sum_add_distrib]
  exact (norm_add_le _ _).trans
    (add_le_add (hA.trans (A.kyFanSum_mono hm)) (hB.trans (B.kyFanSum_mono hm)))

/-- The Ky Fan sums are absolutely homogeneous: `Kₖ(c • A) = ‖c‖ Kₖ(A)`. -/
@[simp]
theorem kyFanSum_smul (c : 𝕜) (A : E →ₗ[𝕜] F) (k : ℕ) :
    (c • A).kyFanSum k = ‖c‖ * A.kyFanSum k := by
  have hle (c : 𝕜) (A : E →ₗ[𝕜] F) : (c • A).kyFanSum k ≤ ‖c‖ * A.kyFanSum k := by
    refine (kyFanSum_le_iff _).mpr fun m hm u v hu hv ↦ ?_
    have hA := A.norm_sum_inner_le_kyFanSum hu hv
    rw [Fintype.card_fin] at hA
    simp only [smul_apply, inner_smul_right, ← mul_sum, norm_mul]
    exact mul_le_mul_of_nonneg_left (hA.trans (A.kyFanSum_mono hm)) (norm_nonneg c)
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  · refine (hle c A).antisymm ?_
    have h := hle c⁻¹ (c • A)
    rwa [inv_smul_smul₀ hc, norm_inv, le_inv_mul_iff₀ (norm_pos_iff.mpr hc)] at h

@[simp]
theorem kyFanSum_neg (A : E →ₗ[𝕜] F) (k : ℕ) : (-A).kyFanSum k = A.kyFanSum k := by
  simpa using kyFanSum_smul (-1 : 𝕜) A k

/-- Composing on the left with an isometric isomorphism leaves the Ky Fan sums unchanged. -/
@[simp]
theorem kyFanSum_linearIsometryEquiv_comp (U : F ≃ₗᵢ[𝕜] F') (A : E →ₗ[𝕜] F) (k : ℕ) :
    ((U : F →ₗ[𝕜] F') ∘ₗ A).kyFanSum k = A.kyFanSum k := by
  refine le_antisymm ((kyFanSum_le_iff _).mpr fun m hm u v hu hv ↦ ?_)
    ((kyFanSum_le_iff _).mpr fun m hm u v hu hv ↦ ?_)
  · have h := A.norm_sum_inner_le_kyFanSum (hu.comp_linearIsometryEquiv U.symm) hv
    rw [Fintype.card_fin] at h
    simpa [U.symm.inner_map_eq_flip] using h.trans (A.kyFanSum_mono hm)
  · have h := ((U : F →ₗ[𝕜] F') ∘ₗ A).norm_sum_inner_le_kyFanSum
      (hu.comp_linearIsometryEquiv U) hv
    rw [Fintype.card_fin] at h
    simpa using h.trans (kyFanSum_mono _ hm)

/-- Composing on the right with an isometric isomorphism leaves the Ky Fan sums unchanged. -/
@[simp]
theorem kyFanSum_comp_linearIsometryEquiv (A : E →ₗ[𝕜] F) (V : E' ≃ₗᵢ[𝕜] E) (k : ℕ) :
    (A ∘ₗ (V : E' →ₗ[𝕜] E)).kyFanSum k = A.kyFanSum k := by
  refine le_antisymm ((kyFanSum_le_iff _).mpr fun m hm u v hu hv ↦ ?_)
    ((kyFanSum_le_iff _).mpr fun m hm u v hu hv ↦ ?_)
  · have h := A.norm_sum_inner_le_kyFanSum hu (hv.comp_linearIsometryEquiv V)
    rw [Fintype.card_fin] at h
    simpa using h.trans (A.kyFanSum_mono hm)
  · have h := (A ∘ₗ (V : E' →ₗ[𝕜] E)).norm_sum_inner_le_kyFanSum hu
      (hv.comp_linearIsometryEquiv V.symm)
    rw [Fintype.card_fin] at h
    simpa using h.trans (kyFanSum_mono _ hm)

namespace IsSymmetric

variable {T : E →ₗ[𝕜] E} {n : ℕ}

/-- **Ky Fan's trace inequality**: for a symmetric `T` and an orthonormal family `(wᵢ)` with `k`
members, `∑ᵢ re ⟪T wᵢ, wᵢ⟫` is at most the sum `λ₀ + ⋯ + λₖ₋₁` of the `k` largest eigenvalues
of `T`. -/
theorem sum_re_inner_apply_self_le_sum_eigenvalues (hT : T.IsSymmetric) (hn : finrank 𝕜 E = n)
    {ι : Type*} [Fintype ι] {w : ι → E} (hw : Orthonormal 𝕜 w) :
    ∑ i, RCLike.re ⟪T (w i), w i⟫ ≤
      ∑ j ∈ univ.filter fun j : Fin n ↦ (j : ℕ) < Fintype.card ι, hT.eigenvalues hn j := by
  have hk : Fintype.card ι ≤ n := hn ▸ hw.linearIndependent.fintype_card_le_finrank
  -- `cⱼ` is the weight the family places on the `j`-th eigenvector.
  obtain ⟨c, hc⟩ : ∃ c : Fin n → ℝ, c = fun j ↦ ∑ i, ‖⟪hT.eigenvectorBasis hn j, w i⟫‖ ^ 2 :=
    ⟨_, rfl⟩
  have hsum : ∑ i, RCLike.re ⟪T (w i), w i⟫ = ∑ j, hT.eigenvalues hn j * c j := by
    simp_rw [hT.re_inner_apply_self_eq_sum_eigenvalues_mul_sq hn,
      OrthonormalBasis.repr_apply_apply, hc, mul_sum]
    exact sum_comm
  -- Extend eigenvalues and weights by zero to `ℕ` and compare there.
  have hmass : ∑ j ∈ Finset.range n, (if h : j < n then c ⟨j, h⟩ else 0) = Fintype.card ι := by
    rw [← sum_fin_eq_sum_range, hc, sum_comm]
    simp [(hT.eigenvectorBasis hn).sum_sq_norm_inner_right, hw.1]
  rw [hsum, sum_fin_eq_sum_range]
  calc _ = ∑ j ∈ Finset.range n, (if h : j < n then hT.eigenvalues hn ⟨j, h⟩ else 0) *
        (if h : j < n then c ⟨j, h⟩ else 0) :=
        sum_congr rfl fun j hj ↦ by simp [Finset.mem_range.mp hj]
    _ ≤ ∑ j ∈ Finset.range (Fintype.card ι), if h : j < n then hT.eigenvalues hn ⟨j, h⟩ else 0 :=
        TauCeti.sum_range_mul_le_sum_range_of_sum_eq hk
          (fun j hj ↦ by simp only [hj, dite_true, hc]; positivity)
          (fun j hj ↦ by
            simpa [hj, hc, norm_inner_symm] using
              hw.sum_inner_products_le (s := univ) (hT.eigenvectorBasis hn ⟨j, hj⟩))
          hmass fun j hj ↦ by
            simpa [hj, (by omega : j < n)] using hT.eigenvalues_antitone hn
              (Fin.mk_le_mk.mpr (Nat.le_succ j))
    _ = _ := by
        rw [sum_filter, sum_fin_eq_sum_range]
        refine (sum_congr rfl fun j hj ↦ ?_).trans
          (sum_subset (Finset.range_subset_range.mpr hk) fun j _ hj ↦ by simp_all)
        simp [Finset.mem_range.mp hj]

end IsSymmetric

end LinearMap
