/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
import TauCeti.Algebra.BigOperators.Group.Finset.Indicator
import TauCeti.Algebra.BigOperators.Intervals

/-!
# Reindexing sequences in `ℓᵖ`

Let `f : ι → G` be a sequence in `ℓᵖ` and let `g : ι' → ι` be injective on a set `s ⊆ ι'`. The
sequence `s.indicator (f ∘ g)`, which reads `f` along `g` on `s` and vanishes off `s`, takes each
value of `f` at most once, so it again lies in `ℓᵖ`, with no larger norm
(`Memℓp.indicator_comp`, `lp.norm_le_of_forall_eq_indicator_comp`). Shifts of a sequence indexed
by `ℕ` are the basic examples: `j ↦ f (j + d)` and, on `{j | d ≤ j}`, `j ↦ f (j - d)`.

Consequently the **window sums** `j ↦ ∑_{j - L ≤ k < j + L} f k` of a sequence indexed by `ℕ`,
a sum of `2 L` shifts, lie in `ℓᵖ`, and for `1 ≤ p` their norm is at most `2 L ‖f‖`
(`Memℓp.sum_Ico_sub_add`, `lp.norm_le_of_forall_eq_sum_Ico_sub_add`). Such sums arise when a
sequence of dyadic pieces is replaced by another one in which each piece only interacts with the
pieces of nearby index, as for two Littlewood–Paley decompositions of the same function.

Similarly, for `0 ≤ r < 1` the **geometric tail sums** `j ↦ ∑_{d ≥ 0} r ^ d f (j + d)` of a
sequence in `ℓᵖ`, `1 ≤ p`, form a sequence in `ℓᵖ` of norm at most `(1 - r)⁻¹ ‖f‖`
(`lp.exists_forall_hasSum_pow_smul_add_and_norm_le`): they are an absolutely convergent series of
shifts. Such sums arise when each dyadic piece interacts with all the pieces of higher index, with
geometrically decaying weights.
-/

public section

open scoped ENNReal

variable {ι ι' G : Type*} [NormedAddCommGroup G] {p : ℝ≥0∞}

/-- **Reindexing in `ℓᵖ`.** If `f ∈ ℓᵖ` and `g` is injective on `s`, then the sequence that reads
`f` along `g` on `s` and vanishes off `s` lies in `ℓᵖ`. -/
theorem Memℓp.indicator_comp {f : ι → G} (hf : Memℓp f p) {g : ι' → ι} {s : Set ι'}
    (hg : s.InjOn g) : Memℓp (s.indicator (f ∘ g)) p := by
  rcases p.trichotomy with rfl | rfl | hp
  · refine memℓp_zero (Set.Finite.of_finite_image (hf.finite_dsupport.subset ?_) (hg.mono ?_))
    · rintro _ ⟨j, hj, rfl⟩
      by_cases hjs : j ∈ s
      · simpa [hjs] using hj
      · simp [hjs] at hj
    · intro j hj
      by_contra hjs
      simp [hjs] at hj
  · obtain ⟨C, hC⟩ := hf.bddAbove
    refine memℓp_infty ⟨max C 0, ?_⟩
    rintro _ ⟨j, rfl⟩
    by_cases hj : j ∈ s
    · simp [hj, hC ⟨g j, rfl⟩]
    · simp [hj]
  · classical
    refine memℓp_gen' (C := ∑' k, ‖f k‖ ^ p.toReal) fun t ↦ ?_
    exact (Finset.sum_apply_indicator_comp_eq_sum_image (h := fun x : G ↦ ‖x‖ ^ p.toReal)
      (by simp [Real.zero_rpow hp.ne']) hg t).trans_le
      ((hf.summable hp).sum_le_tsum _ fun k _ ↦ by positivity)

/-- **Reindexing in `ℓᵖ` does not increase the norm.** If `g` is injective on `s` and `f'` reads
`f` along `g` on `s` and vanishes off `s`, then `‖f'‖ ≤ ‖f‖`. -/
theorem lp.norm_le_of_forall_eq_indicator_comp (hp : p ≠ 0) {f : lp (fun _ : ι ↦ G) p}
    {f' : lp (fun _ : ι' ↦ G) p} {g : ι' → ι} {s : Set ι'} (hg : s.InjOn g)
    (h : ∀ j, f' j = s.indicator (f ∘ g) j) : ‖f'‖ ≤ ‖f‖ := by
  rcases p.trichotomy with rfl | rfl | hp'
  · exact absurd rfl hp
  · refine lp.norm_le_of_forall_le (lp.norm_nonneg' f) fun j ↦ ?_
    rw [h j]
    by_cases hj : j ∈ s
    · simpa [hj] using lp.norm_apply_le_norm hp f (g j)
    · simp [hj, lp.norm_nonneg' f]
  · classical
    refine lp.norm_le_of_forall_sum_le hp' (lp.norm_nonneg' f) fun t ↦ ?_
    simp_rw [h]
    exact (Finset.sum_apply_indicator_comp_eq_sum_image (h := fun x : G ↦ ‖x‖ ^ p.toReal)
      (by simp [Real.zero_rpow hp'.ne']) hg t).trans_le (lp.sum_rpow_le_norm_rpow hp' f _)

/-- **Window sums in `ℓᵖ`.** If `f ∈ ℓᵖ`, then so is `j ↦ ∑_{j - L ≤ k < j + L} f k`. -/
theorem Memℓp.sum_Ico_sub_add {f : ℕ → G} (hf : Memℓp f p) (L : ℕ) :
    Memℓp (fun j ↦ ∑ k ∈ Finset.Ico (j - L) (j + L), f k) p := by
  simp_rw [Finset.sum_Ico_sub_add_eq_sum_range_indicator]
  exact Memℓp.finsetSum _ fun d _ ↦
    hf.indicator_comp fun _ hi _ hi' h ↦ add_right_cancel (tsub_inj_left hi hi' h)

/-- **The norm of window sums.** For `1 ≤ p`, the sequence `j ↦ ∑_{j - L ≤ k < j + L} f k` has
`ℓᵖ` norm at most `2 L ‖f‖`. -/
theorem lp.norm_le_of_forall_eq_sum_Ico_sub_add [Fact (1 ≤ p)] {f f' : lp (fun _ : ℕ ↦ G) p}
    (L : ℕ) (h : ∀ j, f' j = ∑ k ∈ Finset.Ico (j - L) (j + L), f k) : ‖f'‖ ≤ 2 * L * ‖f‖ := by
  have hp : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hg : ∀ d, {i | L ≤ i + d}.InjOn fun i ↦ i + d - L :=
    fun _ _ hi _ hi' h ↦ add_right_cancel (tsub_inj_left hi hi' h)
  set T : ℕ → lp (fun _ : ℕ ↦ G) p := fun d ↦
    ⟨{i | L ≤ i + d}.indicator (f ∘ fun i ↦ i + d - L),
      (lp.memℓp f).indicator_comp (hg d)⟩
  have hT : ∀ d, ‖T d‖ ≤ ‖f‖ := fun d ↦
    lp.norm_le_of_forall_eq_indicator_comp hp (hg d) fun _ ↦ rfl
  have hf' : f' = ∑ d ∈ Finset.range (2 * L), T d := by
    ext j
    rw [h, Finset.sum_Ico_sub_add_eq_sum_range_indicator, lp.coeFn_sum, Finset.sum_apply]
  calc ‖f'‖ ≤ ∑ d ∈ Finset.range (2 * L), ‖T d‖ := hf' ▸ norm_sum_le _ _
    _ ≤ ∑ _d ∈ Finset.range (2 * L), ‖f‖ := Finset.sum_le_sum fun d _ ↦ hT d
    _ = 2 * L * ‖f‖ := by simp

/-- **Geometric tail sums in `ℓᵖ`.** For `1 ≤ p` and `0 ≤ r < 1`, the tail sums
`j ↦ ∑_{d ≥ 0} r ^ d f (d + j)` of a sequence `f ∈ ℓᵖ` converge and form a sequence in `ℓᵖ` of norm
at most `(1 - r)⁻¹ ‖f‖`. -/
theorem lp.exists_forall_hasSum_pow_smul_add_and_norm_le [Fact (1 ≤ p)] [NormedSpace ℝ G]
    [CompleteSpace G] (f : lp (fun _ : ℕ ↦ G) p) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ g : lp (fun _ : ℕ ↦ G) p, (∀ j, HasSum (fun d ↦ r ^ d • f (d + j)) (g j)) ∧
      ‖g‖ ≤ (1 - r)⁻¹ * ‖f‖ := by
  have hp : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hinj (d : ℕ) : (Set.univ : Set ℕ).InjOn fun j ↦ d + j :=
    fun _ _ _ _ h ↦ add_left_cancel h
  -- The shift `T d = (f (d + j))ⱼ`, of norm at most `‖f‖`.
  set T : ℕ → lp (fun _ : ℕ ↦ G) p := fun d ↦
    ⟨Set.univ.indicator (f ∘ fun j ↦ d + j), (lp.memℓp f).indicator_comp (hinj d)⟩
  have hT (d j : ℕ) : T d j = f (d + j) := by simp [T]
  have hbound (d : ℕ) : ‖r ^ d • T d‖ ≤ ‖f‖ * r ^ d := by
    rw [norm_smul, Real.norm_of_nonneg (by positivity), mul_comm]
    exact mul_le_mul_of_nonneg_right
      (lp.norm_le_of_forall_eq_indicator_comp hp (hinj d) fun _ ↦ rfl) (by positivity)
  have hgeom := (summable_geometric_of_lt_one hr0 hr1).mul_left ‖f‖
  have hsum : Summable fun d ↦ r ^ d • T d := Summable.of_norm_bounded hgeom hbound
  refine ⟨∑' d, r ^ d • T d, fun j ↦ ?_, ?_⟩
  · have h := Pi.hasSum.1 (hsum.hasSum.map (lp.coeFnAddMonoidHom (fun _ : ℕ ↦ G) p)
      lp.uniformContinuous_coe.continuous) j
    simpa [lp.coeFnAddMonoidHom_apply, lp.coeFn_smul, hT] using h
  · calc ‖∑' d, r ^ d • T d‖ ≤ ∑' d, ‖f‖ * r ^ d := tsum_of_norm_bounded hgeom.hasSum hbound
      _ = (1 - r)⁻¹ * ‖f‖ := by rw [tsum_mul_left, tsum_geometric_of_lt_one hr0 hr1, mul_comm]
