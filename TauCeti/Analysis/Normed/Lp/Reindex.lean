/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace

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
-/

public section

open scoped ENNReal

variable {ι ι' G : Type*} [NormedAddCommGroup G] {p : ℝ≥0∞}

/-- The finite sums of `‖s.indicator (f ∘ g) j‖ ^ r`, `r > 0`, are finite sums of
`‖f k‖ ^ r`. -/
private theorem exists_sum_rpow_norm_indicator_comp_eq {f : ι → G} {g : ι' → ι} {s : Set ι'}
    (hg : s.InjOn g) {r : ℝ} (hr : 0 < r) (t : Finset ι') :
    ∃ t' : Finset ι, ∑ j ∈ t, ‖s.indicator (f ∘ g) j‖ ^ r = ∑ k ∈ t', ‖f k‖ ^ r := by
  classical
  refine ⟨(t.filter (· ∈ s)).image g, ?_⟩
  rw [Finset.sum_image fun j hj j' hj' ↦ hg (Finset.mem_filter.1 hj).2 (Finset.mem_filter.1 hj').2,
    Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ ↦ ?_
  by_cases hj : j ∈ s
  · simp [hj]
  · simp [hj, Real.zero_rpow hr.ne']

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
  · refine memℓp_gen' (C := ∑' k, ‖f k‖ ^ p.toReal) fun t ↦ ?_
    obtain ⟨t', ht'⟩ := exists_sum_rpow_norm_indicator_comp_eq (f := f) hg hp t
    rw [ht']
    exact (hf.summable hp).sum_le_tsum t' fun k _ ↦ by positivity

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
  · refine lp.norm_le_of_forall_sum_le hp' (lp.norm_nonneg' f) fun t ↦ ?_
    obtain ⟨t', ht'⟩ := exists_sum_rpow_norm_indicator_comp_eq (f := ⇑f) hg hp' t
    simp_rw [h, ht']
    exact lp.sum_rpow_le_norm_rpow hp' f t'

/-- A window sum `∑_{j - L ≤ k < j + L} f k` is the sum of `2 L` shifts of `f`: the `d`-th one
reads `f` at `j + d - L`, where this index is defined. -/
private theorem sum_Ico_sub_add_eq_sum_range_indicator (f : ℕ → G) (L j : ℕ) :
    ∑ k ∈ Finset.Ico (j - L) (j + L), f k =
      ∑ d ∈ Finset.range (2 * L), {i | L ≤ i + d}.indicator (f ∘ fun i ↦ i + d - L) j := by
  classical
  simp only [Set.indicator_apply, Set.mem_ofPred_eq, Function.comp_apply]
  rw [← Finset.sum_filter]
  refine Finset.sum_nbij' (fun k ↦ k + L - j) (fun d ↦ j + d - L) (fun k hk ↦ ?_) (fun d hd ↦ ?_)
    (fun k hk ↦ ?_) (fun d hd ↦ ?_) fun k hk ↦ ?_
  all_goals simp only [Finset.mem_Ico, Finset.mem_filter, Finset.mem_range] at *
  all_goals first | omega | (congr 1; omega)

/-- The `d`-th shift `i ↦ i + d - L` is injective where the index `i + d - L` is defined. -/
private theorem injOn_add_sub (L d : ℕ) : {i | L ≤ i + d}.InjOn fun i ↦ i + d - L :=
  fun i hi i' hi' h ↦ by
    simp only [Set.mem_ofPred_eq] at hi hi' h
    omega

/-- **Window sums in `ℓᵖ`.** If `f ∈ ℓᵖ`, then so is `j ↦ ∑_{j - L ≤ k < j + L} f k`. -/
theorem Memℓp.sum_Ico_sub_add {f : ℕ → G} (hf : Memℓp f p) (L : ℕ) :
    Memℓp (fun j ↦ ∑ k ∈ Finset.Ico (j - L) (j + L), f k) p := by
  simp_rw [sum_Ico_sub_add_eq_sum_range_indicator]
  exact Memℓp.finsetSum _ fun d _ ↦ hf.indicator_comp (injOn_add_sub L d)

/-- **The norm of window sums.** For `1 ≤ p`, the sequence `j ↦ ∑_{j - L ≤ k < j + L} f k` has
`ℓᵖ` norm at most `2 L ‖f‖`. -/
theorem lp.norm_le_of_forall_eq_sum_Ico_sub_add [Fact (1 ≤ p)] {f f' : lp (fun _ : ℕ ↦ G) p}
    (L : ℕ) (h : ∀ j, f' j = ∑ k ∈ Finset.Ico (j - L) (j + L), f k) : ‖f'‖ ≤ 2 * L * ‖f‖ := by
  have hp : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  set T : ℕ → lp (fun _ : ℕ ↦ G) p := fun d ↦
    ⟨{i | L ≤ i + d}.indicator (f ∘ fun i ↦ i + d - L),
      (lp.memℓp f).indicator_comp (injOn_add_sub L d)⟩
  have hT : ∀ d, ‖T d‖ ≤ ‖f‖ := fun d ↦
    lp.norm_le_of_forall_eq_indicator_comp hp (injOn_add_sub L d) fun _ ↦ rfl
  have hf' : f' = ∑ d ∈ Finset.range (2 * L), T d := by
    ext j
    rw [h, sum_Ico_sub_add_eq_sum_range_indicator, lp.coeFn_sum, Finset.sum_apply]
  calc ‖f'‖ ≤ ∑ d ∈ Finset.range (2 * L), ‖T d‖ := hf' ▸ norm_sum_le _ _
    _ ≤ ∑ _d ∈ Finset.range (2 * L), ‖f‖ := Finset.sum_le_sum fun d _ ↦ hT d
    _ = 2 * L * ‖f‖ := by simp
