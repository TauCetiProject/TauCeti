/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
import TauCeti.Algebra.BigOperators.Group.Finset.Indicator
import TauCeti.Algebra.BigOperators.Intervals
import TauCeti.Analysis.Normed.Lp.Basic

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

Likewise a one-sided convolution with a kernel `a`, `∑ₘ ‖aₘ‖ < ∞`, namely
`k ↦ ∑ₘ aₘ • f (k + m)`, a series of the left shifts of `f`, is bounded on `ℓᵖ` for
`1 ≤ p ≤ ∞` with norm at most `∑ₘ ‖aₘ‖` (`lp.exists_hasSum_smul_add_and_norm_le`), a case of
Young's inequality. The right shift `TauCeti.shiftRight M w` of `w`, padded with zeros, is again
in `ℓᵖ` (`Memℓp.shiftRight`), with the same norm (`lp.shiftRight`, `lp.norm_shiftRight`).
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

/-- **Young's inequality for a one-sided `ℓ¹` kernel.** For a kernel `a` with `∑ₘ ‖aₘ‖ < ∞`
and `f ∈ ℓᵖ`, `1 ≤ p ≤ ∞`, the series `∑ₘ aₘ • f (k + m)` converges for every `k`, and its sum
`f' k` defines `f' ∈ ℓᵖ` with norm at most `(∑ₘ ‖aₘ‖) ‖f‖`. -/
theorem lp.exists_hasSum_smul_add_and_norm_le {𝕜 E : Type*} [NormedRing 𝕜]
    [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] [CompleteSpace E] [Fact (1 ≤ p)]
    {a : ℕ → 𝕜} (ha : Summable fun m ↦ ‖a m‖) (f : lp (fun _ : ℕ ↦ E) p) :
    ∃ f' : lp (fun _ : ℕ ↦ E) p, (∀ k, HasSum (fun m ↦ a m • f (k + m)) (f' k)) ∧
      ‖f'‖ ≤ (∑' m, ‖a m‖) * ‖f‖ := by
  have hp : p ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  -- The shifted sequences `k ↦ f (k + m)` have norm at most `‖f‖`.
  have hinj (m : ℕ) : (Set.univ : Set ℕ).InjOn (· + m) := (add_left_injective m).injOn
  let shift (m : ℕ) : lp (fun _ : ℕ ↦ E) p :=
    ⟨Set.univ.indicator (f ∘ (· + m)), (lp.memℓp f).indicator_comp (hinj m)⟩
  have hshift_apply (m k : ℕ) : shift m k = f (k + m) := by simp [shift]
  have hshift (m : ℕ) : ‖shift m‖ ≤ ‖f‖ :=
    lp.norm_le_of_forall_eq_indicator_comp hp (hinj m) fun _ ↦ rfl
  have hbound (m : ℕ) : ‖a m • shift m‖ ≤ ‖a m‖ * ‖f‖ :=
    (norm_smul_le _ _).trans (mul_le_mul_of_nonneg_left (hshift m) (norm_nonneg _))
  have hsum : Summable fun m ↦ a m • shift m :=
    Summable.of_norm_bounded (ha.mul_right ‖f‖) hbound
  refine ⟨∑' m, a m • shift m, fun k ↦ ?_, ?_⟩
  · simpa only [map_smul, lp.evalCLM_apply, hshift_apply] using
      hsum.hasSum.mapL (lp.evalCLM 𝕜 (fun _ : ℕ ↦ E) p k)
  · calc ‖∑' m, a m • shift m‖ ≤ ∑' m, ‖a m‖ * ‖f‖ :=
          tsum_of_norm_bounded (ha.mul_right ‖f‖).hasSum hbound
      _ = (∑' m, ‖a m‖) * ‖f‖ := tsum_mul_right

namespace TauCeti

/-- The sequence `x` shifted `M` places to the right and padded with zeros. -/
def shiftRight {α : Type*} [Zero α] (M : ℕ) (x : ℕ → α) (i : ℕ) : α :=
  if M ≤ i then x (i - M) else 0

/-- The right shift by `M` reads `x n` at index `n + M`. -/
theorem shiftRight_add {α : Type*} [Zero α] (M : ℕ) (x : ℕ → α) (n : ℕ) :
    shiftRight M x (n + M) = x n := by
  simp [shiftRight]

/-- At an index `i ≥ M`, the right shift by `M` reads `x (i - M)`. -/
@[simp]
theorem shiftRight_of_le {α : Type*} [Zero α] {M i : ℕ} (x : ℕ → α) (hi : M ≤ i) :
    shiftRight M x i = x (i - M) := by
  simp [shiftRight, hi]

/-- The right shift by `M` vanishes at the indices `i < M`. -/
@[simp]
theorem shiftRight_of_lt {α : Type*} [Zero α] {M i : ℕ} (x : ℕ → α) (hi : i < M) :
    shiftRight M x i = 0 := by
  simp [shiftRight, not_le.2 hi]

/-- The right shift by `M` reads `x` along `i ↦ i - M` on `{i | M ≤ i}` and vanishes elsewhere. -/
theorem shiftRight_eq_indicator {α : Type*} [Zero α] (M : ℕ) (x : ℕ → α) :
    shiftRight M x = {i | M ≤ i}.indicator (x ∘ (· - M)) := by
  ext i
  by_cases hi : M ≤ i <;> simp [shiftRight, hi]

end TauCeti

open TauCeti

/-- The injectivity of `i ↦ i - M` on `{i | M ≤ i}`, along which the right shift reads. -/
private theorem injOn_tsub_right (M : ℕ) : {i | M ≤ i}.InjOn (· - M) :=
  fun _ ha _ hb h ↦ tsub_inj_left ha hb h

/-- **Right shifts in `ℓᵖ`.** If `x ∈ ℓᵖ`, then so is its right shift by `M`. -/
theorem Memℓp.shiftRight {x : ℕ → G} (hx : Memℓp x p) (M : ℕ) :
    Memℓp (TauCeti.shiftRight M x) p := by
  rw [shiftRight_eq_indicator]
  exact hx.indicator_comp (injOn_tsub_right M)

/-- The right shift by `M`, padded with zeros, of an element of `ℓᵖ`. -/
def lp.shiftRight (M : ℕ) (w : lp (fun _ : ℕ ↦ G) p) : lp (fun _ : ℕ ↦ G) p :=
  ⟨TauCeti.shiftRight M w, (lp.memℓp w).shiftRight M⟩

@[simp]
theorem lp.coeFn_shiftRight (M : ℕ) (w : lp (fun _ : ℕ ↦ G) p) :
    ⇑(lp.shiftRight M w) = TauCeti.shiftRight M w := (rfl)

/-- **The right shift is an isometry of `ℓᵖ`.** -/
theorem lp.norm_shiftRight (hp : p ≠ 0) (M : ℕ) (w : lp (fun _ : ℕ ↦ G) p) :
    ‖lp.shiftRight M w‖ = ‖w‖ :=
  le_antisymm
    (lp.norm_le_of_forall_eq_indicator_comp hp (injOn_tsub_right M) fun i ↦ by
      rw [lp.coeFn_shiftRight, shiftRight_eq_indicator])
    (lp.norm_le_of_forall_eq_indicator_comp (s := Set.univ) hp (add_left_injective M).injOn
      fun n ↦ by simp)
