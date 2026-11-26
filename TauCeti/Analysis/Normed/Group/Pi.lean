/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Topology.Order.Basic

/-!
# Norms on products

The norm on a nonempty finite product of seminormed groups is the maximum of the coordinate norms,
so it is attained at some coordinate (`Pi.exists_norm_apply_eq_norm`). Hence for every positive
exponent `n` its `n`-th power is at most the sum of the `n`-th powers of the coordinate norms
(`Pi.norm_pow_le_sum_norm_pow`). Replacing a coordinate of a point of the closed ball of radius `R`
about `0` by an element of norm at most `R` stays in that ball (`Pi.norm_update_le`).

Over an arbitrary index type, every coordinate of `Pi.single i c` has norm at most `‖c‖`
(`Pi.norm_single_apply_le`). A uniform limit in nonnegative weighted coefficient norms
preserves decay at infinity (`TauCeti.tendsto_zero_of_weighted_uniform_limit`).
-/

public section

/-- The norm on a nonempty finite product of seminormed groups is attained at some coordinate. -/
theorem Pi.exists_norm_apply_eq_norm {ι : Type*} [Fintype ι] [Nonempty ι] {E : ι → Type*}
    [∀ i, SeminormedAddGroup (E i)] (f : ∀ i, E i) : ∃ i, ‖f i‖ = ‖f‖ := by
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_sup Finset.univ Finset.univ_nonempty fun i ↦ ‖f i‖₊
  exact ⟨i, by rw [Pi.norm_def, hi, coe_nnNorm]⟩

/-- The `n`-th power of the norm on a finite product is at most the sum of the `n`-th powers of
the coordinate norms, for every positive exponent `n`. -/
theorem Pi.norm_pow_le_sum_norm_pow {ι : Type*} [Fintype ι] {E : ι → Type*}
    [∀ i, SeminormedAddGroup (E i)] (f : ∀ i, E i) {n : ℕ} (hn : n ≠ 0) :
    ‖f‖ ^ n ≤ ∑ i, ‖f i‖ ^ n := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · simp [Subsingleton.elim f 0, hn]
  obtain ⟨i, hi⟩ := Pi.exists_norm_apply_eq_norm f
  rw [← hi]
  exact Finset.single_le_sum (f := fun i ↦ ‖f i‖ ^ n) (fun _ _ ↦ by positivity)
    (Finset.mem_univ i)

/-- Every coordinate of `Pi.single i c` has norm at most `‖c‖`, over any index type. -/
theorem Pi.norm_single_apply_le {ι : Type*} [DecidableEq ι] {E : ι → Type*}
    [∀ i, SeminormedAddGroup (E i)] (i j : ι) (c : E i) :
    ‖(Pi.single i c : ∀ j, E j) j‖ ≤ ‖c‖ := by
  rcases eq_or_ne j i with rfl | h
  · simp
  · simp [Pi.single_eq_of_ne h]

/-- Replacing a coordinate of a point of norm at most `R` in a finite product by an element of norm
at most `R` gives a point of norm at most `R`. -/
theorem Pi.norm_update_le {ι : Type*} [Fintype ι] [DecidableEq ι] {E : ι → Type*}
    [∀ i, SeminormedAddGroup (E i)] {x : ∀ i, E i} {i : ι} {y : E i} {R : ℝ} (hx : ‖x‖ ≤ R)
    (hy : ‖y‖ ≤ R) : ‖Function.update x i y‖ ≤ R :=
  (pi_norm_le_iff_of_nonneg ((norm_nonneg y).trans hy)).2 fun j ↦ by
    rcases eq_or_ne j i with rfl | hj
    · simpa using hy
    · simpa [Function.update_of_ne hj] using (norm_le_pi_norm x j).trans hx

open Filter Topology in
/-- A uniform limit in nonnegative weighted coefficient norms preserves decay at infinity. -/
theorem TauCeti.tendsto_zero_of_weighted_uniform_limit {ι E : Type*} [SeminormedAddGroup E]
    (w : ι → ℝ) (hw : ∀ t, 0 ≤ w t) (A : ℕ → ι → E) (a : ι → E)
    (hres : ∀ k, Tendsto (fun t ↦ ‖A k t‖ * w t) cofinite (𝓝 0))
    (hunif : ∀ ε > 0, ∃ N, ∀ k ≥ N, ∀ t, ‖A k t - a t‖ * w t ≤ ε) :
    Tendsto (fun t ↦ ‖a t‖ * w t) cofinite (𝓝 0) := by
  refine tendsto_order.mpr ⟨fun b hb ↦ .of_forall fun t ↦
    hb.trans_le (mul_nonneg (norm_nonneg _) (hw t)), fun ε hε ↦ ?_⟩
  obtain ⟨N, hN⟩ := hunif (ε / 2) (half_pos hε)
  filter_upwards [(hres N).eventually (gt_mem_nhds (half_pos hε))] with t ht
  calc
    ‖a t‖ * w t ≤ ‖A N t‖ * w t + ‖A N t - a t‖ * w t := by
      rw [← add_mul]
      exact mul_le_mul_of_nonneg_right (norm_le_norm_add_norm_sub _ _) (hw t)
    _ < ε / 2 + ε / 2 := add_lt_add_of_lt_of_le ht (hN N le_rfl t)
    _ = ε := add_halves ε
