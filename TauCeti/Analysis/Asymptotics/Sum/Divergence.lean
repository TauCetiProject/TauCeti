/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Group.Defs
import Mathlib.Analysis.Normed.Group.Bounded
import TauCeti.Algebra.Order.BigOperators.Ring.Finset
import TauCeti.Analysis.SpecificLimits.Basic

/-!
# Norm divergence of partial sums of rapidly growing sequences

For any sequence `f : ℕ → R` in a preordered, not necessarily associative ring with monotone
addition satisfying `c * f k ≤ f (k + 1)` on `Finset.Ico M m` (`M ≤ m`), telescoping gives the
finite-horizon bound `(c - 1) * ∑ j ∈ Finset.Ico M m, f j + f M ≤ f m`
(`TauCeti.sub_one_mul_sum_Ico_add_le_of_mul_le`). In a seminormed additive group `E`, combining this
with the triangle inequality when `1 ≤ c`, `M ≤ m`, and `c * ‖u k‖ ≤ ‖u (k + 1)‖` on
`Finset.Ico M m` yields
`(c - 2) * ‖u m‖ + ‖u M‖ ≤ (c - 1) * ‖∑ j ∈ Finset.Ico M (m + 1), u j‖`.

Norm divergence of partial sums over `Finset.Ico N n` does not depend on the starting index `N`
(`TauCeti.tendsto_norm_sum_Ico_atTop_iff`). At `c = 2` (with `M ≤ m`), the bound specializes to
`‖u M‖ ≤ ‖∑ j ∈ Finset.Ico M (m + 1), u j‖`. Thus if a sequence `u : ℕ → E` grows by at least a
factor of `c ≥ 2` from each index to the next (`c * ‖u m‖ ≤ ‖u (m + 1)‖` eventually) and has norms
that do not vanish eventually (`∃ᶠ m in atTop, 0 < ‖u m‖`), then the norms of the partial sums
`∑ m ∈ Finset.Ico N n, u m` tend to `+∞` as `n → ∞` for every starting index `N`.

In continued-fraction theory, this is the criterion by which geometric growth (with ratio at least
`2`) of the reduction-of-order summands implies divergence of the reduction-of-order series in
Pincherle's theorem.

## Main results

* `TauCeti.sub_two_mul_norm_add_norm_le_sub_one_mul_norm_sum_Ico_succ_of_mul_norm_le`: if `1 ≤ c`
  and `c * ‖u k‖ ≤ ‖u (k + 1)‖` for `k ∈ Finset.Ico M m` (`M ≤ m`), then
  `(c - 2) * ‖u m‖ + ‖u M‖ ≤ (c - 1) * ‖∑ j ∈ Finset.Ico M (m + 1), u j‖`.
* `TauCeti.tendsto_norm_sum_Ico_atTop_iff`: divergence in norm of partial sums
  `∑ m ∈ Finset.Ico N n, T m` does not depend on the starting index `N`.
* `TauCeti.tendsto_norm_sum_Ico_atTop_of_mul_norm_le`: if `2 ≤ c`, `c * ‖u m‖ ≤ ‖u (m + 1)‖`
  eventually, and `0 < ‖u m‖` frequently, then `‖∑ m ∈ Finset.Ico N n, u m‖ → ∞`.
-/

public section

open Filter Finset

namespace TauCeti

/-- Along a sequence in a seminormed additive group satisfying `c * ‖u k‖ ≤ ‖u (k + 1)‖` for
`k ∈ Ico M m` (`1 ≤ c`, `M ≤ m`),
`(c - 2) * ‖u m‖ + ‖u M‖ ≤ (c - 1) * ‖∑ j ∈ Ico M (m + 1), u j‖`.
At `c = 2` this specializes to `‖u M‖ ≤ ‖∑ j ∈ Ico M (m + 1), u j‖`. -/
theorem sub_two_mul_norm_add_norm_le_sub_one_mul_norm_sum_Ico_succ_of_mul_norm_le
    {E : Type*} [SeminormedAddCommGroup E] {u : ℕ → E} {c : ℝ} (hc : 1 ≤ c)
    {M m : ℕ} (hm : M ≤ m) (hstep : ∀ k ∈ Ico M m, c * ‖u k‖ ≤ ‖u (k + 1)‖) :
    (c - 2) * ‖u m‖ + ‖u M‖ ≤ (c - 1) * ‖∑ j ∈ Ico M (m + 1), u j‖ := by
  have hsum : (c - 1) * ∑ j ∈ Ico M m, ‖u j‖ + ‖u M‖ ≤ ‖u m‖ :=
    sub_one_mul_sum_Ico_add_le_of_mul_le hm hstep
  have htri : ‖u m‖ ≤ ‖∑ j ∈ Ico M (m + 1), u j‖ + ∑ j ∈ Ico M m, ‖u j‖ := by
    have h := norm_le_add_norm_add' (∑ j ∈ Ico M m, u j) (u m)
    rw [← sum_Ico_succ_top hm] at h
    exact h.trans (add_le_add le_rfl (norm_sum_le _ _))
  calc (c - 2) * ‖u m‖ + ‖u M‖
      = (c - 1) * ‖u m‖ - ‖u m‖ + ‖u M‖ := by ring
    _ ≤ ((c - 1) * ‖∑ j ∈ Ico M (m + 1), u j‖ + (c - 1) * ∑ j ∈ Ico M m, ‖u j‖) -
          ((c - 1) * ∑ j ∈ Ico M m, ‖u j‖ + ‖u M‖) + ‖u M‖ := by
        gcongr
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left htri (sub_nonneg.2 hc)
    _ = (c - 1) * ‖∑ j ∈ Ico M (m + 1), u j‖ := by ring

/-- Divergence in norm of partial sums `∑ m ∈ Ico N n, T m` does not depend on the starting index
`N`. -/
theorem tendsto_norm_sum_Ico_atTop_iff {E : Type*} [SeminormedAddCommGroup E] {T : ℕ → E}
    (N M : ℕ) :
    Tendsto (fun n => ‖∑ m ∈ Ico N n, T m‖) atTop atTop ↔
      Tendsto (fun n => ‖∑ m ∈ Ico M n, T m‖) atTop atTop := by
  have hmp (N M : ℕ)
      (hN : Tendsto (fun n => ‖∑ m ∈ Ico N n, T m‖) atTop atTop) :
      Tendsto (fun n => ‖∑ m ∈ Ico M n, T m‖) atTop atTop := by
    let K := max N M
    let C := (∑ m ∈ Ico N K, T m) - ∑ m ∈ Ico M K, T m
    refine ((Metric.tendsto_dist_right_atTop_iff C).2
      (tendsto_norm_atTop_iff_cobounded.1 hN)).congr' ?_
    filter_upwards [eventually_ge_atTop K] with n hn
    have hdiff : (∑ m ∈ Ico N n, T m) - C = ∑ m ∈ Ico M n, T m := by
      rw [← sum_Ico_consecutive T (le_max_left N M) hn,
        ← sum_Ico_consecutive T (le_max_right N M) hn]
      simp only [C]
      abel
    rw [dist_eq_norm, hdiff]
  exact ⟨hmp N M, hmp M N⟩

/-- If `2 ≤ c`, `c * ‖u m‖ ≤ ‖u (m + 1)‖` eventually, and `0 < ‖u m‖` frequently, then the norms
of the partial sums `∑ m ∈ Ico N n, u m` tend to `+∞` for every starting index `N`. -/
theorem tendsto_norm_sum_Ico_atTop_of_mul_norm_le {E : Type*} [SeminormedAddCommGroup E]
    {u : ℕ → E} {c : ℝ} (hc : 2 ≤ c)
    (hstep : ∀ᶠ m in atTop, c * ‖u m‖ ≤ ‖u (m + 1)‖)
    (hne : ∃ᶠ m in atTop, 0 < ‖u m‖) (N : ℕ) :
    Tendsto (fun n ↦ ‖∑ m ∈ Ico N n, u m‖) atTop atTop := by
  have hstep2 : ∀ᶠ m in atTop, 2 * ‖u m‖ ≤ ‖u (m + 1)‖ :=
    hstep.mono fun m hm ↦ (mul_le_mul_of_nonneg_right hc (norm_nonneg (u m))).trans hm
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hstep2
  have hnorm_atTop : Tendsto (fun m ↦ ‖u m‖) atTop atTop :=
    tendsto_atTop_of_eventually_geom_le one_lt_two hstep2 hne
  rw [tendsto_atTop]
  intro K
  obtain ⟨M₁, hM₁⟩ := eventually_atTop.1 (hnorm_atTop.eventually_ge_atTop (2 * K))
  set M₂ := max (max N M₀) M₁
  by_cases! h : ∀ n ≥ M₂, K ≤ ‖∑ j ∈ Ico N n, u j‖
  · exact eventually_atTop.2 ⟨M₂, h⟩
  · obtain ⟨M, hM₂, hMK⟩ := h
    have hNM : N ≤ M := ((le_max_left N M₀).trans (le_max_left _ M₁)).trans hM₂
    have hM₀M : M₀ ≤ M := ((le_max_right N M₀).trans (le_max_left _ M₁)).trans hM₂
    have hM₁M : M₁ ≤ M := (le_max_right _ M₁).trans hM₂
    refine eventually_atTop.2 ⟨M + 1, fun n hn ↦ ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.one_le_of_lt hn)
    have hMm : M ≤ m := by omega
    have hstepM : ∀ k ∈ Ico M m, 2 * ‖u k‖ ≤ ‖u (k + 1)‖ := fun k hk ↦
      hM₀ k (hM₀M.trans (mem_Ico.1 hk).1)
    have htail := sub_two_mul_norm_add_norm_le_sub_one_mul_norm_sum_Ico_succ_of_mul_norm_le
      one_le_two hMm hstepM
    have htri : ‖∑ j ∈ Ico M (m + 1), u j‖ ≤
        ‖∑ j ∈ Ico N (m + 1), u j‖ + ‖∑ j ∈ Ico N M, u j‖ := by
      rw [← sum_Ico_consecutive u hNM (hMm.trans m.le_succ)]
      exact norm_le_add_norm_add' _ _
    linarith [hM₁ M hM₁M]

end TauCeti
