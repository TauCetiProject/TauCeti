/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Analysis.Asymptotics.Basic
import TauCeti.Algebra.Order.BigOperators.Sum.IcoMulLe

/-!
# Norm divergence of partial sums of rapidly growing sequences

For any sequence `f : ℕ → R` in a preordered, not necessarily associative ring with monotone
addition satisfying `c * f k ≤ f (k + 1)` on `Finset.Ico M m` (`M ≤ m`), telescoping gives the
finite-horizon bound `(c - 1) * ∑ j ∈ Finset.Ico M m, f j + f M ≤ f m`
(`TauCeti.sub_one_mul_sum_Ico_add_le_of_mul_le`). In a seminormed additive group `E`, combining this
with the triangle inequality when `1 ≤ c` and `c * ‖u k‖ ≤ ‖u (k + 1)‖` on `Finset.Ico M m` yields
`(c - 2) * ‖u m‖ + ‖u M‖ ≤ (c - 1) * ‖∑ j ∈ Finset.Ico M (m + 1), u j‖`.

At `c = 2`, the bound specializes to `‖u M‖ ≤ ‖∑ j ∈ Finset.Ico M (m + 1), u j‖`. Thus if a
sequence `u : ℕ → E` grows by at least a factor of `c ≥ 2` from each index to the next
(`c * ‖u m‖ ≤ ‖u (m + 1)‖` eventually) and has norms that do not vanish eventually
(`∃ᶠ m in atTop, 0 < ‖u m‖`), then the norms of the partial sums `∑ m ∈ Finset.Ico N n, u m` tend
to `+∞` as `n → ∞` for every starting index `N`.

In particular, this applies whenever `u =o[atTop] fun m ↦ u (m + 1)` and `0 < ‖u m‖` frequently
(for instance when `u m / u (m + 1) → 0` for a sequence of nonzero elements in a normed division
ring). In continued-fraction theory, this is the criterion by which super-exponential growth of the
reduction-of-order summands implies divergence of the reduction-of-order series in Pincherle's
theorem.

## Main results

* `TauCeti.sub_two_mul_norm_add_norm_le_sub_one_mul_norm_sum_Ico_succ_of_mul_norm_le`: if `1 ≤ c`
  and `c * ‖u k‖ ≤ ‖u (k + 1)‖` for `k ∈ Finset.Ico M m` (`M ≤ m`), then
  `(c - 2) * ‖u m‖ + ‖u M‖ ≤ (c - 1) * ‖∑ j ∈ Finset.Ico M (m + 1), u j‖`.
* `TauCeti.tendsto_norm_atTop_of_mul_norm_le`: if `1 < c`, `c * ‖u m‖ ≤ ‖u (m + 1)‖` eventually,
  and `0 < ‖u m‖` frequently, then `‖u n‖ → ∞`.
* `TauCeti.tendsto_norm_sum_Ico_atTop_of_mul_norm_le`: if `2 ≤ c`, `c * ‖u m‖ ≤ ‖u (m + 1)‖`
  eventually, and `0 < ‖u m‖` frequently, then `‖∑ m ∈ Finset.Ico N n, u m‖ → ∞`.
* `Asymptotics.IsLittleO.tendsto_norm_atTop_of_succ`: if `u =o[atTop] fun m ↦ u (m + 1)` and
  `0 < ‖u m‖` frequently, then `‖u n‖ → ∞`.
* `Asymptotics.IsLittleO.eventually_norm_pos_of_succ`: under the same hypotheses, `0 < ‖u m‖`
  eventually.
* `Asymptotics.IsLittleO.tendsto_norm_sum_Ico_atTop_of_succ`: under the same hypotheses,
  `‖∑ m ∈ Finset.Ico N n, u m‖ → ∞` for every `N`.
-/

public section

open Asymptotics Filter Finset

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
  have hsplit : u m = (∑ j ∈ Ico M (m + 1), u j) - ∑ j ∈ Ico M m, u j := by
    rw [sum_Ico_succ_top hm, add_sub_cancel_left]
  have htri : ‖u m‖ ≤ ‖∑ j ∈ Ico M (m + 1), u j‖ + ∑ j ∈ Ico M m, ‖u j‖ :=
    calc ‖u m‖ = ‖(∑ j ∈ Ico M (m + 1), u j) - ∑ j ∈ Ico M m, u j‖ := congrArg norm hsplit
      _ ≤ ‖∑ j ∈ Ico M (m + 1), u j‖ + ‖∑ j ∈ Ico M m, u j‖ := norm_sub_le _ _
      _ ≤ ‖∑ j ∈ Ico M (m + 1), u j‖ + ∑ j ∈ Ico M m, ‖u j‖ := by
          gcongr
          exact norm_sum_le _ _
  calc (c - 2) * ‖u m‖ + ‖u M‖
      = (c - 1) * ‖u m‖ - ‖u m‖ + ‖u M‖ := by ring
    _ ≤ ((c - 1) * ‖∑ j ∈ Ico M (m + 1), u j‖ + (c - 1) * ∑ j ∈ Ico M m, ‖u j‖) -
          ((c - 1) * ∑ j ∈ Ico M m, ‖u j‖ + ‖u M‖) + ‖u M‖ := by
        gcongr
        rw [← mul_add]
        exact mul_le_mul_of_nonneg_left htri (sub_nonneg.2 hc)
    _ = (c - 1) * ‖∑ j ∈ Ico M (m + 1), u j‖ := by ring

/-- If `1 < c`, `c * ‖u m‖ ≤ ‖u (m + 1)‖` eventually, and `0 < ‖u m‖` frequently, then `‖u n‖ → +∞`
as `n → ∞`. -/
theorem tendsto_norm_atTop_of_mul_norm_le {E : Type*} [Norm E]
    {u : ℕ → E} {c : ℝ} (hc : 1 < c)
    (hstep : ∀ᶠ m in atTop, c * ‖u m‖ ≤ ‖u (m + 1)‖)
    (hne : ∃ᶠ m in atTop, 0 < ‖u m‖) :
    Tendsto (fun n ↦ ‖u n‖) atTop atTop := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hstep
  obtain ⟨M, hpos, hM⟩ := (hne.and_eventually (eventually_ge_atTop M₀)).exists
  exact (tendsto_add_atTop_iff_nat M).1 <|
    tendsto_atTop_of_geom_le (v := fun n ↦ ‖u (n + M)‖) (by simpa using hpos) hc
      fun n ↦ by simpa only [Nat.add_right_comm] using hM₀ (n + M) (by omega)

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
    tendsto_norm_atTop_of_mul_norm_le one_lt_two hstep2 hne
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
    have hsplit : ∑ j ∈ Ico M (m + 1), u j =
        (∑ j ∈ Ico N (m + 1), u j) - ∑ j ∈ Ico N M, u j := by
      rw [← sum_Ico_consecutive u hNM (hMm.trans m.le_succ), add_sub_cancel_left]
    have htri : ‖∑ j ∈ Ico M (m + 1), u j‖ ≤
        ‖∑ j ∈ Ico N (m + 1), u j‖ + ‖∑ j ∈ Ico N M, u j‖ := by
      rw [hsplit]
      exact norm_sub_le _ _
    linarith [hM₁ M hM₁M]

end TauCeti

namespace Asymptotics.IsLittleO

/-- If `u =o[atTop] fun m ↦ u (m + 1)` and `0 < ‖u m‖` frequently, then `‖u n‖ → ∞`. -/
theorem tendsto_norm_atTop_of_succ {E : Type*} [Norm E]
    {u : ℕ → E} (hu : u =o[atTop] fun m ↦ u (m + 1))
    (hne : ∃ᶠ m in atTop, 0 < ‖u m‖) :
    Tendsto (fun n ↦ ‖u n‖) atTop atTop :=
  TauCeti.tendsto_norm_atTop_of_mul_norm_le one_lt_two
    ((isBigOWith_inv zero_lt_two).1 (hu.def' (inv_pos.2 zero_lt_two))) hne

/-- If `u =o[atTop] fun m ↦ u (m + 1)` and `0 < ‖u m‖` frequently, then `0 < ‖u m‖` eventually. -/
theorem eventually_norm_pos_of_succ {E : Type*} [Norm E]
    {u : ℕ → E} (hu : u =o[atTop] fun m ↦ u (m + 1))
    (hne : ∃ᶠ m in atTop, 0 < ‖u m‖) :
    ∀ᶠ m in atTop, 0 < ‖u m‖ :=
  (hu.tendsto_norm_atTop_of_succ hne).eventually_gt_atTop 0

/-- If `u =o[atTop] fun m ↦ u (m + 1)` and `0 < ‖u m‖` frequently, then the norms of the partial
sums `∑ m ∈ Ico N n, u m` tend to `+∞` for every starting index `N`. -/
theorem tendsto_norm_sum_Ico_atTop_of_succ {E : Type*} [SeminormedAddCommGroup E]
    {u : ℕ → E} (hu : u =o[atTop] fun m ↦ u (m + 1))
    (hne : ∃ᶠ m in atTop, 0 < ‖u m‖) (N : ℕ) :
    Tendsto (fun n ↦ ‖∑ m ∈ Ico N n, u m‖) atTop atTop :=
  TauCeti.tendsto_norm_sum_Ico_atTop_of_mul_norm_le le_rfl
    ((isBigOWith_inv zero_lt_two).1 (hu.def' (inv_pos.2 zero_lt_two))) hne N

end Asymptotics.IsLittleO
