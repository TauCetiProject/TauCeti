/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Asymptotics.Defs
public import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Algebra.BigOperators.Intervals

/-!
# Norm divergence of partial sums of rapidly growing sequences

If a sequence `u : ℕ → E` in a seminormed additive group grows by at least a factor of `c ≥ 2`
from each index to the next (`c * ‖u m‖ ≤ ‖u (m + 1)‖` eventually) and has norms that do not
vanish eventually (`∃ᶠ m in atTop, 0 < ‖u m‖`), then from any sufficiently large index `M`
onwards each term satisfies `∑ j ∈ Finset.Ico M m, ‖u j‖ + ‖u M‖ ≤ ‖u m‖`, so the norms of the
partial sums `∑ m ∈ Finset.Ico N n, u m` tend to `+∞` as `n → ∞` for every starting index `N`.

In particular, this applies whenever `u =o[atTop] fun m ↦ u (m + 1)` and `0 < ‖u m‖` frequently
(for instance when `u m / u (m + 1) → 0` for a sequence of nonzero elements in a normed division
ring). In continued-fraction theory, this is the criterion by which super-exponential growth of the
reduction-of-order summands implies divergence of the reduction-of-order series in Pincherle's
theorem.

## Main results

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

/-- Along a sequence satisfying `2 * ‖u m‖ ≤ ‖u (m + 1)‖` from `M` onwards,
`∑ j ∈ Ico M m, ‖u j‖ + ‖u M‖ ≤ ‖u m‖` for all `m ≥ M`. -/
private theorem sum_Ico_norm_add_le {E : Type*} [SeminormedAddCommGroup E]
    {u : ℕ → E} {M : ℕ}
    (hstep : ∀ m ≥ M, 2 * ‖u m‖ ≤ ‖u (m + 1)‖) {m : ℕ} (hm : M ≤ m) :
    ∑ j ∈ Ico M m, ‖u j‖ + ‖u M‖ ≤ ‖u m‖ := by
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    rw [sum_Ico_succ_top hm]
    linarith [hstep m hm]

/-- Along a sequence satisfying `2 * ‖u m‖ ≤ ‖u (m + 1)‖` from `M` onwards (`N ≤ M`),
`‖u M‖ ≤ ‖∑ j ∈ Ico N (m + 1), u j‖ + ‖∑ j ∈ Ico N M, u j‖` for all `m ≥ M`. -/
private theorem norm_le_norm_sum_Ico_succ_add {E : Type*} [SeminormedAddCommGroup E]
    {u : ℕ → E} {N M : ℕ} (hNM : N ≤ M)
    (hstep : ∀ m ≥ M, 2 * ‖u m‖ ≤ ‖u (m + 1)‖) {m : ℕ} (hm : M ≤ m) :
    ‖u M‖ ≤ ‖∑ j ∈ Ico N (m + 1), u j‖ + ‖∑ j ∈ Ico N M, u j‖ := by
  have hsplit : u m =
      (∑ j ∈ Ico N (m + 1), u j) - (∑ j ∈ Ico N M, u j) - ∑ j ∈ Ico M m, u j := by
    rw [sum_Ico_succ_top (hNM.trans hm), ← sum_Ico_consecutive u hNM hm]
    abel
  have htri : ‖u m‖ ≤
      ‖∑ j ∈ Ico N (m + 1), u j‖ + ‖∑ j ∈ Ico N M, u j‖ + ∑ j ∈ Ico M m, ‖u j‖ :=
    calc ‖u m‖ = ‖(∑ j ∈ Ico N (m + 1), u j) - (∑ j ∈ Ico N M, u j) - ∑ j ∈ Ico M m, u j‖ :=
          congrArg norm hsplit
      _ ≤ ‖(∑ j ∈ Ico N (m + 1), u j) - ∑ j ∈ Ico N M, u j‖ + ‖∑ j ∈ Ico M m, u j‖ :=
          norm_sub_le _ _
      _ ≤ ‖∑ j ∈ Ico N (m + 1), u j‖ + ‖∑ j ∈ Ico N M, u j‖ + ∑ j ∈ Ico M m, ‖u j‖ := by
          gcongr
          · exact norm_sub_le _ _
          · exact norm_sum_le _ _
  linarith [sum_Ico_norm_add_le hstep hm]

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
    have hstepM : ∀ m ≥ M, 2 * ‖u m‖ ≤ ‖u (m + 1)‖ := fun m hm ↦ hM₀ m (hM₀M.trans hm)
    refine eventually_atTop.2 ⟨M + 1, fun n hn ↦ ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.one_le_of_lt hn)
    linarith [hM₁ M hM₁M, norm_le_norm_sum_Ico_succ_add hNM hstepM (by omega : M ≤ m)]

end TauCeti

namespace Asymptotics.IsLittleO

/-- If `u =o[atTop] fun m ↦ u (m + 1)`, then eventually `3 * ‖u m‖ ≤ ‖u (m + 1)‖`. -/
private theorem eventually_three_mul_norm_le {E : Type*} [Norm E]
    {u : ℕ → E} (hu : u =o[atTop] fun m ↦ u (m + 1)) :
    ∀ᶠ m in atTop, 3 * ‖u m‖ ≤ ‖u (m + 1)‖ := by
  filter_upwards [hu.def (by positivity : (0 : ℝ) < 1 / 3)] with m hm
  linarith

/-- If `u =o[atTop] fun m ↦ u (m + 1)` and `0 < ‖u m‖` frequently, then `‖u n‖ → ∞`. -/
theorem tendsto_norm_atTop_of_succ {E : Type*} [Norm E]
    {u : ℕ → E} (hu : u =o[atTop] fun m ↦ u (m + 1))
    (hne : ∃ᶠ m in atTop, 0 < ‖u m‖) :
    Tendsto (fun n ↦ ‖u n‖) atTop atTop :=
  TauCeti.tendsto_norm_atTop_of_mul_norm_le (by norm_num) hu.eventually_three_mul_norm_le hne

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
  TauCeti.tendsto_norm_sum_Ico_atTop_of_mul_norm_le (by norm_num)
    hu.eventually_three_mul_norm_le hne N

end Asymptotics.IsLittleO
