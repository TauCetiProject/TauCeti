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

If a sequence `u : ℕ → E` in a seminormed additive group grows faster than some geometric ratio
`c > 2` from each index to the next (`c * ‖u m‖ ≤ ‖u (m + 1)‖` eventually) and has norms that do
not vanish eventually (`∃ᶠ m in atTop, 0 < ‖u m‖`), then each term `u m` eventually dominates the
sum of all preceding terms up to a factor `< 1`, so the norms of the partial sums
`∑ m ∈ Finset.Ico N n, u m` tend to `+∞` as `n → ∞` for every starting index `N`.

In particular, this applies whenever `u =o[atTop] fun m ↦ u (m + 1)` and `0 < ‖u m‖` frequently
(for instance when `u m / u (m + 1) → 0` for a sequence of nonzero elements in a normed division
ring). In continued-fraction theory, this is the criterion by which super-exponential growth of a
recessive solution implies divergence of the reduction-of-order series in Pincherle's theorem.

## Main results

* `TauCeti.tendsto_norm_atTop_of_mul_norm_le`: if `1 < c`, `c * ‖u m‖ ≤ ‖u (m + 1)‖` eventually,
  and `0 < ‖u m‖` frequently, then `‖u n‖ → ∞`.
* `TauCeti.tendsto_norm_sum_Ico_atTop_of_mul_norm_le`: if `2 < c`, `c * ‖u m‖ ≤ ‖u (m + 1)‖`
  eventually, and `0 < ‖u m‖` frequently, then `‖∑ m ∈ Finset.Ico N n, u m‖ → ∞`.
* `Asymptotics.IsLittleO.eventually_norm_pos_of_succ`: if `u =o[atTop] fun m ↦ u (m + 1)` and
  `0 < ‖u m‖` frequently, then `0 < ‖u m‖` eventually.
* `Asymptotics.IsLittleO.tendsto_norm_atTop_of_succ`: under the same hypotheses, `‖u n‖ → ∞`.
* `Asymptotics.IsLittleO.tendsto_norm_sum_Ico_atTop`: under the same hypotheses,
  `‖∑ m ∈ Finset.Ico N n, u m‖ → ∞` for every `N`.
-/

public section

open Asymptotics Filter Finset

namespace TauCeti

/-- Along a sequence satisfying `c * ‖u m‖ ≤ ‖u (m + 1)‖` from `M` onwards with `1 ≤ c`, the norms
grow at least geometrically as `c ^ (m - M) * ‖u M‖` and satisfy
`(c - 1) * ∑ j ∈ Ico M m, ‖u j‖ ≤ ‖u m‖`. -/
private theorem pow_mul_le_and_mul_sum_Ico_norm_le {E : Type*} [SeminormedAddCommGroup E]
    {u : ℕ → E} {c : ℝ} (hc : 1 ≤ c) {M : ℕ}
    (hstep : ∀ m ≥ M, c * ‖u m‖ ≤ ‖u (m + 1)‖) {m : ℕ} (hm : M ≤ m) :
    c ^ (m - M) * ‖u M‖ ≤ ‖u m‖ ∧ (c - 1) * ∑ j ∈ Ico M m, ‖u j‖ ≤ ‖u m‖ := by
  induction m, hm using Nat.le_induction with
  | base => simp
  | succ m hm ih =>
    have hc0 : 0 ≤ c := by linarith
    have hstep_m := hstep m hm
    refine ⟨?_, ?_⟩
    · rw [Nat.succ_sub hm, pow_succ', mul_assoc]
      exact (mul_le_mul_of_nonneg_left ih.1 hc0).trans hstep_m
    · rw [sum_Ico_succ_top hm, mul_add]
      linarith [ih.2]

/-- If `1 < c`, `c * ‖u m‖ ≤ ‖u (m + 1)‖` eventually, and `0 < ‖u m‖` frequently, then `‖u n‖ → +∞`
as `n → ∞`. -/
theorem tendsto_norm_atTop_of_mul_norm_le {E : Type*} [SeminormedAddCommGroup E]
    {u : ℕ → E} {c : ℝ} (hc : 1 < c)
    (hstep : ∀ᶠ m in atTop, c * ‖u m‖ ≤ ‖u (m + 1)‖)
    (hne : ∃ᶠ m in atTop, 0 < ‖u m‖) :
    Tendsto (fun n ↦ ‖u n‖) atTop atTop := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hstep
  obtain ⟨M, hpos, hM⟩ := (hne.and_eventually (eventually_ge_atTop M₀)).exists
  refine tendsto_atTop_mono' atTop (f₁ := fun n ↦ c ^ (n - M) * ‖u M‖) ?_
    (((tendsto_pow_atTop_atTop_of_one_lt hc).comp
      (tendsto_sub_atTop_nat M)).atTop_mul_const hpos)
  filter_upwards [eventually_ge_atTop M] with n hn
  exact (pow_mul_le_and_mul_sum_Ico_norm_le hc.le (fun m hm ↦ hM₀ m (hM.trans hm)) hn).1

/-- If `c > 2`, `c * ‖u m‖ ≤ ‖u (m + 1)‖` eventually, and `0 < ‖u m‖` frequently, then the norms
of the partial sums `∑ m ∈ Ico N n, u m` tend to `+∞` for every starting index `N`. -/
theorem tendsto_norm_sum_Ico_atTop_of_mul_norm_le {E : Type*} [SeminormedAddCommGroup E]
    {u : ℕ → E} {c : ℝ} (hc : 2 < c)
    (hstep : ∀ᶠ m in atTop, c * ‖u m‖ ≤ ‖u (m + 1)‖)
    (hne : ∃ᶠ m in atTop, 0 < ‖u m‖) (N : ℕ) :
    Tendsto (fun n ↦ ‖∑ m ∈ Ico N n, u m‖) atTop atTop := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hstep
  obtain ⟨M, -, hM⟩ := (hne.and_eventually (eventually_ge_atTop (max N M₀))).exists
  have hNM : N ≤ M := (le_max_left N M₀).trans hM
  have hM₀M : M₀ ≤ M := (le_max_right N M₀).trans hM
  have hstepM : ∀ m ≥ M, c * ‖u m‖ ≤ ‖u (m + 1)‖ := fun m hm ↦ hM₀ m (hM₀M.trans hm)
  have hnorm_atTop : Tendsto (fun m ↦ ‖u m‖) atTop atTop :=
    tendsto_norm_atTop_of_mul_norm_le (by linarith) hstep hne
  -- Bound `(c - 1) * ‖∑ j ∈ Ico N n, u j‖` below by `(c - 2) * ‖u (n - 1)‖ - const`.
  set B : ℝ := ‖∑ j ∈ Ico N M, u j‖
  have hlower : ∀ᶠ n in atTop,
      ((c - 2) * ‖u (n - 1)‖ - (c - 1) * B) / (c - 1) ≤ ‖∑ j ∈ Ico N n, u j‖ := by
    filter_upwards [eventually_ge_atTop (M + 1)] with n hn
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le' (Nat.one_le_of_lt hn)
    have hm : M ≤ m := by omega
    have hsplit : ∑ j ∈ Ico N (m + 1), u j =
        (∑ j ∈ Ico N M, u j) + (∑ j ∈ Ico M m, u j) + u m := by
      rw [sum_Ico_succ_top (hNM.trans hm), ← sum_Ico_consecutive u hNM hm]
    have htri : ‖u m‖ ≤ ‖∑ j ∈ Ico N (m + 1), u j‖ + B + ∑ j ∈ Ico M m, ‖u j‖ := by
      have heq : u m = (∑ j ∈ Ico N (m + 1), u j) - (∑ j ∈ Ico N M, u j) - ∑ j ∈ Ico M m, u j := by
        rw [hsplit]; abel
      calc ‖u m‖ = ‖(∑ j ∈ Ico N (m + 1), u j) - (∑ j ∈ Ico N M, u j) - ∑ j ∈ Ico M m, u j‖ :=
            congrArg norm heq
        _ ≤ ‖(∑ j ∈ Ico N (m + 1), u j) - ∑ j ∈ Ico N M, u j‖ + ‖∑ j ∈ Ico M m, u j‖ :=
            norm_sub_le _ _
        _ ≤ ‖∑ j ∈ Ico N (m + 1), u j‖ + B + ∑ j ∈ Ico M m, ‖u j‖ := by
            gcongr
            · exact norm_sub_le _ _
            · exact norm_sum_le _ _
    have htail := (pow_mul_le_and_mul_sum_Ico_norm_le (by linarith) hstepM hm).2
    rw [Nat.add_sub_cancel, div_le_iff₀ (by linarith)]
    nlinarith
  refine tendsto_atTop_mono' atTop hlower ?_
  exact (((hnorm_atTop.comp (tendsto_sub_atTop_nat 1)).const_mul_atTop (by linarith)).atTop_add
    tendsto_const_nhds).atTop_div_const (by linarith)

end TauCeti

namespace Asymptotics.IsLittleO

/-- If `u =o[atTop] fun m ↦ u (m + 1)`, then eventually `3 * ‖u m‖ ≤ ‖u (m + 1)‖`. -/
private theorem eventually_three_mul_norm_le {E : Type*} [SeminormedAddCommGroup E]
    {u : ℕ → E} (hu : u =o[atTop] fun m ↦ u (m + 1)) :
    ∀ᶠ m in atTop, 3 * ‖u m‖ ≤ ‖u (m + 1)‖ := by
  filter_upwards [hu.def (by positivity : (0 : ℝ) < 1 / 3)] with m hm
  linarith

/-- If `u =o[atTop] fun m ↦ u (m + 1)` and `0 < ‖u m‖` frequently, then `0 < ‖u m‖` eventually. -/
theorem eventually_norm_pos_of_succ {E : Type*} [SeminormedAddCommGroup E]
    {u : ℕ → E} (hu : u =o[atTop] fun m ↦ u (m + 1))
    (hne : ∃ᶠ m in atTop, 0 < ‖u m‖) :
    ∀ᶠ m in atTop, 0 < ‖u m‖ := by
  obtain ⟨M₀, hM₀⟩ := eventually_atTop.1 hu.eventually_three_mul_norm_le
  obtain ⟨M, hpos, hM⟩ := (hne.and_eventually (eventually_ge_atTop M₀)).exists
  filter_upwards [eventually_ge_atTop M] with m hm
  induction m, hm using Nat.le_induction with
  | base => exact hpos
  | succ m hm ih => linarith [hM₀ m (hM.trans hm)]

/-- If `u =o[atTop] fun m ↦ u (m + 1)` and `0 < ‖u m‖` frequently, then `‖u n‖ → ∞`. -/
theorem tendsto_norm_atTop_of_succ {E : Type*} [SeminormedAddCommGroup E]
    {u : ℕ → E} (hu : u =o[atTop] fun m ↦ u (m + 1))
    (hne : ∃ᶠ m in atTop, 0 < ‖u m‖) :
    Tendsto (fun n ↦ ‖u n‖) atTop atTop :=
  TauCeti.tendsto_norm_atTop_of_mul_norm_le (by norm_num) hu.eventually_three_mul_norm_le hne

/-- If `u =o[atTop] fun m ↦ u (m + 1)` and `0 < ‖u m‖` frequently, then the norms of the partial
sums `∑ m ∈ Ico N n, u m` tend to `+∞` for every starting index `N`. -/
theorem tendsto_norm_sum_Ico_atTop {E : Type*} [SeminormedAddCommGroup E]
    {u : ℕ → E} (hu : u =o[atTop] fun m ↦ u (m + 1))
    (hne : ∃ᶠ m in atTop, 0 < ‖u m‖) (N : ℕ) :
    Tendsto (fun n ↦ ‖∑ m ∈ Ico N n, u m‖) atTop atTop :=
  TauCeti.tendsto_norm_sum_Ico_atTop_of_mul_norm_le (by norm_num)
    hu.eventually_three_mul_norm_le hne N

end Asymptotics.IsLittleO
