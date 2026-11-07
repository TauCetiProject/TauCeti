/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
module

public import TauCeti.Analysis.Complex.GrowthOrder
public import Mathlib.Analysis.Complex.JensenFormula

/-!
# Zero counts from the order of growth

An entire function of order at most `A` that is nonzero at the origin has
`O(R ^ B)` zeros in the closed disk of radius `R`, counted with multiplicity,
for every `B > A`. The count is the finite sum of Mathlib's native divisor on
the disk. Its summands are nonnegative because the function is entire.

The proof applies Mathlib's `AnalyticOnNhd.sum_divisor_le` to disks of radii
`R` and `2 * R`, using the growth bound from `TauCeti.OrderLE`. Negative
exponents reduce to constants by the existing Liouville theorem. This is
the counting estimate used to obtain convergence of sums over the zeros of
an entire function of finite order.

## References

* H. Davenport, *Multiplicative Number Theory*, 3rd ed., Chapter 11.
-/

public section

open Complex Filter Metric Bornology Topology
open scoped BigOperators

namespace TauCeti

variable {f : ℂ → ℂ} {A B : ℝ}

private theorem OrderLE.eventually_sum_divisor_le (h : OrderLE f A) (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) (hAB : A < B) (hB : 0 ≤ B) :
    ∃ C > 0, ∀ᶠ R : ℝ in atTop,
      ((∑ᶠ z, MeromorphicOn.divisor f (closedBall 0 R) z : ℤ) : ℝ) ≤ C * R ^ B := by
  obtain ⟨c, _, hb⟩ := (h.isBigO hAB).exists_pos
  obtain ⟨L, _, hL⟩ := Filter.hasBasis_cobounded_norm.mem_iff.mp hb.bound
  let c' : ℝ := max c 1
  have hc' : 0 < c' := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  let C : ℝ := (|Real.log c' - Real.log ‖f 0‖| + 2 ^ B) / Real.log 2
  refine ⟨C, by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (max L 1)] with R hR
  have hR1 : 1 ≤ R := (le_max_right _ _).trans hR
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  have hRL : L ≤ R := (le_max_left _ _).trans hR
  let M : ℝ := c' * Real.exp ((2 * R) ^ B)
  have hM : 1 ≤ M := by
    exact one_le_mul_of_one_le_of_one_le (le_max_right _ _)
      (Real.one_le_exp (Real.rpow_nonneg (by positivity) _))
  have ha : AnalyticOnNhd ℂ f (closedBall 0 |2 * R|) := fun z _ ↦ hf.analyticAt z
  have hfM : ∀ z ∈ sphere (0 : ℂ) |2 * R|, ‖f z‖ ≤ M := by
    intro z hz
    have hzR : ‖z‖ = 2 * R := by
      simpa [mem_sphere_iff_norm, abs_of_pos (by positivity : 0 < 2 * R)] using hz
    have hzL : L ≤ ‖z‖ := by rw [hzR]; linarith
    have hbz : ‖f z‖ ≤ c * Real.exp ((2 * R) ^ B) := by
      simpa only [Set.mem_ofPred_eq, Real.norm_eq_abs, Real.abs_exp, hzR] using hL hzL
    exact hbz.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.exp_pos _).le)
  have hj := AnalyticOnNhd.sum_divisor_le (r := R) (R := 2 * R)
    (by simpa only [abs_of_pos hR0] using hR0)
    (by rw [abs_of_pos hR0, abs_of_pos (by positivity : 0 < 2 * R)]; linarith)
    hM ha hf0 hfM
  rw [abs_of_pos hR0, mul_div_cancel_right₀ (2 : ℝ) (ne_of_gt hR0)] at hj
  have hfnorm : ‖f 0‖ ≠ 0 := norm_ne_zero_iff.mpr hf0
  have hlogM : Real.log (M / ‖f 0‖) =
      Real.log c' - Real.log ‖f 0‖ + (2 * R) ^ B := by
    rw [Real.log_div (by positivity : M ≠ 0) hfnorm,
      Real.log_mul hc'.ne' (Real.exp_ne_zero _), Real.log_exp]
    ring
  have hpow : 1 ≤ R ^ B := Real.one_le_rpow hR1 hB
  calc
    _ ≤ Real.log (M / ‖f 0‖) / Real.log 2 := hj
    _ ≤ (|Real.log c' - Real.log ‖f 0‖| + 2 ^ B) * R ^ B / Real.log 2 := by
      apply div_le_div_of_nonneg_right _ hlog.le
      rw [hlogM, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hR0.le]
      have habs := le_abs_self (Real.log c' - Real.log ‖f 0‖)
      have hm := mul_le_mul_of_nonneg_left hpow (abs_nonneg (Real.log c' - Real.log ‖f 0‖))
      nlinarith
    _ = C * R ^ B := by dsimp [C]; ring

/-- The zero count, with multiplicity, of an entire function of order at most `A`
is `O(R ^ B)` for every `B > A`, provided the function is nonzero at the origin. -/
theorem OrderLE.isBigO_sum_divisor (h : OrderLE f A) (hf : Differentiable ℂ f)
    (hf0 : f 0 ≠ 0) (hAB : A < B) :
    (fun R : ℝ ↦ ((∑ᶠ z, MeromorphicOn.divisor f (closedBall 0 R) z : ℤ) : ℝ))
      =O[atTop] (fun R : ℝ ↦ R ^ B) := by
  rcases le_or_gt 0 B with hB | hB
  · obtain ⟨C, _, hC⟩ := h.eventually_sum_divisor_le hf hf0 hAB hB
    apply Asymptotics.IsBigO.of_bound C
    filter_upwards [hC, eventually_ge_atTop (0 : ℝ)] with R hR hR0
    have hfa : AnalyticOnNhd ℂ f (closedBall 0 R) := fun z _ ↦ hf.analyticAt z
    have hn : 0 ≤ (∑ᶠ z, MeromorphicOn.divisor f (closedBall 0 R) z : ℤ) :=
      finsum_nonneg (MeromorphicOn.AnalyticOnNhd.divisor_nonneg hfa)
    have hn' : 0 ≤ ((∑ᶠ z, MeromorphicOn.divisor f (closedBall 0 R) z : ℤ) : ℝ) := by
      exact_mod_cast hn
    simpa only [Real.norm_eq_abs, abs_of_nonneg hn',
      abs_of_nonneg (Real.rpow_nonneg hR0 B)] using hR
  · have hc := h.isConst hf (hAB.trans hB)
    have heq : f = fun _ : ℂ ↦ f 0 := funext fun z ↦ hc z 0
    rw [heq]
    simp only [MeromorphicOn.divisor_const, Function.locallyFinsuppWithin.coe_zero, Pi.zero_apply,
      finsum_zero, Int.cast_zero]
    exact Asymptotics.isBigO_zero _ _

end TauCeti
