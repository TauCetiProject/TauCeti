/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Topology.Instances.NNReal.Lemmas

/-!
# Multiplicative functions on nonnegative time

A function turning addition of nonnegative times into multiplication is determined by its
first-order behavior at zero. This is useful for generating functions of convolution semigroups.
The argument subdivides each time into equal pieces and uses Mathlib's exponential limit
`Real.tendsto_one_add_pow_exp_of_tendsto`.
-/

public section

open Filter Topology
open scoped NNReal

namespace TauCeti

/-- A multiplicative function on nonnegative time with initial value one and right-hand slope
`a` at zero is `t ↦ exp (a * t)`. No positivity or continuity away from zero is assumed. -/
theorem eq_exp_mul_of_add_eq_mul_of_tendsto_div {f : ℝ≥0 → ℝ} {a : ℝ}
    (h0 : f 0 = 1) (hadd : ∀ s t, f (s + t) = f s * f t)
    (ha : Tendsto (fun h : ℝ≥0 ↦ (f h - 1) / (h : ℝ)) (𝓝[>] 0) (𝓝 a))
    (t : ℝ≥0) : f t = Real.exp (a * t) := by
  by_cases ht : t = 0
  · simp [ht, h0]
  have hpow (s : ℝ≥0) (n : ℕ) : f (n * s) = f s ^ n := by
    induction n with
    | zero => simp [h0]
    | succ n ih => simpa [Nat.cast_add, add_mul, pow_succ] using
        (hadd (n * s) s).trans (congrArg (fun x ↦ x * f s) ih)
  have htime : Tendsto (fun n : ℕ ↦ t / n) atTop (𝓝[>] (0 : ℝ≥0)) := by
    refine tendsto_nhdsWithin_iff.mpr ⟨tendsto_const_div_atTop_nhds_zero_nat t, ?_⟩
    filter_upwards [eventually_gt_atTop 0] with n hn
    exact_mod_cast div_pos (pos_iff_ne_zero.mpr ht : 0 < t)
      (by exact_mod_cast hn : (0 : ℝ≥0) < n)
  have hslope := (ha.comp htime).mul_const (t : ℝ)
  have hscaled : Tendsto (fun n : ℕ ↦ (n : ℝ) * (f (t / n) - 1)) atTop
      (𝓝 (a * t)) := by
    apply hslope.congr'
    filter_upwards [eventually_gt_atTop 0] with n hn
    dsimp only [Function.comp_apply]
    push_cast
    field_simp
  have hlimit := Real.tendsto_one_add_pow_exp_of_tendsto hscaled
  have heq : (fun n : ℕ ↦ (1 + (f (t / n) - 1)) ^ n) =ᶠ[atTop] fun _ ↦ f t := by
    filter_upwards [eventually_gt_atTop 0] with n hn
    rw [add_sub_cancel, ← hpow]
    congr 1
    exact mul_div_cancel₀ t (by exact_mod_cast hn.ne')
  exact tendsto_nhds_unique tendsto_const_nhds (hlimit.congr' heq)

end TauCeti
