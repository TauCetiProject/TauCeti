/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import Mathlib.Analysis.SpecialFunctions.SmoothTransition
public import Mathlib.Analysis.Calculus.ContDiff.Deriv
public import Mathlib.Analysis.Calculus.Deriv.Slope
public import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# A smooth increasing exhaustion profile

`Real.radialExhaustionProfile` is constant on `(-∞, 1/2]`, equals `1 + r` on `[1, ∞)`,
and is smooth and nondecreasing. Both derivatives are bounded uniformly on the real line.
The exponentially rescaled profile has the corresponding growth and derivative bounds.
These are scalar ingredients for distance exhaustion barriers in noncompact maximum principles;
constructing smooth local distance supports remains a separate geometric step.

## References

* [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions).
* [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public section

open Set Filter Topology
open scoped ContDiff

namespace Real

/-- A smooth nondecreasing radial profile, equal to one up to radius one-half
and to one plus the radius from radius one onward. -/
noncomputable def radialExhaustionProfile (r : ℝ) : ℝ :=
  1 + r * Real.smoothTransition (2 * r - 1)

/-- The radial exhaustion profile is infinitely differentiable on the whole real line. -/
theorem radialExhaustionProfile_contDiff : ContDiff ℝ ∞ radialExhaustionProfile :=
  contDiff_const.add (contDiff_id.mul (Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul contDiff_id).sub contDiff_const)))

/-- The profile is constant on the inner plateau, including its endpoint. -/
theorem radialExhaustionProfile_eq_one {r : ℝ} (hr : r ≤ 1 / 2) :
    radialExhaustionProfile r = 1 := by
  simp only [radialExhaustionProfile,
    Real.smoothTransition.zero_of_nonpos (by linarith : 2 * r - 1 ≤ 0),
    mul_zero, add_zero]

/-- The profile is affine on the outer region, including radius one. -/
theorem radialExhaustionProfile_eq_add {r : ℝ} (hr : 1 ≤ r) :
    radialExhaustionProfile r = 1 + r := by
  simp only [radialExhaustionProfile,
    Real.smoothTransition.one_of_one_le (by linarith : 1 ≤ 2 * r - 1), mul_one]

/-- The profile is everywhere at least one, including at negative arguments. -/
theorem one_le_radialExhaustionProfile (r : ℝ) : 1 ≤ radialExhaustionProfile r := by
  by_cases hr : r ≤ 1 / 2
  · rw [radialExhaustionProfile_eq_one hr]
  · exact le_add_of_nonneg_right
      (mul_nonneg (by linarith) (Real.smoothTransition.nonneg _))

/-- The profile is nondecreasing, so it preserves the order of touching upper supports. -/
theorem radialExhaustionProfile_monotone : Monotone radialExhaustionProfile := by
  intro r s hrs
  by_cases hr : r ≤ 1 / 2
  · rw [radialExhaustionProfile_eq_one hr]
    exact one_le_radialExhaustionProfile s
  · change 1 + r * Real.smoothTransition (2 * r - 1) ≤
      1 + s * Real.smoothTransition (2 * s - 1)
    simpa only [add_comm] using add_le_add_left
      (mul_le_mul hrs (Real.smoothTransition.monotone (by linarith : 2 * r - 1 ≤ 2 * s - 1))
        (Real.smoothTransition.nonneg (2 * r - 1)) (by linarith)) 1

/-- The profile dominates its argument on the whole real line. -/
theorem le_radialExhaustionProfile (r : ℝ) : r ≤ radialExhaustionProfile r := by
  by_cases h : r ≤ 1
  · exact h.trans (one_le_radialExhaustionProfile r)
  · rw [radialExhaustionProfile_eq_add (le_of_not_ge h)]
    linarith

/-- On nonnegative arguments the profile grows at most as one plus the radius. -/
theorem radialExhaustionProfile_le_add {r : ℝ} (hr : 0 ≤ r) :
    radialExhaustionProfile r ≤ 1 + r := by
  change 1 + r * Real.smoothTransition (2 * r - 1) ≤ 1 + r
  have h : r * Real.smoothTransition (2 * r - 1) ≤ r := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (Real.smoothTransition.le_one (2 * r - 1)) hr
  simpa only [add_comm] using add_le_add_left h 1

/-- The derivative is nonnegative everywhere; the inner plateau causes no exception. -/
theorem radialExhaustionProfile_deriv_nonneg (r : ℝ) :
    0 ≤ deriv radialExhaustionProfile r := radialExhaustionProfile_monotone.deriv_nonneg

private theorem profile_derivs_outside {r : ℝ} (hr : r ∉ Icc (1 / 2 : ℝ) 1) :
    (deriv radialExhaustionProfile r = 0 ∨ deriv radialExhaustionProfile r = 1) ∧
      deriv (deriv radialExhaustionProfile) r = 0 := by
  by_cases hleft : r < 1 / 2
  · have h : radialExhaustionProfile =ᶠ[𝓝 r] (fun _ ↦ (1 : ℝ)) := by
      filter_upwards [gt_mem_nhds hleft] with s hs
      exact radialExhaustionProfile_eq_one hs.le
    constructor
    · exact Or.inl (by rw [h.deriv_eq, deriv_const])
    · rw [h.deriv.deriv_eq, deriv_const', deriv_const]
  · have hright : 1 < r := lt_of_not_ge (fun h ↦ hr ⟨le_of_not_gt hleft, h⟩)
    have h : radialExhaustionProfile =ᶠ[𝓝 r] (fun s ↦ (1 : ℝ) + s) := by
      filter_upwards [lt_mem_nhds hright] with s hs
      exact radialExhaustionProfile_eq_add hs.le
    constructor
    · exact Or.inr (by rw [h.deriv_eq, deriv_const_add_id])
    · rw [h.deriv.deriv_eq, deriv_const_add_id', deriv_const]

/-- A single universal constant, at least one, bounds both absolute derivatives.
Compactness is used only on the transition interval; both tails are explicit. -/
theorem exists_radialExhaustionProfile_deriv_bounds :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ r : ℝ,
      |deriv radialExhaustionProfile r| ≤ C ∧
        |deriv (deriv radialExhaustionProfile) r| ≤ C := by
  have hfirst : ContDiff ℝ ∞ (deriv radialExhaustionProfile) :=
    (contDiff_infty_iff_deriv.mp radialExhaustionProfile_contDiff).2
  have hsecond : ContDiff ℝ ∞ (deriv (deriv radialExhaustionProfile)) :=
    (contDiff_infty_iff_deriv.mp hfirst).2
  obtain ⟨B, hB⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hfirst.continuous.continuousOn (s := Icc (1 / 2 : ℝ) 1))
  obtain ⟨D, hD⟩ := isCompact_Icc.exists_bound_of_continuousOn
    (hsecond.continuous.continuousOn (s := Icc (1 / 2 : ℝ) 1))
  refine ⟨max 1 (max B D), le_max_left _ _, fun r ↦ ?_⟩
  by_cases hr : r ∈ Icc (1 / 2 : ℝ) 1
  · constructor
    · have hb : |deriv radialExhaustionProfile r| ≤ B := by
        simpa only [Real.norm_eq_abs] using hB r hr
      exact hb.trans
        ((le_max_left B D).trans (le_max_right _ _))
    · have hd : |deriv (deriv radialExhaustionProfile) r| ≤ D := by
        simpa only [Real.norm_eq_abs] using hD r hr
      exact hd.trans
        ((le_max_right B D).trans (le_max_right _ _))
  · obtain ⟨h, hsecond⟩ := profile_derivs_outside hr
    constructor
    · rcases h with h | h
      · rw [h, abs_zero]
        exact zero_le_one.trans (le_max_left _ _)
      · rw [h, abs_one]
        exact le_max_left _ _
    · rw [hsecond, abs_zero]
      exact zero_le_one.trans (le_max_left _ _)

/-- First derivative of the profile after any constant radial rescaling. -/
theorem radialExhaustionProfile_scaled_deriv (a r : ℝ) :
    deriv (fun s ↦ radialExhaustionProfile (a * s)) r =
      a * deriv radialExhaustionProfile (a * r) := by
  have h := (radialExhaustionProfile_contDiff.differentiable (by simp) (a * r)).hasDerivAt.comp r
    ((hasDerivAt_id r).const_mul a)
  simpa only [Function.comp_def, mul_one, mul_comm] using h.deriv

/-- Second derivative of the profile after any constant radial rescaling. -/
theorem radialExhaustionProfile_scaled_second_deriv (a r : ℝ) :
    deriv (deriv (fun s ↦ radialExhaustionProfile (a * s))) r =
      a ^ 2 * deriv (deriv radialExhaustionProfile) (a * r) := by
  have he : deriv (fun s ↦ radialExhaustionProfile (a * s)) =
      fun s ↦ a * deriv radialExhaustionProfile (a * s) :=
    funext (radialExhaustionProfile_scaled_deriv a)
  rw [he]
  have hd := (contDiff_infty_iff_deriv.mp radialExhaustionProfile_contDiff).2
  have h := ((hd.differentiable (by simp) (a * r)).hasDerivAt.comp r
    ((hasDerivAt_id r).const_mul a)).const_mul a
  simpa only [Function.comp_def, mul_one, pow_two, mul_assoc, mul_left_comm, mul_comm] using h.deriv

/-- The scalar part `S(exp(c*t)*r)` of an evolving-distance exhaustion barrier.
For Ricci-flow applications one takes `c = n*K` and supplies the actual distance. -/
noncomputable def rescaledRadialExhaustionProfile (c t r : ℝ) : ℝ :=
  radialExhaustionProfile (Real.exp (c * t) * r)

/-- Exponential rescaling preserves the profile's lower and linear growth bounds. -/
theorem rescaledRadialExhaustionProfile_growth (c t : ℝ) {r : ℝ} (hr : 0 ≤ r) :
    1 ≤ rescaledRadialExhaustionProfile c t r ∧
      Real.exp (c * t) * r ≤ rescaledRadialExhaustionProfile c t r ∧
      rescaledRadialExhaustionProfile c t r ≤ 1 + Real.exp (c * t) * r := by
  have h := mul_nonneg (Real.exp_pos (c * t)).le hr
  exact ⟨one_le_radialExhaustionProfile _, le_radialExhaustionProfile _,
    radialExhaustionProfile_le_add h⟩

/-- The actual exponential-rescaling consumer has uniform radial derivative bounds
with the exact first and second scaling factors, for all real times and coefficients. -/
theorem exists_rescaledRadialExhaustionProfile_deriv_bounds :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ c t r : ℝ,
      |deriv (rescaledRadialExhaustionProfile c t) r| ≤ C * Real.exp (c * t) ∧
      |deriv (deriv (rescaledRadialExhaustionProfile c t)) r| ≤
        C * Real.exp (c * t) ^ 2 := by
  obtain ⟨C, hC, h⟩ := exists_radialExhaustionProfile_deriv_bounds
  refine ⟨C, hC, fun c t r ↦ ?_⟩
  change |deriv (fun s ↦ radialExhaustionProfile (Real.exp (c * t) * s)) r| ≤ _ ∧
    |deriv (deriv (fun s ↦ radialExhaustionProfile (Real.exp (c * t) * s))) r| ≤ _
  rw [radialExhaustionProfile_scaled_deriv, radialExhaustionProfile_scaled_second_deriv]
  simp only [abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
  constructor
  · simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (h (Real.exp (c * t) * r)).1 (Real.exp_pos _).le
  · simpa only [mul_comm] using
      mul_le_mul_of_nonneg_left (h (Real.exp (c * t) * r)).2
        (sq_nonneg (Real.exp (c * t)))

end Real
