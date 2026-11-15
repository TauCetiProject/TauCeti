/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.CircleMap
public import Mathlib.MeasureTheory.Function.AbsolutelyContinuous
import Mathlib.MeasureTheory.Integral.CircleIntegral
import TauCeti.MeasureTheory.Function.AbsolutelyContinuous.Comp

/-!
# Absolute continuity of `circleMap`

The complex circle parametrization `circleMap c R` is Lipschitz (`lipschitzWith_circleMap`), hence
absolutely continuous on every parameter interval.

Conversely, an angle function `θ` whose values stay in an open arc of length `2π` is absolutely
continuous as soon as the curve `circleMap c R ∘ θ` is, for `R ≠ 0`: on such an arc the angle is
recovered from the point of the circle by a branch of the logarithm.
-/

public section

open Complex Set
open scoped Real

namespace TauCeti

/-- The circle parametrization `circleMap c R` is absolutely continuous on every real parameter
interval, for arbitrary center `c` and signed radius `R`. -/
theorem absolutelyContinuousOnInterval_circleMap (c : ℂ) (R a b : ℝ) :
    AbsolutelyContinuousOnInterval (circleMap c R) a b :=
  (lipschitzWith_circleMap c R).lipschitzOnWith.absolutelyContinuousOnInterval

/-- An angle function with values in an open arc `(θ₀ - π, θ₀ + π)` is absolutely continuous on
`[a, b]` exactly when the circle it parametrizes is, provided the radius is nonzero. Without a
bound on the range of `θ`, the angle could jump by multiples of `2π` without moving the point
on the circle. -/
theorem absolutelyContinuousOnInterval_circleMap_comp_iff {c : ℂ} {R θ₀ a b : ℝ} {θ : ℝ → ℝ}
    (hR : R ≠ 0) (hθ : MapsTo θ (uIcc a b) (Ioo (θ₀ - π) (θ₀ + π))) :
    AbsolutelyContinuousOnInterval (circleMap c R ∘ θ) a b ↔
      AbsolutelyContinuousOnInterval θ a b := by
  refine ⟨fun h ↦ ?_, (lipschitzWith_circleMap c R).comp_absolutelyContinuousOnInterval⟩
  -- Rotating by `-θ₀` brings the trace into the slit plane, where the principal logarithm
  -- recovers the angle.
  obtain ⟨w, hw⟩ : ∃ w : ℂ, w * (R * exp (θ₀ * I)) = 1 :=
    ⟨_, inv_mul_cancel₀ (mul_ne_zero (ofReal_ne_zero.2 hR) (exp_ne_zero _))⟩
  have hrot (x : ℝ) : (circleMap c R x - c) * w = exp ((x - θ₀ : ℝ) * I) := by
    rw [circleMap_sub_center, circleMap_zero, ofReal_sub, sub_mul, exp_sub,
      eq_div_iff (exp_ne_zero _)]
    linear_combination exp (x * I) * hw
  have hlog {t : ℝ} (ht : t ∈ uIcc a b) :
      log ((circleMap c R (θ t) - c) * w) = (θ t - θ₀ : ℝ) * I := by
    obtain ⟨h₁, h₂⟩ := hθ ht
    rw [hrot, log_exp] <;> simp <;> linarith
  have hslit {t : ℝ} (ht : t ∈ uIcc a b) : (circleMap c R (θ t) - c) * w ∈ slitPlane := by
    obtain ⟨h₁, h₂⟩ := hθ ht
    rw [hrot, exp_mem_slitPlane]
    simp only [mul_im, ofReal_re, I_im, mul_one, ofReal_im, I_re, mul_zero, add_zero]
    rw [(toIocMod_eq_self _).2 ⟨by linarith, by linarith⟩]
    linarith
  have hσ : AbsolutelyContinuousOnInterval (fun t ↦ (circleMap c R (θ t) - c) * w) a b :=
    ((h.sub (LipschitzWith.const c).lipschitzOnWith.absolutelyContinuousOnInterval).const_smul
      w).congr fun t _ ↦ by simp [mul_comm w]
  refine ((imCLM.lipschitzWith.comp_absolutelyContinuousOnInterval (hσ.clog fun _ ↦ hslit)).add
    (LipschitzWith.const θ₀).lipschitzOnWith.absolutelyContinuousOnInterval).congr fun t ht ↦ ?_
  simp only [Pi.add_apply, Function.comp_apply, hlog ht]
  simp

end TauCeti
