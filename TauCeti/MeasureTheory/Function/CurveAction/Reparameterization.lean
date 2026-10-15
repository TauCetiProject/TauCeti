/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.CurveAction.Basic
public import TauCeti.MeasureTheory.Function.MetricDerivative.Reparameterization

/-!
# Affine reparameterization of curve action

Changing time by `t ↦ c * t + d`, with `c ≠ 0`, multiplies `p`-action by `|c| ^ (p - 1)`.
Thus one can normalize a nondegenerate time interval to `[0, 1]`
without losing finite action. Time reversal preserves action, and at `p = 1` every invertible
affine change of time preserves action.

The action formula is valid for arbitrary curves in extended pseudometric spaces, with infinite
values retained and no measurability assumption on the curve.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, Chapter 1.
-/

public section

open MeasureTheory Set
open scoped ENNReal Interval

namespace TauCeti

variable {X : Type*} [PseudoEMetricSpace X]

/-- An invertible affine change of time multiplies `p`-action by `|c| ^ (p - 1)`.
This holds for every real exponent and retains infinite action. -/
theorem curveAction_comp_mul_add (p : ℝ) (γ : ℝ → X) {c : ℝ} (hc : c ≠ 0)
    (d a b : ℝ) :
    curveAction p (fun t ↦ γ (c * t + d)) a b =
      ENNReal.ofReal |c| ^ (p - 1) * curveAction p γ (c * a + d) (c * b + d) := by
  simpa only [curveAction_def] using
    setLIntegral_metricDerivative_comp_mul_add_rpow p γ hc d a b

/-- Finite action is invariant under invertible affine changes of time. -/
@[simp]
theorem curveAction_comp_mul_add_ne_top_iff (p : ℝ) (γ : ℝ → X) {c : ℝ} (hc : c ≠ 0)
    (d a b : ℝ) :
    curveAction p (fun t ↦ γ (c * t + d)) a b ≠ ∞ ↔
      curveAction p γ (c * a + d) (c * b + d) ≠ ∞ := by
  have h0 : ENNReal.ofReal |c| ≠ 0 := by simpa using hc
  rw [curveAction_comp_mul_add p γ hc]
  simp [ENNReal.mul_eq_top, hc,
    ENNReal.rpow_ne_top_of_ne_zero h0 ENNReal.ofReal_ne_top]

/-- Reversing a time interval preserves the action. -/
theorem curveAction_reverse (p : ℝ) (γ : ℝ → X) (a b : ℝ) :
    curveAction p (fun t ↦ γ (a + b - t)) a b = curveAction p γ a b := by
  have h := curveAction_comp_mul_add p γ (c := -1) (by norm_num) (a + b) a b
  have hfun : (fun t : ℝ ↦ γ (-1 * t + (a + b))) = fun t ↦ γ (a + b - t) := by
    ext t; congr 1; ring
  have ha : -1 * a + (a + b) = b := by ring
  have hb : -1 * b + (a + b) = a := by ring
  rw [hfun, ha, hb] at h
  simpa [curveAction_comm p γ b a] using h

/-- Normalizing an interval to `[0, 1]` multiplies action by the interval length to the
power `p - 1`. The two endpoints need not be in increasing order. -/
theorem curveAction_comp_mul_add_zero_one (p : ℝ) (γ : ℝ → X) {a b : ℝ} (hab : a ≠ b) :
    curveAction p (fun t ↦ γ ((b - a) * t + a)) 0 1 =
      ENNReal.ofReal |b - a| ^ (p - 1) * curveAction p γ a b := by
  simpa using curveAction_comp_mul_add p γ (sub_ne_zero.2 hab.symm) a 0 1

end TauCeti
