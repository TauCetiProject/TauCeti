/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.CurveAction.Basic
public import TauCeti.MeasureTheory.Function.MetricDerivative.Reparameterization
import TauCeti.MeasureTheory.Integral.IntervalIntegral.Affine

/-!
# Affine reparameterization of metric curves and their action

Changing time by `t ↦ c * t + d`, with `c ≠ 0`, preserves absolute continuity and multiplies
`p`-action by `|c| ^ (p - 1)`. Thus one can normalize a nondegenerate time interval to `[0, 1]`
without losing finite action. Time reversal preserves action, and at `p = 1` every invertible
affine change of time preserves action.

The action formula is valid for arbitrary curves in extended pseudometric spaces, with infinite
values retained and no measurability assumption on the curve. Absolute continuity is treated
on pseudometric spaces, the regime of the fundamental theorem for metric curves.

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
  have h0 : ENNReal.ofReal |c| ≠ 0 := by simpa using hc
  have hscale : ENNReal.ofReal |c| ^ p * ENNReal.ofReal |c⁻¹| =
      ENNReal.ofReal |c| ^ (p - 1) := by
    simp [abs_inv, ENNReal.ofReal_inv_of_pos (abs_pos.2 hc),
      ENNReal.rpow_sub p 1 h0 ENNReal.ofReal_ne_top, div_eq_mul_inv]
  rw [curveAction_def, curveAction_def]
  have hpow (t : ℝ) : (ENNReal.ofReal |c| * metricDerivative γ (c * t + d)) ^ p =
      ENNReal.ofReal |c| ^ p * metricDerivative γ (c * t + d) ^ p := by
    simp [ENNReal.mul_rpow_eq_ite, h0]
  simp_rw [metricDerivative_comp_mul_add γ c, hpow]
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero h0 ENNReal.ofReal_ne_top)]
  rw [setLIntegral_comp_mul_add_uIoc (fun t ↦ metricDerivative γ t ^ p) hc d a b]
  rw [← mul_assoc, hscale]

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
theorem curveAction_comp_unitInterval (p : ℝ) (γ : ℝ → X) {a b : ℝ} (hab : a ≠ b) :
    curveAction p (fun t ↦ γ ((b - a) * t + a)) 0 1 =
      ENNReal.ofReal |b - a| ^ (p - 1) * curveAction p γ a b := by
  simpa using curveAction_comp_mul_add p γ (sub_ne_zero.2 hab.symm) a 0 1

section AbsolutelyContinuous

variable {Y : Type*} [PseudoMetricSpace Y] {γ : ℝ → Y} {c d a b : ℝ}

/-- Invertible affine changes of time preserve absolute continuity of metric-valued curves. -/
theorem _root_.AbsolutelyContinuousOnInterval.comp_mul_add
    (hγ : AbsolutelyContinuousOnInterval γ (c * a + d) (c * b + d)) (hc : c ≠ 0) :
    AbsolutelyContinuousOnInterval (fun t ↦ γ (c * t + d)) a b := by
  have hint (s u : ℝ) :
      ∫⁻ t in Ι s u, metricDerivative (fun t ↦ γ (c * t + d)) t =
        ∫⁻ t in Ι (c * s + d) (c * u + d), metricDerivative γ t := by
    simpa [curveAction_def] using curveAction_comp_mul_add 1 γ hc d s u
  have hmem {t : ℝ} (ht : t ∈ uIcc a b) :
      c * t + d ∈ uIcc (c * a + d) (c * b + d) := by
    have hmul : c * t ∈ uIcc (c * a) (c * b) :=
      image_const_mul_uIcc c a b ▸ mem_image_of_mem (c * ·) ht
    have hadd := mem_image_of_mem (fun x : ℝ ↦ x + d) hmul
    rwa [image_add_const_uIcc] at hadd
  refine absolutelyContinuousOnInterval_of_edist_le_lintegral
    (m := metricDerivative (fun t ↦ γ (c * t + d))) ?_ ?_
  · rw [hint]
    exact hγ.lintegral_metricDerivative_lt_top.ne
  · intro s hs u hu
    rw [hint]
    exact hγ.edist_le_lintegral_metricDerivative (hmem hs) (hmem hu)

/-- Absolute continuity on the transformed interval is equivalent to absolute continuity
of the affinely reparameterized curve on the original interval. -/
theorem absolutelyContinuousOnInterval_comp_mul_add_iff (γ : ℝ → Y) {c : ℝ} (hc : c ≠ 0)
    (d a b : ℝ) :
    AbsolutelyContinuousOnInterval (fun t ↦ γ (c * t + d)) a b ↔
      AbsolutelyContinuousOnInterval γ (c * a + d) (c * b + d) := by
  refine ⟨fun h ↦ ?_, fun h ↦ h.comp_mul_add hc⟩
  have hinv (t : ℝ) : c * (c⁻¹ * t + -(c⁻¹ * d)) + d = t := by
    field_simp
    ring
  have ha : c⁻¹ * (c * a + d) + -(c⁻¹ * d) = a := by field_simp; ring
  have hb : c⁻¹ * (c * b + d) + -(c⁻¹ * d) = b := by field_simp; ring
  have h' := (ha ▸ hb ▸ h).comp_mul_add (inv_ne_zero hc)
  simpa only [hinv] using h'

end AbsolutelyContinuous

end TauCeti
