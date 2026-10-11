/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Algebra.Order.Group.Pointwise.Interval

/-!
# Affine changes of variables in nonnegative interval integrals

The lower integral over an unoriented interval transforms by the reciprocal absolute slope
under an invertible affine change of variables. No measurability hypothesis on the integrand
is needed: the change of variables is a measurable equivalence. This form also handles reversal
of time and infinite integrals, as needed when integrating the speed of a metric curve.
-/

public section

open MeasureTheory Set
open scoped ENNReal Interval

namespace TauCeti

/-- An invertible affine change of variables in a lower integral over an unoriented interval.
The integrand need not be measurable, and either integral may be infinite. -/
theorem setLIntegral_comp_mul_add_uIoc (f : ℝ → ℝ≥0∞) {c : ℝ} (hc : c ≠ 0)
    (d a b : ℝ) :
    ∫⁻ t in Ι a b, f (c * t + d) =
      ENNReal.ofReal |c⁻¹| * ∫⁻ t in Ι (c * a + d) (c * b + d), f t := by
  let e : ℝ ≃ᵐ ℝ :=
    ((Homeomorph.mulLeft₀ c hc).trans (Homeomorph.addRight d)).toMeasurableEquiv
  have he (t : ℝ) : e t = c * t + d := rfl
  have heq : (e : ℝ → ℝ) = (fun t ↦ t + d) ∘ (fun t ↦ c * t) := rfl
  have hmap : volume.map e = ENNReal.ofReal |c⁻¹| • volume := by
    rw [heq, ← Measure.map_map (measurable_add_const d) (measurable_const_mul c),
      Real.map_volume_mul_left hc, Measure.map_smul, map_add_right_eq_self]
    exact (measurable_add_const d).aemeasurable
  have hpre : e ⁻¹' uIcc (c * a + d) (c * b + d) = uIcc a b := by
    rw [heq, preimage_comp, preimage_add_const_uIcc, preimage_const_mul_uIcc hc]
    simp [hc]
  have h := setLIntegral_comp_preimage_of_map_eq_smul hmap f
    (uIcc (c * a + d) (c * b + d))
  rw [hpre] at h
  simpa only [he, uIoc, uIcc, restrict_Ioc_eq_restrict_Icc] using h

end TauCeti
