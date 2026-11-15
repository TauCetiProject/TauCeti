/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Average
public import TauCeti.MeasureTheory.Measure.Real
import Mathlib.Topology.Algebra.Field
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
    (affineHomeomorph c d hc).toMeasurableEquiv
  have heq : (e : ℝ → ℝ) = (fun t ↦ t + d) ∘ (fun t ↦ c * t) := by
    funext t
    simp only [e, Homeomorph.toMeasurableEquiv_coe, affineHomeomorph_apply,
      Function.comp_apply]
  have hmap : volume.map e = ENNReal.ofReal |c⁻¹| • volume := by
    simpa only [heq, Function.comp_def] using map_volume_mul_add hc d
  have hpre : e ⁻¹' uIcc (c * a + d) (c * b + d) = uIcc a b := by
    rw [heq, preimage_comp, preimage_add_const_uIcc, preimage_const_mul_uIcc hc]
    simp [hc]
  have h := setLIntegral_comp_preimage_of_map_eq_smul hmap f
    (uIcc (c * a + d) (c * b + d))
  rw [hpre] at h
  have hrestrict (u v : ℝ) : volume.restrict (Ι u v) = volume.restrict (uIcc u v) :=
    restrict_Ioc_eq_restrict_Icc
  simpa only [heq, Function.comp_def, hrestrict] using h

end TauCeti
