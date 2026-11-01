/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Jacobian
public import TauCeti.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.FDeriv.Affine

/-!
# Affine changes of variables preserving a set

Let `s` be a measurable set of positive finite measure for an additive Haar measure `μ` on a
finite-dimensional real normed space. An affine map `f` with `f '' s = s` multiplies `μ s` by
`|det f.linear|` (`MeasureTheory.Measure.addHaar_image_affineMap`), so this determinant has
absolute value one; in particular `f` is injective. Mathlib's change of variables formula
`MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul` then shows that `f` preserves
integrals over `s`, with no integrability assumption
(`MeasureTheory.setIntegral_comp_continuousAffineMap_of_image_eq`).

Such maps are, for instance, the affine maps of a simplex onto itself that permute its vertices.
This is how two parametrizations of a face of the standard simplex are compared in Stokes'
theorem for a simplex.
-/

public section

open Set
open scoped ENNReal

namespace MeasureTheory

variable {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- An affine map sending a set of positive finite Haar measure onto itself has a linear part
whose determinant has absolute value one. -/
theorem abs_det_linear_eq_one_of_image_eq {s : Set E} (h₀ : μ s ≠ 0) (htop : μ s ≠ ∞)
    (f : E →ᵃ[ℝ] E) (hf : f '' s = s) : |LinearMap.det f.linear| = 1 := by
  have h := Measure.addHaar_image_affineMap μ f s
  rw [hf] at h
  rw [← ENNReal.ofReal_eq_one]
  exact ((ENNReal.mul_left_inj h₀ htop).1 (by rw [one_mul]; exact h)).symm

/-- **Affine change of variables on an invariant set.** An affine map sending a measurable set
of positive finite Haar measure onto itself preserves integrals over that set. -/
theorem setIntegral_comp_continuousAffineMap_of_image_eq {s : Set E} (hs : MeasurableSet s)
    (h₀ : μ s ≠ 0) (htop : μ s ≠ ∞) (f : E →ᴬ[ℝ] E) (hf : f '' s = s) (g : E → G) :
    ∫ x in s, g (f x) ∂μ = ∫ x in s, g x ∂μ := by
  have hdet := abs_det_linear_eq_one_of_image_eq μ h₀ htop f.toAffineMap hf
  have hinj : Function.Injective f := by
    refine (AffineMap.linear_injective_iff f.toAffineMap).1 ?_
    have hu : IsUnit (LinearMap.det f.linear) := by
      refine isUnit_iff_ne_zero.2 fun h0 ↦ ?_
      rw [h0, abs_zero] at hdet
      exact zero_ne_one hdet
    exact (Module.End.isUnit_iff _).1 (LinearMap.isUnit_iff_isUnit_det _ |>.2 hu) |>.injective
  conv_rhs => rw [← hf]
  rw [integral_image_eq_integral_abs_det_fderiv_smul μ hs (fun x _ ↦ f.hasFDerivWithinAt)
    hinj.injOn]
  refine setIntegral_congr_fun hs fun x _ ↦ ?_
  rw [ContinuousLinearMap.det, ContinuousAffineMap.coe_contLinear_eq_linear]
  simp [hdet]

end MeasureTheory
