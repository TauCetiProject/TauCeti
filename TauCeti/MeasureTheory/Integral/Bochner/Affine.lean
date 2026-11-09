/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Affine change of variables for Bochner integrals

An invertible affine map `x ↦ p + L x` rescales an additive Haar measure by
`|det L|⁻¹`. Consequently, integration over its image is integration over the parameter
set with the factor `|det L|`, including for orientation-reversing maps.

`ContinuousLinearEquiv.integral_image_affine` applies to arbitrary parameter sets and
arbitrary integrands: neither measurability nor integrability is required. The identity
uses the totalized Bochner integral, and
`ContinuousLinearEquiv.integrableOn_image_affine_iff` shows that integrability on the image
is equivalent to integrability in the parameters. In particular, both integrals vanish
when the integrands are not integrable.

On `Fin n → ℝ` with Lebesgue measure, taking the parameter set to be `Set.Icc 0 1` gives
the change of variables from the unit cube to an affine parallelepiped. The same formula
in one lower dimension gives the scaling of individual face integrals.

The proofs use `MeasureTheory.Measure.map_affine_addHaar_eq_smul`, the image of an additive Haar
measure under an affine map, and Mathlib's transport of set integrals along measurable
equivalences.
-/

public section

open MeasureTheory Set

namespace ContinuousLinearEquiv

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E]

/-- An integrand is integrable on an invertible affine image exactly when its composition
with the affine map is integrable on the parameter set. No measurability of the set is
required. -/
theorem integrableOn_image_affine_iff (L : V ≃L[ℝ] V) (p : V) (f : V → E) (s : Set V)
    (μ : Measure V) [μ.IsAddHaarMeasure] :
    IntegrableOn f ((fun x ↦ p + L x) '' s) μ ↔
      IntegrableOn (fun x ↦ f (p + L x)) s μ := by
  let e := L.toHomeomorph.toMeasurableEquiv.trans (MeasurableEquiv.addLeft p)
  have he : ⇑e = (fun x ↦ p + L x) := by
    simp only [e, MeasurableEquiv.coe_trans, MeasurableEquiv.coe_addLeft,
      Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph,
      Function.comp_def]
  have hmap : μ.map e = ENNReal.ofReal |(LinearMap.det (L : V →ₗ[ℝ] V))⁻¹| • μ := by
    rw [he]
    exact Measure.map_affine_addHaar_eq_smul μ L p
  have hdet : LinearMap.det (L : V →ₗ[ℝ] V) ≠ 0 := L.toLinearEquiv.isUnit_det'.ne_zero
  have h := integrableOn_map_equiv e (f := f) (s := e '' s) (μ := μ)
  rw [hmap, IntegrableOn, Measure.restrict_smul,
    integrable_smul_measure (by positivity) ENNReal.ofReal_ne_top, e.preimage_image] at h
  simpa only [he, IntegrableOn, Function.comp_def] using h

/-- Change variables under an invertible affine map, with the absolute determinant as
Jacobian. This holds for every integrand and every parameter set, including when the
totalized Bochner integrals are zero because of nonintegrability. -/
theorem integral_image_affine [NormedSpace ℝ E] (L : V ≃L[ℝ] V) (p : V) (f : V → E) (s : Set V)
    (μ : Measure V) [μ.IsAddHaarMeasure] :
    ∫ y in (fun x ↦ p + L x) '' s, f y ∂μ =
      ∫ x in s, |LinearMap.det (L : V →ₗ[ℝ] V)| • f (p + L x) ∂μ := by
  let e := L.toHomeomorph.toMeasurableEquiv.trans (MeasurableEquiv.addLeft p)
  have he : ⇑e = (fun x ↦ p + L x) := by
    simp only [e, MeasurableEquiv.coe_trans, MeasurableEquiv.coe_addLeft,
      Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph,
      Function.comp_def]
  have hmap : μ.map e = ENNReal.ofReal |(LinearMap.det (L : V →ₗ[ℝ] V))⁻¹| • μ := by
    rw [he]
    exact Measure.map_affine_addHaar_eq_smul μ L p
  have hdet : LinearMap.det (L : V →ₗ[ℝ] V) ≠ 0 := L.toLinearEquiv.isUnit_det'.ne_zero
  have h := setIntegral_map_equiv (μ := μ) e f (e '' s)
  rw [hmap, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _), e.preimage_image] at h
  rw [he] at h
  rw [integral_smul]
  calc
    ∫ y in (fun x ↦ p + L x) '' s, f y ∂μ =
        |LinearMap.det (L : V →ₗ[ℝ] V)| •
          (|(LinearMap.det (L : V →ₗ[ℝ] V))⁻¹| •
            ∫ y in (fun x ↦ p + L x) '' s, f y ∂μ) := by
      rw [smul_smul, abs_inv, mul_inv_cancel₀ (abs_ne_zero.mpr hdet), one_smul]
    _ = _ := congrArg (|LinearMap.det (L : V →ₗ[ℝ] V)| • ·) h

end ContinuousLinearEquiv
