/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
public import TauCeti.Topology.Algebra.Module.Determinant
import Mathlib.Algebra.Order.Group.Pointwise.Interval

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

On `ι → ℝ` with Lebesgue measure, taking the parameter set to be `Set.Icc 0 1` gives invariance
under single-coordinate reflections `u k ↦ 1 - u k`
(`ContinuousLinearEquiv.setIntegral_Icc_single_add_negCoord`) and rescaling of arbitrary closed
boxes `Set.Icc a b` (`a ≤ b`) to `Set.Icc 0 1` with Jacobian `∏ i, (b i - a i)`
(`MeasureTheory.setIntegral_Icc_eq_smul_setIntegral_Icc_zero_one`), including on degenerate boxes.

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

section UnitCube

/-- Reflecting the `k`-th coordinate around `1 / 2`, namely `u ↦ Pi.single k 1 + negCoord ℝ k u`,
maps the unit cube `Set.Icc 0 1` onto itself. -/
theorem image_single_add_negCoord_Icc {ι : Type*} [DecidableEq ι] (k : ι) :
    (fun u : ι → ℝ ↦ Pi.single k 1 + negCoord ℝ k u) '' Icc 0 1 = Icc 0 1 := by
  have hmap : (fun u : ι → ℝ ↦ Pi.single k 1 + negCoord ℝ k u) =
      Pi.map (Function.update (fun _ : ι ↦ (id : ℝ → ℝ)) k (fun t : ℝ ↦ 1 - t)) := by
    ext u i
    rcases eq_or_ne i k with rfl | hik <;> simp [sub_eq_add_neg, *]
  rw [hmap, ← Set.pi_univ_Icc, Set.piMap_image_univ_pi]
  refine Set.pi_congr rfl fun i _ ↦ ?_
  rcases eq_or_ne i k with rfl | hik <;> simp [*]

/-- Reflecting the `k`-th coordinate around `1 / 2` maps the open unit cube onto itself. -/
theorem image_single_add_negCoord_pi_Ioo {ι : Type*} [DecidableEq ι] (k : ι) :
    (fun u : ι → ℝ ↦ Pi.single k 1 + negCoord ℝ k u) '' univ.pi (fun _ ↦ Ioo 0 1) =
      univ.pi (fun _ ↦ Ioo 0 1) := by
  have hmap : (fun u : ι → ℝ ↦ Pi.single k 1 + negCoord ℝ k u) =
      Pi.map (Function.update (fun _ : ι ↦ (id : ℝ → ℝ)) k (fun t : ℝ ↦ 1 - t)) := by
    ext u i
    rcases eq_or_ne i k with rfl | hik <;> simp [sub_eq_add_neg, *]
  rw [hmap, Set.piMap_image_univ_pi]
  refine Set.pi_congr rfl fun i _ ↦ ?_
  rcases eq_or_ne i k with rfl | hik <;> simp [*]

/-- Reflecting one coordinate `u k ↦ 1 - u k` of the unit cube `[0, 1]^ι` leaves the Bochner set
integral invariant, without measurability, integrability or completeness hypotheses. -/
theorem setIntegral_Icc_single_add_negCoord {ι : Type*} [Fintype ι] [DecidableEq ι]
    [NormedSpace ℝ E] (k : ι) (f : (ι → ℝ) → E) :
    ∫ u in Icc (0 : ι → ℝ) 1, f (Pi.single k 1 + negCoord ℝ k u) =
      ∫ u in Icc (0 : ι → ℝ) 1, f u := by
  have h := (negCoord ℝ (Q := fun _ : ι ↦ ℝ) k).integral_image_affine
    (Pi.single k 1) f (Icc 0 1) volume
  simpa [image_single_add_negCoord_Icc] using h.symm

/-- Positive coordinatewise scaling from `a` by `b - a` maps the unit cube `[0, 1]^ι` onto the
closed box `Set.Icc a b`. -/
theorem image_add_piCongrRight_smulLeft_Icc {ι : Type*} {a b : ι → ℝ} (hab : ∀ i, a i < b i) :
    (fun u : ι → ℝ ↦ a +
      piCongrRight (fun i ↦
        (smulLeft (Units.mk0 (b i - a i) (sub_ne_zero.mpr (hab i).ne')) : ℝ ≃L[ℝ] ℝ)) u) ''
        Icc 0 1 = Icc a b := by
  have hmap : (fun u : ι → ℝ ↦ a +
      piCongrRight (fun i ↦
        (smulLeft (Units.mk0 (b i - a i) (sub_ne_zero.mpr (hab i).ne')) : ℝ ≃L[ℝ] ℝ)) u) =
      Pi.map fun i t ↦ (b i - a i) * t + a i := by
    ext u i
    simp [add_comm]
  rw [hmap, ← Set.pi_univ_Icc, Set.piMap_image_univ_pi, ← Set.pi_univ_Icc]
  refine Set.pi_congr rfl fun i _ ↦ ?_
  simp [image_affine_Icc' (sub_pos.mpr (hab i))]

end UnitCube

end ContinuousLinearEquiv

namespace MeasureTheory

/-- Rescaling a closed rectangular box `Set.Icc a b` (`a ≤ b`) in `ι → ℝ` to `Set.Icc 0 1` pulls
back any Bochner set integral with the box volume `∏ i, (b i - a i)` as Jacobian, including on
degenerate boxes and without measurability, integrability or completeness hypotheses. -/
theorem setIntegral_Icc_eq_smul_setIntegral_Icc_zero_one {ι E : Type*} [Fintype ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] {a b : ι → ℝ} (hab : a ≤ b) (f : (ι → ℝ) → E) :
    ∫ y in Icc a b, f y =
      (∏ i, (b i - a i)) • ∫ u in Icc (0 : ι → ℝ) 1, f (fun i ↦ a i + (b i - a i) * u i) := by
  by_cases hdeg : ∃ k, a k = b k
  · obtain ⟨k, hk⟩ := hdeg
    have hvol : volume (Icc a b) = 0 := by
      rw [Real.volume_Icc_pi]
      exact Finset.prod_eq_zero (Finset.mem_univ k) (by simp [hk])
    have hprod : ∏ i, (b i - a i) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ k) (sub_eq_zero.mpr hk.symm)
    rw [setIntegral_measure_zero _ hvol, hprod, zero_smul]
  · push Not at hdeg
    have hlt : ∀ i, a i < b i := fun i ↦ (hab i).lt_of_ne (hdeg i)
    let L : (ι → ℝ) ≃L[ℝ] (ι → ℝ) := ContinuousLinearEquiv.piCongrRight fun i ↦
      (ContinuousLinearEquiv.smulLeft
        (Units.mk0 (b i - a i) (sub_ne_zero.mpr (hlt i).ne')) : ℝ ≃L[ℝ] ℝ)
    have hdet : |LinearMap.det (L : (ι → ℝ) →ₗ[ℝ] ι → ℝ)| = ∏ i, (b i - a i) := by
      have hpos : 0 < ∏ i, (b i - a i) :=
        Finset.prod_pos fun i _ ↦ sub_pos.mpr (hlt i)
      have hd : LinearMap.det (L : (ι → ℝ) →ₗ[ℝ] ι → ℝ) = ∏ i, (b i - a i) := by
        simp [L, ContinuousLinearEquiv.det_piCongrRight]
      rw [hd, abs_of_pos hpos]
    have himg : (fun u ↦ a + L u) '' Icc 0 1 = Icc a b :=
      ContinuousLinearEquiv.image_add_piCongrRight_smulLeft_Icc hlt
    have hfun : ∀ u, a + L u = fun i ↦ a i + (b i - a i) * u i := fun u ↦ by
      ext i
      simp [L]
    have h := L.integral_image_affine a f (Icc 0 1) volume
    rw [himg, hdet, integral_smul] at h
    simpa only [hfun] using h

end MeasureTheory
