/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
public import TauCeti.Topology.Algebra.Module.Determinant

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

Read on preimages: for an additive Haar measure on a finite-dimensional real normed space with
its Borel σ-algebra, `T x = p + L x` with `L` invertible, any set `s` and any integrand `f`, the
integral of `f ∘ T` over `T ⁻¹' s` equals the integral of `f` over `s` divided by `|det L|`
(`ContinuousLinearEquiv.integral_preimage_affine`). Over the whole space and without translation,
the integral of `f ∘ A` for a continuous linear automorphism `A` equals the integral of `f`
divided by `|det A|` (`MeasureTheory.Measure.integral_comp_continuousLinearEquiv`).

On `ι → ℝ` with Lebesgue measure, taking the parameter set to be `Set.Icc 0 1` gives invariance
under single-coordinate reflections `u k ↦ 1 - u k`
(`MeasureTheory.setIntegral_Icc_single_add_negCoord`) and rescaling of arbitrary closed
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

/-- **Affine change of variables on a preimage.** Let `μ` be an additive Haar measure on a
finite-dimensional real normed space with its Borel σ-algebra, and `T x = p + L x` with `L`
invertible. For any set `s`, the integral of `f ∘ T` over the preimage `T ⁻¹' s` equals the
integral of `f` over `s` divided by `|det L|`:
`∫ x in T ⁻¹' s, f (T x) ∂μ = |det L|⁻¹ • ∫ y in s, f y ∂μ`. This is
`ContinuousLinearEquiv.integral_image_affine` for the parameter set `T ⁻¹' s`, whose image is `s`;
as there, neither measurability nor integrability is required. -/
theorem integral_preimage_affine [NormedSpace ℝ E] (L : V ≃L[ℝ] V) (p : V) (f : V → E)
    (s : Set V) (μ : Measure V) [μ.IsAddHaarMeasure] :
    ∫ x in (fun x ↦ p + L x) ⁻¹' s, f (p + L x) ∂μ =
      |LinearMap.det (L : V →ₗ[ℝ] V)|⁻¹ • ∫ y in s, f y ∂μ := by
  have hdet : |LinearMap.det (L : V →ₗ[ℝ] V)| ≠ 0 :=
    abs_ne_zero.mpr L.toLinearEquiv.isUnit_det'.ne_zero
  have h := L.integral_image_affine p f ((fun x ↦ p + L x) ⁻¹' s) μ
  rw [image_preimage_eq s fun y ↦ ⟨L.symm (y - p), by simp⟩, integral_smul] at h
  rw [h, smul_smul, inv_mul_cancel₀ hdet, one_smul]

-- Credit: the statement and name follow the sketch in Tau Ceti PR #37628,
-- https://github.com/TauCetiProject/TauCeti/pull/37628.
/-- **Linear change of variables.** Let `μ` be an additive Haar measure on a finite-dimensional
real normed space with its Borel σ-algebra, and `A` a continuous linear automorphism. The integral
of `f ∘ A` equals the integral of `f` divided by `|det A|`:
`∫ x, f (A x) ∂μ = |det A|⁻¹ • ∫ x, f x ∂μ`. No integrability or measurability of `f` is needed.
This is the whole-space, translation-free case of `ContinuousLinearEquiv.integral_preimage_affine`.
-/
theorem _root_.MeasureTheory.Measure.integral_comp_continuousLinearEquiv [NormedSpace ℝ E]
    (μ : Measure V) [μ.IsAddHaarMeasure] (f : V → E) (A : V ≃L[ℝ] V) :
    ∫ x, f (A x) ∂μ = |LinearMap.det (A : V →ₗ[ℝ] V)|⁻¹ • ∫ x, f x ∂μ := by
  simpa only [zero_add, preimage_univ, Measure.restrict_univ] using
    A.integral_preimage_affine 0 f univ μ

end ContinuousLinearEquiv

namespace MeasureTheory

/-- Reflecting one coordinate `u k ↦ 1 - u k` of the unit cube `[0, 1]^ι` leaves the Bochner set
integral invariant, without measurability, integrability or completeness hypotheses. -/
theorem setIntegral_Icc_single_add_negCoord {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ι) (f : (ι → ℝ) → E) :
    ∫ u in Icc (0 : ι → ℝ) 1, f (Pi.single k 1 + ContinuousLinearEquiv.negCoord ℝ k u) =
      ∫ u in Icc (0 : ι → ℝ) 1, f u := by
  have h := (ContinuousLinearEquiv.negCoord ℝ (Q := fun _ : ι ↦ ℝ) k).integral_image_affine
    (Pi.single k 1) f (Icc 0 1) volume
  simpa [TauCeti.image_single_add_negCoord_Icc] using h.symm

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
      TauCeti.image_add_piCongrRight_smulLeft_Icc hlt
    have hfun : ∀ u, a + L u = fun i ↦ a i + (b i - a i) * u i := fun u ↦ by
      ext i
      simp [L]
    have h := L.integral_image_affine a f (Icc 0 1) volume
    rw [himg, hdet, integral_smul] at h
    simpa only [hfun] using h

end MeasureTheory
