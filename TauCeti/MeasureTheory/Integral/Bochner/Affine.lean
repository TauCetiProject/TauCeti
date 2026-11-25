/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
public import TauCeti.Topology.Algebra.Module.Determinant
import TauCeti.MeasureTheory.Integral.Bochner.Periodic

/-!
# Affine change of variables for Bochner integrals

An invertible affine map `x ↦ p + L x` rescales an additive Haar measure by
`|det L|⁻¹`. Consequently, integration over its image is integration over the parameter
set with the factor `|det L|`, including for orientation-reversing maps. For a singular `L` the
image is null and the factor is `0`.

`LinearMap.integral_image_affine` applies to arbitrary linear maps, parameter sets and
arbitrary integrands: neither measurability nor integrability is required. The identity
uses the totalized Bochner integral, and for invertible `L`
`ContinuousLinearEquiv.integrableOn_image_affine_iff` shows that integrability on the image
is equivalent to integrability in the parameters. In particular, both integrals vanish
when the integrands are not integrable.

Read on preimages: for an additive Haar measure on a finite-dimensional real normed space with
its Borel σ-algebra, `T x = p + L x` with `L` any linear map, any set `s` and any integrand `f`,
the integral of `f ∘ T` over `T ⁻¹' s` equals the integral of `f` over `s` divided by `|det L|`
(`LinearMap.integral_preimage_affine`). For singular `L` both sides are `0`, the right one through
`0⁻¹ = 0`. Over the whole space and without translation, the integral of `f ∘ A` for a linear map
`A` equals the integral of `f` divided by `|det A|`
(`MeasureTheory.Measure.integral_comp_linearMap`).

On `ι → ℝ` with Lebesgue measure, taking the parameter set to be `Set.Icc 0 1` gives invariance
under single-coordinate reflections `u k ↦ 1 - u k`
(`MeasureTheory.setIntegral_Icc_single_add_negCoord`) and rescaling of arbitrary closed
boxes `Set.Icc a b` (`a ≤ b`) to `Set.Icc 0 1` with Jacobian `∏ i, (b i - a i)`
(`MeasureTheory.setIntegral_Icc_eq_smul_setIntegral_Icc_zero_one`), including on degenerate boxes.

The proofs use `MeasureTheory.Measure.map_affine_addHaar_eq_smul`, the image of an additive Haar
measure under an affine map, and Mathlib's transport of set integrals along measurable
equivalences. In the singular case, translation invariance along a nonzero kernel vector gives `0`
via `MeasureTheory.integral_eq_zero_of_ae_add_right_eq`.
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

end ContinuousLinearEquiv

namespace LinearMap

/-- A linear endomorphism of a finite-dimensional real normed space with nonzero determinant is
the underlying linear map of a continuous linear automorphism. -/
private theorem exists_continuousLinearEquiv_of_det_ne_zero {V : Type*} [NormedAddCommGroup V]
    [NormedSpace ℝ V] [FiniteDimensional ℝ V] {L : V →ₗ[ℝ] V} (hdet : LinearMap.det L ≠ 0) :
    ∃ L' : V ≃L[ℝ] V, (L' : V →ₗ[ℝ] V) = L :=
  ⟨(L.equivOfDetNeZero hdet).toContinuousLinearEquiv, by
    rw [LinearEquiv.toLinearEquiv_toContinuousLinearEquiv, LinearEquiv.coe_ofIsUnitDet]⟩

variable {V E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Change variables under an affine map `T x = p + L x`, for any linear map `L`, with the absolute
determinant as Jacobian: `∫ y in T '' s, f y ∂μ = ∫ x in s, |det L| • f (T x) ∂μ`. This holds for
every integrand and every parameter set, including when the totalized Bochner integrals are zero
because of nonintegrability. For singular `L` both sides are `0`: the image then lies in a proper
affine subspace, which is null. -/
theorem integral_image_affine (L : V →ₗ[ℝ] V) (p : V) (f : V → E) (s : Set V)
    (μ : Measure V) [μ.IsAddHaarMeasure] :
    ∫ y in (fun x ↦ p + L x) '' s, f y ∂μ = ∫ x in s, |LinearMap.det L| • f (p + L x) ∂μ := by
  rcases eq_or_ne (LinearMap.det L) 0 with hdet | hdet
  · have hnull : μ ((fun x ↦ p + L x) '' s) = 0 := by
      rw [← image_image (p + ·) L s, image_add_left, measure_preimage_add,
        Measure.addHaar_image_linearMap, hdet, abs_zero, ENNReal.ofReal_zero, zero_mul]
    simp [setIntegral_measure_zero _ hnull, hdet]
  obtain ⟨L, rfl⟩ := exists_continuousLinearEquiv_of_det_ne_zero hdet
  simp only [LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv]
  let e := L.toHomeomorph.toMeasurableEquiv.trans (MeasurableEquiv.addLeft p)
  have he : ⇑e = (fun x ↦ p + L x) := by
    simp only [e, MeasurableEquiv.coe_trans, MeasurableEquiv.coe_addLeft,
      Homeomorph.toMeasurableEquiv_coe, ContinuousLinearEquiv.coe_toHomeomorph,
      Function.comp_def]
  have hmap : μ.map e = ENNReal.ofReal |(LinearMap.det (L : V →ₗ[ℝ] V))⁻¹| • μ := by
    rw [he]
    exact Measure.map_affine_addHaar_eq_smul μ L p
  have h := setIntegral_map_equiv (μ := μ) e f (e '' s)
  rw [hmap, Measure.restrict_smul, integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _), e.preimage_image, he] at h
  rw [integral_smul, ← h, smul_smul, abs_inv, mul_inv_cancel₀ (abs_ne_zero.mpr hdet), one_smul]

/-- **Affine change of variables on a preimage.** Let `μ` be an additive Haar measure on a
finite-dimensional real normed space with its Borel σ-algebra, and `T x = p + L x` for any linear
map `L`. For any set `s`, the integral of `f ∘ T` over the preimage `T ⁻¹' s` equals the integral
of `f` over `s` divided by `|det L|`:
`∫ x in T ⁻¹' s, f (T x) ∂μ = |det L|⁻¹ • ∫ y in s, f y ∂μ`. Neither measurability nor
integrability is required. For invertible `L` this is `LinearMap.integral_image_affine` for the
parameter set `T ⁻¹' s`, whose image is `s`.
For singular `L` both sides are `0`: the left integrand is invariant under the translations by the
kernel of `L`, and so is its domain, so it is integrable only when it vanishes almost everywhere. -/
theorem integral_preimage_affine (L : V →ₗ[ℝ] V) (p : V) (f : V → E) (s : Set V)
    (μ : Measure V) [μ.IsAddHaarMeasure] :
    ∫ x in (fun x ↦ p + L x) ⁻¹' s, f (p + L x) ∂μ = |LinearMap.det L|⁻¹ • ∫ y in s, f y ∂μ := by
  rcases eq_or_ne (LinearMap.det L) 0 with hdet | hdet
  swap
  · -- `T` is surjective, so `T ⁻¹' s` is a parameter set of `s`.
    obtain ⟨L', hL'⟩ := exists_continuousLinearEquiv_of_det_ne_zero hdet
    have hT : (fun x ↦ p + L x) '' ((fun x ↦ p + L x) ⁻¹' s) = s :=
      image_preimage_eq s fun y ↦ ⟨L'.symm (y - p), by simp [← hL']⟩
    have h := L.integral_image_affine p f ((fun x ↦ p + L x) ⁻¹' s) μ
    rw [hT, integral_smul] at h
    rw [h, smul_smul, inv_mul_cancel₀ (abs_ne_zero.mpr hdet), one_smul]
  -- For singular `L`, the integrand and its domain are invariant under translation by a
  -- nonzero vector `k` of the kernel of `L`.
  rw [hdet, abs_zero, inv_zero, zero_smul]
  obtain ⟨k, hkL, hk⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.bot_lt_ker_of_det_eq_zero hdet).ne'
  have hLk : ∀ x, L (x + k) = L x := fun x ↦ by
    simp [LinearMap.mem_ker.mp hkL]
  have hS : (· + k) ⁻¹' ((fun x ↦ p + L x) ⁻¹' s) = (fun x ↦ p + L x) ⁻¹' s := by
    ext x
    simp only [mem_preimage, hLk]
  have hmp : MeasurePreserving (· + k) (μ.restrict ((fun x ↦ p + L x) ⁻¹' s))
      (μ.restrict ((fun x ↦ p + L x) ⁻¹' s)) := by
    simpa only [hS] using (measurePreserving_add_right μ k).restrict_preimage_emb
      (measurableEmbedding_addRight k) ((fun x ↦ p + L x) ⁻¹' s)
  exact integral_eq_zero_of_ae_add_right_eq hk hmp (ae_of_all _ fun x ↦ by rw [hLk])

-- Credit: the statement follows the sketch of `integral_comp_continuousLinearEquiv` in Tau Ceti
-- PR #37628, https://github.com/TauCetiProject/TauCeti/pull/37628, extended here from continuous
-- linear automorphisms to all linear maps.
/-- **Linear change of variables.** Let `μ` be an additive Haar measure on a finite-dimensional
real normed space with its Borel σ-algebra, and `A` a linear map. The integral of `f ∘ A` equals
the integral of `f` divided by `|det A|`: `∫ x, f (A x) ∂μ = |det A|⁻¹ • ∫ x, f x ∂μ`, where both
sides are `0` when `A` is singular. No integrability or measurability of `f` is needed. This is the
whole-space, translation-free case of `LinearMap.integral_preimage_affine`. -/
theorem _root_.MeasureTheory.Measure.integral_comp_linearMap (μ : Measure V)
    [μ.IsAddHaarMeasure] (f : V → E) (A : V →ₗ[ℝ] V) :
    ∫ x, f (A x) ∂μ = |LinearMap.det A|⁻¹ • ∫ x, f x ∂μ := by
  simpa only [zero_add, preimage_univ, Measure.restrict_univ] using
    A.integral_preimage_affine 0 f univ μ

end LinearMap

namespace MeasureTheory

/-- Reflecting one coordinate `u k ↦ 1 - u k` of the unit cube `[0, 1]^ι` leaves the Bochner set
integral invariant, without measurability, integrability or completeness hypotheses. -/
theorem setIntegral_Icc_single_add_negCoord {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (k : ι) (f : (ι → ℝ) → E) :
    ∫ u in Icc (0 : ι → ℝ) 1, f (Pi.single k 1 + ContinuousLinearEquiv.negCoord ℝ k u) =
      ∫ u in Icc (0 : ι → ℝ) 1, f u := by
  have h := LinearMap.integral_image_affine
    (ContinuousLinearEquiv.negCoord ℝ (Q := fun _ : ι ↦ ℝ) k : (ι → ℝ) →ₗ[ℝ] ι → ℝ)
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
    have h := LinearMap.integral_image_affine (L : (ι → ℝ) →ₗ[ℝ] ι → ℝ) a f (Icc 0 1) volume
    simp only [LinearEquiv.coe_coe, ContinuousLinearEquiv.coe_toLinearEquiv] at h
    rw [himg, hdet, integral_smul] at h
    simpa only [hfun] using h

end MeasureTheory
