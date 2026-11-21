/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.FDeriv.Equiv
import Mathlib.MeasureTheory.Measure.Lebesgue.Complex
import TauCeti.Analysis.Calculus.FDeriv.Integrable
import TauCeti.Analysis.Calculus.FDeriv.Inv
import TauCeti.Analysis.Complex.Conformal.Area
import TauCeti.Analysis.Normed.Module.Basic
import TauCeti.Analysis.Sobolev.Poincare.Slab

/-!
# The Poincaré inequality at infinity in the plane

Read in the coordinate `w ∈ ℂ ≅ ℝ × ℝ`, a map `χ` on the Riemann sphere which vanishes near `0`
and is compactly supported in `ℂ` has `L²` norm near the point at infinity equal, up to a factor
comparable to one, to

`∫ ‖χ w‖² / |w|⁴`,

because the spherical area element is `4 |dw|² / (1 + |w|²)²`. This file bounds it by the
Dirichlet energy: if `χ` is `C¹`, compactly supported and vanishes on the disc `|w| < R`, then

`∫ ‖χ w‖² / |w|⁴ ≤ (4 / R)² ∫ (‖∂s χ‖² + ‖∂t χ‖²)`

(`TauCeti.integral_inv_sq_mul_norm_sq_le`). This is the Poincaré inequality on a small disc at
the point at infinity. In the coordinate `z = w⁻¹` centred at infinity, the map `η = χ ∘ (·⁻¹)` is
supported in the disc `|z| ≤ 1 / R`. The weight `|w|⁻⁴` is the area distortion `‖(w⁻¹)'‖²` of the
inversion, so the change of variables formula on `ℂ`
(`TauCeti.integral_inv_sq_norm_sq_smul_eq`) turns the left side into `∫ ‖η‖²`, and
the Dirichlet energy is conformally invariant (`TauCeti.fderiv_comp_inv_apply`). The Poincaré
inequality on a strip of width `4 / R` containing that disc
(`TauCeti.integral_norm_sq_le_mul_integral_norm_fderiv_sq_of_abs_snd`) then gives the bound.

The norm on the target is arbitrary, so the Dirichlet energy is only conformally invariant up to
the inequality `‖a v₁ + b v₂‖² ≤ (a² + b²) (‖v₁‖² + ‖v₂‖²)`
(`TauCeti.norm_smul_add_smul_sq_le`), which is enough here.
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Set
open scoped Topology
open _root_.Complex (equivRealProdCLM volume_preserving_equiv_real_prod I)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The Dirichlet energy does not grow under the inversion.** For a `C¹` map `f` of `ℂ` with
integrable Dirichlet energy, the energy of the derivative of `z ↦ f z⁻¹` in the direction `i` is
at most the Dirichlet energy of `f`. -/
private theorem integral_norm_fderiv_comp_inv_I_sq_le {f : ℂ → V}
    (hE : Integrable fun w ↦ ‖fderiv ℝ f w 1‖ ^ 2 + ‖fderiv ℝ f w I‖ ^ 2) :
    ∫ z, ‖fderiv ℝ (fun z ↦ f z⁻¹) z I‖ ^ 2 ≤
      ∫ w, (‖fderiv ℝ f w 1‖ ^ 2 + ‖fderiv ℝ f w I‖ ^ 2) := by
  set E : ℂ → ℝ := fun w ↦ ‖fderiv ℝ f w 1‖ ^ 2 + ‖fderiv ℝ f w I‖ ^ 2
  have hs : MeasurableSet ({0}ᶜ : Set ℂ) := (measurableSet_singleton 0).compl
  have hd (z : ℂ) (hz : z ∈ ({0}ᶜ : Set ℂ)) : DifferentiableAt ℂ (·⁻¹) z := differentiableAt_inv hz
  have himage : (·⁻¹) '' ({0}ᶜ : Set ℂ) = {0}ᶜ := by
    rw [image_inv_eq_inv, compl_inv, inv_singleton, inv_zero]
  -- Pointwise, `‖∂_i (f ∘ inv)‖² ≤ ‖(z⁻¹)'‖² E(z⁻¹)`, by Cauchy–Schwarz in the real coordinates of
  -- the direction `-(z²)⁻¹ i`.
  have hpt (z : ℂ) (hz : z ∈ ({0}ᶜ : Set ℂ)) :
      ‖fderiv ℝ (fun z ↦ f z⁻¹) z I‖ ^ 2 ≤ ‖deriv (·⁻¹) z‖ ^ 2 • E z⁻¹ := by
    have ha : -(z ^ 2)⁻¹ * I = (-(z ^ 2)⁻¹ * I).re • (1 : ℂ) + (-(z ^ 2)⁻¹ * I).im • I := by
      rw [Complex.real_smul, Complex.real_smul, mul_one, Complex.re_add_im]
    have hn (w : ℂ) : ‖w‖ ^ 2 = (w * I).re ^ 2 + (w * I).im ^ 2 := by
      simp [Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [fderiv_comp_inv_apply hz, ha, map_add, map_smul, map_smul, deriv_inv, smul_eq_mul,
      hn (-(z ^ 2)⁻¹)]
    exact norm_smul_add_smul_sq_le _ _ _ _
  have hEi : IntegrableOn (fun z ↦ ‖deriv (·⁻¹) z‖ ^ 2 • E z⁻¹) {0}ᶜ :=
    (integrableOn_image_iff_integrableOn_norm_deriv_sq_smul hd hs inv_injective.injOn E).1
      (himage ▸ hE.integrableOn)
  calc ∫ z, ‖fderiv ℝ (fun z ↦ f z⁻¹) z I‖ ^ 2
      = ∫ z in {0}ᶜ, ‖fderiv ℝ (fun z ↦ f z⁻¹) z I‖ ^ 2 := by
        rw [restrict_compl_singleton]
    _ ≤ ∫ z in {0}ᶜ, ‖deriv (·⁻¹) z‖ ^ 2 • E z⁻¹ :=
        integral_mono_of_nonneg (Eventually.of_forall fun _ ↦ sq_nonneg _) hEi
          ((ae_restrict_iff' hs).2 (Eventually.of_forall hpt))
    _ = ∫ w in (·⁻¹) '' {0}ᶜ, E w :=
        (integral_image_eq_integral_norm_deriv_sq_smul hd hs inv_injective.injOn E).symm
    _ = ∫ w, E w := by rw [himage, restrict_compl_singleton]

/-- An integral over `ℝ × ℝ` is the integral over `ℂ` of the integrand read in the real
coordinates of `ℂ`. -/
private theorem integral_comp_equivRealProdCLM (G : ℝ × ℝ → ℝ) :
    ∫ w : ℂ, G (equivRealProdCLM w) = ∫ p, G p :=
  volume_preserving_equiv_real_prod.integral_comp' G

/-- The chain rule for a map read through a continuous linear equivalence `e`: its derivative at
`x` in the direction `v` is the derivative of the map at `e x` in the direction `e v`. -/
private theorem fderiv_comp_continuousLinearEquiv_apply {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (e : E ≃L[ℝ] F) (g : F → V)
    (x v : E) : fderiv ℝ (g ∘ e) x v = fderiv ℝ g (e x) (e v) := by
  rw [e.comp_right_fderiv, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]

/-- **The Poincaré inequality on a horizontal strip of `ℂ`.** A compactly supported `C¹` map of
`ℂ` vanishing where `r ≤ |Im z|` satisfies `∫ ‖η‖² ≤ (2 r)² ∫ ‖∂_i η‖²`; this is
`TauCeti.integral_norm_sq_le_mul_integral_norm_fderiv_sq_of_abs_snd` read on `ℂ`. -/
private theorem integral_norm_sq_le_mul_integral_norm_fderiv_I_sq {η : ℂ → V} {r : ℝ}
    (hη : ContDiff ℝ 1 η) (hc : HasCompactSupport η) (hr : ∀ z : ℂ, r ≤ |z.im| → η z = 0) :
    ∫ z, ‖η z‖ ^ 2 ≤ (2 * r) ^ 2 * ∫ z, ‖fderiv ℝ η z I‖ ^ 2 := by
  have hpoinc := integral_norm_sq_le_mul_integral_norm_fderiv_sq_of_abs_snd
    (hη.comp equivRealProdCLM.symm.contDiff)
    (hc.comp_homeomorph equivRealProdCLM.symm.toHomeomorph) (r := r) fun p hp ↦
      hr _ (by rwa [Complex.equivRealProdCLM_symm_apply_im])
  have hdη (p : ℝ × ℝ) : fderiv ℝ (η ∘ equivRealProdCLM.symm) p (0, 1) =
      fderiv ℝ η (equivRealProdCLM.symm p) I := by
    rw [fderiv_comp_continuousLinearEquiv_apply,
      show equivRealProdCLM.symm (0, 1) = I by simp [Complex.ext_iff]]
  simp only [hdη, Function.comp_apply] at hpoinc
  rw [← integral_comp_equivRealProdCLM fun p ↦ ‖η (equivRealProdCLM.symm p)‖ ^ 2,
    ← integral_comp_equivRealProdCLM fun p ↦ ‖fderiv ℝ η (equivRealProdCLM.symm p) I‖ ^ 2]
    at hpoinc
  simpa only [ContinuousLinearEquiv.symm_apply_apply] using hpoinc

/-- **The Poincaré inequality at infinity on `ℂ`.** A compactly supported `C¹` map `f` of `ℂ`
vanishing on the disc `‖w‖ < R` has `∫ ‖f z⁻¹‖² ≤ (4 / R)² ∫ (‖∂₁ f‖² + ‖∂_i f‖²)`. -/
private theorem integral_norm_sq_comp_inv_le {f : ℂ → V} {R : ℝ} (hR : 0 < R)
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (hfR : ∀ w : ℂ, ‖w‖ < R → f w = 0) :
    ∫ z, ‖f z⁻¹‖ ^ 2 ≤ (4 / R) ^ 2 * ∫ w, (‖fderiv ℝ f w 1‖ ^ 2 + ‖fderiv ℝ f w I‖ ^ 2) := by
  -- In the coordinate `z = w⁻¹` the map vanishes off the disc `|z| ≤ R⁻¹`.
  have hηR (z : ℂ) (hz : R⁻¹ < ‖z‖) : f z⁻¹ = 0 :=
    hfR _ (by rw [norm_inv]; exact (inv_lt_comm₀ ((inv_pos.2 hR).trans hz) hR).2 hz)
  have hηc : HasCompactSupport fun z ↦ f z⁻¹ :=
    HasCompactSupport.intro (isCompact_closedBall 0 R⁻¹) fun z hz ↦
      hηR z (by simpa [mem_closedBall_zero_iff] using hz)
  -- The Poincaré inequality on the strip `|Im z| < 2 R⁻¹` containing that disc.
  have hpoinc := integral_norm_sq_le_mul_integral_norm_fderiv_I_sq
    (contDiff_comp_inv hf hfc (hfR 0 (by simpa using hR))) hηc (r := 2 * R⁻¹) fun z hz ↦
      hηR z (by linarith [Complex.abs_im_le_norm z, inv_pos.2 hR])
  calc _ ≤ (2 * (2 * R⁻¹)) ^ 2 * ∫ z, ‖fderiv ℝ (fun z ↦ f z⁻¹) z I‖ ^ 2 := hpoinc
    _ ≤ (2 * (2 * R⁻¹)) ^ 2 * ∫ w, (‖fderiv ℝ f w 1‖ ^ 2 + ‖fderiv ℝ f w I‖ ^ 2) :=
        mul_le_mul_of_nonneg_left
          (integral_norm_fderiv_comp_inv_I_sq_le (integrable_norm_fderiv_sq_add hf hfc 1 I))
          (sq_nonneg _)
    _ = _ := by ring

/-- **The Poincaré inequality at infinity in the plane.** Let `χ` be a compactly supported `C¹`
map on `ℝ × ℝ ≅ ℂ` which vanishes on the disc `s² + t² < R²`, `R > 0`. Then

`∫ ‖χ w‖² / |w|⁴ ≤ (4 / R)² ∫ (‖∂s χ‖² + ‖∂t χ‖²)`.

The weight `|w|⁻⁴` is the area element of the sphere near its point at infinity, up to a factor
tending to `4`, so this bounds the `L²` norm of `χ` near infinity by its Dirichlet energy. -/
theorem integral_inv_sq_mul_norm_sq_le {χ : ℝ × ℝ → V} {R : ℝ} (hR : 0 < R)
    (hχ : ContDiff ℝ 1 χ) (hc : HasCompactSupport χ)
    (h0 : ∀ z : ℝ × ℝ, z.1 ^ 2 + z.2 ^ 2 < R ^ 2 → χ z = 0) :
    ∫ z, ((z.1 ^ 2 + z.2 ^ 2) ^ 2)⁻¹ * ‖χ z‖ ^ 2 ≤
      (4 / R) ^ 2 * ∫ z, (‖fderiv ℝ χ z (1, 0)‖ ^ 2 + ‖fderiv ℝ χ z (0, 1)‖ ^ 2) := by
  -- Read `χ` as the map `f = χ ∘ equivRealProdCLM` of `ℂ`.
  set f : ℂ → V := χ ∘ equivRealProdCLM
  have hsq (w : ℂ) : (equivRealProdCLM w).1 ^ 2 + (equivRealProdCLM w).2 ^ 2 = ‖w‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [sq]
  have hdf (w v : ℂ) : fderiv ℝ f w v = fderiv ℝ χ (equivRealProdCLM w) (equivRealProdCLM v) :=
    fderiv_comp_continuousLinearEquiv_apply _ _ _ _
  have hfw (w : ℂ) : χ (equivRealProdCLM w) = f w := (Function.comp_apply ..).symm
  have h1 : equivRealProdCLM 1 = (1, 0) := by simp
  have hI : equivRealProdCLM I = (0, 1) := by simp
  rw [← integral_comp_equivRealProdCLM fun p ↦ ((p.1 ^ 2 + p.2 ^ 2) ^ 2)⁻¹ * ‖χ p‖ ^ 2,
    ← integral_comp_equivRealProdCLM fun p ↦ ‖fderiv ℝ χ p (1, 0)‖ ^ 2 + ‖fderiv ℝ χ p (0, 1)‖ ^ 2]
  simp only [hsq, hfw, ← h1, ← hI, ← hdf]
  have hinv := integral_inv_sq_norm_sq_smul_eq fun w ↦ ‖f w‖ ^ 2
  simp only [smul_eq_mul] at hinv
  rw [hinv]
  exact integral_norm_sq_comp_inv_le hR (hχ.comp equivRealProdCLM.contDiff)
    (hc.comp_homeomorph equivRealProdCLM.toHomeomorph) fun w hw ↦
      h0 _ (by rw [hsq]; exact pow_lt_pow_left₀ hw (norm_nonneg w) two_ne_zero)

end TauCeti
