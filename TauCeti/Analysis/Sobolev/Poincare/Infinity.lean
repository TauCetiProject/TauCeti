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
import TauCeti.Analysis.Calculus.FDeriv.Integrable
import TauCeti.Analysis.Complex.Conformal.Area
import TauCeti.Analysis.Complex.RemovableSingularity
import TauCeti.Analysis.Sobolev.Poincare.Slab
import TauCeti.Geometry.Symplectic.JHolomorphic.Line
import TauCeti.MeasureTheory.Measure.Lebesgue.Complex

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
the point at infinity. Its form on `ℂ`, for a map `f` vanishing on the disc `‖w‖ < R`, is
`∫ ‖f z⁻¹‖² ≤ (4 / R)² ∫ (‖∂₁ f‖² + ‖∂_i f‖²)` (`TauCeti.integral_norm_sq_comp_inv_le`).

In the coordinate `z = w⁻¹` centred at infinity, the map `η = χ ∘ (·⁻¹)` is supported in the
disc `|z| ≤ 1 / R`. The weight `|w|⁻⁴` is the area distortion `‖(w⁻¹)'‖²` of the inversion, so
the change of variables formula on `ℂ` (`TauCeti.integral_inv_sq_norm_sq_smul_eq`) turns the left
side into `∫ ‖η‖²`, and the energy of `∂_i η` is bounded by the Dirichlet energy of `χ`
(`TauCeti.integral_norm_fderiv_comp_inv_apply_sq_le`).
The Poincaré inequality on a strip of width `4 / R` containing that disc
(`TauCeti.integral_norm_sq_le_mul_integral_norm_fderiv_I_sq_of_abs_im`) then gives the bound.
-/

public section

namespace TauCeti

open Filter MeasureTheory Metric Set
open scoped Topology
open _root_.Complex (equivRealProdCLM volume_preserving_equiv_real_prod I)

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- **The Poincaré inequality at infinity on `ℂ`.** A compactly supported `C¹` map `f` of `ℂ`
vanishing on the disc `‖w‖ < R` has `∫ ‖f z⁻¹‖² ≤ (4 / R)² ∫ (‖∂₁ f‖² + ‖∂_i f‖²)`. -/
theorem integral_norm_sq_comp_inv_le {f : ℂ → V} {R : ℝ} (hR : 0 < R)
    (hf : ContDiff ℝ 1 f) (hfc : HasCompactSupport f) (hfR : ∀ w : ℂ, ‖w‖ < R → f w = 0) :
    ∫ z, ‖f z⁻¹‖ ^ 2 ≤ (4 / R) ^ 2 * ∫ w, (‖fderiv ℝ f w 1‖ ^ 2 + ‖fderiv ℝ f w I‖ ^ 2) := by
  -- In the coordinate `z = w⁻¹` the map vanishes off the disc `|z| ≤ R⁻¹`.
  have hηR (z : ℂ) (hz : R⁻¹ < ‖z‖) : f z⁻¹ = 0 :=
    hfR _ (by rw [norm_inv]; exact (inv_lt_comm₀ ((inv_pos.2 hR).trans hz) hR).2 hz)
  have hηc : HasCompactSupport fun z ↦ f z⁻¹ :=
    HasCompactSupport.intro (isCompact_closedBall 0 R⁻¹) fun z hz ↦
      hηR z (by simpa [mem_closedBall_zero_iff] using hz)
  have hη : ContDiff ℝ 1 fun z ↦ f z⁻¹ := by
    have h := hfc.contDiff_update_comp_inv hf
    rwa [Function.update_eq_self_iff.2 (by simp [hfR 0 (by simpa using hR)])] at h
  -- The Poincaré inequality on the strip `|Im z| < 2 R⁻¹` containing that disc.
  have hpoinc := integral_norm_sq_le_mul_integral_norm_fderiv_I_sq_of_abs_im hη hηc
    (r := 2 * R⁻¹) fun z hz ↦ hηR z (by linarith [Complex.abs_im_le_norm z, inv_pos.2 hR])
  calc _ ≤ (2 * (2 * R⁻¹)) ^ 2 * ∫ z, ‖fderiv ℝ (fun z ↦ f z⁻¹) z I‖ ^ 2 := hpoinc
    _ ≤ (2 * (2 * R⁻¹)) ^ 2 * ∫ w, (‖fderiv ℝ f w 1‖ ^ 2 + ‖fderiv ℝ f w I‖ ^ 2) :=
        mul_le_mul_of_nonneg_left
          ((integral_norm_fderiv_comp_inv_apply_sq_le I
            (integrable_norm_fderiv_sq_add hf hfc 1 I)).trans_eq (by simp))
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
  have hfw (w : ℂ) : χ (equivRealProdCLM w) = f w := (Function.comp_apply ..).symm
  rw [← volume_preserving_equiv_real_prod.integral_comp'
      fun p ↦ ((p.1 ^ 2 + p.2 ^ 2) ^ 2)⁻¹ * ‖χ p‖ ^ 2,
    ← volume_preserving_equiv_real_prod.integral_comp'
      fun p ↦ ‖fderiv ℝ χ p (1, 0)‖ ^ 2 + ‖fderiv ℝ χ p (0, 1)‖ ^ 2]
  simp only [Complex.coe_measurableEquivRealProd_eq_equivRealProdCLM, hsq, hfw,
    ← stdComplexLineReal_eq, ← stdComplexLineImag_eq, ← fderiv_comp_equivRealProdCLM_one,
    ← fderiv_comp_equivRealProdCLM_I]
  have hinv := integral_inv_sq_norm_sq_smul_eq fun w ↦ ‖f w‖ ^ 2
  simp only [smul_eq_mul] at hinv
  rw [hinv]
  exact integral_norm_sq_comp_inv_le hR (hχ.comp equivRealProdCLM.contDiff)
    (hc.comp_homeomorph equivRealProdCLM.toHomeomorph) fun w hw ↦
      h0 _ (by rw [hsq]; exact pow_lt_pow_left₀ hw (norm_nonneg w) two_ne_zero)

end TauCeti
