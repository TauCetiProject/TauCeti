/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.CauchyKernel
public import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
public import TauCeti.MeasureTheory.Integral.Circle.Reciprocal
public import TauCeti.MeasureTheory.Integral.PolarCoord
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-!
# The Cauchy integral of a disc indicator

For the indicator of the disc of radius `r ≥ 0` centered at `c`, the actual normalized Cauchy
integral `π⁻¹ ∫ (w - z)⁻¹` equals `conj (w - c)` on the closed disc and `r² / (w - c)` outside.
The two formulas agree on the boundary circle, and total division handles the center and radius
zero. The normalized mass `π⁻¹ ∫ 1_disc = r²` is exactly the coefficient of the reciprocal tail.

These formulas supply explicit examples for the one-derivative regularity and sharp global
integrability assertions in `Disc.Regularity` and `Disc.Lp`.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix B.2, for the Cauchy–Beurling framework used
  here and in the regularity and endpoint calculations of `Disc.Regularity` and `Disc.Lp`.
-/

public noncomputable section

open Complex MeasureTheory Metric Set
open scoped Real Topology ComplexConjugate

namespace TauCeti

/-- The unnormalized reciprocal integral on a disc, computed by its circular averages.
Total division includes a pole at the center and a zero radius. -/
theorem integral_sub_inv_ball_zero {r : ℝ} (hr : 0 ≤ r) (w : ℂ) :
    (∫ z in ball (0 : ℂ) r, (w - z)⁻¹) =
      (π : ℂ) * (min r ‖w‖ : ℝ)^2 / w := by
  -- Apply polar Fubini only after establishing two-dimensional integrability, then discard
  -- the null radius through the pole; the angular integral at that radius need not exist.
  let g : ℂ → ℂ := (ball (0 : ℂ) r).indicator (fun z => (w - z)⁻¹)
  have hint : IntegrableOn (fun z : ℂ => (w - z)⁻¹) (ball 0 r) :=
    ((Complex.locallyIntegrable_sub_inv w).integrableOn_isCompact
      (isCompact_closedBall 0 r)).mono_set ball_subset_closedBall
  have hg : Integrable g := (integrable_indicator_iff measurableSet_ball).mpr hint
  have hp := hg.integral_eq_integral_circleMap 0
  rw [integral_indicator measurableSet_ball] at hp
  let m := min r ‖w‖
  have hm : 0 ≤ m := le_min hr (norm_nonneg w)
  have heq : (fun ρ : ℝ => ρ • ∫ θ in -π..π, g (circleMap 0 ρ θ)) =ᵐ[volume.restrict (Ioi 0)]
      (Iio m).indicator (fun ρ : ℝ => ρ • ((2 * π : ℂ)/w)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi,
      ae_restrict_of_ae (volume.ae_ne ‖w‖)] with ρ hρ hne
    have hρ0 : 0 < ρ := hρ
    have hpoint (θ : ℝ) : g (circleMap 0 ρ θ) =
        if ρ < r then (w - circleMap 0 ρ θ)⁻¹ else 0 := by
      dsimp only [g]
      have hmem : circleMap 0 ρ θ ∈ ball (0 : ℂ) r ↔ ρ < r := by
        simp only [mem_ball, dist_zero_right, norm_circleMap_zero, abs_of_pos hρ0]
      by_cases h : ρ < r
      · rw [indicator_of_mem (hmem.mpr h), ite_eq_left h]
      · rw [indicator_of_notMem (fun hx => h (hmem.mp hx)), ite_eq_right h]
    simp_rw [hpoint]
    by_cases hρr : ρ < r
    · simp only [hρr, ite_true]
      rw [integral_neg_pi_pi_circleMap_sub_inv hρ0 hne.symm]
      by_cases hρw : ρ < ‖w‖
      · simp [hρw, m, lt_min_iff, hρr]
      · simp [hρw, m, lt_min_iff, hρr]
    · simp [hρr, m, lt_min_iff]
  rw [hp, integral_congr_ae heq, setIntegral_indicator measurableSet_Iio]
  have hi : Ioi (0 : ℝ) ∩ Iio m = Ioo 0 m := by ext; simp
  rw [hi]
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hm,
    intervalIntegral.integral_smul_const, integral_id]
  simp only [sub_zero, zero_pow (by decide : 2 ≠ 0), real_smul, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_ofNat]
  ring

/-- The normalized Cauchy integral of a centered disc indicator, including the boundary.
The exterior expression agrees with conjugation on the circle. -/
theorem pi_inv_mul_integral_sub_inv_ball_zero {r : ℝ} (hr : 0 ≤ r) (w : ℂ) :
    (π : ℂ)⁻¹ * (∫ z in ball (0 : ℂ) r, (w - z)⁻¹) =
      if ‖w‖ ≤ r then conj w else (r : ℂ)^2 / w := by
  rw [integral_sub_inv_ball_zero hr]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [← mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ hπ, one_mul]
  split_ifs with hw
  · rw [min_eq_right hw]
    by_cases hw0 : w = 0
    · simp [hw0]
    · apply (div_eq_iff hw0).mpr
      rw [← Complex.ofReal_pow, ← Complex.normSq_eq_norm_sq]
      exact Complex.normSq_eq_conj_mul_self
  · rw [min_eq_left (not_le.mp hw).le]

/-- The centered exterior formula includes the boundary circle and the degenerate radius. -/
theorem pi_inv_mul_integral_sub_inv_ball_zero_of_le {r : ℝ} (hr : 0 ≤ r) {w : ℂ}
    (hw : r ≤ ‖w‖) :
    (π : ℂ)⁻¹ * (∫ z in ball (0 : ℂ) r, (w-z)⁻¹) = (r : ℂ)^2/w := by
  rw [integral_sub_inv_ball_zero hr, min_eq_left hw]
  have hπ : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  rw [← mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ hπ, one_mul]

/-- Translation of the exact normalized disc indicator Cauchy formula. The radius may be zero. -/
theorem pi_inv_mul_integral_sub_inv_ball {r : ℝ} (hr : 0 ≤ r) (c w : ℂ) :
    (π : ℂ)⁻¹ * (∫ z in ball c r, (w - z)⁻¹) =
      if ‖w - c‖ ≤ r then conj (w - c) else (r : ℂ)^2 / (w - c) := by
  have hpres := measurePreserving_add_left (volume : Measure ℂ) c
  have hpre : (fun z : ℂ => c + z) ⁻¹' ball c r = ball 0 r := by
    ext z
    simp [mem_ball, dist_eq_norm]
  calc
    _ = (π : ℂ)⁻¹ * ∫ z in ball (0 : ℂ) r, ((w - c) - z)⁻¹ := by
      congr 1
      rw [← hpres.setIntegral_preimage_emb (MeasurableEquiv.addLeft c).measurableEmbedding,
        hpre]
      congr 1
      funext z
      congr 1
      ring
    _ = _ := pi_inv_mul_integral_sub_inv_ball_zero hr (w - c)

/-- The same formula for the actual whole-plane Cauchy integral of the disc indicator. -/
theorem pi_inv_mul_integral_sub_inv_mul_indicator_ball {r : ℝ} (hr : 0 ≤ r) (c w : ℂ) :
    (π : ℂ)⁻¹ * (∫ z : ℂ, (w-z)⁻¹ * (ball c r).indicator (fun _ => (1 : ℂ)) z) =
      if ‖w-c‖ ≤ r then conj (w-c) else (r : ℂ)^2/(w-c) := by
  simp_rw [← Set.indicator_mul_right (ball c r) (fun z : ℂ ↦ (w-z)⁻¹)
    (fun _ ↦ (1 : ℂ)), mul_one]
  rw [integral_indicator measurableSet_ball]
  exact pi_inv_mul_integral_sub_inv_ball hr c w

/-- The defining unit disc normalization check for the actual Cauchy integral. -/
theorem _root_.Complex.pi_inv_mul_integral_sub_inv_unit_ball (w : ℂ) :
    (π : ℂ)⁻¹ * (∫ z in ball (0 : ℂ) 1, (w - z)⁻¹) =
      if ‖w‖ ≤ 1 then conj w else w⁻¹ := by
  simpa using pi_inv_mul_integral_sub_inv_ball_zero zero_le_one w

/-- The normalized mass of a disc indicator is the coefficient of its exact reciprocal tail. -/
theorem pi_inv_mul_integral_indicator_ball {r : ℝ} (hr : 0 ≤ r) (c : ℂ) :
    (π : ℂ)⁻¹ * ∫ z : ℂ, (ball c r).indicator (fun _ => (1 : ℂ)) z = (r : ℂ)^2 := by
  rw [integral_indicator_const _ measurableSet_ball, measureReal_def, Complex.volume_ball]
  simp only [ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hr,
    ENNReal.coe_toReal, NNReal.coe_real_pi, real_smul, mul_one]
  push_cast
  field_simp


end TauCeti
