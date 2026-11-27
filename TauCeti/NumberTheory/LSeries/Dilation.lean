/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.MellinTransform
public import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.MeasureTheory.Function.LpSpace.InfiniteSum
import TauCeti.MeasureTheory.Integral.DominatedConvergence

/-!
# Dirichlet series and Mellin transforms of dilated kernels

The Mellin transform of a sum of integer dilates of a kernel factors as the product of the
kernel's Mellin transform and the Dirichlet series of the coefficients. This lets one transfer
cutoff estimates on a smoothed sum to approximations of an L-series.
-/

public section

open Complex MeasureTheory Set

namespace LSeriesSummable

/-- If a Dirichlet series and a Mellin integral both converge absolutely, the Mellin
transform of the weighted sum of positive integer dilates is the product of the two
transforms. The weighted sum converges absolutely almost everywhere on `(0, ∞)`. -/
theorem hasMellin_tsum_dilate {a : ℕ → ℂ} {f : ℝ → ℂ} {s : ℂ}
    (ha : LSeriesSummable a s) (hf : MellinConvergent f s) :
    HasMellin (fun t ↦ ∑' n : ℕ, a (n + 1) * f ((n + 1 : ℕ) * t)) s
      (LSeries a s * mellin f s) := by
  let d (n : ℕ) : ℝ := (n + 1 : ℕ)
  have hd (n : ℕ) : 0 < d n := by positivity
  let g (n : ℕ) (t : ℝ) := (t : ℂ) ^ (s - 1) * (a (n + 1) * f (d n * t))
  have hg (n : ℕ) : IntegrableOn (g n) (Ioi 0) := by
    simpa only [g, MellinConvergent, smul_eq_mul] using
      (((MellinConvergent.comp_mul_left (hd n)).2 hf).const_smul (a (n + 1)))
  have hscale (n : ℕ) : (∫ t in Ioi 0, ‖g n t‖) =
      ‖LSeries.term a s (n + 1)‖ * ∫ t : ℝ in Ioi 0, ‖(t : ℂ) ^ (s - 1) * f t‖ := by
    let k (t : ℝ) := ‖(t : ℂ) ^ (s - 1) * f t‖
    calc
      _ = ∫ t in Ioi 0, (‖a (n + 1)‖ / d n ^ (s.re - 1)) * k (d n * t) := by
        refine setIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
        simp only [g, k, norm_mul, norm_cpow_eq_rpow_re_of_pos (mem_Ioi.mp ht),
          norm_cpow_eq_rpow_re_of_pos (mul_pos (hd n) (mem_Ioi.mp ht)), sub_re, one_re,
          Real.mul_rpow (hd n).le (mem_Ioi.mp ht).le]
        field_simp [(Real.rpow_pos_of_pos (hd n) (s.re - 1)).ne']
      _ = _ := by
        rw [integral_const_mul, integral_comp_mul_left_Ioi _ _ (hd n), mul_zero, smul_eq_mul,
          ← mul_assoc, ← div_eq_mul_inv, div_div,
          ← Real.rpow_add_one (hd n).ne', sub_add_cancel]
        rw [LSeries.norm_term_eq, ite_eq_right (Nat.succ_ne_zero n)]
  have hnorm : Summable fun n ↦ ∫ t in Ioi 0, ‖g n t‖ := by
    simp only [hscale]
    exact ((summable_nat_add_iff 1).2 ha.norm).mul_right _
  have hae : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), Summable fun n ↦ ‖g n t‖ := by
    apply summable_norm_of_tsum_eLpNorm_ne_top (p := 1) le_rfl
    simp_rw [fun n ↦ eLpNorm_one_eq_lintegral_eNorm (hg n).aestronglyMeasurable,
      fun n ↦ (ofReal_integral_norm_eq_lintegral_eNorm (hg n)).symm,
      ← ENNReal.ofReal_tsum_of_nonneg (fun n ↦ integral_nonneg fun _ ↦ norm_nonneg (g n _)) hnorm]
    exact ENNReal.ofReal_ne_top
  have hpoint : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)),
      HasSum (fun n ↦ g n t) (∑' n, g n t) := hae.mono fun _ ht ↦ ht.of_norm.hasSum
  have heq (t : ℝ) : (∑' n, g n t) =
      (t : ℂ) ^ (s - 1) • ∑' n : ℕ, a (n + 1) * f (d n * t) := by
    simp only [g, tsum_mul_left, smul_eq_mul]
  have hint := TauCeti.integrable_of_hasSum_of_summable_integral_norm hg hnorm hpoint
  simp_rw [heq] at hint
  refine ⟨hint, ?_⟩
  rw [mellin, setIntegral_congr_fun measurableSet_Ioi (fun t _ ↦ (heq t).symm),
    ← integral_tsum_of_summable_integral_norm hg hnorm]
  have hterm (n : ℕ) : (∫ t in Ioi 0, g n t) = LSeries.term a s (n + 1) * mellin f s := by
    calc
      _ = mellin (fun t ↦ a (n + 1) • f (d n * t)) s := by
        simp only [g, mellin, smul_eq_mul]
      _ = _ := by
        rw [mellin_const_smul, mellin_comp_mul_left f s (hd n), LSeries.term_of_ne_zero
          (Nat.succ_ne_zero n), div_eq_mul_inv, ← cpow_neg]
        simp [d, smul_eq_mul, mul_assoc]
  simp_rw [hterm, tsum_mul_right, LSeries, ha.tsum_eq_zero_add, LSeries.term_zero, zero_add]

end LSeriesSummable
