/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Deligne
import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean
import TauCeti.Analysis.SpecialFunctions.Gamma.HalfPlane
import TauCeti.Analysis.SpecialFunctions.Gamma.LogConvex
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical.Basic

/-!
# Vertical bounds for the real archimedean factor

On a vertical line in the right half-plane, the norm of Deligne's real gamma factor is bounded
by its value at height zero. Log-convexity on the positive real axis then bounds the norm
on a closed strip by the larger of the two real endpoint norms. The factor also absorbs
linear growth in the norm of its argument on such a strip.
-/

public section

open Complex

namespace Complex

open Set

/-- On a vertical line to the right of zero, the norm of the real gamma factor is bounded by
its norm at height zero. -/
theorem norm_Gammaℝ_le_norm_Gammaℝ_re {z : ℂ} (hz : 0 < z.re) :
    ‖Gammaℝ z‖ ≤ ‖Gammaℝ (z.re : ℂ)‖ := by
  rw [norm_Gammaℝ z, norm_Gammaℝ_ofReal hz.le]
  have h := norm_Gamma_le_Gamma_re (s := z / 2) (by rw [div_ofNat_re]; positivity)
  rw [div_ofNat_re] at h
  exact mul_le_mul_of_nonneg_left h (by positivity)

/-- Deligne's real gamma factor has log-convex norm on the positive real axis. -/
theorem convexOn_log_norm_Gammaℝ :
    ConvexOn ℝ (Ioi 0) (fun x : ℝ ↦ Real.log ‖Gammaℝ (x : ℂ)‖) := by
  have hlin : ConvexOn ℝ (Ioi (0 : ℝ)) (fun x ↦ -x / 2 * Real.log Real.pi) := by
    refine ⟨convex_Ioi _, fun x _ y _ a b _ _ _ ↦ ?_⟩
    simp only [smul_eq_mul]
    ring_nf
    exact le_rfl
  have hΓ : ConvexOn ℝ (Ioi (0 : ℝ)) (fun x ↦ Real.log (Real.Gamma (x / 2))) := by
    simpa only [add_zero] using Real.convexOn_log_Gamma_add_div (c := 0) (m := 2)
      (by norm_num) (by norm_num)
  refine (hlin.add hΓ).congr fun x hx ↦ ?_
  have hx' : 0 < x := hx
  simp only [Pi.add_apply]
  rw [norm_Gammaℝ_ofReal hx'.le, Real.log_mul (by positivity)
    (Real.Gamma_pos_of_pos (by positivity : 0 < x / 2)).ne', Real.log_rpow Real.pi_pos]

/-- On a closed strip with positive real endpoints, the norm of the real gamma factor is
bounded by the larger of its norms at the real endpoints. -/
theorem norm_Gammaℝ_le_max_of_re_mem_Icc {a b : ℝ} (ha : 0 < a) {z : ℂ}
    (hz : z.re ∈ Icc a b) : ‖Gammaℝ z‖ ≤ max ‖Gammaℝ (a : ℂ)‖ ‖Gammaℝ (b : ℂ)‖ := by
  have hb : 0 < b := ha.trans_le (hz.1.trans hz.2)
  have hz' : 0 < z.re := ha.trans_le hz.1
  refine (norm_Gammaℝ_le_norm_Gammaℝ_re hz').trans ?_
  have h := convexOn_log_norm_Gammaℝ.le_max_of_mem_Icc (mem_Ioi.mpr ha) (mem_Ioi.mpr hb) hz
  rw [le_max_iff] at h ⊢
  have hpos {x : ℝ} (hx : 0 < x) : 0 < ‖Gammaℝ (x : ℂ)‖ :=
    norm_pos_iff.mpr (Gammaℝ_ne_zero_of_re_pos (by simpa using hx))
  exact h.imp ((Real.log_le_log_iff (hpos hz') (hpos ha)).mp)
    ((Real.log_le_log_iff (hpos hz') (hpos hb)).mp)

end Complex

namespace TauCeti.Complex

/-- `Γ_ℝ(z)` is bounded by a strip-dependent constant times `(1 + ‖z‖)⁻¹` on a closed
vertical strip strictly to the right of zero. -/
theorem exists_norm_Gammaℝ_mul_one_add_norm_le_of_re_mem_Icc {a b : ℝ} (ha : 0 < a) :
    ∃ C > 0, ∀ z : ℂ, z.re ∈ Set.Icc a b → ‖Gammaℝ z‖ * (1 + ‖z‖) ≤ C := by
  let B (x : ℝ) := Real.pi ^ (-x / 2) * (x / 2 + 2) ^ (x / 2 + 2)
  have hcont : ContinuousOn B (Set.Icc a b) := by
    apply (continuous_const.rpow (by fun_prop) (fun _ ↦ Or.inl Real.pi_pos.ne')).continuousOn.mul
    exact (by fun_prop : Continuous fun x : ℝ ↦ x / 2 + 2).continuousOn.rpow
      (by fun_prop) (fun x hx ↦ Or.inl (by linarith [hx.1] : x / 2 + 2 ≠ 0))
  obtain ⟨M, hM⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont
  refine ⟨2 * max 1 M * (1 + a⁻¹), by positivity, fun z hz ↦ ?_⟩
  have hz0 : 0 < ‖z‖ := ha.trans_le (hz.1.trans (re_le_norm z))
  have hg := norm_Gamma_le_re_add_two_rpow_div (z := z / 2)
    (by rw [div_ofNat_re]; linarith [hz.1])
  rw [div_ofNat_re, norm_div, norm_ofNat] at hg
  have hB : ‖Gammaℝ z‖ * ‖z‖ ≤ 2 * max 1 M := by
    rw [norm_Gammaℝ]
    calc
      _ ≤ (Real.pi ^ (-z.re / 2) * ((z.re / 2 + 2) ^ (z.re / 2 + 2) / (‖z‖ / 2))) * ‖z‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hg (by positivity)) hz0.le
      _ = 2 * B z.re := by dsimp only [B]; field_simp
      _ ≤ _ := by linarith [(le_abs_self _).trans ((hM z.re hz).trans (le_max_right 1 M))]
  have hzA : ‖z‖⁻¹ ≤ a⁻¹ := inv_anti₀ ha (hz.1.trans (re_le_norm z))
  calc
    _ = ‖Gammaℝ z‖ * ‖z‖ * (1 + ‖z‖⁻¹) := by field_simp; ring
    _ ≤ _ := mul_le_mul hB (add_le_add_right hzA _) (by positivity) (by positivity)

end TauCeti.Complex
