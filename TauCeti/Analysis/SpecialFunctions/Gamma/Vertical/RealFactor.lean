/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Gamma.Archimedean

import TauCeti.Analysis.SpecialFunctions.Gamma.LogConvex
import TauCeti.Analysis.SpecialFunctions.Gamma.Vertical.Basic

/-!
# Endpoint bounds for the real archimedean gamma factor

On a positive vertical line, the norm of Deligne's real gamma factor is bounded by its value
at height zero. On a closed strip in the right half-plane, its largest norm is therefore the
larger of its two real endpoint values, by the log-convexity of the positive real Gamma function
(`Real.convexOn_log_Gamma`). This gives explicit strip bounds for the gamma factors of Mellin
transforms without any restriction on the imaginary part.
-/

public section

open Set

namespace Complex

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
