/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Poisson

/-!
# Similarity invariance and pointwise estimates for the complex Poisson kernel

The Poisson kernel is unchanged when its center is translated to the origin and its arguments
are multiplied by the inverse of a nonzero complex number. This normalized-coordinate identity
transports formulas between centered unit disks and translated, rescaled disks, including the
Green-kernel boundary derivative formula.

The file also collects elementary pointwise facts about the kernel: continuity away from the pole,
nonnegativity when the pole is no farther from the center than the evaluation point (so for poles
in the disk and evaluation points on its boundary circle), and the far-field bound on the circle
that drives recovery of boundary values by the Poisson integral, together with the derivative of
the Herglotz–Riesz kernel integral on a circle of arbitrary center `c`
(`CircleIntegrable.hasDerivAt_circleAverage_herglotzRieszKernel_smul`).
-/

public section

noncomputable section

namespace TauCeti

open Complex Metric

/-- Translating the center of the Poisson kernel to zero and multiplying by a nonzero complex number
does not change its value. -/
theorem poissonKernel_inv_mul_sub {c a z q : ℂ} (hq : q ≠ 0) :
    poissonKernel 0 (q⁻¹ * (a - c)) (q⁻¹ * (z - c)) = poissonKernel c a z := by
  simp only [poissonKernel_def, sub_zero, sub_sub_sub_cancel_right, ← mul_sub, norm_mul,
    norm_inv]
  field_simp

/-- The Poisson kernel is nonnegative when its pole `w` is no farther from the center `c` than
the evaluation point `z`; in particular for a pole in the closed disk and `z` on its boundary
circle. -/
theorem poissonKernel_nonneg {c w z : ℂ} (h : ‖w - c‖ ≤ ‖z - c‖) : 0 ≤ poissonKernel c w z := by
  rw [poissonKernel_def]
  exact div_nonneg (sub_nonneg.2 (by gcongr)) (by positivity)

/-- Away from its pole, the Poisson kernel is continuous as a function of the evaluation point. -/
@[fun_prop]
theorem continuousOn_poissonKernel {c w : ℂ} {s : Set ℂ} (hw : w ∉ s) :
    ContinuousOn (poissonKernel c w) s := by
  rw [funext (poissonKernel_def c w)]
  refine ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz ↦ ?_
  simpa [sub_eq_zero] using ne_of_mem_of_not_mem hz hw

/-- For a pole `w` in the closed disk and a boundary point `y` at distance at least `d > 0` from
`w`, the Poisson kernel is at most `(R ^ 2 - ‖w - c‖ ^ 2) / d ^ 2`. For fixed `d` this bound
tends to zero as `w` approaches the circle. -/
theorem poissonKernel_le_of_le_dist {c w y : ℂ} {R d : ℝ}
    (hd : 0 < d) (hw : w ∈ closedBall c |R|) (hy : y ∈ sphere c |R|) (hdist : d ≤ dist w y) :
    poissonKernel c w y ≤ (R ^ 2 - ‖w - c‖ ^ 2) / d ^ 2 := by
  rw [poissonKernel_def, mem_sphere_iff_norm.1 hy, sq_abs, sub_sub_sub_cancel_right,
    ← dist_eq_norm y w, dist_comm y w]
  refine div_le_div_of_nonneg_left (sub_nonneg.2 ?_) (by positivity) (by gcongr)
  rw [← sq_abs R]
  gcongr
  exact mem_closedBall_iff_norm.1 hw

end TauCeti

open Complex MeasureTheory Metric Real

/-- **Derivative of the Herglotz–Riesz kernel integral** on an arbitrary circle: if `f` is
circle-integrable on `sphere c |R|` and `w ∉ sphere c |R|`, then
`u ↦ circleAverage (fun ζ ↦ herglotzRieszKernel c u ζ • f ζ) c R` has derivative
`circleAverage (fun ζ ↦ (2 * (ζ - c) / (ζ - w) ^ 2) • f ζ) c R` at `w`.
This extends `hasDerivAt_circleAverage_herglotzRieszKernel_smul` from center `0` to `c`. -/
theorem CircleIntegrable.hasDerivAt_circleAverage_herglotzRieszKernel_smul
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {c w : ℂ} {R : ℝ}
    (hf : CircleIntegrable f c R) (hw : w ∉ sphere c |R|) :
    HasDerivAt (fun u ↦ circleAverage (fun ζ ↦ herglotzRieszKernel c u ζ • f ζ) c R)
      (circleAverage (fun ζ ↦ (2 * (ζ - c) / (ζ - w) ^ 2) • f ζ) c R) w := by
  have hf₀ : CircleIntegrable (fun ζ ↦ f (ζ + c)) 0 R := by
    have hmap : (fun θ ↦ f (circleMap 0 R θ + c)) = fun θ ↦ f (circleMap c R θ) := by
      ext θ
      exact congrArg f (by simp [circleMap]; ring)
    simpa only [CircleIntegrable, hmap] using hf
  have hw₀ : w - c ∉ sphere (0 : ℂ) |R| := by
    simpa [mem_sphere_iff_norm] using hw
  have hd := (_root_.hasDerivAt_circleAverage_herglotzRieszKernel_smul hf₀ hw₀).comp_sub_const w c
  have hfun : (fun u ↦ circleAverage (fun ζ ↦ herglotzRieszKernel 0 (u - c) ζ • f (ζ + c)) 0 R) =
      fun u ↦ circleAverage (fun ζ ↦ herglotzRieszKernel c u ζ • f ζ) c R := by
    ext u
    conv_rhs => rw [← circleAverage_map_add_const]
    simp [herglotzRieszKernel_add_const]
  have hval : circleAverage (fun ζ ↦ (2 * ζ / (ζ - (w - c)) ^ 2) • f (ζ + c)) 0 R =
      circleAverage (fun ζ ↦ (2 * (ζ - c) / (ζ - w) ^ 2) • f ζ) c R := by
    conv_rhs => rw [← circleAverage_map_add_const]
    congr 1
    ext ζ
    simp only [add_sub_cancel_right]
    congr 2
    ring
  rwa [hfun, hval] at hd

end
