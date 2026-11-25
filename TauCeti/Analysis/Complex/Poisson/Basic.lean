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
in the disk and evaluation points on its boundary circle), the far-field bound on the circle
that drives recovery of boundary values by the Poisson integral, and, on the unit circle, its
expression `(1 - w * conj z)⁻¹ + (1 - conj w * z)⁻¹ - 1` through Cauchy–Szegő kernels,
together with positivity of the real part of the Herglotz–Riesz kernel integral of nonnegative
data inside the disk (`CircleIntegrable.re_circleAverage_herglotzRieszKernel_smul_nonneg`) and its
derivative on a circle of arbitrary center `c`
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

open scoped ComplexConjugate in
/-- On the unit circle the Poisson kernel of the unit disk is twice the real part of the
Cauchy–Szegő kernel `(1 - w * conj z)⁻¹`, minus one. -/
theorem ofReal_poissonKernel_eq {w z : ℂ} (hz : ‖z‖ = 1) (hw : ‖w‖ < 1) :
    (poissonKernel 0 w z : ℂ) = (1 - w * conj z)⁻¹ + (1 - conj w * z)⁻¹ - 1 := by
  have hzz : z * conj z = 1 := by rw [mul_conj, normSq_eq_norm_sq, hz]; simp
  have hzw : z - w ≠ 0 := sub_ne_zero.2 (ne_of_apply_ne norm (hz.trans_ne hw.ne'))
  have h1 : 1 - w * conj z = conj z * (z - w) := by linear_combination (-1 : ℂ) * hzz
  have h2 : 1 - conj w * z = z * conj (z - w) := by rw [map_sub]; linear_combination (-1 : ℂ) * hzz
  have hz0 : z ≠ 0 := by rintro rfl; simp at hz
  have hzc : conj z ≠ 0 := by simpa using hz0
  have hzwc : conj (z - w) ≠ 0 := (map_ne_zero _).2 hzw
  rw [poissonKernel_def, h1, h2]
  simp only [sub_zero, hz]
  have hn : ((‖z - w‖ ^ 2 : ℝ) : ℂ) = (z - w) * conj (z - w) := by
    rw [mul_conj, normSq_eq_norm_sq]
  have hww : ((‖w‖ ^ 2 : ℝ) : ℂ) = w * conj w := by rw [mul_conj, normSq_eq_norm_sq]
  push_cast at hn hww ⊢
  rw [hn, hww]
  field_simp
  rw [map_sub]
  linear_combination (z * conj z - w * conj z - conj w * z) * hzz

end TauCeti

open Metric Real

/-- Nonnegative circle-integrable real boundary data on `sphere c |R|` have nonnegative
Herglotz–Riesz real part at every point `w ∈ ball c |R|`. -/
theorem CircleIntegrable.re_circleAverage_herglotzRieszKernel_smul_nonneg
    {f : ℂ → ℝ} {c w : ℂ} {R : ℝ} (hf : CircleIntegrable f c R)
    (hnonneg : ∀ ζ ∈ sphere c |R|, 0 ≤ f ζ) (hw : w ∈ ball c |R|) :
    0 ≤ (circleAverage (fun ζ ↦ herglotzRieszKernel c w ζ • (f ζ : ℂ)) c R).re := by
  have hw_not : w ∉ sphere c |R| := Set.disjoint_right.mp sphere_disjoint_ball hw
  have hf_c : CircleIntegrable (fun ζ ↦ (f ζ : ℂ)) c R := by
    simp only [CircleIntegrable, intervalIntegrable_iff] at hf ⊢
    exact Complex.ofRealCLM.integrable_comp hf
  have hK : CircleIntegrable (fun ζ ↦ herglotzRieszKernel c w ζ • (f ζ : ℂ)) c R :=
    hf_c.continuousOn_smul (continuousOn_herglotzRieszKernel_sphere hw_not)
  rw [← Complex.reCLM_apply, ← Complex.reCLM.circleAverage_comp_comm hK]
  refine circleAverage_nonneg_of_nonneg fun ζ hζ ↦ ?_
  have hre : (Complex.reCLM (herglotzRieszKernel c w ζ • (f ζ : ℂ))) =
      poissonKernel c w ζ * f ζ := by
    simp [poissonKernel_eq_re_herglotzRieszKernel, Complex.mul_re]
  rw [Function.comp_apply, hre]
  exact mul_nonneg
    (TauCeti.poissonKernel_nonneg
      ((mem_ball_iff_norm.mp hw).le.trans (mem_sphere_iff_norm.mp hζ).ge))
    (hnonneg ζ hζ)

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
