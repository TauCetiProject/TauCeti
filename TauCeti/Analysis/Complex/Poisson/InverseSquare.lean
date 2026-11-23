/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Poisson.Integral
import TauCeti.Geometry.Euclidean.Inversion

/-!
# The circle mean of the inverse-square distance

For a point `w` off the circle of radius `R` about `c`, the circle average of `‖z - w‖⁻²` over
that circle is the reciprocal of `|R ^ 2 - ‖w - c‖ ^ 2|`:

* `TauCeti.circleAverage_inv_norm_sub_sq_of_mem_ball`: for `w` inside the circle the average is
  `(R ^ 2 - ‖w - c‖ ^ 2)⁻¹`; this is the statement that the Poisson kernel has mean one, since on
  the circle the Poisson kernel is `(R ^ 2 - ‖w - c‖ ^ 2) / ‖z - w‖ ^ 2`.
* `TauCeti.circleAverage_inv_norm_sub_sq_of_notMem_closedBall`: for `w` outside the closed disc
  the average is `(‖w - c‖ ^ 2 - R ^ 2)⁻¹`. On the circle, `‖z - w‖` is a constant multiple of
  the distance from `z` to the inversion `EuclideanGeometry.inversion c |R| w` of `w` in the
  circle, which lies inside, so this case reduces to the first one.

The second formula is the exact kernel integral in the classical estimate of the proximity
function of a logarithmic derivative: differentiating the Herglotz–Riesz representation of a
logarithm on the circle of radius `R` produces the kernel `2 w / (w - z) ^ 2`, whose norm is
`2 R / ‖z - w‖ ^ 2`, and averaging over `z` on a smaller circle of radius `r` gives
`2 R / (R ^ 2 - r ^ 2)`.

## References

* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. **38** (2025), 627–702, equation (6.1.12) and the proof of Lemma 6.1.7.
-/

public section

namespace TauCeti

open Complex Metric Real Set

variable {c w : ℂ} {R : ℝ}

/-- For `w` strictly inside the circle of radius `|R|` about `c`, the circle average of
`‖z - w‖⁻²` is `(R ^ 2 - ‖w - c‖ ^ 2)⁻¹`. -/
theorem circleAverage_inv_norm_sub_sq_of_mem_ball (hw : w ∈ ball c |R|) :
    circleAverage (fun z ↦ (‖z - w‖ ^ 2)⁻¹) c R = (R ^ 2 - ‖w - c‖ ^ 2)⁻¹ := by
  have hK : EqOn (poissonKernel c w) (fun z ↦ (R ^ 2 - ‖w - c‖ ^ 2) • (‖z - w‖ ^ 2)⁻¹)
      (sphere c |R|) := by
    intro z hz
    rw [mem_sphere_iff_norm] at hz
    simp [poissonKernel_def, hz, div_eq_mul_inv]
  have h := circleAverage_poissonKernel hw
  rw [circleAverage_congr_sphere hK, circleAverage_fun_smul, smul_eq_mul] at h
  exact eq_inv_of_mul_eq_one_right h

/-- For `w` outside the closed disc of radius `|R|` about `c`, the circle average of `‖z - w‖⁻²`
over the boundary circle is `(‖w - c‖ ^ 2 - R ^ 2)⁻¹`. -/
theorem circleAverage_inv_norm_sub_sq_of_notMem_closedBall (hw : w ∉ closedBall c |R|) :
    circleAverage (fun z ↦ (‖z - w‖ ^ 2)⁻¹) c R = (‖w - c‖ ^ 2 - R ^ 2)⁻¹ := by
  rw [mem_closedBall_iff_norm, not_le] at hw
  rcases eq_or_ne R 0 with rfl | hR
  · simp [norm_sub_rev c w]
  have hR' : 0 < |R| := abs_pos.2 hR
  have hb : 0 < ‖w - c‖ := hR'.trans hw
  have hwc : w ≠ c := sub_ne_zero.1 (norm_pos_iff.1 hb)
  set a := EuclideanGeometry.inversion c |R| w
  have ha : ‖a - c‖ = R ^ 2 / ‖w - c‖ := by
    rw [← dist_eq_norm, EuclideanGeometry.dist_inversion_center, dist_eq_norm, sq_abs]
  have ha_mem : a ∈ ball c |R| := by
    rwa [mem_ball, dist_inversion_center_lt_iff hR' hwc, dist_eq_norm]
  have hEq : EqOn (fun z ↦ (‖z - w‖ ^ 2)⁻¹)
      (fun z ↦ (R ^ 2 / ‖w - c‖ ^ 2) • (‖z - a‖ ^ 2)⁻¹) (sphere c |R|) := by
    intro z hz
    have hzc : z ≠ c := ne_of_mem_sphere hz hR'.ne'
    have h := EuclideanGeometry.dist_inversion_mul_dist_center_eq (R := |R|) hzc hwc
    rw [EuclideanGeometry.inversion_of_mem_sphere hz, mem_sphere.1 hz, dist_comm z a] at h
    simp only [dist_eq_norm] at h
    have hzw : ‖z - w‖ = ‖z - a‖ * ‖w - c‖ / |R| := by
      rw [norm_sub_rev z a, ← h, mul_div_cancel_right₀ _ hR'.ne']
    dsimp only
    rw [smul_eq_mul, hzw, div_pow, mul_pow, sq_abs]
    simp only [div_eq_mul_inv, mul_inv, inv_inv]
    ring
  rw [circleAverage_congr_sphere hEq, circleAverage_fun_smul, smul_eq_mul,
    circleAverage_inv_norm_sub_sq_of_mem_ball ha_mem, ha]
  have hb2 : ‖w - c‖ ^ 2 - R ^ 2 ≠ 0 := by
    rw [← sq_abs R]
    exact (sub_pos.2 (pow_lt_pow_left₀ hw hR'.le two_ne_zero)).ne'
  field_simp

end TauCeti
