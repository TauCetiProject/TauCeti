/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.Poisson.Integral

/-!
# The circle mean of the inverse-square distance

For a point `w` off the circle of radius `R` about `c`, the circle average of `‖z - w‖⁻²` over
that circle is the reciprocal of `|R ^ 2 - ‖w - c‖ ^ 2|`:

* `TauCeti.circleAverage_inv_norm_sub_sq_of_mem_ball`: for `w` inside the circle the average is
  `(R ^ 2 - ‖w - c‖ ^ 2)⁻¹`; this is the statement that the Poisson kernel has mean one, since on
  the circle the Poisson kernel is `(R ^ 2 - ‖w - c‖ ^ 2) / ‖z - w‖ ^ 2`.
* `TauCeti.circleAverage_inv_norm_sub_sq_of_notMem_closedBall`: for `w` outside the closed disc
  the average is `(‖w - c‖ ^ 2 - R ^ 2)⁻¹`. On the circle, `‖z - w‖` is a constant multiple of
  the distance from `z` to the reflection `c + R ^ 2 / conj (w - c)` of `w`, which lies inside,
  so this case reduces to the first one.

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

open Complex ComplexConjugate Metric Real Set

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

/-- On the circle of radius `|R|` about `c`, the distance to `w` is `‖w - c‖ / |R|` times the
distance to the reflection `c + R ^ 2 / conj (w - c)` of `w` in that circle. -/
private lemma norm_sub_reflection_mul_norm (hwc : w ≠ c) {z : ℂ} (hz : z ∈ sphere c |R|) :
    ‖z - (c + (R ^ 2 : ℂ) / conj (w - c))‖ * ‖w - c‖ = |R| * ‖z - w‖ := by
  rw [mem_sphere_iff_norm] at hz
  have hb : conj (w - c) ≠ 0 := (map_ne_zero _).2 (sub_ne_zero.2 hwc)
  have hR : (R ^ 2 : ℂ) = (z - c) * conj (z - c) := by
    rw [mul_conj, normSq_eq_norm_sq, hz, sq_abs, ofReal_pow]
  have key : (z - (c + (R ^ 2 : ℂ) / conj (w - c))) * conj (w - c) =
      (z - c) * conj (w - z) := by
    rw [hR, sub_add_eq_sub_sub, sub_mul, div_mul_cancel₀ _ hb, ← mul_sub, ← map_sub,
      sub_sub_sub_cancel_right]
  rw [← norm_conj (w - c), ← norm_mul, key, norm_mul, norm_conj, hz, norm_sub_rev w z]

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
  set a := c + (R ^ 2 : ℂ) / conj (w - c)
  have ha : ‖a - c‖ = R ^ 2 / ‖w - c‖ := by
    rw [add_sub_cancel_left, norm_div, norm_conj, norm_pow, norm_real, Real.norm_eq_abs, sq_abs]
  have ha_mem : a ∈ ball c |R| := by
    rw [mem_ball_iff_norm, ha, div_lt_iff₀ hb, ← sq_abs, sq]
    exact mul_lt_mul_of_pos_left hw hR'
  have hEq : EqOn (fun z ↦ (‖z - w‖ ^ 2)⁻¹)
      (fun z ↦ (R ^ 2 / ‖w - c‖ ^ 2) • (‖z - a‖ ^ 2)⁻¹) (sphere c |R|) := by
    intro z hz
    have h := norm_sub_reflection_mul_norm hwc hz
    have hzw : ‖z - w‖ = ‖z - a‖ * ‖w - c‖ / |R| := by
      rw [h, mul_div_cancel_left₀ _ hR'.ne']
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
