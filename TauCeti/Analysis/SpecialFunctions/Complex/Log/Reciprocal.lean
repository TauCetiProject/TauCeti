/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.Harmonic.Constructions
public import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.Analysis.Complex.Angle
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic

/-!
# The real part of the reciprocal of the logarithm

In polar coordinates `z = r e^{iθ}`, `-π < θ ≤ π`, the principal logarithm is `log r + iθ`, so

`Re (1 / log z) = log r / ((log r)² + θ²)`

(`Complex.inv_log_re`). The logarithm jumps across the negative real axis, but only through the
sign of `θ`, which this expression does not see: `Re (1 / log z)` is continuous at every point
other than `1`, where the logarithm vanishes, including `0`, where it tends to `0` because
`|Re (1 / log z)| ≤ 1 / |log ‖z‖|` (`Complex.continuousAt_inv_log_re`). Away from the negative
real axis and from `1` it is the real part of a holomorphic function, hence harmonic
(`Complex.harmonicAt_inv_log_re`), and it is negative on the punctured unit disc
(`Complex.inv_log_re_neg`).

So `-Re (1 / log z)` is a harmonic function on the unit disc slit along a radius, positive and
continuous up to the slit, and tending to `0` at the end of the slit. This makes it a barrier at
the end of a slit in the sense of Perron's method, and in two dimensions it shows that the end
of a segment outside a domain is a regular boundary point.

## References

* T. Ransford, *Potential Theory in the Complex Plane*, London Mathematical Society Student
  Texts 28, Cambridge University Press, 1995, Section 4.2 (barriers built from `1 / log`).
-/

public section

open Filter Set
open scoped Topology

namespace Complex

/-- **`Re (1 / log z)` in polar coordinates.** For every `z`,
`Re (1 / log z) = log ‖z‖ / ((log ‖z‖)² + (arg z)²)`. At `z = 0` both sides vanish. -/
theorem inv_log_re (z : ℂ) :
    (log z)⁻¹.re = Real.log ‖z‖ / (Real.log ‖z‖ ^ 2 + arg z ^ 2) := by
  rw [inv_re, normSq_apply, log_re, log_im]
  ring

/-- `|Re (1 / log z)| ≤ 1 / |log ‖z‖|`: the reciprocal of the logarithm is small near `0`. -/
theorem abs_inv_log_re_le (z : ℂ) : |(log z)⁻¹.re| ≤ |Real.log ‖z‖|⁻¹ := by
  rw [inv_log_re]
  rcases eq_or_ne (Real.log ‖z‖) 0 with h | h
  · simp [h]
  have hL : 0 < Real.log ‖z‖ ^ 2 := by positivity
  calc |Real.log ‖z‖ / (Real.log ‖z‖ ^ 2 + arg z ^ 2)|
      = |Real.log ‖z‖| / (Real.log ‖z‖ ^ 2 + arg z ^ 2) := by
        rw [abs_div, abs_of_pos (add_pos_of_pos_of_nonneg hL (sq_nonneg _))]
    _ ≤ |Real.log ‖z‖| / Real.log ‖z‖ ^ 2 :=
        div_le_div_of_nonneg_left (abs_nonneg _) hL (le_add_of_nonneg_right (sq_nonneg _))
    _ = |Real.log ‖z‖|⁻¹ := by
        rw [← sq_abs]
        field_simp

/-- **`Re (1 / log z)` is negative on the punctured unit disc.** -/
theorem inv_log_re_neg {z : ℂ} (hz : z ≠ 0) (hz1 : ‖z‖ < 1) : (log z)⁻¹.re < 0 := by
  have hlog : Real.log ‖z‖ < 0 := Real.log_neg (norm_pos_iff.2 hz) hz1
  have : Real.log ‖z‖ ≠ 0 := hlog.ne
  rw [inv_log_re]
  exact div_neg_of_neg_of_pos hlog (by positivity)

/-- **`Re (1 / log z)` is continuous away from `1`.** The logarithm jumps across the negative real
axis, but `Re (1 / log z) = log ‖z‖ / ((log ‖z‖)² + (arg z)²)` depends on the argument only
through `|arg z|`, which is continuous on the punctured plane. At `0` the function tends to its
value `0`. -/
theorem continuousAt_inv_log_re {z : ℂ} (hz : z ≠ 1) :
    ContinuousAt (fun w ↦ (log w)⁻¹.re) z := by
  rcases eq_or_ne z 0 with rfl | hz0
  · -- Near `0`, `|Re (1 / log w)| ≤ 1 / |log ‖w‖|`, and `|log ‖w‖| → ∞`.
    rw [← continuousWithinAt_compl_self, ContinuousWithinAt]
    have hlog : Tendsto (fun w : ℂ ↦ |Real.log ‖w‖|⁻¹) (𝓝[≠] 0) (𝓝 0) :=
      (tendsto_abs_atBot_atTop.comp
        (Real.tendsto_log_nhdsGT_zero.comp tendsto_norm_nhdsNE_zero)).inv_tendsto_atTop
    have h0 : (log (0 : ℂ))⁻¹.re = 0 := by simp
    rw [h0]
    exact squeeze_zero_norm (fun w ↦ (Real.norm_eq_abs _).trans_le (abs_inv_log_re_le w)) hlog
  -- Away from `0`, `(arg w)² = (angle w 1)²`, and the denominator is `‖log z‖² ≠ 0`.
  have hlog : log z ≠ 0 := fun h ↦ hz (by rw [← exp_log hz0, h, exp_zero])
  have heq : (fun w ↦ (log w)⁻¹.re) =ᶠ[𝓝 z] fun w ↦
      Real.log ‖w‖ / (Real.log ‖w‖ ^ 2 + InnerProductGeometry.angle w 1 ^ 2) := by
    filter_upwards [isOpen_ne.mem_nhds hz0] with w hw
    rw [inv_log_re, angle_one_right hw, sq_abs]
  refine ContinuousAt.congr ?_ heq.symm
  have hnorm : ContinuousAt (fun w : ℂ ↦ Real.log ‖w‖) z :=
    (Real.continuousAt_log (norm_ne_zero_iff.2 hz0)).comp continuous_norm.continuousAt
  have hangle : ContinuousAt (fun w : ℂ ↦ InnerProductGeometry.angle w 1) z :=
    (InnerProductGeometry.continuousAt_angle (x := (z, (1 : ℂ))) hz0 one_ne_zero).comp
      (f := fun w : ℂ ↦ (w, (1 : ℂ))) (by fun_prop)
  refine hnorm.div ((hnorm.pow 2).add (hangle.pow 2)) ?_
  have hpos := normSq_pos.2 hlog
  rw [normSq_apply, log_re, log_im] at hpos
  rw [angle_one_right hz0, sq_abs]
  nlinarith

/-- **`Re (1 / log z)` is harmonic on the slit plane away from `1`**, being the real part of the
holomorphic function `1 / log z` there. -/
theorem harmonicAt_inv_log_re {z : ℂ} (hz : z ∈ slitPlane) (hz1 : z ≠ 1) :
    InnerProductSpace.HarmonicAt (fun w ↦ (log w)⁻¹.re) z := by
  have hlog : log z ≠ 0 := fun h ↦ hz1 (by rw [← exp_log (slitPlane_ne_zero hz), h, exp_zero])
  exact ((analyticAt_clog hz).inv hlog).harmonicAt_re

end Complex
