/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Complex.Log.Basic
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.DiscSeries
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Holomorphy

/-!
# Abel's five-term identity for the dilogarithm

For `x y : ℂ` with `‖x‖ + ‖y‖ < 1`, put `a = x / (1 - y)`, `b = y / (1 - x)` and
`c = x y / ((1 - x)(1 - y))`. Abel's five-term identity for the principal dilogarithm reads

`Li₂(c) = Li₂(a) + Li₂(b) - Li₂(x) - Li₂(y) - Log(1 - x) Log(1 - y)`.

The norm condition places all five arguments in the open unit disc, since
`‖c‖ ≤ ‖x‖ ‖y‖ / ((1 - ‖x‖)(1 - ‖y‖))` and the right side is less than `1` exactly when
`‖x‖ + ‖y‖ < 1`. On this domain every point `1 - w` that occurs has positive real part, so the
principal logarithms satisfy `Log(1 - a) = Log(1 - x - y) - Log(1 - y)`,
`Log(1 - b) = Log(1 - x - y) - Log(1 - x)` and `Log(1 - c) = Log(1 - a) - Log(1 - x)` with no
multiple of `2πi`. This principal-branch identity is the starting point for Abel's identity on
analytically continued branches and for the pentagon relation of the Rogers dilogarithm.

## Main results

* `TauCeti.Polylog.polylog_abel`: Abel's five-term identity for `polylog 2` on
  `‖x‖ + ‖y‖ < 1`.

## Implementation notes

Fix `y`. On the disc `‖x‖ < 1 - ‖y‖` the defect of the identity is differentiable in `x`, with
derivative computed from Euler's recursion `z Li₂'(z) = Li₁(z) = -Log(1 - z)` and the three
logarithmic identities above; this derivative vanishes, and the defect vanishes at `x = 0`.

## References

* Joseph Oesterlé, *Polylogarithmes*, Séminaire Bourbaki, exposé 762, Astérisque 216 (1993),
  §4.1, (30), p. 59.
* Don Zagier, *The dilogarithm function*, in *Frontiers in Number Theory, Physics, and
  Geometry II*, Springer (2007), Part I §2, p. 9.
-/

public section

open Metric Set
open Complex (norm_div_one_sub_lt_one norm_mul_div_one_sub_mul_one_sub_lt_one
  one_sub_mem_slitPlane_of_norm_lt_one slitPlane_ne_zero)

namespace TauCeti.Polylog

/-- The three logarithmic product identities behind Abel's identity: on `‖x‖ + ‖y‖ < 1` the
principal logarithms of `1 - a`, `1 - b` and `1 - c` split with no multiple of `2πi`. -/
private lemma log_one_sub_abel {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    Complex.log (1 - x / (1 - y)) = Complex.log (1 - x - y) - Complex.log (1 - y) ∧
    Complex.log (1 - y / (1 - x)) = Complex.log (1 - x - y) - Complex.log (1 - x) ∧
    Complex.log (1 - x * y / ((1 - x) * (1 - y))) =
      Complex.log (1 - x - y) - Complex.log (1 - y) - Complex.log (1 - x) := by
  have hre : ∀ w : ℂ, ‖w‖ < 1 → 0 < (1 - w).re := fun w hw ↦
    Complex.re_one_sub_pos hw.le fun h ↦ by simp [h] at hw
  have hx : ‖x‖ < 1 := by linarith [norm_nonneg y]
  have hy : ‖y‖ < 1 := by linarith [norm_nonneg x]
  have hx1 : 1 - x ≠ 0 := slitPlane_ne_zero (one_sub_mem_slitPlane_of_norm_lt_one hx)
  have hy1 : 1 - y ≠ 0 := slitPlane_ne_zero (one_sub_mem_slitPlane_of_norm_lt_one hy)
  have hxy' : 0 < (1 - x - y).re := by
    rw [sub_sub]
    exact hre _ ((norm_add_le x y).trans_lt hxy)
  have ha : 1 - x / (1 - y) = (1 - x - y) / (1 - y) := by field_simp; ring
  have hb : 1 - y / (1 - x) = (1 - x - y) / (1 - x) := by field_simp
  have hc : 1 - x * y / ((1 - x) * (1 - y)) = (1 - x / (1 - y)) / (1 - x) := by
    field_simp; ring
  have hloga : Complex.log (1 - x / (1 - y)) = Complex.log (1 - x - y) - Complex.log (1 - y) := by
    rw [ha, Complex.log_div_of_re_pos hxy' (hre y hy)]
  refine ⟨hloga, by rw [hb, Complex.log_div_of_re_pos hxy' (hre x hx)], ?_⟩
  rw [hc, Complex.log_div_of_re_pos (hre _ (norm_div_one_sub_lt_one hxy)) (hre x hx), hloga]

/-- The defect of Abel's identity, as a function of `x` for fixed `y`, has derivative zero on
`‖x‖ + ‖y‖ < 1`. -/
private lemma hasDerivAt_abel_defect {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    HasDerivAt (fun w : ℂ ↦ polylog 2 (w * y / ((1 - w) * (1 - y))) - polylog 2 (w / (1 - y)) -
        polylog 2 (y / (1 - w)) + polylog 2 w + polylog 2 y +
        Complex.log (1 - w) * Complex.log (1 - y)) 0 x := by
  have hx : ‖x‖ < 1 := by linarith [norm_nonneg y]
  have hy : ‖y‖ < 1 := by linarith [norm_nonneg x]
  have ha := norm_div_one_sub_lt_one hxy
  have hb := norm_div_one_sub_lt_one (x := y) (y := x) (by linarith)
  have hc := norm_mul_div_one_sub_mul_one_sub_lt_one hxy
  have hx1 : 1 - x ≠ 0 := slitPlane_ne_zero (one_sub_mem_slitPlane_of_norm_lt_one hx)
  have hy1 : 1 - y ≠ 0 := slitPlane_ne_zero (one_sub_mem_slitPlane_of_norm_lt_one hy)
  have hD : ∀ z : ℂ, ‖z‖ < 1 → HasDerivAt (polylog 2) (deriv (polylog 2) z) z := fun z hz ↦
    (differentiableAt_polylog 2 (one_sub_mem_slitPlane_of_norm_lt_one hz)).hasDerivAt
  -- Off `0`, Euler's recursion `z Li₂'(z) = Li₁(z)` gives `Li₂'(z) = -Log(1 - z) / z`.
  have hD' : ∀ z : ℂ, ‖z‖ < 1 → z ≠ 0 → deriv (polylog 2) z = -Complex.log (1 - z) / z :=
    fun z hz hz0 ↦ by
      simpa using deriv_polylog 2 (one_sub_mem_slitPlane_of_norm_lt_one hz) hz0
  have h1x : HasDerivAt (fun w : ℂ ↦ 1 - w) (0 - 1) x :=
    (hasDerivAt_const x 1).sub (hasDerivAt_id' x)
  have h := ((((hD _ hc).comp x (((hasDerivAt_id' x).mul_const y).div
      (h1x.mul_const (1 - y)) (mul_ne_zero hx1 hy1))).sub
    ((hD _ ha).comp x ((hasDerivAt_id' x).div_const (1 - y)))).sub
    ((hD _ hb).comp x ((hasDerivAt_const x y).div h1x hx1))).add (hD x hx) |>.add_const
      (polylog 2 y) |>.add (((Complex.hasDerivAt_log
        (one_sub_mem_slitPlane_of_norm_lt_one hx)).comp x h1x).mul_const (Complex.log (1 - y)))
  refine h.congr_deriv ?_
  -- It remains to show that the derivative computed by the chain rule vanishes.
  rcases eq_or_ne y 0 with rfl | hy0
  · simp
  rw [hD' _ hb (div_ne_zero hy0 hx1)]
  rcases eq_or_ne x 0 with rfl | hx0
  · simp only [zero_mul, zero_div, sub_zero, (hasDerivAt_polylog_zero 2).deriv]
    field_simp
    ring
  obtain ⟨hloga, hlogb, hlogc⟩ := log_one_sub_abel hxy
  rw [hD' _ hc (div_ne_zero (mul_ne_zero hx0 hy0) (mul_ne_zero hx1 hy1)),
    hD' _ ha (div_ne_zero hx0 hy1), hD' x hx hx0, hloga, hlogb, hlogc]
  field_simp
  ring

/-- **Abel's five-term identity.** For `x y : ℂ` with `‖x‖ + ‖y‖ < 1`, the principal dilogarithm
satisfies
`Li₂(x y / ((1 - x)(1 - y))) = Li₂(x / (1 - y)) + Li₂(y / (1 - x)) - Li₂(x) - Li₂(y)
  - Log(1 - x) Log(1 - y)`.
All five arguments lie in the open unit disc. -/
theorem polylog_abel {x y : ℂ} (hxy : ‖x‖ + ‖y‖ < 1) :
    polylog 2 (x * y / ((1 - x) * (1 - y))) =
      polylog 2 (x / (1 - y)) + polylog 2 (y / (1 - x)) - polylog 2 x - polylog 2 y -
        Complex.log (1 - x) * Complex.log (1 - y) := by
  have hy : ‖y‖ < 1 := by linarith [norm_nonneg x]
  let F : ℂ → ℂ := fun w ↦ polylog 2 (w * y / ((1 - w) * (1 - y))) - polylog 2 (w / (1 - y)) -
    polylog 2 (y / (1 - w)) + polylog 2 w + polylog 2 y +
    Complex.log (1 - w) * Complex.log (1 - y)
  have hmem : ∀ w ∈ ball (0 : ℂ) (1 - ‖y‖), ‖w‖ + ‖y‖ < 1 := fun w hw ↦ by
    rw [mem_ball_zero_iff] at hw
    linarith
  have hF : ∀ w ∈ ball (0 : ℂ) (1 - ‖y‖), HasDerivAt F 0 w := fun w hw ↦
    hasDerivAt_abel_defect (hmem w hw)
  have hconst := isOpen_ball.is_const_of_deriv_eq_zero (convex_ball (0 : ℂ) _).isPreconnected
    (fun w hw ↦ (hF w hw).differentiableAt.differentiableWithinAt)
    (fun w hw ↦ (hF w hw).deriv) (x := x) (y := 0)
    (mem_ball_zero_iff.mpr (by linarith)) (mem_ball_self (by linarith))
  have h0 : F 0 = 0 := by simp [F]
  rw [h0] at hconst
  simp only [F] at hconst
  linear_combination hconst

end TauCeti.Polylog
