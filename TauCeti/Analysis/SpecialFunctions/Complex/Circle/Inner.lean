/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Complex.Circle
public import TauCeti.Analysis.Complex.Inner
public import TauCeti.Analysis.InnerProductSpace.Sphere.Cap

/-!
# Real inner products of points of the unit circle

The unit circle `Circle` sits in `ℂ`, a real inner product space. This file records how the real
inner product interacts with the group structure and the exponential of `Circle`: rotating the
circle back by `c` turns the height `Im` into the height `⟪z, c i⟫` along `c i`, and the inner
product of `exp (a i)` and `exp (b i)` is `cos (a - b)`. These identities read arcs of the circle
around a point `c i` as level sets of an inner product, which is how knotted arcs are slid along a
great circle.

## Main results

* `Circle.exp_pi`: `exp (π i) = -1` on the circle.
* `Circle.im_inv_mul_eq_inner`: `Im (c⁻¹ z) = ⟪z, c i⟫`.
* `Circle.inner_exp_exp`: `⟪exp (a i), exp (b i)⟫ = cos (a - b)`.
* `Circle.im_pos_of_le_inner`: the closed arc `⟪z, c i⟫ ≥ r` around `c i` lies in the open upper
  half of the circle when `Re c ≥ 0` and `1 - (Re c)² < r²`.
-/

public section

open Real
open scoped RealInnerProductSpace

namespace Circle

/-- The exponential of the circle sends `π` to `-1`. -/
@[simp]
theorem exp_pi : Circle.exp π = -1 := by
  apply Subtype.ext
  simp [Circle.coe_exp, Complex.exp_pi_mul_I]

/-- Rotating the circle back by `c` turns the height `Im` into the height along `c i`. -/
theorem im_inv_mul_eq_inner (c z : Circle) :
    ((c⁻¹ * z : Circle) : ℂ).im = ⟪(z : ℂ), (c : ℂ) * Complex.I⟫ := by
  rw [Circle.coe_mul, Circle.coe_inv_eq_conj, Complex.inner]
  simp only [Complex.mul_im, Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.I_re,
    Complex.I_im]
  ring

/-- The inner product of two points `exp (a i)` and `exp (b i)` of the circle is `cos (a - b)`. -/
theorem inner_exp_exp (a b : ℝ) :
    ⟪(Circle.exp a : ℂ), (Circle.exp b : ℂ)⟫ = cos (a - b) := by
  rw [Circle.coe_exp, Circle.coe_exp, Complex.inner, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im,
    Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_sub]
  ring

/-- Every closed arc `⟪z, c i⟫ ≥ r` around `c i`, with `c` in the right half-plane, lies in the open
upper half of the circle, when `r > 0` and `1 - (Re c)² < r²`. -/
theorem im_pos_of_le_inner {r : ℝ} (hr : 0 < r) {c z : Circle} (hc : 0 ≤ (c : ℂ).re)
    (hc' : 1 - (c : ℂ).re ^ 2 < r ^ 2) (hz : r ≤ ⟪(z : ℂ), (c : ℂ) * Complex.I⟫) :
    0 < (z : ℂ).im := by
  have hcI : ⟪(c : ℂ) * Complex.I, Complex.I⟫ = (c : ℂ).re := by
    rw [Complex.real_inner_I_right]
    simp
  have := TauCeti.inner_pos_of_le_inner (u := Complex.I) (Circle.norm_coe z) (by simp) (by simp)
    hr (by rwa [hcI]) (by rwa [hcI]) hz
  rwa [Complex.real_inner_I_right] at this

end Circle
