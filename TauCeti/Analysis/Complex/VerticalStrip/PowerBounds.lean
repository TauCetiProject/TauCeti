/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Hadamard

/-!
# Three-lines bounds in a scale parameter

When the bounds on the two edges are powers of a common positive scale, the exponent in
Hadamard's three-lines estimate is the affine interpolation of the two edge exponents.
-/

public section

open Complex Complex.HadamardThreeLines Set

namespace TauCeti.Complex.HadamardThreeLines

/-- Interpolate bounds `A * T ^ p` and `B * T ^ q` across a vertical strip. The constant
`max A B` is uniform in the position in the strip. -/
theorem norm_le_max_mul_rpow_of_mem_verticalClosedStrip {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℂ E] {f : ℂ → E} {a b A B T p q : ℝ} {z : ℂ}
    (hT : 0 < T) (hz : z ∈ verticalClosedStrip a b)
    (hd : DiffContOnCl ℂ f (verticalStrip a b))
    (hbounded : BddAbove ((norm ∘ f) '' verticalClosedStrip a b))
    (ha : ∀ w : ℂ, w.re = a → ‖f w‖ ≤ A * T ^ p)
    (hb : ∀ w : ℂ, w.re = b → ‖f w‖ ≤ B * T ^ q) :
    ‖f z‖ ≤ max A B * T ^ ((1 - (z.re - a) / (b - a)) * p + (z.re - a) / (b - a) * q) := by
  rcases (hz.1.trans hz.2).eq_or_lt with rfl | hab
  · have he : z.re = a := le_antisymm hz.2 hz.1
    simpa only [sub_self, div_zero, sub_zero, one_mul, zero_mul, add_zero] using
      (ha z he).trans (mul_le_mul_of_nonneg_right (le_max_left A B) (by positivity))
  set θ := (z.re - a) / (b - a)
  have hC : 0 ≤ max A B := (nonneg_of_mul_nonneg_left
    ((norm_nonneg _).trans (ha a (ofReal_re a))) (Real.rpow_pos_of_pos hT _)).trans (le_max_left ..)
  refine (norm_le_interp_of_mem_verticalClosedStrip' hab hz hd hbounded
    (fun w hw ↦ (ha w hw).trans (mul_le_mul_of_nonneg_right (le_max_left A B) (by positivity)))
    (fun w hw ↦ (hb w hw).trans (mul_le_mul_of_nonneg_right (le_max_right A B) (by positivity))))
    |>.trans_eq ?_
  rw [Real.mul_rpow hC (by positivity), Real.mul_rpow hC (by positivity)]
  rw [← Real.rpow_mul hT.le, ← Real.rpow_mul hT.le]
  calc
    _ = ((max A B) ^ (1 - θ) * (max A B) ^ θ) * (T ^ (p * (1 - θ)) * T ^ (q * θ)) := by ring
    _ = _ := by rw [← Real.rpow_add' hC (by ring_nf; norm_num), sub_add_cancel, Real.rpow_one,
      ← Real.rpow_add hT, mul_comm p, mul_comm q]

end TauCeti.Complex.HadamardThreeLines
