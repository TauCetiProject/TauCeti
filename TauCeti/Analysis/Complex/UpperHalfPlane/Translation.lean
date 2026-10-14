/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.UpperHalfPlane.Metric
import TauCeti.Analysis.Complex.UpperHalfPlane.Bisector.Basic
import Mathlib.Algebra.Order.Round

/-!
# Real translations of the upper half-plane

A real number `r` translates a point `z` of `ℍ` to `r +ᵥ z`. The translation is an isometry of
the hyperbolic metric but not of the modulus: for `r ≠ 0` it preserves `‖z‖` exactly when `z`
lies on the perpendicular bisector `re = -r / 2` of `0` and `-r`, since then `z` and `r +ᵥ z` are
mirror images in the imaginary axis. The lemmas here prove that this condition is sufficient, for
every `r`. For `r = ±1` that line contains a vertical edge of the standard fundamental domain,
which is how the fundamental-domain API uses these lemmas.

The distance inequalities for opposite translations cut out a vertical strip. Rounding the
horizontal displacement gives a nearest translate in that strip. These metric facts reduce
distance constraints near a parabolic fixed point to a bounded horizontal range.

## Main results

* `UpperHalfPlane.normSq_coe_vadd_of_re_eq`, `UpperHalfPlane.norm_coe_vadd_of_re_eq`: on the
  line `re = -r / 2`, translation by `r` preserves the squared norm and the norm.
* `UpperHalfPlane.dist_le_dist_vadd_and_neg_vadd_iff`: the two adjacent distance constraints
  describe a vertical strip.
* `UpperHalfPlane.exists_int_vadd_re_sub_le_and_dist_le`: a nearest integer translate has
  horizontal displacement at most half the translation length.

The nearest-translate construction uses Mathlib's `round_le` and `abs_sub_round`, together with
`TauCeti.UpperHalfPlane.dist_le_dist_iff`.
-/

public section

namespace UpperHalfPlane

/-- On the perpendicular bisector `re = -r / 2` of `0` and `-r`, translation by `r` preserves the
norm-square. -/
lemma normSq_coe_vadd_of_re_eq {r : ℝ} {p : ℍ} (hre : p.re = -r / 2) :
    Complex.normSq ((r +ᵥ p : ℍ) : ℂ) = Complex.normSq (p : ℂ) := by
  simp [Complex.normSq_add, hre]
  ring

/-- On the line `re = -r / 2`, translation by `r` preserves the norm. -/
lemma norm_coe_vadd_of_re_eq {r : ℝ} {p : ℍ} (hre : p.re = -r / 2) :
    ‖((r +ᵥ p : ℍ) : ℂ)‖ = ‖(p : ℂ)‖ := by
  rw [Complex.norm_def, Complex.norm_def, normSq_coe_vadd_of_re_eq hre]

/-- The distance constraints from translations by `±w` cut out the vertical strip of
half-width `w / 2` centred at `p.re`. -/
@[simp]
theorem dist_le_dist_vadd_and_neg_vadd_iff {w : ℝ} (hw : 0 < w) (z p : ℍ) :
    (dist z p ≤ dist z (w +ᵥ p) ∧ dist z p ≤ dist z ((-w) +ᵥ p)) ↔
      |z.re - p.re| ≤ w / 2 := by
  simp only [TauCeti.UpperHalfPlane.dist_le_dist_iff, vadd_im,
    Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    coe_re, coe_im, vadd_re, mul_le_mul_iff_right₀ p.im_pos, abs_le]
  constructor
  · rintro ⟨h₁, h₂⟩
    constructor <;> nlinarith
  · rintro ⟨h₁, h₂⟩
    constructor <;> nlinarith

/-- Some integer multiple of a positive translation moves `q` within horizontal distance
`w / 2` of `z`, while minimizing the hyperbolic distance to `z` among all such translates. -/
theorem exists_int_vadd_re_sub_le_and_dist_le (w : ℝ) (hw : 0 < w) (z q : ℍ) :
    ∃ n : ℤ, |z.re - ((n : ℝ) * w +ᵥ q).re| ≤ w / 2 ∧
      ∀ m : ℤ, dist z ((n : ℝ) * w +ᵥ q) ≤ dist z ((m : ℝ) * w +ᵥ q) := by
  let n := round ((z.re - q.re) / w)
  have heq (m : ℤ) : z.re - ((m : ℝ) * w +ᵥ q).re =
      w * ((z.re - q.re) / w - m) := by
    simp only [vadd_re]
    field_simp
    ring
  refine ⟨n, ?_, fun m ↦ ?_⟩
  · rw [heq, abs_mul, abs_of_pos hw]
    nlinarith [abs_sub_round ((z.re - q.re) / w)]
  · have hnear : |z.re - ((n : ℝ) * w +ᵥ q).re| ≤
        |z.re - ((m : ℝ) * w +ᵥ q).re| := by
      simp only [heq, abs_mul, abs_of_pos hw]
      exact mul_le_mul_of_nonneg_left (round_le _ _) hw.le
    have hsq := (sq_le_sq).mpr hnear
    rw [TauCeti.UpperHalfPlane.dist_le_dist_iff]
    simp only [vadd_im, Complex.dist_eq, Complex.sq_norm, Complex.normSq_apply,
      Complex.sub_re, Complex.sub_im, coe_re, coe_im]
    nlinarith [q.im_pos]

end UpperHalfPlane

end
