/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.Gaussian.IsoperimetricProfile

/-!
# Shifting intervals of fixed Gaussian measure

Write `φ = gaussianPDFReal 0 1` and `Φ = cdf (gaussianReal 0 1)`, so that the interval `(a, b)`
has standard Gaussian measure `Φ(b) − Φ(a)` and its two endpoints contribute `φ(a) + φ(b)` to its
Gaussian perimeter. This file proves that shifting an interval with `a + b ≥ 0` to the right,
keeping its Gaussian measure, strictly decreases this sum: if `a < a'` and
`Φ(b') − Φ(a') = Φ(b) − Φ(a)`, then `φ(a') + φ(b') < φ(a) + φ(b)`
(`TauCeti.Probability.gaussianPDFReal_add_lt_of_shift_right`). The mirror statement for
`a + b ≤ 0` and shifts to the left follows by the symmetry `x ↦ −x`. When the shifted interval is
a half-line `(a', ∞)`, whose perimeter is `φ(a')`, the sum also decreases, and here no sign
condition on `a + b` is needed, since the mirror case is again a half-line `(a', ∞)`
(`TauCeti.Probability.gaussianPDFReal_lt_of_shift_right_Ioi`).

The proof parametrises the shifted intervals by the measure `u = Φ(a')` of the half-line to the
left of them: with `m = Φ(b) − Φ(a)`, the sum is `I(u) + I(u + m)` for the Gaussian isoperimetric
function `I`, whose derivative `I'(u) = −Φ⁻¹(u)` gives the derivative `−(a' + b')` of the sum.
Since `a' > a` and `b' > b`, this is negative along the shift.

## Main results

* `TauCeti.Probability.gaussianPDFReal_add_lt_of_shift_right`: right shifts for `a + b ≥ 0`.
* `TauCeti.Probability.gaussianPDFReal_add_lt_of_shift_left`: left shifts for `a + b ≤ 0`.
* `TauCeti.Probability.gaussianPDFReal_lt_of_shift_right_Ioi`,
  `TauCeti.Probability.gaussianPDFReal_lt_of_shift_left_Iio`: shifts to a half-line, for any
  `a` and `b`.

## References

* A. Cianchi, N. Fusco, F. Maggi, A. Pratelli, *On the isoperimetric deficit in Gauss space*,
  American Journal of Mathematics 133 (2011), 131–186; preprint on cvgmt (paper 1587),
  Definition 3.2 and Lemma 3.3. Their perimeter is `√(2π)` times the one used here, and their `Φ`
  is the upper tail `1 − Φ`; the inequality is homogeneous in perimeter.
-/

public section

noncomputable section

open Set ProbabilityTheory

namespace TauCeti.Probability

/-- Along the shifts of an interval `(a, b)` with `a ≤ b` and `a + b ≥ 0`, parametrised by
`u = Φ(a')`, the sum `I(u) + I(u + Φ(b) − Φ(a))` is strictly decreasing. -/
private theorem strictAntiOn_shift {a b : ℝ} (hab : a ≤ b) (hsum : 0 ≤ a + b) :
    StrictAntiOn (fun u => gaussianIsoperimetricProfile u + gaussianIsoperimetricProfile
      (u + (cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a)))
      (Icc (cdf (gaussianReal 0 1) a)
        (1 - (cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a))) := by
  set m := cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a
  have hmono := strictMono_cdf_gaussianReal 0 (one_ne_zero : (1 : NNReal) ≠ 0)
  have hm : 0 ≤ m := sub_nonneg.2 (hmono.monotone hab)
  have ha0 := cdf_gaussianReal_pos 0 (one_ne_zero : (1 : NNReal) ≠ 0) a
  refine strictAntiOn_of_deriv_neg (convex_Icc _ _)
    (continuous_gaussianIsoperimetricProfile.add
      (continuous_gaussianIsoperimetricProfile.comp
        (continuous_id.add continuous_const))).continuousOn
    fun u hu => ?_
  rw [interior_Icc] at hu
  have hu1 : u ∈ Ioo 0 1 := ⟨ha0.trans hu.1, by linarith [hu.2]⟩
  have hu2 : u + m ∈ Ioo 0 1 := ⟨by linarith [hu1.1], by linarith [hu.2]⟩
  have hd : HasDerivAt (fun u => gaussianIsoperimetricProfile u +
      gaussianIsoperimetricProfile (u + m))
      (-(gaussianReal 0 1).quantile u + -(gaussianReal 0 1).quantile (u + m)) u :=
    (hasDerivAt_gaussianIsoperimetricProfile hu1).add
      ((hasDerivAt_gaussianIsoperimetricProfile hu2).comp_add_const u m)
  rw [hd.deriv]
  have h1 : a < (gaussianReal 0 1).quantile u :=
    ((gaussianReal 0 1).lt_quantile_iff hu1.1 hu1.2).2 hu.1
  have h2 : b < (gaussianReal 0 1).quantile (u + m) :=
    ((gaussianReal 0 1).lt_quantile_iff hu2.1 hu2.2).2 (by linarith [hu.1])
  linarith

/-- The finite case of `TauCeti.Probability.gaussianPDFReal_add_lt_of_shift_right` for
`a ≤ b`. -/
private theorem gaussianPDFReal_add_lt_of_shift_right_of_le {a b a' b' : ℝ} (hab : a ≤ b)
    (hsum : 0 ≤ a + b) (ha : a < a')
    (h : cdf (gaussianReal 0 1) b' - cdf (gaussianReal 0 1) a' =
      cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a) :
    gaussianPDFReal 0 1 a' + gaussianPDFReal 0 1 b' <
      gaussianPDFReal 0 1 a + gaussianPDFReal 0 1 b := by
  have hmono := strictMono_cdf_gaussianReal 0 (one_ne_zero : (1 : NNReal) ≠ 0)
  have hb1 := cdf_gaussianReal_lt_one 0 (one_ne_zero : (1 : NNReal) ≠ 0) b
  have hb'1 := cdf_gaussianReal_lt_one 0 (one_ne_zero : (1 : NNReal) ≠ 0) b'
  have key := strictAntiOn_shift hab hsum ⟨le_rfl, by linarith⟩
    ⟨(hmono ha).le, by linarith⟩ (hmono ha)
  have e1 : cdf (gaussianReal 0 1) a + (cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a) =
      cdf (gaussianReal 0 1) b := by ring
  have e2 : cdf (gaussianReal 0 1) a' + (cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a) =
      cdf (gaussianReal 0 1) b' := by linarith
  simpa only [e1, e2, gaussianIsoperimetricProfile_cdf] using key

/-- **Shifting an interval to the right.** If `a + b ≥ 0`, `a < a'` and the intervals `(a, b)`
and `(a', b')` have the same standard Gaussian measure, `Φ(b') − Φ(a') = Φ(b) − Φ(a)`, then
`φ(a') + φ(b') < φ(a) + φ(b)`. -/
theorem gaussianPDFReal_add_lt_of_shift_right {a b a' b' : ℝ} (hsum : 0 ≤ a + b) (ha : a < a')
    (h : cdf (gaussianReal 0 1) b' - cdf (gaussianReal 0 1) a' =
      cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a) :
    gaussianPDFReal 0 1 a' + gaussianPDFReal 0 1 b' <
      gaussianPDFReal 0 1 a + gaussianPDFReal 0 1 b := by
  rcases le_or_gt a b with hab | hab
  · exact gaussianPDFReal_add_lt_of_shift_right_of_le hab hsum ha h
  -- For `b < a` the interval is `(b, a)`, shifted to `(b', a')` with `b < b'`.
  have hmono := strictMono_cdf_gaussianReal 0 (one_ne_zero : (1 : NNReal) ≠ 0)
  have hb : b < b' := hmono.lt_iff_lt.1 (by linarith [hmono ha])
  have := gaussianPDFReal_add_lt_of_shift_right_of_le (a := b) (b := a) (a' := b') (b' := a')
    hab.le (by linarith) hb (by linarith)
  linarith

/-- **Shifting an interval to the left.** If `a + b ≤ 0`, `b' < b` and the intervals `(a, b)` and
`(a', b')` have the same standard Gaussian measure, then `φ(a') + φ(b') < φ(a) + φ(b)`. -/
theorem gaussianPDFReal_add_lt_of_shift_left {a b a' b' : ℝ} (hsum : a + b ≤ 0) (hb : b' < b)
    (h : cdf (gaussianReal 0 1) b' - cdf (gaussianReal 0 1) a' =
      cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a) :
    gaussianPDFReal 0 1 a' + gaussianPDFReal 0 1 b' <
      gaussianPDFReal 0 1 a + gaussianPDFReal 0 1 b := by
  have := gaussianPDFReal_add_lt_of_shift_right (a := -b) (b := -a) (a' := -b') (b' := -a')
    (by linarith) (by linarith) (by simp only [cdf_gaussianReal_zero_one_neg]; linarith)
  simp only [gaussianPDFReal_zero_neg] at this
  linarith

/-- The case `a + b ≥ 0` of `TauCeti.Probability.gaussianPDFReal_lt_of_shift_right_Ioi`. -/
private theorem gaussianPDFReal_lt_of_shift_right_Ioi_of_nonneg {a b a' : ℝ}
    (hsum : 0 ≤ a + b)
    (h : 1 - cdf (gaussianReal 0 1) a' =
      cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a) :
    gaussianPDFReal 0 1 a' < gaussianPDFReal 0 1 a + gaussianPDFReal 0 1 b := by
  have hmono := strictMono_cdf_gaussianReal 0 (one_ne_zero : (1 : NNReal) ≠ 0)
  have ha'1 := cdf_gaussianReal_lt_one 0 (one_ne_zero : (1 : NNReal) ≠ 0) a'
  have hab : a ≤ b := (hmono.lt_iff_lt.1 (by linarith)).le
  have hb1 := cdf_gaussianReal_lt_one 0 (one_ne_zero : (1 : NNReal) ≠ 0) b
  have ha : a < a' := hmono.lt_iff_lt.1 (by linarith)
  have key := strictAntiOn_shift hab hsum ⟨le_rfl, by linarith⟩
    ⟨(hmono ha).le, by linarith⟩ (hmono ha)
  have e1 : cdf (gaussianReal 0 1) a + (cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a) =
      cdf (gaussianReal 0 1) b := by ring
  have e2 : cdf (gaussianReal 0 1) a' + (cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a) =
      1 := by linarith
  simpa only [e1, e2, gaussianIsoperimetricProfile_cdf, gaussianIsoperimetricProfile_one,
    add_zero] using key

/-- **Shifting an interval to a half-line on the right.** If the half-line `(a', ∞)` has the
standard Gaussian measure of `(a, b)`, `1 − Φ(a') = Φ(b) − Φ(a)`, then `φ(a') < φ(a) + φ(b)`.
No sign condition on `a + b` is needed, and `a < a'` follows from the equation. -/
theorem gaussianPDFReal_lt_of_shift_right_Ioi {a b a' : ℝ}
    (h : 1 - cdf (gaussianReal 0 1) a' =
      cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a) :
    gaussianPDFReal 0 1 a' < gaussianPDFReal 0 1 a + gaussianPDFReal 0 1 b := by
  rcases le_total 0 (a + b) with hsum | hsum
  · exact gaussianPDFReal_lt_of_shift_right_Ioi_of_nonneg hsum h
  -- For `a + b ≤ 0`, the mirror interval `(−b, −a)` has the same measure and perimeter.
  have := gaussianPDFReal_lt_of_shift_right_Ioi_of_nonneg (a := -b) (b := -a) (a' := a')
    (by linarith) (by simp only [cdf_gaussianReal_zero_one_neg]; linarith)
  simp only [gaussianPDFReal_zero_neg] at this
  linarith

/-- **Shifting an interval to a half-line on the left.** If the half-line `(−∞, b')` has the
standard Gaussian measure of `(a, b)`, `Φ(b') = Φ(b) − Φ(a)`, then `φ(b') < φ(a) + φ(b)`.
No sign condition on `a + b` is needed, and `b' < b` follows from the equation. -/
theorem gaussianPDFReal_lt_of_shift_left_Iio {a b b' : ℝ}
    (h : cdf (gaussianReal 0 1) b' = cdf (gaussianReal 0 1) b - cdf (gaussianReal 0 1) a) :
    gaussianPDFReal 0 1 b' < gaussianPDFReal 0 1 a + gaussianPDFReal 0 1 b := by
  have := gaussianPDFReal_lt_of_shift_right_Ioi (a := a) (b := b) (a' := -b')
    (by simp only [cdf_gaussianReal_zero_one_neg]; linarith)
  rwa [gaussianPDFReal_zero_neg] at this

end TauCeti.Probability
