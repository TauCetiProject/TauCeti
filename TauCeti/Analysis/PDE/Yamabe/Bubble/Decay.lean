/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.PDE.Yamabe.Bubble.Basic

/-!
# Pointwise decay of Yamabe bubbles

The bubble and its first differential have the spatial decay rates `r ^ (2 - n)` and
`r ^ (1 - n)`, with an explicit common scale factor `(2 t) ^ ((n - 2) / 2)`.
The exterior-radius estimates are uniform in the point and hold for every positive scale `t`,
without requiring `t < R`, with the explicit scale factor above. In particular,
on a fixed annulus they control the first differential of a bubble multiplied by an arbitrary
differentiable cutoff. These pointwise estimates are useful for bounding annular errors in
localized Dirichlet energies; no support or integrability assumption on the cutoff is needed.

The estimates include dimension two, where the bubble is constant and its differential vanishes.
Only first derivatives are treated here.

Outside the ball of radius `r` about the centre, the critical power, the square and the squared
differential of the bubble of scale `t` are bounded by `(2 t / r) ^ n`, `(2 t / r) ^ (n - 2)` and
`4 (2 t / r) ^ (n - 2)` times the same quantities for the bubble of scale `r`. Integrating these
comparisons bounds annular errors by the integrable bubble of scale `r`, with the sharp power of
`t` and no radial integration.

## References

* J. M. Lee and T. H. Parker, *The Yamabe problem*, Bull. Amer. Math. Soc. 17 (1987), §§3, 6.
-/

public section

noncomputable section

namespace TauCeti.Yamabe

open InnerProductSpace Module

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Away from its centre, the bubble is bounded by its leading spatial decay profile.
The estimate holds for every positive scale `t`, with explicit factor `(2 t) ^ ((n - 2) / 2)`. -/
theorem bubble_le_rpow_norm_sub (hn : 2 ≤ finrank ℝ E) {t : ℝ} (ht : 0 < t)
    {b x : E} (hx : x ≠ b) :
    bubble t b x ≤ (2 * t) ^ (((finrank ℝ E : ℝ) - 2) / 2) *
      ‖x - b‖ ^ (2 - (finrank ℝ E : ℝ)) := by
  have hr : 0 < ‖x - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hk : 0 ≤ ((finrank ℝ E : ℝ) - 2) / 2 := by
    have : (2 : ℝ) ≤ finrank ℝ E := by exact_mod_cast hn
    linarith
  calc
    bubble t b x ≤ (2 * t / ‖x - b‖ ^ 2) ^ (((finrank ℝ E : ℝ) - 2) / 2) := by
      rw [bubble_apply]
      apply Real.rpow_le_rpow (by positivity) _ hk
      exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by nlinarith [sq_nonneg t])
    _ = _ := by
      rw [Real.div_rpow (by positivity) (by positivity), ← Real.rpow_natCast _ 2,
        ← Real.rpow_mul hr.le, div_eq_mul_inv, ← Real.rpow_neg hr.le]
      congr 2
      ring

/-- A logarithmic derivative bound for the bubble away from its centre. It is often convenient
when a cutoff estimate already contains the bubble itself. -/
theorem norm_fderiv_bubble_le_div_norm_sub {t : ℝ} (ht : 0 < t) {b x : E}
    (hx : x ≠ b) :
    ‖fderiv ℝ (bubble t b) x‖ ≤
      |(finrank ℝ E : ℝ) - 2| * bubble t b x / ‖x - b‖ := by
  have hr : 0 < ‖x - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  rw [norm_fderiv_bubble ht]
  calc
    _ ≤ |(finrank ℝ E : ℝ) - 2| * bubble t b x * ‖x - b‖ / ‖x - b‖ ^ 2 :=
      div_le_div_of_nonneg_left
        (mul_nonneg (mul_nonneg (abs_nonneg _) (bubble_pos ht b x).le) hr.le)
        (by positivity) (by nlinarith [sq_nonneg t])
    _ = _ := by field_simp

/-- The first differential has one additional power of spatial decay compared with the bubble.
Both bounds have the same scale factor. -/
theorem norm_fderiv_bubble_le_rpow_norm_sub (hn : 2 ≤ finrank ℝ E) {t : ℝ} (ht : 0 < t)
    {b x : E} (hx : x ≠ b) :
    ‖fderiv ℝ (bubble t b) x‖ ≤ ((finrank ℝ E : ℝ) - 2) *
      (2 * t) ^ (((finrank ℝ E : ℝ) - 2) / 2) * ‖x - b‖ ^ (1 - (finrank ℝ E : ℝ)) := by
  have hr : 0 < ‖x - b‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hx)
  have hn' : 0 ≤ (finrank ℝ E : ℝ) - 2 := by
    have : (2 : ℝ) ≤ finrank ℝ E := by exact_mod_cast hn
    linarith
  calc
    _ ≤ ((finrank ℝ E : ℝ) - 2) * bubble t b x / ‖x - b‖ := by
      simpa [abs_of_nonneg hn'] using norm_fderiv_bubble_le_div_norm_sub ht hx
    _ ≤ ((finrank ℝ E : ℝ) - 2) *
        ((2 * t) ^ (((finrank ℝ E : ℝ) - 2) / 2) *
          ‖x - b‖ ^ (2 - (finrank ℝ E : ℝ))) / ‖x - b‖ := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (bubble_le_rpow_norm_sub hn ht hx) hn') hr.le
    _ = _ := by
      -- Subtract one from the bubble exponent so `Real.rpow_sub_one` divides by the radius.
      rw [show 1 - (finrank ℝ E : ℝ) = (2 - (finrank ℝ E : ℝ)) - 1 by ring,
        Real.rpow_sub_one hr.ne']
      ring

/-- Outside a ball of positive radius, the bubble has a bound uniform in the point.
For dimension greater than two, its scale factor tends to zero as the scale tends to zero. -/
theorem bubble_le_of_le_norm_sub (hn : 2 ≤ finrank ℝ E) {t R : ℝ} (ht : 0 < t)
    (hR : 0 < R) {b x : E} (hx : R ≤ ‖x - b‖) :
    bubble t b x ≤ (2 * t) ^ (((finrank ℝ E : ℝ) - 2) / 2) *
      R ^ (2 - (finrank ℝ E : ℝ)) := by
  have hn' : (2 : ℝ) ≤ finrank ℝ E := by exact_mod_cast hn
  exact (bubble_le_rpow_norm_sub hn ht (by
    intro h
    simpa [h] using hR.trans_le hx)).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hR hx (by linarith)) (by positivity))

/-- Outside a ball of positive radius, the first differential has a bound uniform in the point
with the same scale factor as the bubble. -/
theorem norm_fderiv_bubble_le_of_le_norm_sub (hn : 2 ≤ finrank ℝ E) {t R : ℝ}
    (ht : 0 < t) (hR : 0 < R) {b x : E} (hx : R ≤ ‖x - b‖) :
    ‖fderiv ℝ (bubble t b) x‖ ≤ ((finrank ℝ E : ℝ) - 2) *
      (2 * t) ^ (((finrank ℝ E : ℝ) - 2) / 2) * R ^ (1 - (finrank ℝ E : ℝ)) := by
  have hn' : (2 : ℝ) ≤ finrank ℝ E := by exact_mod_cast hn
  exact (norm_fderiv_bubble_le_rpow_norm_sub hn ht (by
    intro h
    simpa [h] using hR.trans_le hx)).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_nonpos hR hx (by linarith)) (by positivity))

/-- A quantitative exterior bound for the differential of a cutoff bubble. In particular, a
cutoff whose value and first differential are bounded on a fixed annulus gives a bound of order
`t ^ ((n - 2) / 2)` there. -/
theorem norm_fderiv_mul_bubble_le (hn : 2 ≤ finrank ℝ E) {t R : ℝ} (ht : 0 < t)
    (hR : 0 < R) {b x : E} (hx : R ≤ ‖x - b‖) {χ : E → ℝ}
    (hχ : DifferentiableAt ℝ χ x) :
    ‖fderiv ℝ (fun y ↦ χ y * bubble t b y) x‖ ≤
      (‖fderiv ℝ χ x‖ + |χ x| * ((finrank ℝ E : ℝ) - 2) / R) *
        (2 * t) ^ (((finrank ℝ E : ℝ) - 2) / 2) * R ^ (2 - (finrank ℝ E : ℝ)) := by
  have hu := ((contDiff_bubble ht.ne' b : ContDiff ℝ 1 (bubble t b)).differentiable
    one_ne_zero).differentiableAt (x := x)
  have hrpow : R ^ (1 - (finrank ℝ E : ℝ)) = R ^ (2 - (finrank ℝ E : ℝ)) / R := by
    -- The subtraction-by-one form lets `Real.rpow_sub_one` extract the factor `1 / R`.
    rw [show 1 - (finrank ℝ E : ℝ) = (2 - (finrank ℝ E : ℝ)) - 1 by ring,
      Real.rpow_sub_one hR.ne']
  have hmul : fderiv ℝ (fun y ↦ χ y * bubble t b y) x =
      bubble t b x • fderiv ℝ χ x + χ x • fderiv ℝ (bubble t b) x := by
    simpa only [Pi.mul_def, add_comm] using (hχ.hasFDerivAt.mul hu.hasFDerivAt).fderiv
  rw [hmul]
  calc
    _ ≤ ‖bubble t b x • fderiv ℝ χ x‖ + ‖χ x • fderiv ℝ (bubble t b) x‖ := norm_add_le _ _
    _ = bubble t b x * ‖fderiv ℝ χ x‖ + |χ x| * ‖fderiv ℝ (bubble t b) x‖ := by
      rw [norm_smul, norm_smul, Real.norm_of_nonneg (bubble_pos ht b x).le, Real.norm_eq_abs]
    _ ≤ ((2 * t) ^ (((finrank ℝ E : ℝ) - 2) / 2) * R ^ (2 - (finrank ℝ E : ℝ))) *
          ‖fderiv ℝ χ x‖ + |χ x| * (((finrank ℝ E : ℝ) - 2) *
          (2 * t) ^ (((finrank ℝ E : ℝ) - 2) / 2) * R ^ (1 - (finrank ℝ E : ℝ))) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right (bubble_le_of_le_norm_sub hn ht hR hx) (norm_nonneg _))
        (mul_le_mul_of_nonneg_left (norm_fderiv_bubble_le_of_le_norm_sub hn ht hR hx)
          (abs_nonneg _))
    _ = _ := by rw [hrpow]; ring

/-! ### Comparison with a bubble of fixed scale -/

/-- Outside the ball of radius `r`, the bubble profile of scale `t` is dominated by `2 t / r`
times the profile of scale `r`. -/
private lemma two_mul_div_add_sq_le_mul {t r ρ : ℝ} (ht : 0 < t) (hr : 0 < r) (hρ : r ≤ ρ) :
    2 * t / (t ^ 2 + ρ ^ 2) ≤ 2 * t / r * (2 * r / (r ^ 2 + ρ ^ 2)) := by
  rw [div_mul_div_comm, mul_comm r, ← mul_assoc, mul_div_mul_right _ _ hr.ne',
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_le_mul hρ hρ hr.le (hr.le.trans hρ)]

/-- Outside the ball of radius `r` about the centre, the critical power of the bubble of scale
`t` is at most `(2 t / r) ^ n` times that of the bubble of scale `r`. This holds for every
positive scale `t`. -/
theorem bubble_rpow_criticalExponent_le_mul_of_le_norm_sub (hn : finrank ℝ E ≠ 2) {t r : ℝ}
    (ht : 0 < t) (hr : 0 < r) {b x : E} (hx : r ≤ ‖x - b‖) :
    bubble t b x ^ criticalExponent (finrank ℝ E) ≤
      (2 * t / r) ^ finrank ℝ E * bubble r b x ^ criticalExponent (finrank ℝ E) := by
  rw [bubble_rpow_criticalExponent hn ht, bubble_rpow_criticalExponent hn hr, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (two_mul_div_add_sq_le_mul ht hr hx) _

/-- Outside the ball of radius `r` about the centre, the square of the bubble of scale `t` is at
most `(2 t / r) ^ (n - 2)` times that of the bubble of scale `r`. -/
theorem bubble_sq_le_mul_of_le_norm_sub (hn : 2 ≤ finrank ℝ E) {t r : ℝ}
    (ht : 0 < t) (hr : 0 < r) {b x : E} (hx : r ≤ ‖x - b‖) :
    bubble t b x ^ 2 ≤ (2 * t / r) ^ (finrank ℝ E - 2) * bubble r b x ^ 2 := by
  rw [bubble_sq hn ht.le, bubble_sq hn hr.le, ← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (two_mul_div_add_sq_le_mul ht hr hx) _

/-- Outside the ball of radius `r` about the centre, the squared norm of the differential of the
bubble of scale `t` is at most `4 (2 t / r) ^ (n - 2)` times that of the bubble of scale `r`. -/
theorem norm_fderiv_bubble_sq_le_mul_of_le_norm_sub (hn : 2 ≤ finrank ℝ E) {t r : ℝ}
    (ht : 0 < t) (hr : 0 < r) {b x : E} (hx : r ≤ ‖x - b‖) :
    ‖fderiv ℝ (bubble t b) x‖ ^ 2 ≤
      4 * (2 * t / r) ^ (finrank ℝ E - 2) * ‖fderiv ℝ (bubble r b) x‖ ^ 2 := by
  have hpow := pow_le_pow_left₀ (by positivity) (two_mul_div_add_sq_le_mul ht hr hx)
    (finrank ℝ E)
  rw [mul_pow] at hpow
  have hcoef : (((finrank ℝ E : ℝ) - 2) / (2 * t)) ^ 2 * (2 * t / r) ^ 2 =
      4 * (((finrank ℝ E : ℝ) - 2) / (2 * r)) ^ 2 := by
    field_simp
    ring
  rw [norm_fderiv_bubble_sq ht, norm_fderiv_bubble_sq hr]
  calc
    _ ≤ (((finrank ℝ E : ℝ) - 2) / (2 * t)) ^ 2 * ‖x - b‖ ^ 2 *
        ((2 * t / r) ^ finrank ℝ E * (2 * r / (r ^ 2 + ‖x - b‖ ^ 2)) ^ finrank ℝ E) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = _ := by
      rw [← pow_mul_pow_sub _ hn]
      linear_combination ‖x - b‖ ^ 2 * (2 * t / r) ^ (finrank ℝ E - 2) *
        (2 * r / (r ^ 2 + ‖x - b‖ ^ 2)) ^ finrank ℝ E * hcoef

end TauCeti.Yamabe
