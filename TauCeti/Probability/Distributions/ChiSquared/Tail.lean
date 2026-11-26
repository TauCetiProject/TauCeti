/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bastiaan Braams
-/
module

public import TauCeti.Probability.Distributions.ChiSquared.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp

/-!
# Chi-squared tail bounds

For `Z` of law `chiSquaredMeasure k` and `t ≥ 0`,

* `P(Z - k ≥ 2√(kt) + 2t) ≤ e^{-t}` (`TauCeti.Probability.chiSquared_tail_upper`);
* `P(k - Z > 2√(kt)) ≤ e^{-t}` (`TauCeti.Probability.chiSquared_tail_lower`).

These are the sub-gamma tail bounds of Boucheron, Lugosi and Massart, *Concentration
Inequalities*, §2.4, pp. 28–29, and Example 2.7, p. 33: `χ²ₖ` is sub-gamma on the right with
variance factor `2k` and scale `2`, and on the left with variance factor `2k` and scale `0`.

Together they control the deviation of a chi-squared variable from its mean `k`: with
probability at least `1 - 2e^{-t}`, `|Z - k| ≤ 2√(kt) + 2t`. So the fluctuations are of order
`√k`, Gaussian-like for `t ≲ k` and exponential for larger `t`. They are the basic input for
the norm concentration of Gaussian vectors, `‖g‖² ~ χ²ₙ` for `g` standard Gaussian in `ℝⁿ`.

Both bounds are stated for every real `k` and `t`: for `k < 0` the measure `chiSquaredMeasure k`
is zero, and for `t < 0` the right-hand side `e^{-t}` exceeds `1`.
The lower event is strict: for `k = 0` the law is the Dirac mass at `0`, and the non-strict
event `{Z ≤ 0}` would have probability `1`.

The file also proves the optimised Chernoff bounds in rate-function form: for `β ≥ 1`,

* `P(Z ≥ βk) ≤ exp(-k(β - 1 - log β)/2)` (`TauCeti.Probability.chiSquared_tail_upper_rate`),

and for `β ≤ 1`,

* `P(Z ≤ βk) ≤ exp(-k(β - 1 - log β)/2)` (`TauCeti.Probability.chiSquared_tail_lower_rate`).

The exponent `(β - 1 - log β)/2` is the Cramér rate function of `χ²₁` at `β`, attained by the
Chernoff bound at `s = (1 - 1/β)/2`. These are the bounds behind the Johnson–Lindenstrauss lemma
in the proof of Dasgupta and Gupta, Lemma 2.2, where they are optimised in the same way. For
`β ≤ 0` and `k > 0` the lower event is null; there the right-hand side involves Mathlib's
conventions for `log`, and the bound carries no information.

## References

* S. Dasgupta and A. Gupta, *An elementary proof of a theorem of Johnson and Lindenstrauss*,
  Random Structures and Algorithms 22 (2003), 60–65, Lemma 2.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real Set

namespace TauCeti.Probability

/-- The upper chi-squared tail: for `Z` of law `χ²ₖ`, `P(Z ≥ k + 2√(kt) + 2t) ≤ e^{-t}`
(Boucheron–Lugosi–Massart, §2.4 and Example 2.7). The bound is trivial for `k < 0` or `t < 0`. -/
theorem chiSquared_tail_upper (k t : ℝ) :
    (chiSquaredMeasure k).real {z | k + 2 * √(k * t) + 2 * t ≤ z} ≤ exp (-t) := by
  rcases lt_or_ge k 0 with hk | hk0
  · simp only [chiSquaredMeasure_of_neg hk, measureReal_zero]
    positivity
  have := isProbabilityMeasure_chiSquaredMeasure hk0
  rcases lt_or_ge t 0 with ht | ht
  · exact measureReal_le_one.trans (one_le_exp (by linarith))
  rcases hk0.eq_or_lt with rfl | hk
  · rcases ht.eq_or_lt with rfl | ht
    · simp
    · rw [chiSquaredMeasure_zero, measureReal_def, Measure.dirac_apply,
        indicator_of_notMem (by simpa using ht)]
      positivity
  -- Cramér–Chernoff with the cumulant-generating function `-(k / 2) log (1 - 2s)` at the rate
  -- `s = r / (q + 2r)`, where `q = √k` and `r = √t`, and `log y ≤ (y - y⁻¹) / 2` for `y ≥ 1`.
  set q := √k
  set r := √t
  have hq : 0 < q := sqrt_pos.2 hk
  have hr : 0 ≤ r := sqrt_nonneg t
  have hkq : k = q ^ 2 := (sq_sqrt (hk0)).symm
  have htr : t = r ^ 2 := (sq_sqrt ht).symm
  have hq2r : 0 < q + 2 * r := by positivity
  set s := r / (q + 2 * r)
  have hs : 0 ≤ s := by positivity
  have hs2 : s < 2⁻¹ := by
    rw [div_lt_iff₀ hq2r]
    linarith
  have hint : s ∈ integrableExpSet id (chiSquaredMeasure k) := by
    rwa [integrableExpSet_id_chiSquaredMeasure hk, one_div]
  refine (measure_ge_le_exp_cgf (X := id) _ hs hint).trans (exp_le_exp.2 ?_)
  rw [cgf_id_chiSquaredMeasure (hk0) hs2]
  -- `1 - 2s = y⁻¹` with `y = (q + 2r) / q ≥ 1`.
  set y := (q + 2 * r) / q
  have hy : 1 ≤ y := by rw [le_div_iff₀ hq]; linarith
  have hy0 : 0 < y := by positivity
  have h1 : 1 - 2 * s = y⁻¹ := by
    simp only [s, y]
    field_simp
    ring
  have hlog : log y ≤ (y - y⁻¹) / 2 := by
    rw [← sinh_log hy0]
    exact self_le_sinh_iff.2 (log_nonneg hy)
  have hkt : √(k * t) = q * r := sqrt_mul (hk0) t
  rw [h1, log_inv, hkt, hkq, htr]
  have key :
      -s * (q ^ 2 + 2 * (q * r) + 2 * r ^ 2) + q ^ 2 / 2 * ((y - y⁻¹) / 2) = -r ^ 2 := by
    simp only [s, y]
    field_simp
    ring
  nlinarith [mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ q ^ 2 / 2)]

/-- The lower chi-squared tail: for `Z` of law `χ²ₖ`, `P(Z < k - 2√(kt)) ≤ e^{-t}`. The event is
strict, so that `k = 0` (`chiSquaredMeasure 0 = dirac 0`) is covered; the bound is trivial for
`k < 0` or `t < 0`. -/
theorem chiSquared_tail_lower (k t : ℝ) :
    (chiSquaredMeasure k).real {z | z < k - 2 * √(k * t)} ≤ exp (-t) := by
  rcases lt_or_ge k 0 with hk | hk0
  · simp only [chiSquaredMeasure_of_neg hk, measureReal_zero]
    positivity
  have := isProbabilityMeasure_chiSquaredMeasure hk0
  rcases lt_or_ge t 0 with ht | ht
  · exact measureReal_le_one.trans (one_le_exp (by linarith))
  rcases hk0.eq_or_lt with rfl | hk
  · rw [chiSquaredMeasure_zero, measureReal_def, Measure.dirac_apply,
      indicator_of_notMem (by simp)]
    positivity
  -- Cramér–Chernoff with the cumulant-generating function `-(k / 2) log (1 - 2s)` at the rate
  -- `s = -r / q`, where `q = √k` and `r = √t`, and `2x / (x + 2) ≤ log (1 + x)` for `x ≥ 0`.
  set q := √k
  set r := √t
  have hq : 0 < q := sqrt_pos.2 hk
  have hr : 0 ≤ r := sqrt_nonneg t
  have hkq : k = q ^ 2 := (sq_sqrt (hk0)).symm
  have htr : t = r ^ 2 := (sq_sqrt ht).symm
  set l := r / q
  have hl : 0 ≤ l := by positivity
  have hint : -l ∈ integrableExpSet id (chiSquaredMeasure k) := by
    rw [integrableExpSet_id_chiSquaredMeasure hk]
    exact (neg_nonpos.2 hl).trans_lt one_half_pos
  have hmono : (chiSquaredMeasure k).real {z | z < k - 2 * √(k * t)} ≤
      (chiSquaredMeasure k).real {z | id z ≤ k - 2 * √(k * t)} :=
    measureReal_mono (fun z hz ↦ le_of_lt hz.out)
  refine hmono.trans <| (measure_le_le_exp_cgf (X := id) _ (neg_nonpos.2 hl) hint).trans
    (exp_le_exp.2 ?_)
  rw [cgf_id_chiSquaredMeasure (hk0) (by linarith)]
  have hlog : 2 * (2 * l) / (2 * l + 2) ≤ log (1 + 2 * l) :=
    le_log_one_add_of_nonneg (by positivity)
  have hkt : √(k * t) = q * r := sqrt_mul (hk0) t
  -- At the rate `-l` the logarithm in the cgf is `log (1 + 2l)`, matching `hlog`.
  have hrate : 1 - 2 * -l = 1 + 2 * l := by ring
  rw [hkt, hkq, htr, hrate]
  have key : - -l * (q ^ 2 - 2 * (q * r)) + -(q ^ 2 / 2) * (2 * (2 * l) / (2 * l + 2)) =
      -r ^ 2 - r ^ 3 / (q + r) := by
    simp only [l]
    field_simp
    ring
  have hr3 : 0 ≤ r ^ 3 / (q + r) := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hlog (by positivity : (0 : ℝ) ≤ q ^ 2 / 2)]

/-- The value of the Chernoff exponent of a chi-squared law at the rate `s = (1 - β⁻¹) / 2`
and the threshold `βk`: it is `-k(β - 1 - log β)/2`. -/
private theorem chernoff_exponent_chiSquaredMeasure {k β : ℝ} (hk : 0 ≤ k) (hβ : 0 < β) :
    -((1 - β⁻¹) / 2) * (β * k) + cgf id (chiSquaredMeasure k) ((1 - β⁻¹) / 2) =
      -(k * (β - 1 - log β) / 2) := by
  have hs : (1 - β⁻¹) / 2 < 2⁻¹ := by
    have := inv_pos.2 hβ
    linarith
  have h1 : 1 - 2 * ((1 - β⁻¹) / 2) = β⁻¹ := by ring
  rw [cgf_id_chiSquaredMeasure hk hs, h1, log_inv]
  field_simp
  ring

/-- The upper chi-squared tail in rate-function form: for `Z` of law `χ²ₖ` and `β ≥ 1`,
`P(Z ≥ βk) ≤ exp(-k(β - 1 - log β)/2)` (Dasgupta–Gupta, Lemma 2.2). The bound holds for every
real `k`, trivially for `k ≤ 0`. -/
theorem chiSquared_tail_upper_rate {k β : ℝ} (hβ : 1 ≤ β) :
    (chiSquaredMeasure k).real {z | β * k ≤ z} ≤ exp (-(k * (β - 1 - log β) / 2)) := by
  rcases lt_or_ge k 0 with hk | hk0
  · simp only [chiSquaredMeasure_of_neg hk, measureReal_zero]
    positivity
  have := isProbabilityMeasure_chiSquaredMeasure hk0
  rcases hk0.eq_or_lt with rfl | hk
  · simp
  have hβ0 : 0 < β := zero_lt_one.trans_le hβ
  have hs : 0 ≤ (1 - β⁻¹) / 2 := by
    have := inv_le_one_of_one_le₀ hβ
    linarith
  have hint : (1 - β⁻¹) / 2 ∈ integrableExpSet id (chiSquaredMeasure k) := by
    rw [integrableExpSet_id_chiSquaredMeasure hk, Set.mem_Iio]
    linarith [inv_pos.2 hβ0]
  rw [← chernoff_exponent_chiSquaredMeasure hk0 hβ0]
  exact measure_ge_le_exp_cgf (X := id) _ hs hint

/-- The lower chi-squared tail in rate-function form: for `Z` of law `χ²ₖ` and `β ≤ 1`,
`P(Z ≤ βk) ≤ exp(-k(β - 1 - log β)/2)` (Dasgupta–Gupta, Lemma 2.2). The bound holds for every
real `k`, trivially for `k ≤ 0`. For `β ≤ 0` and `k > 0` the event is null, since `Z > 0` almost
surely; there the right-hand side uses Mathlib's conventions `log 0 = 0` and `log β = log |β|`. -/
theorem chiSquared_tail_lower_rate {k β : ℝ} (hβ : β ≤ 1) :
    (chiSquaredMeasure k).real {z | z ≤ β * k} ≤ exp (-(k * (β - 1 - log β) / 2)) := by
  rcases lt_or_ge k 0 with hk | hk0
  · simp only [chiSquaredMeasure_of_neg hk, measureReal_zero]
    positivity
  have := isProbabilityMeasure_chiSquaredMeasure hk0
  rcases hk0.eq_or_lt with rfl | hk
  · simp
  rcases le_or_gt β 0 with hβ0 | hβ0
  · -- The event lies in the null half-line `z ≤ 0`.
    have hnull : (chiSquaredMeasure k).real {z | z ≤ β * k} = 0 := by
      refine (measureReal_eq_zero_iff (measure_ne_top _ _)).2 <| measure_mono_null (fun z hz ↦ ?_)
        (ae_iff.1 (ae_pos_chiSquaredMeasure hk))
      exact not_lt.2 (le_trans hz.out (mul_nonpos_of_nonpos_of_nonneg hβ0 hk.le))
    rw [hnull]
    positivity
  have hs : (1 - β⁻¹) / 2 ≤ 0 := by
    have := one_le_inv₀ hβ0 |>.2 hβ
    linarith
  have hint : (1 - β⁻¹) / 2 ∈ integrableExpSet id (chiSquaredMeasure k) := by
    rw [integrableExpSet_id_chiSquaredMeasure hk, Set.mem_Iio]
    linarith
  rw [← chernoff_exponent_chiSquaredMeasure hk0 hβ0]
  exact measure_le_le_exp_cgf (X := id) _ hs hint

end TauCeti.Probability
