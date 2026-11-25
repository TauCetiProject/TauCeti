/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Normed.Group.Ultra

/-!
# Schwarz's lemma for power series with ultrametric values

Let `f` have the power series `q` on a ball about `x`, with values in a normed space whose norm is
ultrametric. If the terms of `q` of degree `< T` vanish and `‖q n‖ r ^ n ≤ M` for every `n`, then
`‖f (x + y)‖ ≤ M (‖y‖ / r) ^ T` whenever `x + y` lies in the ball and `‖y‖ ≤ r`. By the
ultrametric inequality the sum is bounded by its largest term, and the term of degree `n ≥ T` is at
most `‖q n‖ r ^ n (‖y‖ / r) ^ n ≤ M (‖y‖ / r) ^ T`.

Over `ℂ` the corresponding statement (Mathlib's
`Complex.dist_le_mul_div_pow_of_mapsTo_ball_of_isLittleO`) assumes a bound for the values of `f`
on the disc whose radius appears in the denominator. Here the hypothesis is instead a bound for
the coefficients at the radius `r`. The scalars may form any nontrivially normed field and the
domain any normed space over it; only the norm of the codomain has to be ultrametric. This is
the form in which Schwarz's lemma enters transcendence proofs at a `p`-adic place: a function with
a zero of order `T` at the centre is small on a smaller disc.

## Main results

* `HasFPowerSeriesOnBall.norm_le_mul_div_pow_of_isUltrametricDist`: Schwarz's lemma
  `‖f (x + y)‖ ≤ M (‖y‖ / r) ^ T`.

## References

* A. Baker, *Transcendental Number Theory*, Cambridge University Press, 1975, Chapter 2, for the
  complex Schwarz lemma in transcendence proofs, which this file replaces at a `p`-adic place.
-/

public section

open scoped ENNReal

variable {𝕜 E F : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  [NormedAddCommGroup F] [NormedSpace 𝕜 F] [IsUltrametricDist F]

/-- **Schwarz's lemma for ultrametric values.** Let `f` have the power series `q` on the ball of
radius `R` about `x`, with values in a normed space with an ultrametric norm. If the terms of `q`
of degree `< T` vanish and `‖q n‖ r ^ n ≤ M` for every `n`, then `‖f (x + y)‖ ≤ M (‖y‖ / r) ^ T`
whenever `x + y` lies in the ball and `‖y‖ ≤ r`. -/
theorem HasFPowerSeriesOnBall.norm_le_mul_div_pow_of_isUltrametricDist {f : E → F}
    {q : FormalMultilinearSeries 𝕜 E F} {x : E} {R : ℝ≥0∞} (hf : HasFPowerSeriesOnBall f q x R)
    {T : ℕ} (hT : ∀ n < T, q n = 0) {r M : ℝ} (hM : ∀ n, ‖q n‖ * r ^ n ≤ M) {y : E}
    (hyr : ‖y‖ ≤ r) (hyR : y ∈ Metric.eball (0 : E) R) :
    ‖f (x + y)‖ ≤ M * (‖y‖ / r) ^ T := by
  have hr : 0 ≤ r := (norm_nonneg y).trans hyr
  have hM0 : 0 ≤ M := (by positivity : 0 ≤ ‖q 0‖ * r ^ 0).trans (hM 0)
  have hs : 0 ≤ ‖y‖ / r := by positivity
  rw [← (hf.hasSum hyR).tsum_eq]
  refine IsUltrametricDist.norm_tsum_le_of_forall_le_of_nonneg (by positivity) fun n ↦ ?_
  rcases lt_or_ge n T with hn | hn
  · rw [hT n hn, zero_apply, norm_zero]
    positivity
  -- The term of degree `n ≥ T` is at most `‖q n‖ ‖y‖ ^ n`.
  refine ((q n).le_opNorm _).trans ?_
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rcases hr.eq_or_lt with rfl | hr
  · -- For `r = 0` also `y = 0`, and the bound reads `‖q n‖ 0 ^ n ≤ M 0 ^ T` for `n ≥ T`.
    rw [norm_le_zero_iff.1 hyr, norm_zero, div_zero]
    rcases T.eq_zero_or_pos with rfl | hT0
    · simpa using hM n
    · rw [zero_pow (by omega), zero_pow hT0.ne', mul_zero, mul_zero]
  · calc ‖q n‖ * ‖y‖ ^ n = ‖q n‖ * r ^ n * (‖y‖ / r) ^ n := by
          rw [div_pow, mul_assoc, mul_div_cancel₀ _ (pow_pos hr n).ne']
      _ ≤ M * (‖y‖ / r) ^ T :=
          mul_le_mul (hM n) (pow_le_pow_of_le_one hs (div_le_one_of_le₀ hyr hr.le) hn)
            (by positivity) hM0
