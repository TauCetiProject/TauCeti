/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals
import TauCeti.MeasureTheory.Integral.Dilation

/-!
# Gaussian integrals of homogeneous functions

Let `E` be a finite-dimensional real normed space of dimension `D` with an additive Haar measure
`μ`, let `Q : E → ℝ` be positively homogeneous of degree `2` (`Q (c • x) = c ^ 2 * Q x` for
`c > 0`), for instance the square of a norm or a positive definite quadratic form, and let
`g : E → ℝ≥0∞` be positively homogeneous of degree `k`. Then:

* *scaling*: `∫ g exp (-t Q) dμ = t ^ (-(D + k) / 2) * ∫ g exp (-Q) dμ` for `t > 0`;
* *integration by parts against the Gaussian*: if `E ≠ 0`, `Q` is positive away from `0` and
  `D + k > 0`, then multiplication by `Q` acts on `g` as the scalar `(D + k) / 2`,
  `∫ Q g exp (-Q) dμ = (D + k) / 2 * ∫ g exp (-Q) dμ`;
* iterating, `∫ Q ^ m g exp (-Q) dμ = ∏_{j < m} ((D + k) / 2 + j) * ∫ g exp (-Q) dμ`, the rising
  factorial of `(D + k) / 2`.

For `Q = |x|²` on `ℝ^D` the second identity is the integration by parts
`∫ g (x · ∇) e^{-|x|²} = -∫ div (g x) e^{-|x|²}` combined with Euler's identity
`x · ∇g = k g`. It is proved here without derivatives: writing `exp (-Q x)` as
`∫_{t > 1} Q x exp (-t Q x) dt` and exchanging the integrals, the scaling law for the
`(k + 2)`-homogeneous function `Q g` reduces the identity to `∫_{t > 1} t ^ (-(D + k) / 2 - 1) dt`.
All integrals are lower Lebesgue integrals, so no integrability hypothesis is needed.

These identities compute the Gaussian moments of homogeneous polynomials, for instance the
weighted norms of the polynomial vectors of the Fock model.

## Main results

* `MeasureTheory.Measure.lintegral_mul_ofReal_exp_neg_mul_of_homogeneous`: the scaling law.
* `MeasureTheory.Measure.lintegral_ofReal_mul_mul_ofReal_exp_neg_of_homogeneous`: integration by
  parts.
* `MeasureTheory.Measure.lintegral_ofReal_pow_mul_mul_ofReal_exp_neg_of_homogeneous`: the
  moments.
-/

public section

open MeasureTheory Set Module
open scoped ENNReal

namespace MeasureTheory.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] (μ : Measure E) [μ.IsAddHaarMeasure] {Q : E → ℝ}
  {g : E → ℝ≥0∞} {k : ℝ}

/-- **Scaling of Gaussian integrals of homogeneous functions.** If `Q` is positively homogeneous
of degree `2` and `g` positively homogeneous of degree `k`, then for `t > 0`,
`∫ g exp (-t Q) dμ = t ^ (-(D + k) / 2) * ∫ g exp (-Q) dμ`, with `D` the dimension of `E`. -/
theorem lintegral_mul_ofReal_exp_neg_mul_of_homogeneous
    (hQ : ∀ c : ℝ, 0 < c → ∀ x, Q (c • x) = c ^ 2 * Q x)
    (hg : ∀ c : ℝ, 0 < c → ∀ x, g (c • x) = ENNReal.ofReal (c ^ k) * g x) {t : ℝ} (ht : 0 < t) :
    ∫⁻ x, g x * ENNReal.ofReal (Real.exp (-(t * Q x))) ∂μ =
      ENNReal.ofReal (t ^ (-(finrank ℝ E + k) / 2)) *
        ∫⁻ x, g x * ENNReal.ofReal (Real.exp (-Q x)) ∂μ := by
  have hs : 0 < √t := Real.sqrt_pos.2 ht
  -- Substituting `x = √t • y` in the right-hand integral gives the left-hand one.
  have h_sub := μ.lintegral_comp_smul (fun x ↦ g x * ENNReal.ofReal (Real.exp (-Q x)))
    hs.ne'
  simp only [hg _ hs, hQ _ hs, Real.sq_sqrt ht.le, mul_assoc] at h_sub
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at h_sub
  have h_pow : √t ^ k * t ^ (-(finrank ℝ E + k) / 2) = |(√t ^ finrank ℝ E)⁻¹| := by
    rw [abs_of_nonneg (by positivity), ← Real.rpow_natCast, ← Real.rpow_neg hs.le,
      Real.sqrt_eq_rpow, ← Real.rpow_mul ht.le, ← Real.rpow_mul ht.le, ← Real.rpow_add ht]
    ring_nf
  have h_ne : ENNReal.ofReal (√t ^ k) ≠ 0 := by
    simpa using Real.rpow_pos_of_pos hs k
  refine (ENNReal.mul_right_inj h_ne ENNReal.ofReal_ne_top).1 ?_
  rw [h_sub, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity), h_pow]

/-- **Integration by parts against the Gaussian.** Let `Q` be positively homogeneous of degree `2`
and positive away from `0`, and `g` positively homogeneous of degree `k`, on a nonzero space `E`
of dimension `D` with `D + k > 0`. Then multiplication by `Q` acts on `g` as `(D + k) / 2`:
`∫ Q g exp (-Q) dμ = (D + k) / 2 * ∫ g exp (-Q) dμ`. -/
theorem lintegral_ofReal_mul_mul_ofReal_exp_neg_of_homogeneous [Nontrivial E]
    (hQ_meas : AEMeasurable Q μ) (hQ : ∀ c : ℝ, 0 < c → ∀ x, Q (c • x) = c ^ 2 * Q x)
    (hQ_pos : ∀ x, x ≠ 0 → 0 < Q x) (hg_meas : AEMeasurable g μ)
    (hg : ∀ c : ℝ, 0 < c → ∀ x, g (c • x) = ENNReal.ofReal (c ^ k) * g x)
    (hk : 0 < finrank ℝ E + k) :
    ∫⁻ x, ENNReal.ofReal (Q x) * g x * ENNReal.ofReal (Real.exp (-Q x)) ∂μ =
      ENNReal.ofReal ((finrank ℝ E + k) / 2) *
        ∫⁻ x, g x * ENNReal.ofReal (Real.exp (-Q x)) ∂μ := by
  set J := ∫⁻ x, ENNReal.ofReal (Q x) * g x * ENNReal.ofReal (Real.exp (-Q x)) ∂μ
  -- `Q g` is positively homogeneous of degree `k + 2`.
  have hQg (c : ℝ) (hc : 0 < c) (x : E) : ENNReal.ofReal (Q (c • x)) * g (c • x) =
      ENNReal.ofReal (c ^ (k + 2)) * (ENNReal.ofReal (Q x) * g x) := by
    rw [hQ c hc, hg c hc, ENNReal.ofReal_mul (by positivity), Real.rpow_add hc,
      ENNReal.ofReal_mul (by positivity), Real.rpow_two]
    ring
  -- Write `exp (-Q x)` as an integral over `t > 1`, exchange, and rescale in `x`.
  have h_inner : ∀ᵐ x ∂μ, g x * ENNReal.ofReal (Real.exp (-Q x)) =
      ∫⁻ t in Ioi 1, ENNReal.ofReal (Q x) * g x * ENNReal.ofReal (Real.exp (-(t * Q x))) := by
    filter_upwards [μ.ae_ne 0] with x hx
    have hq := hQ_pos x hx
    have h_eq (t : ℝ) : -(t * Q x) = -Q x * t := by ring
    simp_rw [h_eq]
    rw [lintegral_const_mul _ (by fun_prop),
      TauCeti.lintegral_Ioi_ofReal_exp_mul (neg_neg_of_pos hq), mul_comm (ENNReal.ofReal (Q x)),
      mul_assoc, ← ENNReal.ofReal_mul hq.le]
    congr 2
    field_simp
  have h_swap : ∫⁻ x, g x * ENNReal.ofReal (Real.exp (-Q x)) ∂μ =
      ∫⁻ t in Ioi 1, ENNReal.ofReal (t ^ (-((finrank ℝ E + k) / 2) - 1)) * J := by
    rw [lintegral_congr_ae h_inner, lintegral_lintegral_swap (by
      have hQ' := hQ_meas.comp_fst (ν := (volume : Measure ℝ).restrict (Ioi 1))
      have hg' := hg_meas.comp_fst (ν := (volume : Measure ℝ).restrict (Ioi 1))
      exact (hQ'.ennreal_ofReal.mul hg').mul (Real.measurable_exp.comp_aemeasurable
        (measurable_snd.aemeasurable.mul hQ').neg).ennreal_ofReal)]
    refine setLIntegral_congr_fun measurableSet_Ioi fun t ht ↦ ?_
    rw [μ.lintegral_mul_ofReal_exp_neg_mul_of_homogeneous hQ hQg (zero_lt_one.trans ht)]
    congr 3
    ring
  have h_one : (finrank ℝ E + k) / 2 * (-1 ^ (-((finrank ℝ E + k) / 2) - 1 + 1) /
      (-((finrank ℝ E + k) / 2) - 1 + 1)) = 1 := by
    rw [Real.one_rpow, sub_add_cancel, neg_div_neg_eq, mul_one_div_cancel (half_pos hk).ne']
  rw [h_swap, lintegral_mul_const _ (by fun_prop),
    TauCeti.lintegral_Ioi_ofReal_rpow_of_lt (by linarith [half_pos hk]) one_pos, ← mul_assoc,
    ← ENNReal.ofReal_mul (half_pos hk).le, h_one, ENNReal.ofReal_one, one_mul]

/-- **Gaussian moments of homogeneous functions.** Under the hypotheses of
`MeasureTheory.Measure.lintegral_ofReal_mul_mul_ofReal_exp_neg_of_homogeneous`, multiplication by
`Q ^ m` acts on `g` as the rising factorial `∏_{j < m} ((D + k) / 2 + j)`:
`∫ Q ^ m g exp (-Q) dμ = ∏_{j < m} ((D + k) / 2 + j) * ∫ g exp (-Q) dμ`. -/
theorem lintegral_ofReal_pow_mul_mul_ofReal_exp_neg_of_homogeneous [Nontrivial E]
    (hQ_meas : AEMeasurable Q μ) (hQ : ∀ c : ℝ, 0 < c → ∀ x, Q (c • x) = c ^ 2 * Q x)
    (hQ_pos : ∀ x, x ≠ 0 → 0 < Q x) (hg_meas : AEMeasurable g μ)
    (hg : ∀ c : ℝ, 0 < c → ∀ x, g (c • x) = ENNReal.ofReal (c ^ k) * g x)
    (hk : 0 < finrank ℝ E + k) (m : ℕ) :
    ∫⁻ x, ENNReal.ofReal (Q x) ^ m * g x * ENNReal.ofReal (Real.exp (-Q x)) ∂μ =
      (∏ j ∈ Finset.range m, ENNReal.ofReal ((finrank ℝ E + k) / 2 + j)) *
        ∫⁻ x, g x * ENNReal.ofReal (Real.exp (-Q x)) ∂μ := by
  induction m with
  | zero => simp
  | succ m ih =>
    -- `Q ^ m g` is positively homogeneous of degree `k + 2 m`.
    have hQg (c : ℝ) (hc : 0 < c) (x : E) : ENNReal.ofReal (Q (c • x)) ^ m * g (c • x) =
        ENNReal.ofReal (c ^ (k + 2 * m)) * (ENNReal.ofReal (Q x) ^ m * g x) := by
      rw [hQ c hc, hg c hc, ENNReal.ofReal_mul (by positivity), Real.rpow_add hc,
        ENNReal.ofReal_mul (by positivity), mul_pow, Real.rpow_mul hc.le, ← ENNReal.ofReal_pow
        (by positivity), Real.rpow_two, Real.rpow_natCast, ← pow_mul]
      ring
    have h_step := μ.lintegral_ofReal_mul_mul_ofReal_exp_neg_of_homogeneous hQ_meas hQ hQ_pos
      (g := fun x ↦ ENNReal.ofReal (Q x) ^ m * g x)
      ((hQ_meas.ennreal_ofReal.pow_const m).mul hg_meas) hQg
      (by have : (0 : ℝ) ≤ 2 * m := by positivity
          linarith)
    simp only [← mul_assoc] at h_step
    simp_rw [pow_succ, mul_comm _ (ENNReal.ofReal (Q _))]
    rw [h_step, ih, Finset.prod_range_succ]
    ring_nf

end MeasureTheory.Measure
