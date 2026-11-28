/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.GaussianSum.Cotype.Basic

import TauCeti.Analysis.Normed.Module.GaussianSum.Truncation
import TauCeti.Analysis.Normed.Operator.AbsolutelySumming.Gaussian
import TauCeti.Probability.Distributions.Gaussian.Moments

/-!
# Gaussian-to-Rademacher comparison in cotype-2 spaces

In a real normed space `Y` of Gaussian cotype `2` with constant `C`, the Gaussian second moment of
every finite family `y` in `Y` is dominated by its Rademacher second moment. Applying the real
`2`-summing bound (`ContinuousLinearMap.summingENorm_two_le_of_hasGaussianCotype`) and the
integrated Pietsch tail bound
(`ContinuousLinearMap.integral_norm_sq_comp_tailVec_le_of_summingENorm_le`)
to the canonical operator `gaussianSumCLM y : EuclideanSpace ℝ ι →L[ℝ] Y`, and splitting each
standard Gaussian coordinate at a threshold `t` with `C * (𝔼[g² 1_{|g| > t}])^(1/2) ≤ 1 / 2`,
bounds the truncated sum by `t * R₂(y)` (`TauCeti.integral_norm_sq_truncatedGaussianSum_le`) and
the tail sum by `(1 / 2) * G₂(y)`. Absorption yields `G₂(y) ≤ 2 * t * R₂(y)` (Pisier, Lemma 3.8).
We also record the tail threshold certificate `TauCeti.mul_sqrt_setIntegral_sq_tail_gaussianReal_le`
derived from `TauCeti.Probability.sqrt_setIntegral_sq_tail_gaussianReal_le`.

## Main declarations

* `TauCeti.mul_sqrt_setIntegral_sq_tail_gaussianReal_le`:
  `C * √(∫_{|r| > t} r² dγ₁) ≤ 1 / 2` whenever `0 < t` and `C * √3 / t ≤ 1 / 2`.
* `TauCeti.gaussianSecondMoment_le_mul_rademacherSecondMoment_of_tail_bound`:
  `G₂(y) ≤ 2 * t * R₂(y)` when `C * √(∫_{|r| > t} r² dγ₁) ≤ 1 / 2`.

## References

* G. Pisier, *Factorization of Linear Operators and Geometry of Banach Spaces*,
  §3, Lemma 3.8, pp. 34–36.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace TauCeti

/-- Tail threshold certificate for Pisier's Gaussian–Rademacher comparison: if `0 < t` and
`C * √3 / t ≤ 1 / 2`, then `C * √(∫_{|r| > t} r² dγ₁) ≤ 1 / 2`. -/
theorem mul_sqrt_setIntegral_sq_tail_gaussianReal_le {C : ℝ≥0} {t : ℝ} (ht : 0 < t)
    (hCt : (C : ℝ) * √3 / t ≤ 1 / 2) :
    (C : ℝ) * √(∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1) ≤ 1 / 2 :=
  calc
    (C : ℝ) * √(∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1)
        ≤ C * (√3 / t) := by
      gcongr
      exact Probability.sqrt_setIntegral_sq_tail_gaussianReal_le ht
    _ = (C : ℝ) * √3 / t := by ring
    _ ≤ 1 / 2 := hCt

/-- Specialization of `ContinuousLinearMap.integral_norm_sq_comp_tailVec_le_of_summingENorm_le`
to `gaussianSumCLM y` under Gaussian cotype `2`. -/
private theorem integral_norm_sq_tailGaussianSum_le {ι Y : Type*} [Fintype ι]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {C : ℝ≥0} (hY : HasGaussianCotype Y 2 C)
    (y : ι → Y) (t : ℝ) :
    ∫ g, ‖∑ i, EuclideanSpace.tailVec t g i • y i‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) ≤
      ((C : ℝ) * gaussianSecondMoment y) ^ 2 *
        ∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1 := by
  have hsum : (gaussianSumCLM y).summingENorm 2 ≤ ENNReal.ofReal (C * gaussianSecondMoment y) := by
    simpa only [← Function.comp_def, gaussianSumCLM_basisFun] using
      (gaussianSumCLM y).summingENorm_two_le_of_hasGaussianCotype (EuclideanSpace.basisFun ι ℝ) hY
  have hCG : 0 ≤ (C : ℝ) * gaussianSecondMoment y :=
    mul_nonneg C.property (gaussianSecondMoment_nonneg y)
  simpa only [gaussianSumCLM_apply] using
    (gaussianSumCLM y).integral_norm_sq_comp_tailVec_le_of_summingENorm_le hCG hsum t

/-- **Pisier's Gaussian-to-Rademacher comparison (threshold form).** If `Y` has Gaussian cotype `2`
with constant `C` and `t` satisfies `C * √(∫_{|r| > t} r² dγ₁) ≤ 1 / 2`, then every finite family
`y` in `Y` satisfies `G₂(y) ≤ 2 * t * R₂(y)`. -/
theorem gaussianSecondMoment_le_mul_rademacherSecondMoment_of_tail_bound
    {ι Y : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {C : ℝ≥0} (hY : HasGaussianCotype Y 2 C) {t : ℝ}
    (ht : (C : ℝ) * √(∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1) ≤ 1 / 2)
    (y : ι → Y) :
    gaussianSecondMoment y ≤ 2 * t * rademacherSecondMoment y := by
  rcases lt_or_ge t 0 with ht_neg | ht0
  · -- When `t < 0`, the tail integral equals `1`, forcing `C ≤ 1 / 2 < 1` and `Subsingleton Y`.
    have huniv : {r : ℝ | t < |r|} = Set.univ :=
      Set.eq_univ_of_forall fun r ↦ ht_neg.trans_le (abs_nonneg r)
    rw [huniv, Measure.restrict_univ, TauCeti.Probability.integral_sq_gaussianReal] at ht
    simp only [NNReal.coe_one, zero_pow two_ne_zero, add_zero, Real.sqrt_one, mul_one] at ht
    have hC1 : C < 1 := by exact_mod_cast ht.trans_lt (by norm_num : (1 / 2 : ℝ) < 1)
    have : Subsingleton Y := hY.subsingleton_of_lt_one hC1
    have hy : y = 0 := Subsingleton.elim _ _
    simp [hy]
  · have htri := gaussianSecondMoment_le_trunc_add_tail_lpNorm y t
    have htrunc :
        √(∫ g, ‖∑ i, EuclideanSpace.truncVec t g i • y i‖ ^ 2
              ∂stdGaussian (EuclideanSpace ℝ ι)) ≤
          t * rademacherSecondMoment y :=
      Real.sqrt_le_iff.2 ⟨mul_nonneg ht0 (rademacherSecondMoment_nonneg y),
        integral_norm_sq_truncatedGaussianSum_le y ht0⟩
    have htail :
        √(∫ g, ‖∑ i, EuclideanSpace.tailVec t g i • y i‖ ^ 2
              ∂stdGaussian (EuclideanSpace ℝ ι)) ≤
          (1 / 2) * gaussianSecondMoment y := calc
      √(∫ g, ‖∑ i, EuclideanSpace.tailVec t g i • y i‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι))
          ≤ √(((C : ℝ) * gaussianSecondMoment y) ^ 2 *
              ∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1) :=
        Real.sqrt_le_sqrt (integral_norm_sq_tailGaussianSum_le hY y t)
      _ = (C : ℝ) * √(∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1) *
            gaussianSecondMoment y := by
        rw [Real.sqrt_mul (sq_nonneg _),
          Real.sqrt_sq (mul_nonneg (NNReal.coe_nonneg C) (gaussianSecondMoment_nonneg y))]
        ring
      _ ≤ (1 / 2) * gaussianSecondMoment y :=
        mul_le_mul_of_nonneg_right ht (gaussianSecondMoment_nonneg y)
    linarith

end TauCeti
