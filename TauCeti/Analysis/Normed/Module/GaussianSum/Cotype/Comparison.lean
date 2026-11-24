/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.GaussianSum.Cotype.Basic

import TauCeti.Analysis.Normed.Module.GaussianSum.Truncation
import TauCeti.Analysis.Normed.Operator.AbsolutelySumming.Gaussian
import TauCeti.Analysis.Normed.Operator.AbsolutelySumming.Pietsch
import TauCeti.Probability.Distributions.Gaussian.CoordinateTails
import TauCeti.Probability.Distributions.Gaussian.Moments

/-!
# Gaussian-to-Rademacher comparison in cotype-2 spaces

In a real normed space `Y` of Gaussian cotype `2` with constant `C`, the Gaussian second moment of
every finite family `y` in `Y` is dominated by its Rademacher second moment. Applying the real
`2`-summing bound (`ContinuousLinearMap.summingENorm_two_le_of_hasGaussianCotype`) and integrated
Pietsch domination (`ContinuousLinearMap.integral_norm_apply_rpow_le_of_summingENorm_le`) to the
canonical operator `EuclideanSpace ℝ ι →L[ℝ] Y` associated to `y`, and splitting each standard
Gaussian coordinate at a threshold `t` with `C * (𝔼[g² 1_{|g| > t}])^(1/2) ≤ 1 / 2`, bounds the
truncated sum by `t * R₂(y)` (`TauCeti.integral_norm_sq_truncVec_le`) and the tail sum by
`(1 / 2) * G₂(y)`. Absorption yields `G₂(y) ≤ 2 * t * R₂(y)` (Pisier, Lemma 3.8). Combining
`gaussianSecondMoment_le_two_mul_rademacherSecondMoment` at `t = 4 * C` with the threshold
certificate `mul_sqrt_setIntegral_sq_tail_four_mul_le` and Gaussian cotype `2` gives Rademacher
cotype `2` with constant `8 * C²`.

## Main declarations

* `TauCeti.gaussianSecondMoment_le_two_mul_rademacherSecondMoment`:
  `G₂(y) ≤ 2 * t * R₂(y)` when `C * √(∫_{|r| > t} r² dγ₁) ≤ 1 / 2`.
* `TauCeti.Probability.mul_sqrt_setIntegral_sq_tail_four_mul_le`:
  `C * √(∫_{|r| > 4C} r² dγ₁) ≤ 1 / 2` for all `C ≥ 0`.
* `TauCeti.HasGaussianCotype.hasCotype_two`: Gaussian cotype `2` implies Rademacher cotype `2`
  with constant `8 * C²`.

## References

* G. Pisier, *Factorization of Linear Operators and Geometry of Banach Spaces*,
  §3, Lemma 3.8, pp. 34–36.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal

namespace TauCeti.Probability

/-- The threshold condition `C * (𝔼[g² 1_{|g| > 4C}])^(1/2) ≤ 1 / 2` holds for all `C ≥ 0`. -/
theorem mul_sqrt_setIntegral_sq_tail_four_mul_le (C : ℝ≥0) :
    (C : ℝ) * √(∫ r in {r : ℝ | 4 * (C : ℝ) < |r|}, r ^ 2 ∂gaussianReal 0 1) ≤ 1 / 2 := by
  rcases eq_or_ne C 0 with rfl | hC
  · simp
  have hCpos : 0 < (C : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hC)
  have htpos : 0 < 4 * (C : ℝ) := by positivity
  calc
    (C : ℝ) * √(∫ r in {r : ℝ | 4 * (C : ℝ) < |r|}, r ^ 2 ∂gaussianReal 0 1)
        ≤ (C : ℝ) * √(3 / (4 * (C : ℝ)) ^ 2) := by
      gcongr
      exact setIntegral_sq_tail_gaussianReal_le htpos
    _ = √3 / 4 := by
      rw [Real.sqrt_div (by norm_num), Real.sqrt_sq htpos.le]
      field_simp [hCpos.ne']
    _ ≤ 1 / 2 := by
      have h3 : √3 ≤ 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
      linarith

end TauCeti.Probability

namespace TauCeti

/-- Integrated Pietsch domination bounds the tail Gaussian sum using Proposition 3.7. -/
private theorem integral_norm_sq_tailVec_le {ι Y : Type*} [Fintype ι]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {C : ℝ≥0} (hY : HasGaussianCotype Y 2 C)
    (y : ι → Y) (t : ℝ) :
    ∫ g, ‖∑ i, EuclideanSpace.tailVec t g i • y i‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) ≤
      ((C : ℝ) * gaussianSecondMoment y) ^ 2 *
        ∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1 := by
  let U : EuclideanSpace ℝ ι →L[ℝ] Y := (EuclideanSpace.basisFun ι ℝ).toBasis.constrL y
  have hU_basis : U ∘ EuclideanSpace.basisFun ι ℝ = y := by
    ext i
    rw [Function.comp_apply, ← (EuclideanSpace.basisFun ι ℝ).coe_toBasis]
    exact Module.Basis.constrL_basis (EuclideanSpace.basisFun ι ℝ).toBasis y i
  have hsum : U.summingENorm 2 ≤ ENNReal.ofReal (C * gaussianSecondMoment y) := by
    simpa only [← Function.comp_def, hU_basis] using
      U.summingENorm_two_le_of_hasGaussianCotype (EuclideanSpace.basisFun ι ℝ) hY
  have hCG : 0 ≤ (C : ℝ) * gaussianSecondMoment y :=
    mul_nonneg C.property (gaussianSecondMoment_nonneg y)
  have hmem : MemLp (EuclideanSpace.tailVec (ι := ι) t) 2 (stdGaussian (EuclideanSpace ℝ ι)) := by
    simpa only [ContinuousLinearMap.id_apply] using
      Probability.memLp_comp_tailVec (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι)) t (by simp)
  have hs : MeasurableSet {r : ℝ | t < |r|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hpietsch := U.integral_norm_apply_rpow_le_of_summingENorm_le (p := 2) (by simp) hCG hsum
    hmem (M := ∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1) fun f hf ↦ by
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs,
        Probability.integral_sq_apply_tailVec]
      exact mul_le_of_le_one_left (setIntegral_nonneg hs fun _ _ ↦ sq_nonneg _)
        (by nlinarith [norm_nonneg f])
  simpa only [U, EuclideanSpace.basisFun_toBasis_constrL_apply, ENNReal.toReal_ofNat,
    Real.rpow_two] using hpietsch

/-- **Pisier's Gaussian-to-Rademacher comparison (threshold form).** If `Y` has Gaussian cotype `2`
with constant `C` and `t` satisfies `C * √(∫_{|r| > t} r² dγ₁) ≤ 1 / 2`, then every finite family
`y` in `Y` satisfies `G₂(y) ≤ 2 * t * R₂(y)`. -/
theorem gaussianSecondMoment_le_two_mul_rademacherSecondMoment
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
  · have htri := gaussianSecondMoment_le_trunc_add_tail y t
    have htrunc :
        √(∫ g, ‖∑ i, EuclideanSpace.truncVec t g i • y i‖ ^ 2
              ∂stdGaussian (EuclideanSpace ℝ ι)) ≤
          t * rademacherSecondMoment y :=
      Real.sqrt_le_iff.2 ⟨mul_nonneg ht0 (rademacherSecondMoment_nonneg y),
        integral_norm_sq_truncVec_le y ht0⟩
    have htail :
        √(∫ g, ‖∑ i, EuclideanSpace.tailVec t g i • y i‖ ^ 2
              ∂stdGaussian (EuclideanSpace ℝ ι)) ≤
          (1 / 2) * gaussianSecondMoment y := calc
      √(∫ g, ‖∑ i, EuclideanSpace.tailVec t g i • y i‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι))
          ≤ √(((C : ℝ) * gaussianSecondMoment y) ^ 2 *
              ∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1) :=
        Real.sqrt_le_sqrt (integral_norm_sq_tailVec_le hY y t)
      _ = (C : ℝ) * √(∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1) *
            gaussianSecondMoment y := by
        rw [Real.sqrt_mul (sq_nonneg _),
          Real.sqrt_sq (mul_nonneg (NNReal.coe_nonneg C) (gaussianSecondMoment_nonneg y))]
        ring
      _ ≤ (1 / 2) * gaussianSecondMoment y :=
        mul_le_mul_of_nonneg_right ht (gaussianSecondMoment_nonneg y)
    linarith

/-- Gaussian cotype `2` with constant `C` implies Rademacher cotype `2` with constant `8 * C²`. -/
theorem HasGaussianCotype.hasCotype_two {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {C : ℝ≥0} (hY : HasGaussianCotype Y 2 C) : HasCotype Y 2 (8 * C ^ 2) := by
  rw [hasCotype_iff]
  intro n y
  calc
    ‖WithLp.toLp 2 y‖ ≤ C * gaussianSecondMoment y := hY.norm_toLp_le y
    _ ≤ C * (2 * (4 * C) * rademacherSecondMoment y) := by
      gcongr
      exact gaussianSecondMoment_le_two_mul_rademacherSecondMoment hY
        (Probability.mul_sqrt_setIntegral_sq_tail_four_mul_le C) y
    _ = ((8 * C ^ 2 : ℝ≥0) : ℝ) * rademacherSecondMoment y := by push_cast; ring

end TauCeti
