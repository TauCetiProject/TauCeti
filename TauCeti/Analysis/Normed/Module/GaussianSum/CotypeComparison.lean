/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.GaussianSum.Cotype

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Distributions.Gaussian.Fernique
import Mathlib.Topology.Instances.RealVectorSpace
import TauCeti.Analysis.Normed.Module.RademacherSum.Contraction
import TauCeti.Analysis.Normed.Module.WeakDual.Integral
import TauCeti.Analysis.Normed.Operator.AbsolutelySumming.Gaussian
import TauCeti.Analysis.Normed.Operator.AbsolutelySumming.Pietsch
import TauCeti.MeasureTheory.Function.LpSeminorm.LpNorm
import TauCeti.Probability.Distributions.Gaussian.CoordinateTails
import TauCeti.Probability.Distributions.Gaussian.Moments
import TauCeti.Probability.Distributions.Gaussian.Symmetry

/-!
# Gaussian-to-Rademacher comparison in cotype-2 spaces

In a real normed space `Y` of Gaussian cotype `2` with constant `C`, the Gaussian second moment of
every finite family `y` in `Y` is dominated by its Rademacher second moment. Applying the real
`2`-summing bound (`ContinuousLinearMap.summingENorm_two_le_of_hasGaussianCotype`) and Pietsch
domination to the canonical operator `EuclideanSpace ℝ ι →L[ℝ] Y` associated to `y`, and splitting
each standard Gaussian coordinate at a threshold `t` with
`C * (𝔼[g² 1_{|g| > t}])^(1/2) ≤ 1 / 2`, bounds the truncated sum by `t * R₂(y)` (by sign-flip
invariance and Rademacher contraction) and the tail sum by `(1 / 2) * G₂(y)` (by Pietsch
domination and Fubini). Absorption yields `G₂(y) ≤ 2 * t * R₂(y)` (Pisier, Lemma 3.8). Choosing
`t = 4 * C` via `𝔼[g⁴] = 3` gives the explicit bound `G₂(y) ≤ 8 * C * R₂(y)`, and hence Gaussian
cotype `2` implies Rademacher cotype `2` with constant `8 * C²`.

## Main declarations

* `TauCeti.gaussianSecondMoment_le_two_mul_rademacherSecondMoment`:
  `G₂(y) ≤ 2 * t * R₂(y)` when `C * √(∫_{|r| > t} r² dγ₁) ≤ 1 / 2`.
* `TauCeti.gaussianSecondMoment_le_eight_mul_rademacherSecondMoment`:
  `G₂(y) ≤ 8 * C * R₂(y)` under Gaussian cotype `2`.
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

namespace TauCeti

section TailHelpers

variable {ι : Type*} [Fintype ι]

/-- Sign-flip invariance of the squared norm of `(EuclideanSpace.basisFun ι ℝ).toBasis.constrL y ∘
truncVec t`. -/
private theorem integral_norm_sq_truncVec_units_smul {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (y : ι → Y) (t : ℝ) (ε : ι → ℤˣ) :
    ∫ g, ‖(EuclideanSpace.basisFun ι ℝ).toBasis.constrL y (EuclideanSpace.truncVec t g)‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι) =
      ∫ g, ‖∑ i, ε i • (EuclideanSpace.truncVec t g i • y i)‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι) := by
  let U := (EuclideanSpace.basisFun ι ℝ).toBasis.constrL y
  have hmeas : StronglyMeasurable fun g : EuclideanSpace ℝ ι ↦
      ‖U (EuclideanSpace.truncVec t g)‖ ^ 2 :=
    (U.continuous.comp_stronglyMeasurable
      (EuclideanSpace.measurable_truncVec t).stronglyMeasurable).norm.pow 2
  conv_lhs =>
    rw [← Probability.stdGaussian_map_units_smul ε,
      integral_map (μ := stdGaussian (EuclideanSpace ℝ ι)) (by fun_prop)
        hmeas.aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun g ↦ ?_)
  dsimp only [U]
  rw [EuclideanSpace.basisFun_toBasis_constrL_apply]
  simp_rw [EuclideanSpace.truncVec_units_smul, smul_assoc]

/-- Sign-flip invariance and Rademacher contraction bound the truncated Gaussian sum by
`t * R₂(y)`. -/
private theorem integral_norm_sq_truncVec_le [DecidableEq ι] {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (y : ι → Y) {t : ℝ} (ht : 0 ≤ t) :
    ∫ g, ‖(EuclideanSpace.basisFun ι ℝ).toBasis.constrL y (EuclideanSpace.truncVec t g)‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι) ≤
      (t * rademacherSecondMoment y) ^ 2 := by
  have hint_ε (ε : ι → ℤˣ) :
      Integrable (fun g : EuclideanSpace ℝ ι ↦
          ‖∑ i, ε i • (EuclideanSpace.truncVec t g i • y i)‖ ^ 2)
        (stdGaussian (EuclideanSpace ℝ ι)) := by
    have heq (g : EuclideanSpace ℝ ι) :
        ∑ i, ε i • (EuclideanSpace.truncVec t g i • y i) =
          (EuclideanSpace.basisFun ι ℝ).toBasis.constrL (fun i ↦ ε i • y i)
            (EuclideanSpace.truncVec t g) := by
      rw [EuclideanSpace.basisFun_toBasis_constrL_apply]
      exact Finset.sum_congr rfl fun i _ ↦ smul_comm _ _ _
    simp_rw [heq]
    exact (Probability.memLp_comp_truncVec
      ((EuclideanSpace.basisFun ι ℝ).toBasis.constrL fun i ↦ ε i • y i) t (by simp))
      |>.integrable_norm_pow (by norm_num)
  have havg : ∫ g, ‖(EuclideanSpace.basisFun ι ℝ).toBasis.constrL y
          (EuclideanSpace.truncVec t g)‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) =
      ∫ g, 𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • (EuclideanSpace.truncVec t g i • y i)‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι) := by
    simp_rw [Fintype.expect_eq_sum_div_card]
    rw [integral_div, integral_finsetSum _ fun ε _ ↦ hint_ε ε]
    simp_rw [← integral_norm_sq_truncVec_units_smul y t, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    have hcard : (Fintype.card (ι → ℤˣ) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
    field_simp [hcard]
  rw [havg]
  calc
    ∫ g, 𝔼 ε : ι → ℤˣ, ‖∑ i, ε i • (EuclideanSpace.truncVec t g i • y i)‖ ^ 2
          ∂stdGaussian (EuclideanSpace ℝ ι)
        ≤ ∫ _, (t * rademacherSecondMoment y) ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) := by
      refine integral_mono ?_ (integrable_const _) fun g ↦ ?_
      · simp_rw [Fintype.expect_eq_sum_div_card]
        exact (integrable_finsetSum _ fun ε _ ↦ hint_ε ε).div_const _
      · rw [← rademacherSecondMoment_sq]
        exact pow_le_pow_left₀ (rademacherSecondMoment_nonneg _)
          (rademacherSecondMoment_smul_le (EuclideanSpace.abs_truncVec_apply_le ht g) y) 2
    _ = (t * rademacherSecondMoment y) ^ 2 := by simp

private theorem integral_sq_apply_tailVec_le_of_mem_closedBall
    (f : WeakDual.closedBall ℝ (EuclideanSpace ℝ ι) 1) (t : ℝ) :
    ∫ g, ‖(f : WeakDual ℝ (EuclideanSpace ℝ ι)) (EuclideanSpace.tailVec t g)‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι) ≤
      ∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1 := by
  simp_rw [Real.norm_eq_abs, ← WeakDual.toStrongDual_apply]
  rw [Probability.integral_sq_apply_tailVec
    (WeakDual.toStrongDual (f : WeakDual ℝ (EuclideanSpace ℝ ι))) t]
  have hf1 : ‖WeakDual.toStrongDual (f : WeakDual ℝ (EuclideanSpace ℝ ι))‖ ≤ 1 :=
    WeakDual.norm_toStrongDual_le_of_mem_closedBall f
  exact mul_le_of_le_one_left (setIntegral_nonneg
    (measurableSet_lt measurable_const continuous_abs.measurable) fun _ _ ↦ sq_nonneg _)
    (by nlinarith [norm_nonneg (WeakDual.toStrongDual (f : WeakDual ℝ (EuclideanSpace ℝ ι)))])

/-- Pietsch domination and Fubini bound the tail Gaussian sum using Proposition 3.7. -/
private theorem integral_norm_sq_tailVec_le {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {C : ℝ≥0} (hY : HasGaussianCotype Y 2 C)
    (y : ι → Y) (t : ℝ) :
    ∫ g, ‖(EuclideanSpace.basisFun ι ℝ).toBasis.constrL y (EuclideanSpace.tailVec t g)‖ ^ 2
        ∂stdGaussian (EuclideanSpace ℝ ι) ≤
      ((C : ℝ) * gaussianSecondMoment y) ^ 2 *
        ∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1 := by
  let : MeasurableSpace (WeakDual ℝ (EuclideanSpace ℝ ι)) := borel _
  let : BorelSpace (WeakDual ℝ (EuclideanSpace ℝ ι)) := ⟨rfl⟩
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
  obtain ⟨ν, _, _, hν⟩ :=
    U.exists_isProbabilityMeasure_of_summingENorm_le_ofReal (p := 2)
      (by simp) hCG hsum
  let Φ : EuclideanSpace ℝ ι × WeakDual.closedBall ℝ (EuclideanSpace ℝ ι) 1 → ℝ :=
    fun p ↦ ‖(p.snd : WeakDual ℝ (EuclideanSpace ℝ ι)) (EuclideanSpace.tailVec t p.fst)‖ ^ 2
  have hΦ_int : Integrable Φ ((stdGaussian (EuclideanSpace ℝ ι)).prod ν) :=
    (stdGaussian (EuclideanSpace ℝ ι)).integrable_norm_apply_closedBall_sq ν
      (EuclideanSpace.measurable_tailVec t)
      ((Probability.memLp_comp_tailVec (ContinuousLinearMap.id ℝ (EuclideanSpace ℝ ι))
        t (by simp)).integrable_norm_pow (by norm_num))
  have hpt (g : EuclideanSpace ℝ ι) :
      ‖U (EuclideanSpace.tailVec t g)‖ ^ 2 ≤
        ((C : ℝ) * gaussianSecondMoment y) ^ 2 * ∫ f, Φ (g, f) ∂ν := by
    have h2 := pow_le_pow_left₀ (norm_nonneg _) (hν (EuclideanSpace.tailVec t g)) 2
    rw [mul_pow, ENNReal.toReal_ofNat, ← Real.rpow_mul_natCast
      (integral_nonneg fun _ ↦ by positivity)] at h2
    simpa [Φ] using h2
  calc
    ∫ g, ‖U (EuclideanSpace.tailVec t g)‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι)
        ≤ ∫ g, ((C : ℝ) * gaussianSecondMoment y) ^ 2 * ∫ f, Φ (g, f) ∂ν
            ∂stdGaussian (EuclideanSpace ℝ ι) :=
      integral_mono ((Probability.memLp_comp_tailVec U t (by simp)).integrable_norm_pow
        (by norm_num)) (hΦ_int.integral_prod_left.const_mul _) hpt
    _ = ((C : ℝ) * gaussianSecondMoment y) ^ 2 *
          ∫ g, ∫ f, Φ (g, f) ∂ν ∂stdGaussian (EuclideanSpace ℝ ι) :=
      integral_const_mul _ _
    _ = ((C : ℝ) * gaussianSecondMoment y) ^ 2 *
          ∫ f, ∫ g, Φ (g, f) ∂stdGaussian (EuclideanSpace ℝ ι) ∂ν := by
      rw [integral_integral_swap hΦ_int]
    _ ≤ ((C : ℝ) * gaussianSecondMoment y) ^ 2 *
          ∫ _, ∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1 ∂ν :=
      mul_le_mul_of_nonneg_left (integral_mono hΦ_int.integral_prod_right (integrable_const _)
        fun f ↦ integral_sq_apply_tailVec_le_of_mem_closedBall f t) (sq_nonneg _)
    _ = ((C : ℝ) * gaussianSecondMoment y) ^ 2 *
          ∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1 := by simp

/-- The `L²` Minkowski triangle inequality splits `G₂(y)` into its truncated and tail parts. -/
private theorem gaussianSecondMoment_le_trunc_add_tail {Y : Type*}
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (y : ι → Y) (t : ℝ) :
    gaussianSecondMoment y ≤
      √(∫ g, ‖(EuclideanSpace.basisFun ι ℝ).toBasis.constrL y (EuclideanSpace.truncVec t g)‖ ^ 2
          ∂stdGaussian (EuclideanSpace ℝ ι)) +
        √(∫ g, ‖(EuclideanSpace.basisFun ι ℝ).toBasis.constrL y (EuclideanSpace.tailVec t g)‖ ^ 2
          ∂stdGaussian (EuclideanSpace ℝ ι)) := by
  let U : EuclideanSpace ℝ ι →L[ℝ] Y := (EuclideanSpace.basisFun ι ℝ).toBasis.constrL y
  have hsplit (g : EuclideanSpace ℝ ι) : ∑ i, g i • y i =
      ((fun g ↦ U (EuclideanSpace.truncVec t g)) +
        (fun g ↦ U (EuclideanSpace.tailVec t g))) g := by
    rw [Pi.add_apply, ← U.map_add, EuclideanSpace.truncVec_add_tailVec]
    exact (EuclideanSpace.basisFun_toBasis_constrL_apply y g).symm
  rw [gaussianSecondMoment_def]
  simp_rw [hsplit]
  exact (Probability.memLp_comp_truncVec U t (by simp)).sqrt_integral_norm_add_sq_le
    (Probability.memLp_comp_tailVec U t (by simp))

end TailHelpers

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
        √(∫ g, ‖(EuclideanSpace.basisFun ι ℝ).toBasis.constrL y
              (EuclideanSpace.truncVec t g)‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι)) ≤
          t * rademacherSecondMoment y :=
      Real.sqrt_le_iff.2 ⟨mul_nonneg ht0 (rademacherSecondMoment_nonneg y),
        integral_norm_sq_truncVec_le y ht0⟩
    have htail :
        √(∫ g, ‖(EuclideanSpace.basisFun ι ℝ).toBasis.constrL y
              (EuclideanSpace.tailVec t g)‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι)) ≤
          (1 / 2) * gaussianSecondMoment y := calc
      √(∫ g, ‖(EuclideanSpace.basisFun ι ℝ).toBasis.constrL y (EuclideanSpace.tailVec t g)‖ ^ 2
            ∂stdGaussian (EuclideanSpace ℝ ι))
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

/-- **Pisier's Gaussian-to-Rademacher comparison (explicit constant).** In a real normed space of
Gaussian cotype `2` with constant `C`, the Gaussian second moment of every finite family is at most
`8 * C` times its Rademacher second moment. -/
theorem gaussianSecondMoment_le_eight_mul_rademacherSecondMoment
    {ι Y : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {C : ℝ≥0} (hY : HasGaussianCotype Y 2 C) (y : ι → Y) :
    gaussianSecondMoment y ≤ 8 * C * rademacherSecondMoment y :=
  (gaussianSecondMoment_le_two_mul_rademacherSecondMoment hY
    (Probability.mul_sqrt_setIntegral_sq_tail_four_mul_le C) y).trans_eq (by ring)

/-- Gaussian cotype `2` with constant `C` implies Rademacher cotype `2` with constant `8 * C²`. -/
theorem HasGaussianCotype.hasCotype_two {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    {C : ℝ≥0} (hY : HasGaussianCotype Y 2 C) : HasCotype Y 2 (8 * C ^ 2) := by
  rw [hasCotype_iff]
  intro n y
  calc
    ‖WithLp.toLp 2 y‖ ≤ C * gaussianSecondMoment y := hY.norm_toLp_le y
    _ ≤ C * (8 * C * rademacherSecondMoment y) := by
      gcongr
      exact gaussianSecondMoment_le_eight_mul_rademacherSecondMoment hY y
    _ = ((8 * C ^ 2 : ℝ≥0) : ℝ) * rademacherSecondMoment y := by push_cast; ring

end TauCeti
