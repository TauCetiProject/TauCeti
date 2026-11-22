/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.AbsolutelySumming.Gaussian
public import TauCeti.Analysis.Normed.Module.RademacherSum.TypeCotype

import TauCeti.Analysis.Normed.Module.GaussianSum.CotypeComparison
import TauCeti.Probability.Distributions.Gaussian.Moments

/-!
# Cotype-2 summing bounds

Let `Y` be a seminormed space of Rademacher cotype `2` with constant `C`, and let `U : E →L[𝕜] Y`
be a bounded operator from a finite-dimensional inner product space `E` with orthonormal basis `b`
over `𝕜 = ℝ` or `ℂ` (or any `RCLike` field).

Passing to `SeparationQuotient Y` for seminormed targets and combining the Gaussian summing bound
(`ContinuousLinearMap.summingENorm_two_le_ofReal_one_add_norm_I_mul_gaussianSecondMoment`) with
Pisier's Gaussian-to-Rademacher comparison
(`TauCeti.gaussianSecondMoment_le_two_mul_rademacherSecondMoment`) yields Pisier's cotype-`2`
summing bounds (Pisier, Theorem 3.9):
`π₂(U) ≤ (1 + ‖(RCLike.I : 𝕜)‖) * (2 * C * t) * R₂(U ∘ b)` whenever
`C * √(∫_{|r| > t} r² dγ₁) ≤ 1 / 2`, specializing to `π₂(U) ≤ 2 * C * t * R₂(U ∘ b)` and
`π₂(U) ≤ 8 * C² * R₂(U ∘ b)` over `ℝ`, and to `π₂(U) ≤ 4 * C * t * R₂(U ∘ b)` and
`π₂(U) ≤ 16 * C² * R₂(U ∘ b)` over any `RCLike` field.

## Main declarations

* `ContinuousLinearMap.summingENorm_two_le_ofReal_one_add_norm_I_mul_rademacherSecondMoment`:
  unified `RCLike` threshold-form cotype-`2` summing bound retaining the factor `1 + ‖I‖`.
* `ContinuousLinearMap.summingENorm_two_le_ofReal_two_mul_rademacherSecondMoment`,
  `ContinuousLinearMap.summingENorm_two_le_ofReal_four_mul_rademacherSecondMoment`:
  threshold-form cotype-`2` summing bounds over `ℝ` and over any `RCLike` field.
* `ContinuousLinearMap.summingENorm_two_le_ofReal_eight_mul_sq_mul_rademacherSecondMoment`,
  `ContinuousLinearMap.summingENorm_two_le_ofReal_sixteen_mul_sq_mul_rademacherSecondMoment`:
  explicit-constant cotype-`2` summing bounds over `ℝ` and over any `RCLike` field.

## References

* G. Pisier, *Factorization of Linear Operators and Geometry of Banach Spaces*,
  §3, Theorem 3.9, pp. 36–37.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti
open scoped BigOperators ENNReal NNReal

namespace ContinuousLinearMap

/-- **Pisier's cotype-`2` summing bound (unified `RCLike` threshold form).** If `Y` has
Rademacher cotype `2` with constant `C` and `C * √(∫_{|r| > t} r² dγ₁) ≤ 1 / 2`, then every
bounded `𝕜`-linear operator `U : E →L[𝕜] Y` from an inner product space with a finite orthonormal
basis `b` satisfies `π₂(U) ≤ (1 + ‖(RCLike.I : 𝕜)‖) * (2 * C * t) * R₂(U ∘ b)`. -/
theorem summingENorm_two_le_ofReal_one_add_norm_I_mul_rademacherSecondMoment
    {𝕜 ι E Y : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {C : ℝ≥0} (hY : HasCotype Y 2 C) {t : ℝ}
    (ht : (C : ℝ) * √(∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1) ≤ 1 / 2)
    (b : OrthonormalBasis ι 𝕜 E) (U : E →L[𝕜] Y) :
    U.summingENorm 2 ≤
      ENNReal.ofReal ((1 + ‖(RCLike.I : 𝕜)‖) * (2 * C * t) * rademacherSecondMoment (U ∘ b)) := by
  let : NormedSpace ℝ (SeparationQuotient Y) :=
    NormedSpace.restrictScalars ℝ 𝕜 (SeparationQuotient Y)
  let Uq : E →L[𝕜] SeparationQuotient Y := (SeparationQuotient.mkCLM 𝕜 Y).comp U
  have hYq : HasGaussianCotype (SeparationQuotient Y) 2 C :=
    hY.separationQuotient.hasGaussianCotype_two
  have hrad : rademacherSecondMoment (Uq ∘ b) = rademacherSecondMoment (U ∘ b) := by
    simp [Uq, Function.comp_def]
  rw [← summingENorm_comp_separationQuotient U, ← hrad]
  refine (Uq.summingENorm_two_le_ofReal_one_add_norm_I_mul_gaussianSecondMoment hYq b).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hG := gaussianSecondMoment_le_two_mul_rademacherSecondMoment hYq ht (Uq ∘ b)
  calc
    (1 + ‖(RCLike.I : 𝕜)‖) * (C : ℝ) * gaussianSecondMoment (Uq ∘ b)
        ≤ (1 + ‖(RCLike.I : 𝕜)‖) * C * (2 * t * rademacherSecondMoment (Uq ∘ b)) := by gcongr
    _ = (1 + ‖(RCLike.I : 𝕜)‖) * (2 * C * t) * rademacherSecondMoment (Uq ∘ b) := by ring

/-- **Pisier's cotype-`2` summing bound (real case, threshold form).** If `Y` has Rademacher cotype
`2` with constant `C` and `C * √(∫_{|r| > t} r² dγ₁) ≤ 1 / 2`, then every bounded real-linear
operator `U : E →L[ℝ] Y` from an inner product space with a finite orthonormal basis `b` satisfies
`π₂(U) ≤ 2 * C * t * R₂(U ∘ b)`. -/
theorem summingENorm_two_le_ofReal_two_mul_rademacherSecondMoment
    {ι E Y : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
    {C : ℝ≥0} (hY : HasCotype Y 2 C) {t : ℝ}
    (ht : (C : ℝ) * √(∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1) ≤ 1 / 2)
    (b : OrthonormalBasis ι ℝ E) (U : E →L[ℝ] Y) :
    U.summingENorm 2 ≤ ENNReal.ofReal (2 * C * t * rademacherSecondMoment (U ∘ b)) := by
  simpa [RCLike.norm_I] using
    summingENorm_two_le_ofReal_one_add_norm_I_mul_rademacherSecondMoment hY ht b U

/-- **Pisier's cotype-`2` summing bound (`RCLike` case, threshold form).** If `Y` has Rademacher
cotype `2` with constant `C` and `C * √(∫_{|r| > t} r² dγ₁) ≤ 1 / 2`, then every bounded
`𝕜`-linear operator `U : E →L[𝕜] Y` from an inner product space with a finite orthonormal basis `b`
satisfies `π₂(U) ≤ 4 * C * t * R₂(U ∘ b)`. -/
theorem summingENorm_two_le_ofReal_four_mul_rademacherSecondMoment
    {𝕜 ι E Y : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {C : ℝ≥0} (hY : HasCotype Y 2 C) {t : ℝ}
    (ht : (C : ℝ) * √(∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1) ≤ 1 / 2)
    (b : OrthonormalBasis ι 𝕜 E) (U : E →L[𝕜] Y) :
    U.summingENorm 2 ≤ ENNReal.ofReal (4 * C * t * rademacherSecondMoment (U ∘ b)) := by
  refine (summingENorm_two_le_ofReal_one_add_norm_I_mul_rademacherSecondMoment hY ht b U).trans ?_
  rcases le_or_gt t 0 with ht0 | ht_neg
  · have h1 : (1 + ‖(RCLike.I : 𝕜)‖) * (2 * C * t) * rademacherSecondMoment (U ∘ b) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by positivity)
          (mul_nonpos_of_nonneg_of_nonpos (by positivity) ht0))
        (rademacherSecondMoment_nonneg _)
    simp [ENNReal.ofReal_of_nonpos h1]
  · apply ENNReal.ofReal_le_ofReal
    have hI : ‖(RCLike.I : 𝕜)‖ ≤ 1 := by
      rw [RCLike.norm_I]
      split_ifs <;> norm_num
    have hnonneg : 0 ≤ (C : ℝ) * t * rademacherSecondMoment (U ∘ b) :=
      mul_nonneg (mul_nonneg C.property ht_neg.le) (rademacherSecondMoment_nonneg _)
    nlinarith

/-- **Pisier's cotype-`2` summing bound (real case, explicit constant).** If `Y` has Rademacher
cotype `2` with constant `C`, then every bounded real-linear operator `U : E →L[ℝ] Y` from an
inner product space with a finite orthonormal basis `b` satisfies
`π₂(U) ≤ 8 * C² * R₂(U ∘ b)`. -/
theorem summingENorm_two_le_ofReal_eight_mul_sq_mul_rademacherSecondMoment
    {ι E Y : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
    {C : ℝ≥0} (hY : HasCotype Y 2 C)
    (b : OrthonormalBasis ι ℝ E) (U : E →L[ℝ] Y) :
    U.summingENorm 2 ≤ ENNReal.ofReal (8 * (C : ℝ) ^ 2 * rademacherSecondMoment (U ∘ b)) :=
  (summingENorm_two_le_ofReal_two_mul_rademacherSecondMoment hY
    (Probability.mul_sqrt_setIntegral_sq_tail_four_mul_le C) b U).trans_eq (by ring_nf)

/-- **Pisier's cotype-`2` summing bound (`RCLike` case, explicit constant).** If `Y` has Rademacher
cotype `2` with constant `C`, then every bounded `𝕜`-linear operator `U : E →L[𝕜] Y` from an
inner product space with a finite orthonormal basis `b` satisfies `π₂(U) ≤ 16 * C² * R₂(U ∘ b)`. -/
theorem summingENorm_two_le_ofReal_sixteen_mul_sq_mul_rademacherSecondMoment
    {𝕜 ι E Y : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {C : ℝ≥0} (hY : HasCotype Y 2 C)
    (b : OrthonormalBasis ι 𝕜 E) (U : E →L[𝕜] Y) :
    U.summingENorm 2 ≤ ENNReal.ofReal (16 * (C : ℝ) ^ 2 * rademacherSecondMoment (U ∘ b)) :=
  (summingENorm_two_le_ofReal_four_mul_rademacherSecondMoment hY
    (Probability.mul_sqrt_setIntegral_sq_tail_four_mul_le C) b U).trans_eq (by ring_nf)

end ContinuousLinearMap
