/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Operator.AbsolutelySumming.Gaussian
public import TauCeti.Analysis.Normed.Module.RademacherSum.TypeCotype

import TauCeti.Analysis.Normed.Module.GaussianSum.Cotype.Comparison
import TauCeti.Analysis.Normed.Module.GaussianSum.Rademacher
import TauCeti.Analysis.RCLike.Basic

/-!
# Cotype-2 summing bounds

Let `Y` be a seminormed space of Rademacher cotype `2` with constant `C`, and let `U : E →L[𝕜] Y`
be a bounded operator from a finite-dimensional inner product space `E` with orthonormal basis `b`
over `𝕜 = ℝ` or `ℂ` (or any `RCLike` field).

Passing to `SeparationQuotient Y` for seminormed targets and combining the Gaussian summing bound
(`ContinuousLinearMap.summingENorm_two_le_ofReal_one_add_norm_I_mul_const_mul_gaussianSecondMoment`)
with Pisier's Gaussian-to-Rademacher comparison
(`TauCeti.gaussianSecondMoment_le_mul_rademacherSecondMoment_of_tail_bound`) yields Pisier's
cotype-`2` summing bounds (Pisier, Theorem 3.9):
`π₂(U) ≤ (1 + ‖(RCLike.I : 𝕜)‖) * (2 * C * t) * R₂(U ∘ b)` whenever
`C * √(∫_{|r| > t} r² dγ₁) ≤ 1 / 2`, specializing to `π₂(U) ≤ 2 * C * t * R₂(U ∘ b)` over `ℝ` and
to `π₂(U) ≤ 4 * C * t * R₂(U ∘ b)` and `π₂(U) ≤ 16 * C² * R₂(U ∘ b)` over any `RCLike` field,
while `t = 2 √3 C` gives the sharper real bound `π₂(U) ≤ 4 √3 C² R₂(U eᵢ)` for seminormed `Y`.

## Main declarations

* `summingENorm_two_le_one_add_norm_I_mul_const_mul_rademacherSecondMoment_of_tail_bound`:
  unified `RCLike` threshold-form cotype-`2` summing bound retaining the factor `1 + ‖I‖`.
* `ContinuousLinearMap.summingENorm_two_le_two_mul_const_mul_rademacherSecondMoment_of_tail_bound`,
  `ContinuousLinearMap.summingENorm_two_le_four_mul_const_mul_rademacherSecondMoment_of_tail_bound`:
  threshold-form cotype-`2` summing bounds over `ℝ` and over any `RCLike` field.
* `ContinuousLinearMap.summingENorm_two_le_ofReal_sixteen_mul_sq_mul_rademacherSecondMoment`:
  explicit-constant cotype-`2` summing bound `π₂(U) ≤ 16 * C² * R₂(U ∘ b)` over any `RCLike`
  field.
* `ContinuousLinearMap.summingENorm_two_le_mul_rademacherSecondMoment_of_hasGaussianCotype`,
  `ContinuousLinearMap.summingENorm_two_le_mul_rademacherSecondMoment_of_hasCotype`:
  `π₂(U) ≤ 4 √3 C² R₂(U eᵢ)` over `ℝ`.

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
theorem summingENorm_two_le_one_add_norm_I_mul_const_mul_rademacherSecondMoment_of_tail_bound
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
  refine (summingENorm_two_le_ofReal_one_add_norm_I_mul_const_mul_gaussianSecondMoment
    hYq b Uq).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hG := gaussianSecondMoment_le_mul_rademacherSecondMoment_of_tail_bound hYq ht (Uq ∘ b)
  calc
    (1 + ‖(RCLike.I : 𝕜)‖) * (C : ℝ) * gaussianSecondMoment (Uq ∘ b)
        ≤ (1 + ‖(RCLike.I : 𝕜)‖) * C * (2 * t * rademacherSecondMoment (Uq ∘ b)) := by gcongr
    _ = (1 + ‖(RCLike.I : 𝕜)‖) * (2 * C * t) * rademacherSecondMoment (Uq ∘ b) := by ring

/-- **Pisier's cotype-`2` summing bound (real case, threshold form).** If `Y` has Rademacher cotype
`2` with constant `C` and `C * √(∫_{|r| > t} r² dγ₁) ≤ 1 / 2`, then every bounded real-linear
operator `U : E →L[ℝ] Y` from an inner product space with a finite orthonormal basis `b` satisfies
`π₂(U) ≤ 2 * C * t * R₂(U ∘ b)`. -/
theorem summingENorm_two_le_two_mul_const_mul_rademacherSecondMoment_of_tail_bound
    {ι E Y : Type*} [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
    {C : ℝ≥0} (hY : HasCotype Y 2 C) {t : ℝ}
    (ht : (C : ℝ) * √(∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1) ≤ 1 / 2)
    (b : OrthonormalBasis ι ℝ E) (U : E →L[ℝ] Y) :
    U.summingENorm 2 ≤ ENNReal.ofReal (2 * C * t * rademacherSecondMoment (U ∘ b)) := by
  simpa [RCLike.norm_I] using
    summingENorm_two_le_one_add_norm_I_mul_const_mul_rademacherSecondMoment_of_tail_bound
      hY ht b U

/-- **Pisier's cotype-`2` summing bound (`RCLike` case, threshold form).** If `Y` has Rademacher
cotype `2` with constant `C` and `C * √(∫_{|r| > t} r² dγ₁) ≤ 1 / 2`, then every bounded
`𝕜`-linear operator `U : E →L[𝕜] Y` from an inner product space with a finite orthonormal basis `b`
satisfies `π₂(U) ≤ 4 * C * t * R₂(U ∘ b)`. -/
theorem summingENorm_two_le_four_mul_const_mul_rademacherSecondMoment_of_tail_bound
    {𝕜 ι E Y : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {C : ℝ≥0} (hY : HasCotype Y 2 C) {t : ℝ}
    (ht : (C : ℝ) * √(∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1) ≤ 1 / 2)
    (b : OrthonormalBasis ι 𝕜 E) (U : E →L[𝕜] Y) :
    U.summingENorm 2 ≤ ENNReal.ofReal (4 * C * t * rademacherSecondMoment (U ∘ b)) := by
  refine
    (summingENorm_two_le_one_add_norm_I_mul_const_mul_rademacherSecondMoment_of_tail_bound
      hY ht b U).trans ?_
  rcases le_or_gt t 0 with ht0 | ht_neg
  · have h1 : (1 + ‖(RCLike.I : 𝕜)‖) * (2 * C * t) * rademacherSecondMoment (U ∘ b) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg
        (mul_nonpos_of_nonneg_of_nonpos (by positivity)
          (mul_nonpos_of_nonneg_of_nonpos (by positivity) ht0))
        (rademacherSecondMoment_nonneg _)
    simp [ENNReal.ofReal_of_nonpos h1]
  · apply ENNReal.ofReal_le_ofReal
    have hI : ‖(RCLike.I : 𝕜)‖ ≤ 1 := RCLike.norm_I_le_one
    have hnonneg : 0 ≤ (C : ℝ) * t * rademacherSecondMoment (U ∘ b) :=
      mul_nonneg (mul_nonneg C.property ht_neg.le) (rademacherSecondMoment_nonneg _)
    nlinarith

/-- **Pisier's cotype-`2` summing bound (`RCLike` case, explicit constant).** If `Y` has Rademacher
cotype `2` with constant `C`, then every bounded `𝕜`-linear operator `U : E →L[𝕜] Y` from an
inner product space with a finite orthonormal basis `b` satisfies `π₂(U) ≤ 16 * C² * R₂(U ∘ b)`. -/
theorem summingENorm_two_le_ofReal_sixteen_mul_sq_mul_rademacherSecondMoment
    {𝕜 ι E Y : Type*} [RCLike 𝕜] [Fintype ι] [DecidableEq ι]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [SeminormedAddCommGroup Y] [NormedSpace 𝕜 Y]
    {C : ℝ≥0} (hY : HasCotype Y 2 C)
    (b : OrthonormalBasis ι 𝕜 E) (U : E →L[𝕜] Y) :
    U.summingENorm 2 ≤ ENNReal.ofReal (16 * (C : ℝ) ^ 2 * rademacherSecondMoment (U ∘ b)) := by
  rcases eq_or_ne C 0 with rfl | hC
  · simpa using
      summingENorm_two_le_four_mul_const_mul_rademacherSecondMoment_of_tail_bound
        hY (t := 0) (by simp) b U
  have : 0 < (C : ℝ) := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hC)
  have ht : (C : ℝ) * √(∫ r in {r : ℝ | 4 * (C : ℝ) < |r|}, r ^ 2 ∂gaussianReal 0 1) ≤ 1 / 2 :=
    mul_sqrt_setIntegral_sq_tail_gaussianReal_le (by positivity) (by
      rw [show (C : ℝ) * √3 / (4 * C) = √3 / 4 by field_simp]
      have h3 : √3 ≤ 2 := Real.sqrt_le_iff.2 ⟨by norm_num, by norm_num⟩
      linarith)
  exact (summingENorm_two_le_four_mul_const_mul_rademacherSecondMoment_of_tail_bound
    hY ht b U).trans_eq (by ring_nf)

section RademacherSecondMoment

variable {ι E : Type*} [Fintype ι] [DecidableEq ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  {C : ℝ≥0}

/-- **The `2`-summing norm under Gaussian cotype `2`, by Rademacher averages.** If `Y` has
Gaussian cotype `2` with constant `C`, every operator `U` from a real inner product space with
orthonormal basis `(eᵢ)` into `Y` satisfies `π₂(U) ≤ 4 √3 C² R₂(U eᵢ)`. -/
theorem summingENorm_two_le_mul_rademacherSecondMoment_of_hasGaussianCotype
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : E →L[ℝ] Y) (b : OrthonormalBasis ι ℝ E) (h : HasGaussianCotype Y 2 C) :
    U.summingENorm 2 ≤
      ENNReal.ofReal (4 * √3 * C ^ 2 * rademacherSecondMoment fun i ↦ U (b i)) := by
  refine (U.summingENorm_two_le_of_hasGaussianCotype b h).trans (ENNReal.ofReal_le_ofReal ?_)
  calc (C : ℝ) * gaussianSecondMoment (fun i ↦ U (b i))
      ≤ C * (4 * √3 * C * rademacherSecondMoment fun i ↦ U (b i)) :=
        mul_le_mul_of_nonneg_left (h.gaussianSecondMoment_le _) C.coe_nonneg
    _ = _ := by ring

/-- **The cotype-`2` summing bound.** If `Y` has Rademacher cotype `2` with constant `C`, every
operator `U` from a real inner product space with orthonormal basis `(eᵢ)` into a seminormed
space `Y` satisfies `π₂(U) ≤ 4 √3 C² R₂(U eᵢ)`, with a constant independent of the dimension. -/
theorem summingENorm_two_le_mul_rademacherSecondMoment_of_hasCotype
    {Y : Type*} [SeminormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U : E →L[ℝ] Y) (b : OrthonormalBasis ι ℝ E) (h : HasCotype Y 2 C) :
    U.summingENorm 2 ≤
      ENNReal.ofReal (4 * √3 * C ^ 2 * rademacherSecondMoment fun i ↦ U (b i)) := by
  let Uq : E →L[ℝ] SeparationQuotient Y := (SeparationQuotient.mkCLM ℝ Y).comp U
  have hrad : rademacherSecondMoment (fun i ↦ Uq (b i)) =
      rademacherSecondMoment (fun i ↦ U (b i)) := by
    simp [Uq]
  rw [← summingENorm_comp_separationQuotient U, ← hrad]
  exact Uq.summingENorm_two_le_mul_rademacherSecondMoment_of_hasGaussianCotype b
    h.separationQuotient.hasGaussianCotype_two

end RademacherSecondMoment

end ContinuousLinearMap
