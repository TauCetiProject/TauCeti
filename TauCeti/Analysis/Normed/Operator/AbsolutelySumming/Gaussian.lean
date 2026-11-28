/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.PiL2
public import TauCeti.Analysis.Normed.Module.GaussianSum.Cotype.Basic
public import TauCeti.Analysis.Normed.Operator.AbsolutelySumming.Basic

import TauCeti.Analysis.Normed.Module.GaussianSum.Comparison
import TauCeti.Analysis.Normed.Module.GaussianSum.WeakTwo
import TauCeti.Analysis.Normed.Operator.AbsolutelySumming.Pietsch
import TauCeti.Analysis.RCLike.Basic
import TauCeti.Probability.Distributions.Gaussian.CoordinateTails

/-!
# Gaussian cotype-2 summing bounds

Let `Y` be a normed space of Gaussian cotype `2` (or Rademacher cotype `2`) with constant `C`, and
let `U : E →L[𝕜] Y` be a bounded operator from a finite-dimensional inner product space `E` with
orthonormal basis `b` over `𝕜 = ℝ` or `ℂ` (or any `RCLike` field).

Every finite family in `E` of weak `ℓ²` norm `W` is weakly square-dominated by `(W • bᵢ)ᵢ` over `ℝ`
(and by `(W • bᵢ, W • (I • bᵢ))ᵢ` over any `RCLike` field via
`ContinuousLinearMap.weakTwo_dom_of_orthonormalBasis`).
Gaussian comparison (`TauCeti.gaussianSecondMoment_le_of_weakTwo_le`) then gives the unified
`2`-summing bound `π₂(U) ≤ (1 + ‖(RCLike.I : 𝕜)‖) * C * G₂(U ∘ b)` over any `RCLike` field,
specializing to `π₂(U) ≤ C * G₂(U ∘ b)` over `ℝ` and `π₂(U) ≤ 2 * C * G₂(U ∘ b)` in general
(Pisier, Proposition 3.7).

We also record `ContinuousLinearMap.integral_norm_sq_comp_tailVec_le_of_summingENorm_le`, which
combines integrated Pietsch domination with the coordinate-tail covariance identity to bound
`𝔼[‖U (tailVec t g)‖²]` for any `2`-summing operator `U : EuclideanSpace ℝ ι →L[ℝ] Y`.

## Main declarations

* `summingENorm_two_le_ofReal_one_add_norm_I_mul_const_mul_gaussianSecondMoment`:
  `π₂(U) ≤ (1 + ‖(RCLike.I : 𝕜)‖) * C * G₂(U ∘ b)` over any `RCLike` field under Gaussian
  cotype `2`.
* `ContinuousLinearMap.summingENorm_two_le_ofReal_two_mul_const_mul_gaussianSecondMoment`:
  `π₂(U) ≤ 2 * C * G₂(U ∘ b)` over any `RCLike` field under Gaussian cotype `2`.
* `ContinuousLinearMap.summingENorm_two_le_of_hasGaussianCotype`,
  `ContinuousLinearMap.summingENorm_two_le_of_hasCotype`: `π₂(U) ≤ C * G₂(U eᵢ)` for a real
  operator out of an inner product space with a finite orthonormal basis.
* `ContinuousLinearMap.integral_norm_sq_comp_tailVec_le_of_summingENorm_le`:
  `𝔼[‖U (tailVec t g)‖²] ≤ A² ∫_{|r| > t} r² dγ₁` whenever `π₂(U) ≤ A`.

## References

* G. Pisier, *Factorization of Linear Operators and Geometry of Banach Spaces*,
  §3, Proposition 3.7, pp. 33–34.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory TauCeti
open scoped BigOperators ENNReal NNReal

namespace ContinuousLinearMap

/-- **Pisier's Gaussian summing bound (unified `RCLike` form).** If `Y` has Gaussian cotype `2`
with constant `C`, then every bounded `𝕜`-linear operator `U : E →L[𝕜] Y` from an inner product
space with a finite orthonormal basis `b` satisfies
`π₂(U) ≤ (1 + ‖(RCLike.I : 𝕜)‖) * C * G₂(U ∘ b)`. -/
theorem summingENorm_two_le_ofReal_one_add_norm_I_mul_const_mul_gaussianSecondMoment
    {𝕜 ι E Y : Type*} [RCLike 𝕜] [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [NormedSpace ℝ Y]
    {C : ℝ≥0} (hY : HasGaussianCotype Y 2 C)
    (b : OrthonormalBasis ι 𝕜 E) (U : E →L[𝕜] Y) :
    U.summingENorm 2 ≤
      ENNReal.ofReal ((1 + ‖(RCLike.I : 𝕜)‖) * C * gaussianSecondMoment (U ∘ b)) := by
  have hconst_nonneg : 0 ≤ (1 + ‖(RCLike.I : 𝕜)‖) * C * gaussianSecondMoment (U ∘ b) :=
    mul_nonneg (mul_nonneg (by positivity) C.property) (gaussianSecondMoment_nonneg _)
  rw [summingENorm_le_ofReal_iff hconst_nonneg]
  intro m x
  set W := weakLpNorm (𝕜 := 𝕜) 2 x
  have hW : 0 ≤ W := apply_nonneg _ _
  let y : ι ⊕ ι → Y :=
    Sum.elim (fun i ↦ W • (U ∘ b) i) (fun i ↦ W • ((RCLike.I : 𝕜) • (U ∘ b) i))
  have hsmulI : gaussianSecondMoment (fun i ↦ (RCLike.I : 𝕜) • (U ∘ b) i) ≤
      ‖(RCLike.I : 𝕜)‖ * gaussianSecondMoment (U ∘ b) :=
    gaussianSecondMoment_map_le (LinearMap.lsmul 𝕜 Y (RCLike.I : 𝕜))
      (fun v ↦ by simp [norm_smul]) (U ∘ b)
  have hG : gaussianSecondMoment (U ∘ x) ≤
      (1 + ‖(RCLike.I : 𝕜)‖) * gaussianSecondMoment (U ∘ b) * W := calc
    gaussianSecondMoment (U ∘ x) ≤ gaussianSecondMoment y :=
      gaussianSecondMoment_le_of_weakTwo_le (U ∘ x) y (U.weakTwo_dom_of_orthonormalBasis b x)
    _ ≤ gaussianSecondMoment (fun i ↦ W • (U ∘ b) i) +
          gaussianSecondMoment (fun i ↦ W • ((RCLike.I : 𝕜) • (U ∘ b) i)) :=
      gaussianSecondMoment_sumElim_le _ _
    _ = W * gaussianSecondMoment (U ∘ b) +
          W * gaussianSecondMoment (fun i ↦ (RCLike.I : 𝕜) • (U ∘ b) i) := by
      rw [gaussianSecondMoment_smul, gaussianSecondMoment_smul, abs_of_nonneg hW]
    _ ≤ W * gaussianSecondMoment (U ∘ b) +
          W * (‖(RCLike.I : 𝕜)‖ * gaussianSecondMoment (U ∘ b)) := by gcongr
    _ = (1 + ‖(RCLike.I : 𝕜)‖) * gaussianSecondMoment (U ∘ b) * W := by ring
  calc
    ‖WithLp.toLp 2 (fun j ↦ U (x j))‖ ≤ C * gaussianSecondMoment (U ∘ x) := hY.norm_toLp_le (U ∘ x)
    _ ≤ C * ((1 + ‖(RCLike.I : 𝕜)‖) * gaussianSecondMoment (U ∘ b) * W) := by gcongr
    _ = (1 + ‖(RCLike.I : 𝕜)‖) * C * gaussianSecondMoment (U ∘ b) * W := by ring

/-- **Pisier's Gaussian summing bound (`RCLike` case).** If `Y` has Gaussian cotype `2` with
constant `C`, then every bounded `𝕜`-linear operator `U : E →L[𝕜] Y` from an inner product space
with a finite orthonormal basis `b` satisfies `π₂(U) ≤ 2 * C * G₂(U ∘ b)`. -/
theorem summingENorm_two_le_ofReal_two_mul_const_mul_gaussianSecondMoment
    {𝕜 ι E Y : Type*} [RCLike 𝕜] [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [NormedSpace ℝ Y]
    {C : ℝ≥0} (hY : HasGaussianCotype Y 2 C)
    (b : OrthonormalBasis ι 𝕜 E) (U : E →L[𝕜] Y) :
    U.summingENorm 2 ≤ ENNReal.ofReal (2 * C * gaussianSecondMoment (U ∘ b)) := by
  refine
    (summingENorm_two_le_ofReal_one_add_norm_I_mul_const_mul_gaussianSecondMoment hY b U).trans ?_
  apply ENNReal.ofReal_le_ofReal
  have hI : ‖(RCLike.I : 𝕜)‖ ≤ 1 := RCLike.norm_I_le_one
  have hG : 0 ≤ (C : ℝ) * gaussianSecondMoment (U ∘ b) :=
    mul_nonneg C.property (gaussianSecondMoment_nonneg _)
  nlinarith

/-- **The `2`-summing norm under Gaussian cotype.** If `Y` has Gaussian cotype `2` with constant
`C`, then every operator `U` from a real inner product space with orthonormal basis `(eᵢ)` into
`Y` satisfies `π₂(U) ≤ C G₂(U eᵢ)`. -/
theorem summingENorm_two_le_of_hasGaussianCotype
    {ι E Y : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {C : ℝ≥0}
    (U : E →L[ℝ] Y) (b : OrthonormalBasis ι ℝ E) (h : HasGaussianCotype Y 2 C) :
    U.summingENorm 2 ≤ ENNReal.ofReal (C * gaussianSecondMoment fun i ↦ U (b i)) := by
  simpa [RCLike.norm_I, Function.comp_def] using
    summingENorm_two_le_ofReal_one_add_norm_I_mul_const_mul_gaussianSecondMoment h b U

/-- **The `2`-summing norm under cotype `2`.** If `Y` has Rademacher cotype `2` with constant
`C`, then every operator `U` from a real inner product space with orthonormal basis `(eᵢ)` into
`Y` satisfies `π₂(U) ≤ C G₂(U eᵢ)`. -/
theorem summingENorm_two_le_of_hasCotype
    {ι E Y : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {C : ℝ≥0}
    (U : E →L[ℝ] Y) (b : OrthonormalBasis ι ℝ E) (h : HasCotype Y 2 C) :
    U.summingENorm 2 ≤ ENNReal.ofReal (C * gaussianSecondMoment fun i ↦ U (b i)) :=
  U.summingENorm_two_le_of_hasGaussianCotype b h.hasGaussianCotype_two

/-- Integrated Pietsch domination bounds the expected squared norm of
`U (EuclideanSpace.tailVec t g)` for any operator `U : EuclideanSpace ℝ ι →L[ℝ] Y` satisfying
`π₂(U) ≤ A`. -/
theorem integral_norm_sq_comp_tailVec_le_of_summingENorm_le {ι Y : Type*} [Fintype ι]
    [SeminormedAddCommGroup Y] [NormedSpace ℝ Y] (U : EuclideanSpace ℝ ι →L[ℝ] Y)
    {A : ℝ} (hA : 0 ≤ A) (hU : U.summingENorm 2 ≤ ENNReal.ofReal A) (t : ℝ) :
    ∫ g, ‖U (EuclideanSpace.tailVec t g)‖ ^ 2 ∂stdGaussian (EuclideanSpace ℝ ι) ≤
      A ^ 2 * ∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1 := by
  have hmem := TauCeti.Probability.memLp_tailVec (ι := ι) t (p := 2) (by simp)
  have hs : MeasurableSet {r : ℝ | t < |r|} :=
    measurableSet_lt measurable_const continuous_abs.measurable
  have hpietsch := U.integral_norm_apply_rpow_le_of_summingENorm_le (p := 2)
    (by simp) hA hU hmem (M := ∫ r in {r : ℝ | t < |r|}, r ^ 2 ∂gaussianReal 0 1) fun f hf ↦ by
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs,
        ContinuousLinearMap.integral_sq_apply_tailVec]
      exact mul_le_of_le_one_left (setIntegral_nonneg hs fun _ _ ↦ sq_nonneg _)
        (by nlinarith [norm_nonneg f])
  simpa only [ENNReal.toReal_ofNat, Real.rpow_two] using hpietsch

end ContinuousLinearMap
