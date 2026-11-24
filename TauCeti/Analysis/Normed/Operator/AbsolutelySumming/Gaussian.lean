/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Module.GaussianSum.Cotype.Basic
public import TauCeti.Analysis.Normed.Operator.AbsolutelySumming.Basic

import TauCeti.Analysis.Normed.Module.GaussianSum.Comparison
import TauCeti.Analysis.Normed.Module.GaussianSum.WeakTwo
import TauCeti.Analysis.RCLike.Basic

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

## Main declarations

* `ContinuousLinearMap.summingENorm_two_le_ofReal_one_add_norm_I_mul_gaussianSecondMoment`:
  `π₂(U) ≤ (1 + ‖(RCLike.I : 𝕜)‖) * C * G₂(U ∘ b)` over any `RCLike` field under Gaussian
  cotype `2`.
* `ContinuousLinearMap.summingENorm_two_le_ofReal_two_mul_gaussianSecondMoment`:
  `π₂(U) ≤ 2 * C * G₂(U ∘ b)` over any `RCLike` field under Gaussian cotype `2`.
* `ContinuousLinearMap.summingENorm_two_le_of_hasGaussianCotype`,
  `ContinuousLinearMap.summingENorm_two_le_of_hasCotype`: `π₂(U) ≤ C * G₂(U ∘ b)` for a real
  operator out of an inner product space with a finite orthonormal basis.

## References

* G. Pisier, *Factorization of Linear Operators and Geometry of Banach Spaces*,
  §3, Proposition 3.7, pp. 33–34.
-/

public section

noncomputable section

open TauCeti
open scoped BigOperators ENNReal NNReal

namespace ContinuousLinearMap

/-- **Pisier's Gaussian summing bound (unified `RCLike` form).** If `Y` has Gaussian cotype `2`
with constant `C`, then every bounded `𝕜`-linear operator `U : E →L[𝕜] Y` from an inner product
space with a finite orthonormal basis `b` satisfies
`π₂(U) ≤ (1 + ‖(RCLike.I : 𝕜)‖) * C * G₂(U ∘ b)`. -/
theorem summingENorm_two_le_ofReal_one_add_norm_I_mul_gaussianSecondMoment
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
theorem summingENorm_two_le_ofReal_two_mul_gaussianSecondMoment
    {𝕜 ι E Y : Type*} [RCLike 𝕜] [Fintype ι]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
    [NormedAddCommGroup Y] [NormedSpace 𝕜 Y] [NormedSpace ℝ Y]
    {C : ℝ≥0} (hY : HasGaussianCotype Y 2 C)
    (b : OrthonormalBasis ι 𝕜 E) (U : E →L[𝕜] Y) :
    U.summingENorm 2 ≤ ENNReal.ofReal (2 * C * gaussianSecondMoment (U ∘ b)) := by
  refine (summingENorm_two_le_ofReal_one_add_norm_I_mul_gaussianSecondMoment hY b U).trans ?_
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
    summingENorm_two_le_ofReal_one_add_norm_I_mul_gaussianSecondMoment h b U

/-- **The `2`-summing norm under cotype `2`.** If `Y` has Rademacher cotype `2` with constant
`C`, then every operator `U` from a real inner product space with orthonormal basis `(eᵢ)` into
`Y` satisfies `π₂(U) ≤ C G₂(U eᵢ)`. -/
theorem summingENorm_two_le_of_hasCotype
    {ι E Y : Type*} [Fintype ι] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] {C : ℝ≥0}
    (U : E →L[ℝ] Y) (b : OrthonormalBasis ι ℝ E) (h : HasCotype Y 2 C) :
    U.summingENorm 2 ≤ ENNReal.ofReal (C * gaussianSecondMoment fun i ↦ U (b i)) :=
  U.summingENorm_two_le_of_hasGaussianCotype b h.hasGaussianCotype_two

end ContinuousLinearMap
