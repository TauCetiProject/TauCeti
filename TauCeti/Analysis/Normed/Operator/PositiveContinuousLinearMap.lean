/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Topology.Algebra.InfiniteSum.Module

/-!
# Operator-norm series of positive continuous linear maps

For an indexed family `f : ι → (E₁ →P[𝕜] E₂)` of positive continuous linear maps between
seminormed ordered vector spaces whose codomain has a closed order compatible with addition,
the operator-norm infinite sum `∑' i, (f i : E₁ →L[𝕜] E₂)` is again monotone and therefore defines
a positive continuous linear map `PositiveContinuousLinearMap.tsum f : E₁ →P[𝕜] E₂`.

When the series converges in operator norm, it evaluates pointwise
(`PositiveContinuousLinearMap.hasSum_tsum_apply`, `PositiveContinuousLinearMap.tsum_apply`),
dominates every summand on nonnegative elements (`PositiveContinuousLinearMap.le_tsum_apply`), and
vanishes at a nonnegative element if and only if every summand vanishes there
(`PositiveContinuousLinearMap.tsum_apply_eq_zero_iff`).

## Main declarations

* `PositiveContinuousLinearMap.tsum`: the operator-norm `tsum` of an indexed family of positive
  continuous linear maps.
* `PositiveContinuousLinearMap.toContinuousLinearMap_tsum`: coercion to `E₁ →L[𝕜] E₂`.
* `PositiveContinuousLinearMap.hasSum_tsum_apply`, `PositiveContinuousLinearMap.tsum_apply`:
  pointwise evaluation of a summable positive series.
* `PositiveContinuousLinearMap.le_tsum_apply`,
  `PositiveContinuousLinearMap.tsum_apply_eq_zero_iff`: termwise domination and kernel
  characterization on the positive cone.
-/

public section

noncomputable section

open Filter Topology

namespace PositiveContinuousLinearMap

variable {ι 𝕜 E₁ E₂ : Type*} [NontriviallyNormedField 𝕜]
  [SeminormedAddCommGroup E₁] [NormedSpace 𝕜 E₁] [PartialOrder E₁]
  [SeminormedAddCommGroup E₂] [NormedSpace 𝕜 E₂] [PartialOrder E₂]

private theorem hasSum_apply_of_summable {f : ι → E₁ →P[𝕜] E₂}
    (hf : Summable fun i => (f i : E₁ →L[𝕜] E₂)) (a : E₁) :
    HasSum (fun i => f i a) ((∑' i, (f i : E₁ →L[𝕜] E₂)) a) := by
  simpa only [ContinuousLinearMap.apply_apply, coe_toContinuousLinearMap] using
    (ContinuousLinearMap.apply 𝕜 E₂ a).hasSum hf.hasSum

variable [IsOrderedAddMonoid E₂] [OrderClosedTopology E₂]

private theorem tsum_monotone (f : ι → E₁ →P[𝕜] E₂) :
    Monotone ⇑(∑' i, (f i : E₁ →L[𝕜] E₂)) := by
  intro x y hxy
  by_cases hf : Summable fun i => (f i : E₁ →L[𝕜] E₂)
  · refine le_of_tendsto_of_tendsto (hasSum_apply_of_summable hf x)
      (hasSum_apply_of_summable hf y) ?_
    exact Eventually.of_forall fun s => Finset.sum_le_sum fun i _ => (f i).mono hxy
  · rw [tsum_eq_zero_of_not_summable hf, _root_.zero_apply, _root_.zero_apply]

/-- The sum of an indexed family of positive continuous linear maps, formed as the operator-norm
`tsum` in `E₁ →L[𝕜] E₂` (or `0` if the family is not summable). -/
def tsum (f : ι → E₁ →P[𝕜] E₂) : E₁ →P[𝕜] E₂ :=
  { __ := ∑' i, (f i : E₁ →L[𝕜] E₂), monotone' := tsum_monotone f }

/-- The underlying continuous linear map of `tsum f` is the operator-norm `tsum`. -/
@[simp]
theorem toContinuousLinearMap_tsum (f : ι → E₁ →P[𝕜] E₂) :
    (tsum f : E₁ →L[𝕜] E₂) = ∑' i, (f i : E₁ →L[𝕜] E₂) :=
  (rfl)

/-- A summable family of positive continuous linear maps evaluates pointwise by summing its
values. -/
theorem hasSum_tsum_apply {f : ι → E₁ →P[𝕜] E₂} (hf : Summable fun i => (f i : E₁ →L[𝕜] E₂))
    (a : E₁) :
    HasSum (fun i => f i a) (tsum f a) :=
  hasSum_apply_of_summable hf a

/-- A summable family of positive continuous linear maps evaluates pointwise as the `tsum` of its
values. -/
theorem tsum_apply {f : ι → E₁ →P[𝕜] E₂} (hf : Summable fun i => (f i : E₁ →L[𝕜] E₂)) (a : E₁) :
    tsum f a = ∑' i, f i a :=
  (hasSum_tsum_apply hf a).tsum_eq.symm

/-- On a nonnegative element, every summand of a summable positive series is bounded above by the
sum. -/
theorem le_tsum_apply {f : ι → E₁ →P[𝕜] E₂} (hf : Summable fun i => (f i : E₁ →L[𝕜] E₂))
    {a : E₁} (ha : 0 ≤ a) (i : ι) :
    f i a ≤ tsum f a := by
  refine ge_of_tendsto (hasSum_tsum_apply hf a) ?_
  filter_upwards [eventually_ge_atTop {i}] with s hs
  exact Finset.single_le_sum (fun j _ => (f j).map_nonneg ha) (hs (Finset.mem_singleton_self i))

/-- A summable series of positive continuous linear maps vanishes on a nonnegative element if and
only if every summand vanishes on it. -/
theorem tsum_apply_eq_zero_iff {f : ι → E₁ →P[𝕜] E₂} (hf : Summable fun i => (f i : E₁ →L[𝕜] E₂))
    {a : E₁} (ha : 0 ≤ a) :
    tsum f a = 0 ↔ ∀ i, f i a = 0 := by
  refine ⟨fun h i => le_antisymm (h ▸ le_tsum_apply hf ha i) ((f i).map_nonneg ha), fun h => ?_⟩
  rw [tsum_apply hf]
  simp [h]

end PositiveContinuousLinearMap
