/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Positive
import Mathlib.Topology.Algebra.InfiniteSum.ContinuousEval
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
(`PositiveContinuousLinearMap.tsum_apply_eq_zero_iff`). The bundled sum satisfies `tsum_zero`,
`tsum_const_zero`, `tsum_eq_zero_of_not_summable`, `tsum_eq_sum`, and `tsum_add`.

## Main declarations

* `PositiveContinuousLinearMap.tsum`: the operator-norm `tsum` of an indexed family of positive
  continuous linear maps.
* `PositiveContinuousLinearMap.toContinuousLinearMap_tsum`: coercion to `E₁ →L[𝕜] E₂`.
* `PositiveContinuousLinearMap.tsum_zero`, `PositiveContinuousLinearMap.tsum_const_zero`,
  `PositiveContinuousLinearMap.tsum_eq_zero_of_not_summable`,
  `PositiveContinuousLinearMap.tsum_eq_sum`,
  `PositiveContinuousLinearMap.tsum_add`: algebraic, finite-support, and nonsummable
  simplification laws.
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
  [IsOrderedAddMonoid E₂] [OrderClosedTopology E₂]

private theorem tsum_monotone (f : ι → E₁ →P[𝕜] E₂) :
    Monotone ⇑(∑' i, (f i : E₁ →L[𝕜] E₂)) := by
  intro x y hxy
  by_cases hf : Summable fun i => (f i : E₁ →L[𝕜] E₂)
  · exact hasSum_le (fun i => (f i).mono hxy) (hasSum_apply hf.hasSum x) (hasSum_apply hf.hasSum y)
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

/-- The `tsum` of the zero family is `0`. -/
@[simp]
theorem tsum_zero : tsum (0 : ι → E₁ →P[𝕜] E₂) = 0 :=
  toContinuousLinearMap_injective <| by
    rw [toContinuousLinearMap_tsum]
    exact _root_.tsum_zero

/-- The `tsum` of a pointwise-zero family is `0`. -/
@[simp]
theorem tsum_const_zero : tsum (fun _ : ι => (0 : E₁ →P[𝕜] E₂)) = 0 :=
  tsum_zero

/-- A nonsummable family has `tsum` equal to `0`. -/
@[simp]
theorem tsum_eq_zero_of_not_summable {f : ι → E₁ →P[𝕜] E₂}
    (hf : ¬ Summable fun i => (f i : E₁ →L[𝕜] E₂)) : tsum f = 0 :=
  toContinuousLinearMap_injective <| by
    simpa [toContinuousLinearMap_tsum] using _root_.tsum_eq_zero_of_not_summable hf

/-- The `tsum` of a family vanishing outside a `Finset` equals the finite sum over that
`Finset`. -/
theorem tsum_eq_sum {f : ι → E₁ →P[𝕜] E₂} {s : Finset ι} (hf : ∀ i ∉ s, f i = 0) :
    tsum f = ∑ i ∈ s, f i := by
  refine toContinuousLinearMap_injective ?_
  rw [toContinuousLinearMap_tsum, _root_.tsum_eq_sum fun i hi => by simp [hf i hi]]
  exact (map_sum (AddMonoidHom.mk' (fun g : E₁ →P[𝕜] E₂ => (g : E₁ →L[𝕜] E₂))
    PositiveContinuousLinearMap.toContinuousLinearMap_add) f s).symm

/-- The `tsum` of the sum of two summable families is the sum of their `tsum`s. -/
theorem tsum_add {f g : ι → E₁ →P[𝕜] E₂}
    (hf : Summable fun i => (f i : E₁ →L[𝕜] E₂))
    (hg : Summable fun i => (g i : E₁ →L[𝕜] E₂)) :
    tsum (fun i => f i + g i) = tsum f + tsum g :=
  toContinuousLinearMap_injective <| by
    simpa [toContinuousLinearMap_tsum] using hf.tsum_add hg

/-- A summable family of positive continuous linear maps evaluates pointwise by summing its
values. -/
theorem hasSum_tsum_apply {f : ι → E₁ →P[𝕜] E₂} (hf : Summable fun i => (f i : E₁ →L[𝕜] E₂))
    (a : E₁) :
    HasSum (fun i => f i a) (tsum f a) :=
  hasSum_apply hf.hasSum a

/-- A summable family of positive continuous linear maps evaluates pointwise as the `tsum` of its
values. -/
theorem tsum_apply {f : ι → E₁ →P[𝕜] E₂} (hf : Summable fun i => (f i : E₁ →L[𝕜] E₂)) (a : E₁) :
    tsum f a = ∑' i, f i a :=
  (hasSum_tsum_apply hf a).tsum_eq.symm

/-- On a nonnegative element, every summand of a summable positive series is bounded above by the
sum. -/
theorem le_tsum_apply {f : ι → E₁ →P[𝕜] E₂} (hf : Summable fun i => (f i : E₁ →L[𝕜] E₂))
    {a : E₁} (ha : 0 ≤ a) (i : ι) :
    f i a ≤ tsum f a :=
  le_hasSum (hasSum_tsum_apply hf a) i fun j _ => (f j).map_nonneg ha

/-- A summable series of positive continuous linear maps vanishes on a nonnegative element if and
only if every summand vanishes on it. -/
theorem tsum_apply_eq_zero_iff {f : ι → E₁ →P[𝕜] E₂} (hf : Summable fun i => (f i : E₁ →L[𝕜] E₂))
    {a : E₁} (ha : 0 ≤ a) :
    tsum f a = 0 ↔ ∀ i, f i a = 0 := by
  refine ⟨fun h i => le_antisymm (h ▸ le_tsum_apply hf ha i) ((f i).map_nonneg ha), fun h => ?_⟩
  rw [tsum_apply hf]
  simp [h]

end PositiveContinuousLinearMap
