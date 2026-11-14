/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Finite sums of `MemLp.toLp` classes and `compLp` functoriality

Mathlib provides `MeasureTheory.MemLp.toLp_zero`, `MeasureTheory.MemLp.toLp_add`, and
`MeasureTheory.Lp.coeFn_finsetSum`, as well as `MeasureTheory.memLp_finsetSum` and
`MeasureTheory.memLp_finsetSum'`. This file records the companion identities identifying the `Lp`
class of a finite sum of `Lᵖ` functions with the sum of their `Lp` classes, together with the
composition and identity laws for `ContinuousLinearMap.compLp` and `ContinuousLinearMap.compLpL`.

## Main declarations

* `MeasureTheory.MemLp.toLp_finsetSum'`: `hsum.toLp (∑ i ∈ s, f i) = ∑ i ∈ s, (hf i).toLp (f i)`.
* `MeasureTheory.MemLp.toLp_finsetSum`:
  `hsum.toLp (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, (hf i).toLp (f i)`.
* `ContinuousLinearMap.comp_compLp`, `ContinuousLinearMap.comp_compLpL`,
  `ContinuousLinearMap.compLpL_compLpL`: composition laws for `compLp` and `compLpL`.
* `ContinuousLinearMap.id_compLp`, `ContinuousLinearMap.id_compLpL`: identity laws for `compLp` and
  `compLpL`.
-/

public section

open scoped ENNReal

namespace MeasureTheory.MemLp

variable {α E ι : Type*} {_ : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup E]
  {p : ℝ≥0∞} {s : Finset ι} {f : ι → α → E}

/-- The `Lp` class of a finite sum of `Lᵖ` functions is the sum of their `Lp` classes. -/
theorem toLp_finsetSum' (hsum : MemLp (∑ i ∈ s, f i) p μ) (hf : ∀ i, MemLp (f i) p μ) :
    hsum.toLp (∑ i ∈ s, f i) = ∑ i ∈ s, (hf i).toLp (f i) :=
  Lp.ext_iff.2 <| hsum.coeFn_toLp.trans <|
    (eventuallyEq_sum fun i _ ↦ (hf i).coeFn_toLp.symm).trans
      (Lp.coeFn_finsetSum s fun i ↦ (hf i).toLp (f i)).symm

/-- The `Lp` class of a pointwise finite sum `fun x ↦ ∑ i ∈ s, f i x` of `Lᵖ` functions is the
sum of their `Lp` classes. -/
theorem toLp_finsetSum (hsum : MemLp (fun x ↦ ∑ i ∈ s, f i x) p μ) (hf : ∀ i, MemLp (f i) p μ) :
    hsum.toLp (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, (hf i).toLp (f i) := by
  convert (memLp_finsetSum' s fun i _ ↦ hf i).toLp_finsetSum' hf using 1
  exact toLp_congr _ _ (.of_forall fun x ↦ (Finset.sum_apply x s f).symm)

end MeasureTheory.MemLp

namespace ContinuousLinearMap

open MeasureTheory

variable {α E F G 𝕜 : Type*} {_ : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 E] [NormedSpace 𝕜 F] [NormedSpace 𝕜 G]

/-- Composing `Lp` pushforwards of continuous linear maps agrees with the pushforward of their
composition. -/
theorem comp_compLp (L : F →L[𝕜] G) (M : E →L[𝕜] F) (f : Lp E p μ) :
    L.compLp (M.compLp f) = (L.comp M).compLp f := by
  ext1
  filter_upwards [L.coeFn_compLp (M.compLp f), M.coeFn_compLp f, (L.comp M).coeFn_compLp f] with
    x hx1 hx2 hx3
  rw [hx1, hx2, hx3, comp_apply]

/-- Composing `compLpL` operators agrees with `compLpL` of the composed operator. -/
theorem comp_compLpL [Fact (1 ≤ p)] (L : F →L[𝕜] G) (M : E →L[𝕜] F) :
    (L.compLpL p μ).comp (M.compLpL p μ) = (L.comp M).compLpL p μ := by
  ext1 f
  exact L.comp_compLp M f

/-- Applying `compLpL` in succession agrees with `compLpL` of the composed operator. -/
theorem compLpL_compLpL [Fact (1 ≤ p)] (L : F →L[𝕜] G) (M : E →L[𝕜] F) (f : Lp E p μ) :
    L.compLpL p μ (M.compLpL p μ f) = (L.comp M).compLpL p μ f :=
  L.comp_compLp M f

/-- Pushing an `Lp` function forward along the identity map returns it unchanged. -/
@[simp]
theorem id_compLp (f : Lp E p μ) : (ContinuousLinearMap.id 𝕜 E).compLp f = f := by
  ext1
  exact (ContinuousLinearMap.id 𝕜 E).coeFn_compLp f

/-- The `compLpL` operator of the identity map is the identity operator on `Lp`. -/
@[simp]
theorem id_compLpL [Fact (1 ≤ p)] :
    (ContinuousLinearMap.id 𝕜 E).compLpL p μ = ContinuousLinearMap.id 𝕜 (Lp E p μ) := by
  ext1 f
  exact id_compLp f

end ContinuousLinearMap
