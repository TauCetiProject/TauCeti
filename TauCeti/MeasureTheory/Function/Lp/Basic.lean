/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Basic lemmas on `Lp` classes and `ContinuousLinearMap.compLp`

Mathlib provides `MeasureTheory.MemLp.toLp_zero`, `MeasureTheory.MemLp.toLp_add`, and
`MeasureTheory.Lp.coeFn_finsetSum`, as well as `MeasureTheory.memLp_finsetSum` and
`MeasureTheory.memLp_finsetSum'`. This file records the companion identities identifying the `Lp`
class of a finite sum of `Lᵖ` functions with the sum of their `Lp` classes, for any `MemLp`
witness on the sum, together with functoriality of `ContinuousLinearMap.compLp` under composition of
continuous linear maps.

## Main declarations

* `MeasureTheory.MemLp.toLp_finsetSum'`: `hsum.toLp (∑ i ∈ s, f i) = ∑ i ∈ s, (hf i).toLp (f i)`.
* `MeasureTheory.MemLp.toLp_finsetSum`:
  `hsum.toLp (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, (hf i).toLp (f i)`.
* `ContinuousLinearMap.compLp_comp`: `L₁.compLp (L₂.compLp f) = (L₁.comp L₂).compLp f`.
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

/-- Composing `Lp` postcompositions by two continuous linear maps agrees with postcomposing by their
composition. -/
@[simp]
theorem compLp_comp {α 𝕜 F₁ F₂ F₃ : Type*} {_ : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}
    [NontriviallyNormedField 𝕜] [NormedAddCommGroup F₁] [NormedSpace 𝕜 F₁]
    [NormedAddCommGroup F₂] [NormedSpace 𝕜 F₂] [NormedAddCommGroup F₃] [NormedSpace 𝕜 F₃]
    (L₁ : F₂ →L[𝕜] F₃) (L₂ : F₁ →L[𝕜] F₂) (f : Lp F₁ p μ) :
    L₁.compLp (L₂.compLp f) = (L₁.comp L₂).compLp f := by
  apply Lp.ext
  filter_upwards [L₁.coeFn_compLp (L₂.compLp f), L₂.coeFn_compLp f,
    (L₁.comp L₂).coeFn_compLp f] with x h₁ h₂ h₁₂
  rw [h₁, h₂, h₁₂, ContinuousLinearMap.comp_apply]

end ContinuousLinearMap
