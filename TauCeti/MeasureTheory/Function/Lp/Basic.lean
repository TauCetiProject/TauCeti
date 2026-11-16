/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Basic `Lᵖ` identities

This file records basic identities on `MeasureTheory.Lp` that complement
`Mathlib.MeasureTheory.Function.LpSpace.Basic`:

* Finite-sum identities for `MeasureTheory.MemLp.toLp` (complementing
  `MeasureTheory.MemLp.toLp_zero`, `MeasureTheory.MemLp.toLp_add`,
  `MeasureTheory.Lp.coeFn_finsetSum`, `MeasureTheory.memLp_finsetSum`, and
  `MeasureTheory.memLp_finsetSum'`).
* Evaluation and functoriality identities for `ContinuousLinearMap.compLp` and
  `ContinuousLinearMap.compLpL`.

## Main declarations

* `MeasureTheory.MemLp.toLp_finsetSum'`: `hsum.toLp (∑ i ∈ s, f i) = ∑ i ∈ s, (hf i).toLp (f i)`.
* `MeasureTheory.MemLp.toLp_finsetSum`:
  `hsum.toLp (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, (hf i).toLp (f i)`.
* `ContinuousLinearMap.compLpL_apply`: `L.compLpL p μ f = L.compLp f`.
* `ContinuousLinearMap.id_compLp`: `(ContinuousLinearMap.id 𝕜 E).compLp f = f`.
* `ContinuousLinearMap.comp_compLp`: `(L₂.comp L₁).compLp f = L₂.compLp (L₁.compLp f)`.
* `ContinuousLinearMap.id_compLpL`:
  `(ContinuousLinearMap.id 𝕜 E).compLpL p μ = ContinuousLinearMap.id 𝕜 (Lp E p μ)`.
* `ContinuousLinearMap.comp_compLpL`:
  `(L₂.comp L₁).compLpL p μ = (L₂.compLpL p μ).comp (L₁.compLpL p μ)`.
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

variable {α 𝕜 𝕜₂ 𝕜₃ E F G : Type*} {_ : MeasurableSpace α} {p : ℝ≥0∞} {μ : Measure α}
  [NormedAddCommGroup E] [NormedAddCommGroup F] [NormedAddCommGroup G]
  [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜₂] [NontriviallyNormedField 𝕜₃]
  [NormedSpace 𝕜 E] [NormedSpace 𝕜₂ F] [NormedSpace 𝕜₃ G]
  {σ : 𝕜 →+* 𝕜₂} {σ₁₂ : 𝕜 →+* 𝕜₂} {σ₂₃ : 𝕜₂ →+* 𝕜₃} {σ₁₃ : 𝕜 →+* 𝕜₃}

/-- Evaluating `L.compLpL p μ` at `f` is `L.compLp f`. -/
@[simp]
theorem compLpL_apply [RingHomIsometric σ] [Fact (1 ≤ p)] (L : E →SL[σ] F) (f : Lp E p μ) :
    L.compLpL p μ f = L.compLp f :=
  rfl

/-- Postcomposing an `Lᵖ` class with the identity continuous linear map leaves it unchanged. -/
@[simp]
theorem id_compLp (f : Lp E p μ) : (ContinuousLinearMap.id 𝕜 E).compLp f = f :=
  Lp.ext <| (ContinuousLinearMap.id 𝕜 E).coeFn_compLp f

/-- Postcomposition on `Lᵖ` is functorial in the continuous semilinear map:
`(L₂.comp L₁).compLp f = L₂.compLp (L₁.compLp f)`. -/
theorem comp_compLp [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
    [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃]
    (L₂ : F →SL[σ₂₃] G) (L₁ : E →SL[σ₁₂] F) (f : Lp E p μ) :
    (L₂.comp L₁).compLp f = L₂.compLp (L₁.compLp f) := by
  refine Lp.ext ?_
  filter_upwards [(L₂.comp L₁).coeFn_compLp f, L₂.coeFn_compLp (L₁.compLp f),
    L₁.coeFn_compLp f] with a h₁ h₂ h₃
  rw [h₁, h₂, h₃, comp_apply]

/-- The continuous linear map on `Lᵖ` induced by the identity is the identity. -/
@[simp]
theorem id_compLpL [Fact (1 ≤ p)] :
    (ContinuousLinearMap.id 𝕜 E).compLpL p μ = ContinuousLinearMap.id 𝕜 (Lp E p μ) := by
  ext1 f
  exact id_compLp f

/-- Postcomposition on `Lᵖ` as a continuous semilinear map preserves composition:
`(L₂.comp L₁).compLpL p μ = (L₂.compLpL p μ).comp (L₁.compLpL p μ)`. -/
theorem comp_compLpL [RingHomCompTriple σ₁₂ σ₂₃ σ₁₃]
    [RingHomIsometric σ₁₂] [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃] [Fact (1 ≤ p)]
    (L₂ : F →SL[σ₂₃] G) (L₁ : E →SL[σ₁₂] F) :
    (L₂.comp L₁).compLpL p μ = (L₂.compLpL p μ).comp (L₁.compLpL p μ) := by
  ext1 f
  exact comp_compLp L₂ L₁ f

end ContinuousLinearMap
