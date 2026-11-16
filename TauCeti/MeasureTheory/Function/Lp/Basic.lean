/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Finite sums of `MemLp.toLp` classes, and composition with a continuous linear map

Mathlib provides `MeasureTheory.MemLp.toLp_zero`, `MeasureTheory.MemLp.toLp_add`, and
`MeasureTheory.Lp.coeFn_finsetSum`, as well as `MeasureTheory.memLp_finsetSum` and
`MeasureTheory.memLp_finsetSum'`. This file records the companion identities identifying the `Lp`
class of a finite sum of `Lᵖ` functions with the sum of their `Lp` classes, for any `MemLp`
witness on the sum.

Mathlib composes `f : Lp E p μ` with `L : E →SL[σ] F` both as an element `L.compLp f` and through
the bundled continuous semilinear map `L.compLpL p μ`; this file records that the two agree and
that postcomposition is functorial and respects negation and subtraction.

## Main declarations

* `MeasureTheory.MemLp.toLp_finsetSum'`: `hsum.toLp (∑ i ∈ s, f i) = ∑ i ∈ s, (hf i).toLp (f i)`.
* `MeasureTheory.MemLp.toLp_finsetSum`:
  `hsum.toLp (fun x ↦ ∑ i ∈ s, f i x) = ∑ i ∈ s, (hf i).toLp (f i)`.
* `ContinuousLinearMap.compLpL_apply`: the bundled composition applied to `f` is `L.compLp f`.
* `ContinuousLinearMap.id_compLp`, `ContinuousLinearMap.comp_compLp`,
  `ContinuousLinearMap.id_compLpL`, `ContinuousLinearMap.comp_compLpL`: functoriality of
  postcomposition on `Lᵖ`.
* `ContinuousLinearMap.neg_compLp`, `ContinuousLinearMap.sub_compLp`,
  `ContinuousLinearMap.neg_compLpL`, `ContinuousLinearMap.sub_compLpL`: compatibility with negation
  and subtraction.
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

variable {α E F 𝕜 𝕜' : Type*} {_ : MeasurableSpace α} {μ : Measure α} {p : ℝ≥0∞}
  [NontriviallyNormedField 𝕜] [NontriviallyNormedField 𝕜'] {σ : 𝕜 →+* 𝕜'} [RingHomIsometric σ]
  [NormedAddCommGroup E] [NormedSpace 𝕜 E] [NormedAddCommGroup F] [NormedSpace 𝕜' F]

/-- The bundled composition `L.compLpL p μ` applied to `f` is the composition `L.compLp f`. -/
@[simp]
theorem compLpL_apply [Fact (1 ≤ p)] (L : E →SL[σ] F) (f : Lp E p μ) :
    L.compLpL p μ f = L.compLp f :=
  rfl

/-- Postcomposing an `Lᵖ` class with the identity map leaves it unchanged. -/
@[simp]
theorem id_compLp (f : Lp E p μ) : (ContinuousLinearMap.id 𝕜 E).compLp f = f :=
  Subtype.ext (AEEqFun.comp_id f.1)

/-- Postcomposition on `Lᵖ` is functorial in the continuous semilinear map. -/
theorem comp_compLp {𝕜'' G : Type*} [NontriviallyNormedField 𝕜'']
    [NormedAddCommGroup G] [NormedSpace 𝕜'' G] {σ₂₃ : 𝕜' →+* 𝕜''} {σ₁₃ : 𝕜 →+* 𝕜''}
    [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃] [RingHomCompTriple σ σ₂₃ σ₁₃]
    (L₁ : F →SL[σ₂₃] G) (L₂ : E →SL[σ] F) (f : Lp E p μ) :
    (L₁.comp L₂).compLp f = L₁.compLp (L₂.compLp f) :=
  Subtype.ext (AEEqFun.comp_comp L₁ L₂ L₁.continuous L₂.continuous f.1).symm

/-- Postcomposing an `Lᵖ` class with `-L` negates `L.compLp f`. -/
@[simp]
theorem neg_compLp (L : E →SL[σ] F) (f : Lp E p μ) : (-L).compLp f = -L.compLp f := by
  simpa only [neg_one_smul] using smul_compLp (-1 : 𝕜') L f

/-- Postcomposing an `Lᵖ` class with `L - L'` subtracts the postcompositions. -/
theorem sub_compLp (L L' : E →SL[σ] F) (f : Lp E p μ) :
    (L - L').compLp f = L.compLp f - L'.compLp f := by
  rw [sub_eq_add_neg, add_compLp, neg_compLp, sub_eq_add_neg]

/-- The bundled postcomposition by the identity is the identity on `Lᵖ`. -/
@[simp]
theorem id_compLpL [Fact (1 ≤ p)] :
    (ContinuousLinearMap.id 𝕜 E).compLpL p μ = ContinuousLinearMap.id 𝕜 (Lp E p μ) :=
  ext id_compLp

/-- Bundled postcomposition on `Lᵖ` is functorial in the continuous semilinear map. -/
theorem comp_compLpL [Fact (1 ≤ p)] {𝕜'' G : Type*} [NontriviallyNormedField 𝕜'']
    [NormedAddCommGroup G] [NormedSpace 𝕜'' G] {σ₂₃ : 𝕜' →+* 𝕜''} {σ₁₃ : 𝕜 →+* 𝕜''}
    [RingHomIsometric σ₂₃] [RingHomIsometric σ₁₃] [RingHomCompTriple σ σ₂₃ σ₁₃]
    (L₁ : F →SL[σ₂₃] G) (L₂ : E →SL[σ] F) :
    (L₁.comp L₂).compLpL p μ = (L₁.compLpL p μ).comp (L₂.compLpL p μ) :=
  ext (comp_compLp L₁ L₂)

/-- Bundled postcomposition respects negation of continuous semilinear maps. -/
@[simp]
theorem neg_compLpL [Fact (1 ≤ p)] (L : E →SL[σ] F) : (-L).compLpL p μ = -L.compLpL p μ :=
  ext (neg_compLp L)

/-- Bundled postcomposition respects subtraction of continuous semilinear maps. -/
theorem sub_compLpL [Fact (1 ≤ p)] (L L' : E →SL[σ] F) :
    (L - L').compLpL p μ = L.compLpL p μ - L'.compLpL p μ :=
  ext (sub_compLp L L')

end ContinuousLinearMap
