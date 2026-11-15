/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.Holder
public import Mathlib.MeasureTheory.Function.LpSpace.ContinuousFunctions

/-!
# Algebraic compatibility of `ContinuousMap.toLp`

On a compact topological space `α` equipped with a finite Borel measure `μ`, Mathlib's bounded
linear map `ContinuousMap.toLp p μ 𝕜 : C(α, E) →L[𝕜] Lp E p μ` sends every continuous function to
its `Lᵖ` equivalence class. This file records its compatibility with constants and with Hölder
scalar multiplication (`HSMul (Lp 𝕜 p μ) (Lp E q μ) (Lp E r μ)`):

* `ContinuousMap.toLp_const`: `toLp p μ 𝕜 (const α c) = Lp.const p μ c`.
* `ContinuousMap.toLp_one`: `toLp p μ 𝕜 1 = Lp.const p μ 1`.
* `ContinuousMap.toLp_smul_toLp`: under `[ENNReal.HolderTriple p q r]`,
  `toLp p μ 𝕜 f • toLp q μ 𝕜 g = toLp r μ 𝕜 (f • g)`.
-/

public section

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace ContinuousMap

variable {α 𝕜 E : Type*} [TopologicalSpace α] [MeasurableSpace α] [BorelSpace α]
  [CompactSpace α] {μ : Measure α} [IsFiniteMeasure μ]
  [NormedRing 𝕜] [NormedAddCommGroup E] [Module 𝕜 E] [IsBoundedSMul 𝕜 E]
  [SecondCountableTopologyEither α E]

/-- `ContinuousMap.toLp` sends the constant continuous map `c` to `MeasureTheory.Lp.const p μ c`. -/
@[simp]
theorem toLp_const {p : ℝ≥0∞} [Fact (1 ≤ p)] (c : E) :
    toLp p μ 𝕜 (const α c) = Lp.const p μ c := by
  apply Lp.ext
  filter_upwards [coeFn_toLp (p := p) (𝕜 := 𝕜) μ (const α c),
    Lp.coeFn_const p μ c] with x hc hconst
  rw [hc, hconst, const_apply, Function.const_apply]

/-- `ContinuousMap.toLp` sends `1 : C(α, E)` to `MeasureTheory.Lp.const p μ 1`. -/
@[simp]
theorem toLp_one {p : ℝ≥0∞} [Fact (1 ≤ p)] [One E] :
    toLp p μ 𝕜 (1 : C(α, E)) = Lp.const p μ (1 : E) := by
  apply Lp.ext
  filter_upwards [coeFn_toLp (p := p) (𝕜 := 𝕜) μ (1 : C(α, E)),
    Lp.coeFn_const p μ (1 : E)] with x h1 hconst
  rw [h1, hconst, one_apply, Function.const_apply]

/-- Heterogeneous scalar multiplication of `ContinuousMap.toLp` classes on a compact finite-measure
space represents pointwise scalar multiplication `f • g : C(α, E)`. -/
theorem toLp_smul_toLp {p q r : ℝ≥0∞} [Fact (1 ≤ p)] [Fact (1 ≤ q)] [Fact (1 ≤ r)]
    [ENNReal.HolderTriple p q r] [SecondCountableTopologyEither α 𝕜]
    (f : C(α, 𝕜)) (g : C(α, E)) :
    (toLp p μ 𝕜 f • toLp q μ 𝕜 g : Lp E r μ) = toLp r μ 𝕜 (f • g) := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_lpSMul (r := r) (toLp p μ 𝕜 f) (toLp q μ 𝕜 g),
    coeFn_toLp (p := p) (𝕜 := 𝕜) μ f, coeFn_toLp (p := q) (𝕜 := 𝕜) μ g,
    coeFn_toLp (p := r) (𝕜 := 𝕜) μ (f • g)] with x hsmul hf hg hfg
  rw [hsmul, Pi.smul_apply', hf, hg, hfg, smul_apply']

end ContinuousMap

end
