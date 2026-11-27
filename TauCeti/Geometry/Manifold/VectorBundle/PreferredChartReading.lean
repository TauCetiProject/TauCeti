/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.VectorBundle.Basic
public import Mathlib.Geometry.Manifold.ChartedSpace

/-!
# A section read in the preferred charts

For a fibre bundle `V` with fibre `F` over a manifold `M` modelled on `E`, a section `s` is read at
a point `c` in the preferred manifold chart `φ_c = chartAt E c` and the preferred trivialization
`e_c = trivializationAt F V c` as the function `y ↦ (e_c (s (φ_c⁻¹ y))).2` on the model space.

## Main definitions and results

* `TauCeti.preferredChartReading`: the reading of a section in the preferred charts at a point.
* `TauCeti.preferredChartReading_chartAt`: at the chart coordinate of a point `z` of the chart
  source, the reading is `s z` read in the preferred trivialization.
* `TauCeti.preferredChartReading_chartAt_self`: for a vector bundle, the reading of a section
  vanishing at `c` vanishes at the chart coordinate of `c`.
-/

@[expose] public section

noncomputable section

open Bundle

namespace TauCeti

section FiberBundle

variable {E M F : Type*} [TopologicalSpace E] [TopologicalSpace M] [ChartedSpace E M]
  [TopologicalSpace F] {V : M → Type*} [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V]

variable (E F) in
/-- The reading of a section `s` in the preferred manifold chart and the preferred trivialization
at `c`: the function `y ↦ (e_c (s (φ_c⁻¹ y))).2` on the model space, where `φ_c = chartAt E c` and
`e_c = trivializationAt F V c`. -/
def preferredChartReading (s : ∀ x, V x) (c : M) (y : E) : F :=
  (trivializationAt F V c (TotalSpace.mk' F ((chartAt E c).symm y) (s ((chartAt E c).symm y)))).2

variable (E F) in
theorem preferredChartReading_apply (s : ∀ x, V x) (c : M) (y : E) :
    preferredChartReading E F s c y =
      (trivializationAt F V c
        (TotalSpace.mk' F ((chartAt E c).symm y) (s ((chartAt E c).symm y)))).2 :=
  (rfl)

variable (E F) in
/-- At the chart coordinate of a point `z` of the chart source, the reading of `s` at `c` is `s z`
read in the preferred trivialization at `c`. -/
theorem preferredChartReading_chartAt (s : ∀ x, V x) {c z : M} (hz : z ∈ (chartAt E c).source) :
    preferredChartReading E F s c (chartAt E c z) = (trivializationAt F V c ⟨z, s z⟩).2 := by
  rw [preferredChartReading_apply, (chartAt E c).left_inv hz]

end FiberBundle

section VectorBundle

variable {R E M F : Type*} [NontriviallyNormedField R] [TopologicalSpace E] [TopologicalSpace M]
  [ChartedSpace E M] [NormedAddCommGroup F] [NormedSpace R F] {V : M → Type*}
  [∀ x, AddCommMonoid (V x)] [∀ x, Module R (V x)] [TopologicalSpace (TotalSpace F V)]
  [∀ x, TopologicalSpace (V x)] [FiberBundle F V] [VectorBundle R F V]

variable (R E F) in
include R in
/-- The reading at `c` of a section vanishing at `c` vanishes at the chart coordinate of `c`. -/
theorem preferredChartReading_chartAt_self {s : ∀ x, V x} {c : M} (hs : s c = 0) :
    preferredChartReading E F s c (chartAt E c c) = 0 := by
  rw [preferredChartReading_chartAt E F s (mem_chart_source E c), hs]
  exact congrArg Prod.snd
    ((trivializationAt F V c).zeroSection R (mem_baseSet_trivializationAt F V c))

end VectorBundle

end TauCeti
