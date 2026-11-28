/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSpace.Indicator
import Mathlib.MeasureTheory.Function.SimpleFuncDenseLp
import Mathlib.Topology.EMetricSpace.Lipschitz

/-!
# Continuity of families of measure-preserving `L^p` pullbacks

Let `T : Y → α → β` be a family of measure-preserving maps from `μ` to `ν`, parametrized by a
topological space `Y`. If for every measurable set `s` of finite measure the measure
`μ ((T y ⁻¹' s) ∆ (T y₀ ⁻¹' s))` tends to `0` as `y → y₀`, then for `1 ≤ p < ∞` the pullback
`y ↦ f ∘ T y` of every `f ∈ Lᵖ(ν)` is continuous from `Y` to `Lᵖ(μ)`.

The hypothesis is continuity on indicators, and simple functions are dense in `Lᵖ`. This is the
argument of Mathlib's `MeasureTheory.Lp.compMeasurePreserving_continuous`, which proves joint
continuity for continuous maps between R₁ spaces; here the maps need not be continuous, and the
symmetric-difference limit is a hypothesis. It applies to measurable group actions, where no
topology on `α` is available.

## Main declarations

* `MeasureTheory.Lp.continuous_compMeasurePreserving_of_tendsto_measure_symmDiff`: continuity of
  the pullbacks from the symmetric-difference limit.
-/

public section

open Filter Topology
open scoped ENNReal symmDiff

namespace MeasureTheory
namespace Lp

variable {α β Y E : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
  {ν : Measure β} [TopologicalSpace Y] [NormedAddCommGroup E] {p : ℝ≥0∞} [Fact (1 ≤ p)]

/-- Let `T y` be measure-preserving maps from `μ` to `ν`, and suppose that for every measurable
set `s` of finite measure, `μ ((T y ⁻¹' s) ∆ (T y₀ ⁻¹' s)) → 0` as `y → y₀`. Then for `p ≠ ∞` the
pullback `y ↦ f ∘ T y` of every `f ∈ Lᵖ(ν)` is continuous. -/
theorem continuous_compMeasurePreserving_of_tendsto_measure_symmDiff {T : Y → α → β}
    (hT : ∀ y, MeasurePreserving (T y) μ ν) (hp : p ≠ ∞)
    (h : ∀ ⦃s : Set β⦄, MeasurableSet s → ν s ≠ ∞ → ∀ y₀,
      Tendsto (fun y ↦ μ ((T y ⁻¹' s) ∆ (T y₀ ⁻¹' s))) (𝓝 y₀) (𝓝 0))
    (f : Lp E p ν) : Continuous fun y ↦ compMeasurePreserving (T y) (hT y) f := by
  have hp₀ : p ≠ 0 := (one_pos.trans_le Fact.out).ne'
  have H : Continuous fun fy : Lp E p ν × Y ↦ compMeasurePreserving (T fy.2) (hT fy.2) fy.1 := by
    refine continuous_prod_of_dense_continuous_lipschitzWith _ 1 (simpleFunc.dense hp) ?_
      fun y ↦ (isometry_compMeasurePreserving (hT y)).lipschitzWith
    intro f hf
    lift f to simpleFunc E p ν using hf
    induction f using simpleFunc.induction hp₀ hp with
    | add hfp hgp _ ihf ihg => exact ihf.add ihg
    | @indicatorConst c s hs hνs =>
      dsimp only [simpleFunc.coe_indicatorConst, indicatorConstLp_compMeasurePreserving]
      exact continuous_indicatorConstLp_set hp (h hs hνs.ne)
  exact H.comp (continuous_const.prodMk continuous_id)

end Lp
end MeasureTheory
