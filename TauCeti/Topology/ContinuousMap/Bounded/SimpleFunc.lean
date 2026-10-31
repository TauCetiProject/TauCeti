/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.SimpleFunc
public import TauCeti.Topology.ContinuousMap.Bounded.Normed

/-!
# Simple functions on a discrete space as bounded continuous functions

On a discrete space `X`, a simple function has finite range, so it is a bounded continuous
function. When every subset of `X` is measurable, every finite-valued function is simple, and so
simple functions are uniformly dense among bounded real functions on `X`.

## Main definitions

* `MeasureTheory.SimpleFunc.toBoundedContinuousFunction`: a simple function on a discrete space
  as a bounded continuous function.
* `MeasureTheory.SimpleFunc.toBoundedContinuousFunctionLinearMap`: the same inclusion, as a
  linear map.

## Main results

* `MeasureTheory.SimpleFunc.denseRange_toBoundedContinuousFunction`: on a discrete space where
  every subset is measurable, simple functions are uniformly dense among bounded real functions.
-/

public section

noncomputable section

open scoped BoundedContinuousFunction

namespace MeasureTheory.SimpleFunc

variable {X : Type*} [MeasurableSpace X] [TopologicalSpace X] [DiscreteTopology X]

section PseudoMetricSpace

variable {E : Type*} [PseudoMetricSpace E]

/-- On a discrete space, a simple function as a bounded continuous function. -/
def toBoundedContinuousFunction (g : SimpleFunc X E) : X →ᵇ E :=
  BoundedContinuousFunction.mkOfDiscrete g (Metric.diam (Set.range g)) fun x y =>
    Metric.dist_le_diam_of_mem g.finite_range.isBounded (Set.mem_range_self x)
      (Set.mem_range_self y)

@[simp]
theorem toBoundedContinuousFunction_apply (g : SimpleFunc X E) (x : X) :
    g.toBoundedContinuousFunction x = g x :=
  (rfl)

end PseudoMetricSpace

/-- A simple function equal to `c` on `s` and to `0` off `s` is `c` times the characteristic
function of `s`. -/
theorem toBoundedContinuousFunction_piecewise_const {s : Set X} (hs : MeasurableSet s) (c : ℝ) :
    (piecewise s hs (const X c) (const X 0)).toBoundedContinuousFunction =
      c • BoundedContinuousFunction.indicator s (isClopen_discrete s) := by
  ext x
  by_cases hx : x ∈ s <;> simp [hx]

/-- On a discrete space where every subset is measurable, simple functions are uniformly dense
among bounded real functions. -/
theorem denseRange_toBoundedContinuousFunction [DiscreteMeasurableSpace X] :
    DenseRange (toBoundedContinuousFunction : SimpleFunc X ℝ → X →ᵇ ℝ) := by
  refine Metric.denseRange_iff.2 fun f ε hε => ?_
  obtain ⟨g, hg, hfg⟩ := f.exists_finite_range_dist_lt hε
  let g' : SimpleFunc X ℝ := ⟨g, fun _ => .of_discrete, hg⟩
  have hg' : g'.toBoundedContinuousFunction = g := by
    ext x
    simp [g']
  exact ⟨g', hg' ▸ hfg⟩

section LinearMap

variable {E : Type*} [SeminormedAddCommGroup E]

@[simp]
theorem toBoundedContinuousFunction_add (f g : SimpleFunc X E) :
    (f + g).toBoundedContinuousFunction =
      f.toBoundedContinuousFunction + g.toBoundedContinuousFunction :=
  (rfl)

variable (𝕜 : Type*) [NormedField 𝕜] [NormedSpace 𝕜 E]

/-- On a discrete space, the inclusion of simple functions into bounded continuous functions, as
a linear map. -/
def toBoundedContinuousFunctionLinearMap : SimpleFunc X E →ₗ[𝕜] X →ᵇ E where
  toFun := toBoundedContinuousFunction
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem coe_toBoundedContinuousFunctionLinearMap :
    ⇑(toBoundedContinuousFunctionLinearMap 𝕜 : SimpleFunc X E →ₗ[𝕜] X →ᵇ E) =
      toBoundedContinuousFunction :=
  (rfl)

theorem toBoundedContinuousFunctionLinearMap_apply (g : SimpleFunc X E) :
    toBoundedContinuousFunctionLinearMap 𝕜 g = g.toBoundedContinuousFunction :=
  (rfl)

/-- On a discrete space where every subset is measurable, simple functions are uniformly dense
among bounded real functions, stated for the linear inclusion. -/
theorem denseRange_toBoundedContinuousFunctionLinearMap [DiscreteMeasurableSpace X] :
    DenseRange (toBoundedContinuousFunctionLinearMap ℝ : SimpleFunc X ℝ →ₗ[ℝ] X →ᵇ ℝ) := by
  simpa using denseRange_toBoundedContinuousFunction

end LinearMap

end MeasureTheory.SimpleFunc
