/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.MeasureTheory.Measure.Map

/-!
# Measures on one-dimensional Euclidean space

Over a one-element index type `ι`, reading off the unique coordinate and including it back with
`EuclideanSpace.single` are inverse to each other. So every measure on `EuclideanSpace ℝ ι` is the
image of its law on the unique coordinate under `EuclideanSpace.single default`. This reduces a
one-dimensional identification of a law on `EuclideanSpace ℝ ι` to its coordinate marginal.

## Main results

* `EuclideanSpace.measurable_single`: the inclusion of one coordinate is measurable.
* `EuclideanSpace.map_single_map_eval`: over a one-element index type, a measure is the image of
  its coordinate law under `EuclideanSpace.single default`.
-/

public section

open MeasureTheory

namespace EuclideanSpace

variable {ι : Type*} [DecidableEq ι]

/-- The inclusion `EuclideanSpace.single i` of the `i`-th coordinate is measurable. -/
theorem measurable_single [Countable ι] (i : ι) :
    Measurable (EuclideanSpace.single i : ℝ → EuclideanSpace ℝ ι) := by
  -- `EuclideanSpace.single` is `toLp` applied to `Pi.single`.
  have h (a : ℝ) : EuclideanSpace.single i a =
      WithLp.toLp 2 (Pi.single (M := fun _ : ι => ℝ) i a) :=
    (PiLp.toLp_single 2 (β := fun _ : ι => ℝ) i a).symm
  rw [funext h]
  exact (WithLp.measurable_toLp 2 _).comp (continuous_single i).measurable

/-- **A measure on one-dimensional Euclidean space is determined by its coordinate law.** Over a
one-element index type, pushing a measure forward to the unique coordinate and back along
`EuclideanSpace.single default` returns the measure. -/
theorem map_single_map_eval [Unique ι] (μ : Measure (EuclideanSpace ℝ ι)) :
    (μ.map fun x => x default).map (EuclideanSpace.single default) = μ := by
  have hcomp : (EuclideanSpace.single (default : ι)) ∘
      (fun x : EuclideanSpace ℝ ι => x default) = id := by
    funext x
    ext i
    simp [Unique.eq_default i]
  rw [Measure.map_map (measurable_single default) (by fun_prop), hcomp, Measure.map_id]

end EuclideanSpace
