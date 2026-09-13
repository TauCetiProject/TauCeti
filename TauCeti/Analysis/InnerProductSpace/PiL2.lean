/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.Normed.Lp.MeasurableSpace
public import Mathlib.Topology.Algebra.Monoid.FunOnFinite

/-!
# Fibrewise sums of Euclidean coordinates

A map `f : ι → κ` of finite index types coarsens a Euclidean coordinate system: the coordinates
of a vector indexed by `ι` are merged into the groups cut out by the fibres of `f`, one group
summed into each coordinate of a vector indexed by `κ`.  This is Mathlib's `FunOnFinite.map`,
here read through `EuclideanSpace.equiv` so that it acts on Euclidean space, where it is again
continuous and measurable.

## Main definitions

* `TauCeti.euclideanFiberSum` sums the coordinates of a Euclidean vector over each fibre of a map
  of index types.
-/

public section

noncomputable section

namespace TauCeti

variable {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Sum the coordinates of a Euclidean vector over each fibre of `f`.

This is Mathlib's `FunOnFinite.map` read in Euclidean coordinates. -/
def euclideanFiberSum (f : ι → κ) (x : EuclideanSpace ℝ ι) : EuclideanSpace ℝ κ :=
  (EuclideanSpace.equiv κ ℝ).symm (FunOnFinite.map f (EuclideanSpace.equiv ι ℝ x))

@[simp]
theorem euclideanFiberSum_apply [DecidableEq κ] (f : ι → κ) (x : EuclideanSpace ℝ ι) (j : κ) :
    euclideanFiberSum f x j = ∑ i with f i = j, x i := by
  simp [euclideanFiberSum, FunOnFinite.map_apply_apply]

/-- Fibrewise summation is continuous. -/
@[fun_prop]
theorem continuous_euclideanFiberSum (f : ι → κ) :
    Continuous (euclideanFiberSum (ι := ι) f) :=
  (EuclideanSpace.equiv κ ℝ).symm.continuous.comp <|
    (FunOnFinite.continuous_map ℝ f).comp (EuclideanSpace.equiv ι ℝ).continuous

/-- Fibrewise summation is measurable. -/
@[fun_prop]
theorem measurable_euclideanFiberSum (f : ι → κ) :
    Measurable (euclideanFiberSum (ι := ι) f) :=
  (continuous_euclideanFiberSum f).measurable

end TauCeti
