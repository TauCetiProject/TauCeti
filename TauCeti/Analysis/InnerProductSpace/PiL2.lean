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
continuous and measurable. The coordinates may be real or complex; measurability uses the
Borel measurable structure on the scalar field.

## Main definitions

* `TauCeti.euclideanFiberSum` sums the coordinates of a Euclidean vector over each fibre of a map
  of index types.
-/

public section

noncomputable section

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜] {ι κ : Type*} [Fintype ι] [Fintype κ]

/-- Sum the coordinates of a Euclidean vector over each fibre of `f`.

This is Mathlib's `FunOnFinite.map` read in Euclidean coordinates. -/
def euclideanFiberSum (f : ι → κ) (x : EuclideanSpace 𝕜 ι) : EuclideanSpace 𝕜 κ :=
  (EuclideanSpace.equiv κ 𝕜).symm (FunOnFinite.map f (EuclideanSpace.equiv ι 𝕜 x))

@[simp]
theorem euclideanFiberSum_apply [DecidableEq κ] (f : ι → κ) (x : EuclideanSpace 𝕜 ι) (j : κ) :
    euclideanFiberSum f x j = ∑ i with f i = j, x i := by
  simp [euclideanFiberSum, FunOnFinite.map_apply_apply]

/-- Fibrewise summation is continuous. -/
@[fun_prop]
theorem continuous_euclideanFiberSum (f : ι → κ) :
    Continuous (euclideanFiberSum (𝕜 := 𝕜) (ι := ι) f) :=
  (EuclideanSpace.equiv κ 𝕜).symm.continuous.comp <|
    (FunOnFinite.continuous_map 𝕜 f).comp (EuclideanSpace.equiv ι 𝕜).continuous

/-- Fibrewise summation is measurable. -/
@[fun_prop]
theorem measurable_euclideanFiberSum [MeasurableSpace 𝕜] [BorelSpace 𝕜] (f : ι → κ) :
    Measurable (euclideanFiberSum (𝕜 := 𝕜) (ι := ι) f) :=
  (continuous_euclideanFiberSum (𝕜 := 𝕜) f).measurable

end TauCeti
