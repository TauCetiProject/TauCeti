/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Convenient.ContinuousMapGeneratedBy

/-!
# `X`-continuous maps on `X`-generated domains

This file supplements Mathlib's `Mathlib.Topology.Convenient.ContinuousMapGeneratedBy` with basic
API for `Topology.ContinuousGeneratedBy` and `Topology.ContinuousMapGeneratedBy`:

* `Topology.continuousGeneratedBy_iff_continuous`: on an `X`-generated domain, `X`-continuity
  coincides with ordinary continuity.
* `Topology.ContinuousMapGeneratedBy.toContinuousMap`: bundles an `X`-continuous map out of an
  `X`-generated domain as an ordinary `ContinuousMap`.

## References

* M. Escardó, J. Lawson, and A. Simpson, *Comparing Cartesian closed categories of (core)
  compactly generated spaces*, Topology Appl. 143 (2004), 105–145.
-/

public section

namespace Topology

/-- On an `X`-generated domain, `X`-continuity is ordinary continuity. -/
@[simp]
theorem continuousGeneratedBy_iff_continuous {ι : Type*} {X : ι → Type*}
    [∀ i, TopologicalSpace (X i)] {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    [IsGeneratedBy X Y] (g : Y → Z) :
    ContinuousGeneratedBy X g ↔ Continuous g :=
  (IsGeneratedBy.continuous_iff X g).symm

namespace ContinuousMapGeneratedBy

@[simp]
theorem coe_mk {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]
    (f : Y → Z) (hf : ContinuousGeneratedBy X f) :
    ⇑(ContinuousMapGeneratedBy.mk f hf) = f :=
  (rfl)

/-- On an `X`-generated domain `Y`, an `X`-continuous map `Y → Z` is an ordinary continuous map. -/
def toContinuousMap {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] [IsGeneratedBy X Y]
    (g : ContinuousMapGeneratedBy X Y Z) : C(Y, Z) :=
  ⟨g, (continuousGeneratedBy_iff_continuous g).1 g.prop⟩

@[simp]
theorem toContinuousMap_apply {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] [IsGeneratedBy X Y]
    (g : ContinuousMapGeneratedBy X Y Z) (y : Y) :
    g.toContinuousMap y = g y :=
  (rfl)

@[simp]
theorem coe_toContinuousMap {ι : Type*} {X : ι → Type*} [∀ i, TopologicalSpace (X i)]
    {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z] [IsGeneratedBy X Y]
    (g : ContinuousMapGeneratedBy X Y Z) :
    ⇑g.toContinuousMap = g :=
  (rfl)

end ContinuousMapGeneratedBy

end Topology
