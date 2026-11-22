/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Compactness.Compact
public import Mathlib.Topology.Sets.Closeds

/-!
# Clopen subsets: compactness and preimages

This file supplies the compact-space instance on a clopen subset of a compact space and defines the
pullback `TopologicalSpace.Clopens.comap` of a clopen subset along a continuous map.
-/

public section

open TopologicalSpace

namespace TopologicalSpace.Clopens

/-- A clopen subset of a compact space is compact. -/
instance instCompactSpace [TopologicalSpace X] [CompactSpace X] (s : Clopens X) : CompactSpace s :=
  isCompact_iff_compactSpace.mp s.isClosed.isCompact

/-- The preimage of a clopen subset along a continuous map, as a clopen subset. -/
@[expose]
def comap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (g : C(Y, X)) (U : Clopens X) : Clopens Y :=
  ⟨g ⁻¹' U, U.isClopen.preimage g.continuous⟩

/-- The underlying set of `Clopens.comap g U` is `g ⁻¹' U`. -/
@[simp]
theorem coe_comap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (g : C(Y, X)) (U : Clopens X) :
    (comap g U : Set Y) = g ⁻¹' U :=
  (rfl)

/-- Membership in `Clopens.comap g U` is membership of `g y` in `U`. -/
@[simp]
theorem mem_comap {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {g : C(Y, X)} {U : Clopens X} {y : Y} :
    y ∈ comap g U ↔ g y ∈ U :=
  Iff.rfl

end TopologicalSpace.Clopens
