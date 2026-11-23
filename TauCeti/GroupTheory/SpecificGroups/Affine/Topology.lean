/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Ring.Basic
public import Mathlib.Topology.ContinuousMap.Basic
public import TauCeti.GroupTheory.SpecificGroups.Affine.Basic

/-!
# Affine maps of a topological ring

For a topological ring `F`, each element `(b, a)` of the affine group `TauCeti.AffineGroup F`
acts on `F` by the continuous map `x ↦ b + a x`.

## Main definitions

* `TauCeti.AffineGroup.toContinuousMap`: the affine map `x ↦ b + a x` of a topological ring.
-/

public section

namespace TauCeti.AffineGroup

variable {F : Type*} [Ring F] [TopologicalSpace F] [IsTopologicalSemiring F]

/-- The affine map `x ↦ b + a x` of a topological ring attached to `(b, a)`, as a continuous
map. -/
def toContinuousMap (g : AffineGroup F) : C(F, F) where
  toFun x := g • x
  continuous_toFun := by
    simp_rw [AffineGroup.smul_def]
    fun_prop

@[simp]
theorem toContinuousMap_apply (g : AffineGroup F) (x : F) : g.toContinuousMap x = g • x :=
  (rfl)

end TauCeti.AffineGroup
