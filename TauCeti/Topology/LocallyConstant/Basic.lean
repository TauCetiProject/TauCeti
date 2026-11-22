/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.LocallyConstant.Basic

/-!
# Locally constant functions: discrete codomains and pairing

For a discrete codomain, locally constant functions are exactly continuous maps:
`LocallyConstant.equivContinuousMap`. For two locally constant functions on the same space,
`LocallyConstant.prodMk` bundles their pointwise pairing.
-/

public section

namespace LocallyConstant

/-- Pair two locally constant functions on the same space into a locally constant function into
the product. -/
@[expose, simps]
def prodMk {X α β : Type*} [TopologicalSpace X]
    (f : LocallyConstant X α) (g : LocallyConstant X β) : LocallyConstant X (α × β) :=
  ⟨fun x ↦ (f x, g x), f.isLocallyConstant.prodMk g.isLocallyConstant⟩

/-- For a discrete codomain, locally constant functions are the same as continuous maps. -/
@[expose, simps apply]
def equivContinuousMap (X Y : Type*) [TopologicalSpace X] [TopologicalSpace Y]
    [DiscreteTopology Y] : LocallyConstant X Y ≃ C(X, Y) where
  toFun := toContinuousMap
  invFun f := ⟨f, (IsLocallyConstant.iff_continuous f).2 f.continuous⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Passing to a continuous map and back recovers the locally constant function. -/
@[simp]
theorem equivContinuousMap_symm_toContinuousMap {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [DiscreteTopology Y] (f : LocallyConstant X Y) :
    (equivContinuousMap X Y).symm f.toContinuousMap = f :=
  (rfl)

/-- The locally constant function attached to a continuous map to a discrete space has the same
underlying function. -/
@[simp]
theorem coe_equivContinuousMap_symm {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [DiscreteTopology Y] (f : C(X, Y)) : ⇑((equivContinuousMap X Y).symm f) = f :=
  (rfl)

/-- The locally constant function attached to a continuous map to a discrete space is that map
again as a continuous map. -/
@[simp]
theorem toContinuousMap_equivContinuousMap_symm {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [DiscreteTopology Y] (f : C(X, Y)) :
    ((equivContinuousMap X Y).symm f).toContinuousMap = f :=
  (rfl)

end LocallyConstant
