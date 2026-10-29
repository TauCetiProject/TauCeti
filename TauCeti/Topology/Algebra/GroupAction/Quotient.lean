/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient
public import TauCeti.Algebra.GroupAction.OrbitRelQuotient

/-!
# Continuous maps from group quotients

This file records continuity results for maps out of group quotients that do not require
transitivity of an action.

## Main results

* `TauCeti.continuous_ofQuotientStabilizer` proves continuity of the orbit map descended to a
  stabilizer quotient when the corresponding orbit map is continuous.
* `TauCeti.continuous_orbitRelQuotientLift_iff`: the descent of a `G`-invariant map to the orbit
  space is continuous exactly when the map is.
-/

public section

open MulAction

namespace TauCeti

section Lift

variable {G X Y : Type*} [Group G] [MulAction G X] [TopologicalSpace X] [TopologicalSpace Y]
  {f : X → Y} {hf : ∀ (g : G) (x : X), f (g • x) = f x}

/-- The descent of a `G`-invariant map to the orbit space is continuous exactly when the map is. -/
theorem continuous_orbitRelQuotientLift_iff :
    Continuous (MulAction.orbitRelQuotientLift f hf) ↔ Continuous f := by
  have hq : Topology.IsQuotientMap (Quotient.mk (MulAction.orbitRel G X)) := isQuotientMap_quot_mk
  rw [hq.continuous_iff, MulAction.orbitRelQuotientLift_comp_mk]

end Lift

variable (G : Type*) {X : Type*} [Group G] [TopologicalSpace G] [TopologicalSpace X]
  [MulAction G X]

/-- The orbit map descended to the stabilizer quotient is continuous when the orbit map is. -/
@[fun_prop]
theorem continuous_ofQuotientStabilizer (b : X) (hb : Continuous fun g : G => g • b) :
    Continuous (ofQuotientStabilizer G b) := by
  unfold ofQuotientStabilizer
  exact hb.quotient_liftOn' _

end TauCeti
