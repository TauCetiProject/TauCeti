/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.ContinuousMap.Basic

/-!
# Restriction of continuous maps

Composition with the subtype inclusion agrees with restriction, allowing formulas using
pullback to be rewritten in terms of restricted continuous maps.
-/

public section

namespace TauCeti

/-- Pullback along the subtype inclusion is restriction to the subset. -/
theorem comp_subtypeVal_eq_restrict {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (s : Set X) (f : C(X, Y)) :
    f.comp (ContinuousMap.subtypeVal s) = f.restrict s := by
  ext x
  rw [ContinuousMap.comp_apply, ContinuousMap.subtypeVal_apply, ContinuousMap.restrict_apply]

end TauCeti
