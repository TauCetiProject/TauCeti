/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.CategoryTheory.Action.Basic

/-!
# Smooth `G`-sets

For a topological group `G`, a `G`-set is *smooth* when the stabilizer of every point is open.
For the discrete topology on the set, this is continuity of the action. For compact `G`, every
orbit of a smooth `G`-set is finite.

## Main declarations

* `Action.isSmooth G`: the `G`-sets whose stabilizers are open.
* `Action.SmoothSet G`: the category of smooth `G`-sets.
* `Action.isSmooth.finite_orbit`: for compact `G`, orbits in a smooth `G`-set are finite.
-/

public section

open CategoryTheory

universe u

namespace Action

variable (G : Type u) [Group G] [TopologicalSpace G]

/-- A `G`-set is smooth when every stabilizer is open; for the discrete topology on the set,
this is continuity of the action (`continuousSMul_iff_stabilizer_isOpen`). -/
def isSmooth : ObjectProperty (Action (Type u) G) :=
  fun X ↦ ∀ x : X.V, IsOpen (MulAction.stabilizer G x : Set G)

/-- The category of smooth `G`-sets: sets with an action of `G` whose stabilizers are open. -/
abbrev SmoothSet : Type (u + 1) := (isSmooth G).FullSubcategory

variable {G}

/-- A `G`-set is smooth exactly when the stabilizer of every point is open. -/
theorem isSmooth_iff (X : Action (Type u) G) :
    isSmooth G X ↔ ∀ x : X.V, IsOpen (MulAction.stabilizer G x : Set G) :=
  Iff.rfl

/-- For compact `G`, orbits in a smooth `G`-set are finite. -/
theorem isSmooth.finite_orbit [SeparatelyContinuousMul G] [CompactSpace G]
    {X : Action (Type u) G} (hX : isSmooth G X) (x : X.V) : Finite (MulAction.orbit G x) :=
  have := Subgroup.quotient_finite_of_isOpen _ (hX x)
  (MulAction.orbitEquivQuotientStabilizer G x).finite_iff.2 this

end Action
