/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected

/-!
# The fundamental groupoid of a simply connected space

A space is simply connected exactly when its fundamental groupoid is codiscrete: there is one
and only one morphism between any two of its objects. This file records that uniqueness as a
`Unique` instance on the hom types, so that a transport map along a path inside a simply
connected space can be written down without naming the path, and two such transports agree
because the morphisms realizing them are equal.

The two lemmas about a functor out of such a groupoid say that the resulting transport maps
compose as expected and that the unique endomorphism of an object is sent to an identity.
-/

public section

open CategoryTheory

variable {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]

namespace FundamentalGroupoid

/-- In a simply connected space there is exactly one morphism of the fundamental groupoid
between any two points; `default` is that morphism. -/
noncomputable instance instUniqueHom (x y : FundamentalGroupoid X) : Unique (x ⟶ y) :=
  ((simply_connected_iff_unique_homotopic X).mp inferInstance).2 x.as y.as |>.some

variable {D : Type*} [Category D] (F : FundamentalGroupoid X ⥤ D)

/-- A functor out of the fundamental groupoid of a simply connected space sends the unique
endomorphism of an object to the identity. -/
@[simp]
theorem map_default_self (x : FundamentalGroupoid X) : F.map (default : x ⟶ x) = 𝟙 (F.obj x) := by
  rw [Subsingleton.elim (default : x ⟶ x) (𝟙 x), F.map_id]

/-- A functor out of the fundamental groupoid of a simply connected space sends the unique
morphisms `x ⟶ y` and `y ⟶ z` to maps whose composite is the image of the unique morphism
`x ⟶ z`. -/
@[reassoc (attr := simp)]
theorem map_default_comp (x y z : FundamentalGroupoid X) :
    F.map (default : x ⟶ y) ≫ F.map (default : y ⟶ z) = F.map (default : x ⟶ z) := by
  rw [← F.map_comp]
  exact congrArg _ (Subsingleton.elim _ _)

end FundamentalGroupoid
