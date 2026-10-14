/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
public import TauCeti.AlgebraicTopology.FundamentalGroupoid.Basic

/-!
# The fundamental groupoid of a simply connected space

A space is simply connected exactly when its fundamental groupoid is codiscrete: there is one
and only one morphism between any two of its objects. This file records that uniqueness as a
`Unique` instance on the hom types, so that a transport map along a path inside a simply
connected space can be written down without naming the path, and two such transports agree
because the morphisms realizing them are equal.

The two lemmas about a functor out of such a groupoid say that the resulting transport maps
compose as expected and that the unique endomorphism of an object is sent to an identity.

For a continuous map `f` out of a simply connected space, `ContinuousMap.pathClass f x y` is the
image under `f` of the unique path class from `x` to `y`: the path class from `f x` to `f y`
traced inside the image of `f`. For a singular simplex or cube it is the transport inside the
simplex or cube used to define chains with local coefficients.
-/

public section

open CategoryTheory

variable {X : Type*} [TopologicalSpace X] [SimplyConnectedSpace X]

namespace FundamentalGroupoid

/-- In a simply connected space there is exactly one morphism of the fundamental groupoid
between any two points; `default` is that morphism. -/
noncomputable instance instUniqueHom (x y : FundamentalGroupoid X) : Unique (x ⟶ y) :=
  ((simply_connected_iff_unique_homotopic X).mp inferInstance).2 x.as y.as |>.some

end FundamentalGroupoid

namespace CategoryTheory.Functor

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

end CategoryTheory.Functor

namespace ContinuousMap

variable {Y Z : Type*} [TopologicalSpace Y] [TopologicalSpace Z]

/-- The **path class inside the image** of a map `f` out of a simply connected space, from `f x`
to `f y`: the image under `f` of the unique path class from `x` to `y`. -/
noncomputable def pathClass (f : C(X, Y)) (x y : X) :
    FundamentalGroupoid.mk (f x) ⟶ FundamentalGroupoid.mk (f y) :=
  (FundamentalGroupoid.map f).map (default : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y)

/-- The path class inside the image of `f` is the image under `f` of the unique morphism of the
fundamental groupoid of its source. -/
theorem pathClass_def (f : C(X, Y)) (x y : X) :
    f.pathClass x y =
      (FundamentalGroupoid.map f).map
        (default : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) :=
  (rfl)

/-- The path class inside the image of `f` is the image of any path joining the two points. -/
theorem pathClass_eq_mk (f : C(X, Y)) {x y : X} (q : Path x y) :
    f.pathClass x y = Path.Homotopic.Quotient.mk (q.map f.continuous) := by
  rw [pathClass, Subsingleton.elim (default : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y)
    (Path.Homotopic.Quotient.mk q)]
  exact (Path.Homotopic.Quotient.mk_map q f).symm

/-- The path class inside the image of `f` from a point to itself is the identity. -/
@[simp]
theorem pathClass_self (f : C(X, Y)) (x : X) : f.pathClass x x = 𝟙 _ :=
  Functor.map_default_self _ _

/-- Path classes inside the image of `f` compose. -/
@[reassoc (attr := simp)]
theorem pathClass_comp_pathClass (f : C(X, Y)) (x y z : X) :
    f.pathClass x y ≫ f.pathClass y z = f.pathClass x z :=
  Functor.map_default_comp _ _ _ _

/-- A path class inside the image of `f ∘ g`, for `g` a map between simply connected spaces, is a
path class inside the image of `f`. -/
@[simp]
theorem pathClass_comp [SimplyConnectedSpace Z] (f : C(X, Y)) (g : C(Z, X)) (x y : Z) :
    (f.comp g).pathClass x y = f.pathClass (g x) (g y) := by
  have h : ((FundamentalGroupoid.map g).map
      (default : FundamentalGroupoid.mk x ⟶ FundamentalGroupoid.mk y) :
        FundamentalGroupoid.mk (g x) ⟶ FundamentalGroupoid.mk (g y)) = default :=
    Subsingleton.elim _ _
  exact (FundamentalGroupoid.map_comp_map _ _ _).trans (congrArg _ h)

/-- A continuous map `h` sends a path class inside the image of `f` to the path class inside the
image of `h ∘ f`. -/
theorem map_pathClass (h : C(Y, Z)) (f : C(X, Y)) (x y : X) :
    (FundamentalGroupoid.map h).map (f.pathClass x y) = (h.comp f).pathClass x y :=
  (FundamentalGroupoid.map_comp_map _ _ _).symm

end ContinuousMap
