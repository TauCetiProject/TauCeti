/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.Smooth.Center

/-!
# Examples for the smooth centre

For the trivial group the smooth centre is the coefficient ring. The image of a scalar acts on
every smooth representation as that scalar, and on morphisms the centre acts from either side.
-/

public section

open CategoryTheory Representation

namespace TauCeti

/-- For `G` trivial, `SmoothCenter A G ≅ A`. -/
noncomputable example (A : Type) [CommRing A] : A ≃ₐ[A] SmoothCenter.{0} A Unit :=
  SmoothCenter.algEquivOfSubsingleton A Unit

variable {A G : Type*} [CommRing A] [Group G] [TopologicalSpace G]

/-- The image of `a : A` in the smooth centre acts on the trivial representation `A` by `a`. -/
example (a b : A) :
    ((algebraMap A (SmoothCenter A G) a).app (SmoothRep.of (trivial A G A))).hom.hom b = a * b :=
  SmoothCenter.algebraMap_app_hom_hom_apply (V := SmoothRep.of (trivial A G A)) a b

/-- The centre acts on `Hom_G(V, W)` compatibly from both sides. -/
example (z : SmoothCenter A G) {V W : SmoothRep A G} (f : V ⟶ W) :
    z.app V ≫ f = f ≫ z.app W :=
  (z.naturality f).symm

end TauCeti
