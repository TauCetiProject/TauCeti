/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.NormalCone.OpenImmersion

/-!
# Examples: normal cones of the identity and of an empty source

Examples of normal cones (Fulton, *Intersection Theory*, §4.1):

* the identity of a scheme has zero conormal sheaf, and the projections of its normal cone and of
  its normal sheaf (the normal bundle) are isomorphisms;
* an immersion with empty source has empty normal cone and empty normal sheaf, for instance
  the empty scheme in `Spec R`.
-/

public section

open AlgebraicGeometry CategoryTheory Limits

namespace TauCeti.NormalConeExample

universe u

-- The identity has zero conormal sheaf.
example (X : Scheme.{u}) : IsZero (Scheme.Hom.conormal (𝟙 X)) :=
  Scheme.Hom.isZero_conormal _

-- The projection of the normal cone of the identity is an isomorphism.
example (X : Scheme.{u}) : IsIso (Scheme.Hom.normalConeToBase (𝟙 X)) :=
  inferInstance

-- The projection of the normal bundle `Spec_X (Sym (I/I²))` of the identity is an isomorphism.
example (X : Scheme.{u}) : IsIso (Scheme.Hom.normalSheafToBase (𝟙 X)) :=
  inferInstance

-- The normal cone of the identity is the scheme itself.
example (X : Scheme.{u}) : Nonempty (Scheme.Hom.normalCone (𝟙 X) ≅ X) :=
  ⟨asIso (Scheme.Hom.normalConeToBase (𝟙 X))⟩

-- An immersion with empty source has empty normal cone and empty normal sheaf.
example {X Y : Scheme.{u}} [IsEmpty X] (i : X ⟶ Y) [IsImmersion i] :
    IsEmpty i.normalCone ∧ IsEmpty i.normalSheaf :=
  ⟨inferInstance, inferInstance⟩

-- The empty scheme in `Spec R` has empty normal cone.
example (R : CommRingCat.{u}) :
    IsEmpty (Scheme.Hom.normalCone (initial.to (Spec R))) :=
  inferInstance

end TauCeti.NormalConeExample
