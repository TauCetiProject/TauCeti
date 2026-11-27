/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.Descent.BandedMorphism.BandEquivalence

/-!
# Checks for band preservation along modifications and inverse equivalences

* The identity invertible modification of `η` leaves its band preservation unchanged.
* For an invertible modification `e : η ≅ θ`, band preservation of `θ` gives back that of `η`
  through `e.symm`.
* The inverse of a band-carrying fibre equivalence sends the band automorphism of `a` at `y` to
  that of the same coefficient `a` at `P⁻¹ y`.
-/

public section

namespace TauCeti.Examples.GerbeBandEquivalence

open CategoryTheory CategoryTheory.Pseudofunctor Opposite Bicategory
open scoped Pseudofunctor.StrongTrans
open GerbeBandEquivalence

variable {C : Type*} [Category* C] {F G : LocallyDiscrete Cᵒᵖ ⥤ᵖ Cat}
  {J : GrothendieckTopology C} {A : Sheaf J AddCommGrpCat}
  {bF : F.AbelianBanding J A} {bG : G.AbelianBanding J A}

/-- The identity modification leaves band preservation unchanged. -/
example (η : F ⟶ G) : BandPreserving bF bG η ↔ BandPreserving bF bG η :=
  modificationIso_iff (Iso.refl η)

/-- Band preservation of `θ` gives that of `η` through the inverse modification. -/
example {η θ : F ⟶ G} (e : η ≅ θ) [BandPreserving bF bG θ] : BandPreserving bF bG η :=
  of_modificationIso e.symm

/-- The inverse of a band-carrying equivalence carries the same coefficient. -/
example {U : C} (P : F.obj (.mk (op U)) ⥤ G.obj (.mk (op U))) [P.IsEquivalence]
    (hP : MapsBand bF bG U P) (y : G.obj (.mk (op U))) (a : Multiplicative (A.obj.obj (op U))) :
    P.inv.mapAut y (bG.mulEquiv U y a) = bF.mulEquiv U (P.inv.obj y) a :=
  mapsBand_iff.1 (inverse_map_band hP) y a

end TauCeti.Examples.GerbeBandEquivalence
