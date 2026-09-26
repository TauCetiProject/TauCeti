/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Dual
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Monoidal
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Restriction of finite free sheaves

Restriction to a slice carries a finite free sheaf of modules to a free sheaf on the same finite
index type. The isomorphism uses the description of a finite free sheaf as a finite biproduct of
copies of the tensor unit: restriction preserves both the unit and finite biproducts.

This is the local free-module calculation needed when comparing internal Homs and duals after
restriction.

The preservation-of-biproducts argument adapts Mathlib's
`CategoryTheory.Functor.preservesFiniteBiproductsOfAdditive` to a finite index type in the
sheaf's universe.
-/

public section

open CategoryTheory Limits MonoidalCategory

namespace TauCeti

universe u

noncomputable section

namespace SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
variable [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {R : Sheaf J CommRingCat.{u}} (X : C) (I : Type u) [Finite I]

/-- Restriction of a finite free sheaf is isomorphic to a free sheaf on the same finite index
type. -/
def overFreeIso :
    (_root_.SheafOfModules.free (R := ringCatSheaf R) I).over X ≅
      _root_.SheafOfModules.free (R := (ringCatSheaf R).over X) I := by
  let F := _root_.SheafOfModules.overFunctor (ringCatSheaf R) X
  letI : F.Additive := inferInstance
  haveI := Fintype.ofFinite I
  letI : PreservesBiproduct (fun _ : I ↦ 𝟙_ (_root_.SheafOfModules (ringCatSheaf R))) F :=
    ⟨fun {b} hb => ⟨isBilimitOfTotal _ (by
      -- The mapped bicone has the mapped legs; this presentation avoids unfolding its point.
      change (∑ i, F.map (b.π i) ≫ F.map (b.ι i)) = 𝟙 _
      simpa only [← F.map_comp, ← F.map_sum, F.map_id] using
        congrArg F.map (IsBilimit.total hb))⟩⟩
  exact (F.mapIso (biproductIsoFree (R := R) I).symm) ≪≫
    (F.mapBiproduct (fun _ : I ↦ 𝟙_ (_root_.SheafOfModules (ringCatSheaf R)))) ≪≫
    (biproduct.mapIso (fun _ ↦ (_root_.SheafOfModules.overUnitIso (R := R) X).symm)) ≪≫
    biproductIsoFree (R := R.over X) I

end SheafOfModules

end

end TauCeti
