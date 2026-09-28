/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.TensorProduct.Restriction.Closed

/-!
# Internal Hom under restriction on finite free charts

The internal-Hom comparison for restriction to a slice is invertible when its source sheaf is
equipped with a finite basis. This transports the finite-free calculation across the basis
isomorphism (`SheafOfModules.overIhomComparison_isIso_of_iso_free`), so it applies to the
actual sheaf rather than only to the chosen standard free model. It therefore supplies the
hypothesis of the restriction formulas `SheafOfModules.overIhomIso` and
`SheafOfModules.overDualIso` for internal Hom and for the dual.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed

namespace TauCeti

universe u

noncomputable section

namespace SheafOfModules

open _root_.SheafOfModules

variable {C : Type u} [SmallCategory C]
  {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  {R : Sheaf J CommRingCat.{u}}
  {M : _root_.SheafOfModules.{u} (ringCatSheaf R)}

/-- The monoidal structure on sheaves of modules over the restriction of `R` to `X`. -/
local instance finiteFreeLocalMonoidalCategory (X : C) : MonoidalCategory
    (_root_.SheafOfModules.{u} ((ringCatSheaf R).over X)) :=
  monoidalCategory (R.over X)

/-- The closed monoidal structure on sheaves of modules over the restriction of `R` to `X`. -/
local instance finiteFreeLocalMonoidalClosed (X : C) : MonoidalClosed
    (_root_.SheafOfModules.{u} ((ringCatSheaf R).over X)) :=
  monoidalClosed (R.over X)

/-- A finite basis makes the internal-Hom comparison for restriction invertible. -/
theorem _root_.SheafOfModules.GeneratingSections.isIso_overIhomComparison
    (σ : M.GeneratingSections) [IsIso σ.π] [Finite σ.I] (X : C) :
    IsIso (M.overIhomComparison R X).natTrans :=
  overIhomComparison_isIso_of_iso_free R X σ.I (asIso σ.π).symm

end SheafOfModules

end

end TauCeti
