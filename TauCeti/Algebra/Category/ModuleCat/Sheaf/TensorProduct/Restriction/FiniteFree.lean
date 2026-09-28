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
isomorphism, so it applies to the actual sheaf on a chart rather than only to the chosen standard
free model.

The resulting natural isomorphism gives the restriction formula for internal Hom on a finite free
chart. Specializing its target to the tensor unit gives the corresponding restriction formula for
the dual, including the monoidal unit comparison. These formulas are the local compatibility used
to descend duals and tensor--Hom comparisons for finite locally free sheaves.
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

/-- Restriction to a slice inverts the internal-Hom comparison out of any sheaf isomorphic to a
finite free sheaf. -/
theorem overIhomComparison_isIso_of_iso_free (X : C) (I : Type u) [Finite I]
    (e : M ≅ free (R := ringCatSheaf R) I) :
    IsIso (M.overIhomComparison R X).natTrans := by
  let F := _root_.SheafOfModules.overFunctor (ringCatSheaf R) X
  have hfree : IsIso (F.ihomComparison (free (R := ringCatSheaf R) I)).natTrans := by
    rw [← overIhomComparison_eq_ihomComparison R X]
    exact overIhomComparison_free_isIso R X I
  have h := CategoryTheory.Functor.ihomComparison_isIso_of_iso F hfree e
  rw [overIhomComparison_eq_ihomComparison R X]
  exact h

/-- A finite basis makes the internal-Hom comparison for restriction invertible. -/
theorem _root_.SheafOfModules.GeneratingSections.isIso_overIhomComparison
    (σ : M.GeneratingSections) [IsIso σ.π] [Finite σ.I] (X : C) :
    IsIso (M.overIhomComparison R X).natTrans :=
  overIhomComparison_isIso_of_iso_free X σ.I (asIso σ.π).symm

/-- The restriction formula for internal Hom out of a sheaf equipped with a finite basis. -/
def _root_.SheafOfModules.GeneratingSections.overIhomIso
    (σ : M.GeneratingSections) [IsIso σ.π] [Finite σ.I] (X : C) :
    ihom M ⋙ _root_.SheafOfModules.overFunctor (ringCatSheaf R) X ≅
      _root_.SheafOfModules.overFunctor (ringCatSheaf R) X ⋙ ihom (M.over X) := by
  letI := σ.isIso_overIhomComparison (R := R) X
  exact asIso (M.overIhomComparison R X).natTrans

/-- The forward map of the finite-basis internal-Hom restriction isomorphism is the canonical
internal-Hom comparison. -/
@[simp]
theorem _root_.SheafOfModules.GeneratingSections.overIhomIso_hom_app
    (σ : M.GeneratingSections) [IsIso σ.π] [Finite σ.I] (X : C)
    (N : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    (σ.overIhomIso (R := R) X).hom.app N =
      (M.overIhomComparison R X).natTrans.app N := by
  simp only [GeneratingSections.overIhomIso, asIso_hom]

/-- The restriction formula for the internal-Hom dual of a sheaf equipped with a finite basis.
The target is the internal Hom into the tensor unit on the slice site. -/
def _root_.SheafOfModules.GeneratingSections.overDualIso
    (σ : M.GeneratingSections) [IsIso σ.π] [Finite σ.I] (X : C) :
    ((ihom M).obj (unit (ringCatSheaf R))).over X ≅
      (ihom (M.over X)).obj (unit ((ringCatSheaf R).over X)) :=
  (σ.overIhomIso (R := R) X).app (unit (ringCatSheaf R)) ≪≫
    (ihom (M.over X)).mapIso (_root_.SheafOfModules.overUnitIso (R := R) X)

/-- The forward dual restriction map is the internal-Hom comparison followed by the image of the
monoidal unit comparison. -/
@[simp]
theorem _root_.SheafOfModules.GeneratingSections.overDualIso_hom
    (σ : M.GeneratingSections) [IsIso σ.π] [Finite σ.I] (X : C) :
    (σ.overDualIso (R := R) X).hom =
      (M.overIhomComparison R X).natTrans.app (unit (ringCatSheaf R)) ≫
        (ihom (M.over X)).map (_root_.SheafOfModules.overUnitIso (R := R) X).hom := by
  simp only [GeneratingSections.overDualIso, Iso.trans_hom, Iso.app_hom,
    GeneratingSections.overIhomIso_hom_app]
  rfl

end SheafOfModules

end

end TauCeti
