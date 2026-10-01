/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Dualizable
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Invertible.LocalTriviality

/-!
# Duals of invertible sheaves

The dual of an invertible sheaf of modules is its internal Hom into the tensor unit. It is again
invertible: on a rank-one trivializing cover, restriction commutes with internal Hom and the dual
of the standard free rank-one sheaf is standard free rank one.

Evaluation against the dual is an isomorphism for an invertible sheaf. Thus an invertible sheaf
and its dual are mutually inverse under tensor product.

## Main declarations

* `SheafOfModules.IsInvertible.dual` says that the dual of an invertible sheaf is invertible;
* `SheafOfModules.isIso_evaluation_dual_of_isInvertible` says that evaluation of an invertible
  sheaf against its dual is an isomorphism.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Section 6.
* The Stacks Project, Section *Invertible modules*, Tag 01CR.
-/

public section

open CategoryTheory Limits MonoidalCategory MonoidalClosed

namespace TauCeti

universe u

noncomputable section

namespace SheafOfModules

open _root_.SheafOfModules

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [HasWeakSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, (J.over X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasPullbacks C]
  {R : Sheaf J CommRingCat.{u}}

/-- The monoidal structure on sheaves of modules over the restriction of `R` to `X`. -/
local instance invertibleDualMonoidalCategory (X : C) : MonoidalCategory
    (_root_.SheafOfModules.{u} ((ringCatSheaf R).over X)) :=
  monoidalCategory (R.over X)

/-- The closed monoidal structure on sheaves of modules over the restriction of `R` to `X`. -/
local instance invertibleDualMonoidalClosed (X : C) : MonoidalClosed
    (_root_.SheafOfModules.{u} ((ringCatSheaf R).over X)) :=
  monoidalClosed (R.over X)

/-- The dual of an invertible sheaf of modules is invertible. -/
instance _root_.SheafOfModules.IsInvertible.dual
    (M : _root_.SheafOfModules.{u} (ringCatSheaf R)) [IsInvertible M] :
    IsInvertible M.dual := by
  let t := LocalTrivializations.ofIsInvertible M
  refine LocalTrivializations.isInvertible
    { I := t.I
      X := t.X
      coversTop := t.coversTop
      iso := fun i ↦
        (dualFreeIso (R := R.over (t.X i)) PUnit).symm ≪≫
          dualIso (R := R.over (t.X i)) (t.iso i) ≪≫
          (M.overDualIso R (t.X i)).symm }

/-- Evaluation of an invertible sheaf against its internal-Hom dual is an isomorphism. -/
instance _root_.SheafOfModules.isIso_evaluation_dual_of_isInvertible
    (M : _root_.SheafOfModules.{u} (ringCatSheaf R)) [IsInvertible M] :
    IsIso ((ihom.ev M).app (unit (ringCatSheaf R))) := by
  let t := LocalTrivializations.ofIsInvertible M
  refine isIso_of_coversTop t.coversTop _ fun i ↦ ?_
  let F := overFunctor (ringCatSheaf R) (t.X i)
  have heval : IsIso ((ihom.ev (M.over (t.X i))).app
      (unit ((ringCatSheaf R).over (t.X i)))) :=
    isIso_evaluation_dual_of_iso_freePUnit (R := R.over (t.X i))
      (M.over (t.X i)) (t.iso i)
  have : IsIso (F.ihomComparison M).natTrans := by
    rw [← overIhomComparison_def]
    infer_instance
  have : IsIso ((F.ihomComparison M).natTrans.app (unit (ringCatSheaf R))) :=
    NatIso.isIso_app_of_isIso _ _
  have : IsIso (Functor.OplaxMonoidal.η F) := inferInstance
  have : IsIso ((ihom (M.over (t.X i))).map (Functor.OplaxMonoidal.η F)) := inferInstance
  have : IsIso ((F.ihomComparison M).natTrans.app (unit (ringCatSheaf R)) ≫
      (ihom (M.over (t.X i))).map (Functor.OplaxMonoidal.η F)) := inferInstance
  have : IsIso (M.over (t.X i) ◁
      ((F.ihomComparison M).natTrans.app (unit (ringCatSheaf R)) ≫
        (ihom (M.over (t.X i))).map (Functor.OplaxMonoidal.η F))) := inferInstance
  have h := F.whiskerLeft_ihomComparison_app_unit_comp_map_η_comp_ev M
  have hlocal : IsIso (M.over (t.X i) ◁
      ((F.ihomComparison M).natTrans.app (unit (ringCatSheaf R)) ≫
        (ihom (M.over (t.X i))).map (Functor.OplaxMonoidal.η F)) ≫
      (ihom.ev (M.over (t.X i))).app (unit ((ringCatSheaf R).over (t.X i)))) :=
    IsIso.comp_isIso' inferInstance heval
  have hglobal : IsIso (Functor.LaxMonoidal.μ F M M.dual ≫
      F.map ((ihom.ev M).app (unit (ringCatSheaf R))) ≫
      Functor.OplaxMonoidal.η F) := h ▸ hlocal
  have : IsIso (Functor.LaxMonoidal.μ F M M.dual) := inferInstance
  have : IsIso (Functor.LaxMonoidal.μ F M M.dual ≫
      F.map ((ihom.ev M).app (unit (ringCatSheaf R)))) :=
    IsIso.of_isIso_comp_right _ (Functor.OplaxMonoidal.η F)
  exact IsIso.of_isIso_comp_left (Functor.LaxMonoidal.μ F M M.dual) _

end SheafOfModules

end

end TauCeti
