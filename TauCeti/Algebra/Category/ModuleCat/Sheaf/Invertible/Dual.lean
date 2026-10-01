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

Evaluation against the dual is an isomorphism for an invertible sheaf. This is first checked for
the standard free rank-one sheaf and then on a trivializing cover. Thus an invertible sheaf and
its dual are mutually inverse under tensor product.

## Main declarations

* `SheafOfModules.dual` is the internal-Hom dual of a sheaf of modules;
* `SheafOfModules.IsInvertible.dual` says that the dual of an invertible sheaf is invertible;
* `SheafOfModules.isIso_evaluation_dual_of_isInvertible` says that evaluation of an invertible
  sheaf against its dual is an isomorphism.

## References

* R. Hartshorne, *Algebraic Geometry*, Chapter II, Section 6.
* The Stacks Project, Section *Invertible modules*, Tag 01CR.

No formalization is vendored. The proof reuses Tau Ceti's internal-Hom restriction comparison and
Mathlib's local criterion for isomorphisms of sheaves.
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

/-- The internal-Hom dual of a sheaf of modules. -/
abbrev _root_.SheafOfModules.dual
    (M : _root_.SheafOfModules.{u} (ringCatSheaf R)) :
    _root_.SheafOfModules.{u} (ringCatSheaf R) :=
  (ihom M).obj (unit (ringCatSheaf R))

/-- The dual of the standard free rank-one sheaf is the standard free rank-one sheaf. -/
def _root_.SheafOfModules.dualFreePUnitIso :
    dual (free (R := ringCatSheaf R) PUnit) ≅ free (R := ringCatSheaf R) PUnit :=
  dualFreeIso (R := R) PUnit

/-- An isomorphism of sheaves induces an isomorphism of their duals. -/
def _root_.SheafOfModules.dualIso {M N : _root_.SheafOfModules.{u} (ringCatSheaf R)}
    (e : M ≅ N) : M.dual ≅ N.dual := by
  have hpre : IsIso (pre e.inv) := MonoidalClosed.pre_isIso e.symm
  exact asIso ((pre e.inv).app (unit (ringCatSheaf R)))

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
        (dualFreePUnitIso (R := R.over (t.X i))).symm ≪≫
          dualIso (R := R.over (t.X i)) (t.iso i) ≪≫
          (M.overDualIso R (t.X i)).symm }

/-- Evaluation of the standard free rank-one sheaf against its dual is an isomorphism. -/
instance _root_.SheafOfModules.isIso_evaluation_dual_freePUnit :
    IsIso ((ihom.ev (free (R := ringCatSheaf R) PUnit)).app
      (unit (ringCatSheaf R))) := by
  let ι := ιFree (R := ringCatSheaf R) PUnit.unit
  have : IsIso ι := by
    change IsIso (Sigma.ι
      (fun _ : PUnit.{u + 1} ↦ unit (ringCatSheaf R)) PUnit.unit)
    rw [← coproductUniqueIso_inv
      (fun _ : PUnit.{u + 1} ↦ unit (ringCatSheaf R))]
    infer_instance
  let ιdual := dualFreeι (R := R) PUnit.unit
  have : IsIso ιdual := by
    exact IsIso.of_isIso_fac_right (dualFreeι_comp_dualFreeIso_hom (R := R) PUnit.unit)
  have : IsIso (ι ⊗ₘ ιdual) := inferInstance
  have hevaluation := ιFree_tensorHom_dualFreeι_comp_ev (R := R) PUnit.unit
  have : IsIso ((ι ⊗ₘ ιdual) ≫
      (ihom.ev (free (R := ringCatSheaf R) PUnit)).app (unit (ringCatSheaf R))) :=
    hevaluation ▸ inferInstance
  exact IsIso.of_isIso_comp_left (ι ⊗ₘ ιdual)
    ((ihom.ev (free (R := ringCatSheaf R) PUnit)).app (unit (ringCatSheaf R)))

omit [∀ X, (J.over X).HasSheafCompose (forget₂ CommRingCat RingCat.{u})]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasPullbacks C] in
/-- Evaluation against the dual is an isomorphism for a sheaf isomorphic to the standard free
rank-one sheaf. -/
theorem _root_.SheafOfModules.isIso_evaluation_dual_of_iso_freePUnit
    (M : _root_.SheafOfModules.{u} (ringCatSheaf R))
    (e : free (R := ringCatSheaf R) PUnit ≅ M) :
    IsIso ((ihom.ev M).app (unit (ringCatSheaf R))) := by
  have h := id_tensor_pre_app_comp_ev e.hom (unit (ringCatSheaf R))
  have hpre : IsIso (pre e.hom) := MonoidalClosed.pre_isIso e
  have : IsIso ((pre e.hom).app (unit (ringCatSheaf R))) :=
    (NatTrans.isIso_iff_isIso_app (pre e.hom)).1 hpre _
  have : IsIso (free (R := ringCatSheaf R) PUnit ◁
      (pre e.hom).app (unit (ringCatSheaf R)) ≫
        (ihom.ev (free (R := ringCatSheaf R) PUnit)).app (unit (ringCatSheaf R))) :=
    inferInstance
  have : IsIso (e.hom ▷ M.dual ≫
      (ihom.ev M).app (unit (ringCatSheaf R))) := h ▸ inferInstance
  exact IsIso.of_isIso_comp_left (e.hom ▷ M.dual)
    ((ihom.ev M).app (unit (ringCatSheaf R)))

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
