/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.RightDerivedFunctor.Homology.Plus
public import TauCeti.CategoryTheory.Abelian.RightDerived.Evaluation
public import TauCeti.Topology.Sheaves.LocalCohomology.Module
public import TauCeti.Topology.Sheaves.SupportedCohomology.Derived

/-!
# Local cohomology as derived supported sections

For a closed subset `S`, deriving the sheaf-valued supported-section functor gives the local
cohomology sheaf. On an injective resolution, cohomology before sheafification can be computed
on each open by the supported Ext comparison. Exactness of sheafification then identifies
the two sheaf-valued functors.

The cohomology of the bounded below derived functors on a sheaf placed in degree zero
therefore computes both the supported Ext groups on opens and the local cohomology sheaves.

## References

* M. Kashiwara and P. Schapira, *Sheaves on Manifolds*, §2.6.
-/

public section

noncomputable section

open CategoryTheory Limits Opposite TopologicalSpace

universe u w w'

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} {R : Type u} [CommRing R] (S : Closeds X)

local notation "J" => Opens.grothendieckTopology X
local notation "A" => ModuleCat R
local notation "P" => supportedSubmoduleFunctor (R := R) S ⋙ sheafToPresheaf J A
local notation "ev" => evaluation (Opens X)ᵒᵖ A

/-- The presheaf-valued right derived functors of supported sections agree with the
supported Ext presheaves. The isomorphism on each open is the supported-section-to-Ext
comparison evaluated on that open. -/
def rightDerivedSupportedSubmodulePresheafIso (n : ℕ) :
    (P).rightDerived n ≅ supportedModuleHPresheafFunctor (R := R) S n :=
  NatIso.ofComponents (fun F ↦ NatIso.ofComponents
    (fun W ↦ ((P).rightDerivedEvaluationIso n W).app F ≪≫
      (rightDerivedSupportedSubmoduleSectionsIso (R := R) S W.unop n).app F)
    (fun i ↦ by
      have he := congrArg (fun τ ↦ τ.app F)
        ((P).rightDerivedEvaluationIso_hom_naturality n i)
      have hr := congrArg (fun τ ↦ τ.app F)
        (rightDerivedSupportedSubmoduleSectionsIso_hom_restrict (R := R) S i.unop n)
      simp only [supportedSubmoduleSectionsRestrict_eq_whiskerLeft_evaluation,
        NatTrans.comp_app, Functor.whiskerLeft_app, Quiver.Hom.op_unop] at hr
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app, evaluation_map_app] at he
      simp only [Iso.trans_hom, Iso.app_hom]
      -- The two evaluation functors act by the respective presheaf restrictions.
      erw [← Category.assoc, he, Category.assoc]
      rw [Category.assoc]
      exact congrArg (_ ≫ ·) hr))
    (fun f ↦ by
      apply NatTrans.ext
      funext W
      simp only [NatTrans.comp_app, NatIso.ofComponents_hom_app, Iso.trans_hom, Iso.app_hom,
        Category.assoc]
      -- Convert the presheaf components to the maps of the evaluated functors.
      erw [((P).rightDerivedEvaluationIso n W).hom.naturality_assoc,
        (rightDerivedSupportedSubmoduleSectionsIso (R := R) S W.unop n).hom.naturality]
      rfl)

/-- The presheaf comparison on an open is evaluation followed by the Ext comparison
for supported sections on that open. -/
@[simp]
lemma rightDerivedSupportedSubmodulePresheafIso_hom_app_app (n : ℕ) (F : Sheaf J A)
    (W : (Opens X)ᵒᵖ) :
    ((rightDerivedSupportedSubmodulePresheafIso S n).hom.app F).app W =
      ((P).rightDerivedEvaluationIso n W).hom.app F ≫
        (rightDerivedSupportedSubmoduleSectionsIso S W.unop n).hom.app F :=
  (rfl)

/-- The sheaf-valued right derived functors of supported sections are the local cohomology
sheaves, naturally in the coefficient sheaf. -/
def rightDerivedSupportedSubmoduleIso (n : ℕ) :
    (supportedSubmoduleFunctor (R := R) S).rightDerived n ≅
      supportedModuleHSheafFunctor (R := R) S n := by
  let L := presheafToSheaf J (ModuleCat.{u} R)
  have : L.Additive := inferInstanceAs ((presheafToSheaf J (ModuleCat.{u} R)).Additive)
  have : L.PreservesHomology :=
    inferInstanceAs ((presheafToSheaf J (ModuleCat.{u} R)).PreservesHomology)
  let e : P ⋙ L ≅ 𝟭 (Sheaf J A) ⋙ supportedSubmoduleFunctor (R := R) S :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (sheafificationNatIso J A).symm ≪≫
      Functor.rightUnitor _ ≪≫ (Functor.leftUnitor _).symm
  exact (Functor.leftUnitor _).symm ≪≫
    (Functor.rightDerivedCompIso P L (𝟭 _) (supportedSubmoduleFunctor S) e n).symm ≪≫
    Functor.isoWhiskerRight (rightDerivedSupportedSubmodulePresheafIso (R := R) S n) L

section BoundedBelow

open DerivedCategory

variable [HasDerivedCategory.{w} (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))]

/-- On a sheaf in degree zero, the bounded below derived supported-section sheaf has
cohomology equal to the local cohomology sheaf in every nonnegative degree. -/
def rightDerivedFunctorPlusSupportedSubmoduleHomologyIso (n : ℕ) :
    Plus.singleFunctor (Sheaf J (ModuleCat.{u} R)) 0 ⋙
        (supportedSubmoduleFunctor (R := R) S).rightDerivedFunctorPlus ⋙
        Plus.homologyFunctor (Sheaf J (ModuleCat.{u} R)) n ≅
      supportedModuleHSheafFunctor (R := R) S n :=
  (supportedSubmoduleFunctor (R := R) S).rightDerivedFunctorPlusHomologyIso n ≪≫
    rightDerivedSupportedSubmoduleIso S n

variable [HasDerivedCategory.{w'} (ModuleCat.{u} R)]

/-- On a sheaf in degree zero, the bounded below derived functor of supported sections on
an open has cohomology equal to the supported Ext groups on that open. -/
def rightDerivedFunctorPlusSupportedSubmoduleSectionsHomologyIso (W : Opens X) (n : ℕ) :
    Plus.singleFunctor (Sheaf J (ModuleCat.{u} R)) 0 ⋙
        (supportedSubmoduleSectionsFunctor (R := R) S W).rightDerivedFunctorPlus ⋙
        Plus.homologyFunctor (ModuleCat.{u} R) n ≅
      supportedModuleHPresheafFunctor (R := R) S n ⋙ (ev).obj (op W) :=
  (supportedSubmoduleSectionsFunctor (R := R) S W).rightDerivedFunctorPlusHomologyIso n ≪≫
    rightDerivedSupportedSubmoduleSectionsIso S W n

end BoundedBelow

end CategoryTheory.Sheaf
