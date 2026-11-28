/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.DerivedCategory.RightDerivedFunctor.Homology.Plus
public import TauCeti.CategoryTheory.Abelian.RightDerived.Evaluation
public import TauCeti.Topology.Sheaves.SupportedCohomology.Sections
public import TauCeti.CategoryTheory.Abelian.Injective.Ext

/-!
# Derived supported sections and supported Ext groups

For a closed subset `S` and an open `W`, the supported-section functor
`F ↦ Γ_S(W,F)` is represented by the relative free module sheaf `Q_S(W)`.
Right deriving this representation identifies its native right derived functors
with the existing supported cohomology groups `Extⁿ(Q_S(W),F)`, naturally in `F`.
Thus supported Ext groups and derived supported sections are two computations of
the same functor, rather than unrelated cohomology carriers. The comparison also
commutes with restriction to smaller opens: right deriving supported-section
restriction gives the existing restriction in `supportedModuleHPresheaf`. The openwise
comparisons assemble into an isomorphism of presheaves and identify the bounded below derived
computation on each open.

The construction uses `Closeds.supportedFreeModuleSheafHomEquiv` for the
representation, `NatIso.rightDerived` for its transport, and
`CategoryTheory.rightDerivedLinearCoyonedaIsoExt` for the injective-resolution
computation of Ext. No flasqueness hypothesis on the coefficient sheaf is needed.

## References

* A. Grothendieck, *Local cohomology*, Lecture Notes in Mathematics 41, §1.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace

universe u w w'

namespace CategoryTheory.Sheaf

variable {X : TopCat.{u}} {R : Type u} [CommRing R] (S : Closeds X) (W : Opens X)

noncomputable section

/-- The relative free module sheaf `Q_S(W)` represents sections on `W` supported in `S`,
naturally in the coefficient sheaf. -/
def supportedSubmoduleSectionsRepresentableIso :
    (linearCoyoneda R _).obj (op ((S.supportedFreeModuleSheafFunctor R).obj W)) ≅
      supportedSubmoduleSectionsFunctor (R := R) S W :=
  NatIso.ofComponents (fun F ↦ (S.supportedFreeModuleSheafHomEquiv R W F).toModuleIso)
    fun {F G} f ↦ by
      ext g
      apply Subtype.ext
      -- The functor's section object is bundled by evaluation; the ambient-section
      -- computation lemma avoids unfolding the supported-section lift.
      change (S.supportedFreeModuleSheafHomEquiv R W G (g ≫ f) : G.obj.obj (op W)) =
        Subtype.val (p := (· ∈ G.supportedSubmodule S W))
          ((supportedSubmoduleSectionsFunctor S W).map f
            (S.supportedFreeModuleSheafHomEquiv R W F g))
      exact (S.coe_supportedFreeModuleSheafHomEquiv_comp R W g f).trans
        (coe_supportedSubmoduleFunctor_map_hom_app_apply S f (op W) _).symm

/-- The representing isomorphism sends a morphism out of `Q_S(W)` to its supported section. -/
-- Rewrite before functor evaluation simplifies the bundled section object.
@[simp↓]
lemma supportedSubmoduleSectionsRepresentableIso_hom_app_apply
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (g : (S.supportedFreeModuleSheafFunctor R).obj W ⟶ F) :
    (supportedSubmoduleSectionsRepresentableIso (R := R) S W).hom.app F g =
      S.supportedFreeModuleSheafHomEquiv R W F g :=
  (rfl)

/-- The inverse representing isomorphism recovers the morphism associated with a supported
section. -/
-- Rewrite before functor evaluation simplifies the bundled section object.
@[simp↓]
lemma supportedSubmoduleSectionsRepresentableIso_inv_app_apply
    (F : Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))
    (s : F.supportedSubmodule S W) :
    (supportedSubmoduleSectionsRepresentableIso (R := R) S W).inv.app F s =
      (S.supportedFreeModuleSheafHomEquiv R W F).symm s :=
  (rfl)

/-- The representation of supported sections by `Q_S(W)` respects restriction of opens. -/
@[reassoc]
lemma supportedSubmoduleSectionsRepresentableIso_hom_restrict {W' : Opens X} (i : W' ⟶ W) :
    (linearCoyoneda R _).map ((S.supportedFreeModuleSheafFunctor R).map i).op ≫
        (supportedSubmoduleSectionsRepresentableIso (R := R) S W').hom =
      (supportedSubmoduleSectionsRepresentableIso (R := R) S W).hom ≫
        supportedSubmoduleSectionsRestrict S i := by
  ext F g
  apply Subtype.ext
  -- Unbundle composition and the linear coyoneda action before using the opaque
  -- representing isomorphism's application lemmas.
  change (((supportedSubmoduleSectionsRepresentableIso (R := R) S W').hom.app F)
      ((S.supportedFreeModuleSheafFunctor R).map i ≫ g)).val =
    (((supportedSubmoduleSectionsRestrict (R := R) S i).app F)
      (((supportedSubmoduleSectionsRepresentableIso (R := R) S W).hom.app F) g)).val
  -- `erw` identifies the evaluated `linearCoyoneda` module containing `g` with
  -- the sheaf Hom module, and the evaluated section module with its supported subtype.
  -- Plain `rw` cannot typecheck `map i ≫ g` across the first of these wrappers.
  erw [supportedSubmoduleSectionsRepresentableIso_hom_app_apply,
    coe_supportedSubmoduleSectionsRestrict_app_apply,
    supportedSubmoduleSectionsRepresentableIso_hom_app_apply]
  exact S.coe_supportedFreeModuleSheafHomEquiv_map_comp R i F g

/-- Right derived supported sections are the supported Ext groups, naturally in the
coefficient sheaf. The target evaluates the existing supported cohomology presheaf on `W`. -/
def rightDerivedSupportedSubmoduleSectionsIso (n : ℕ) :
    (supportedSubmoduleSectionsFunctor (R := R) S W).rightDerived n ≅
      supportedModuleHPresheafFunctor (R := R) S n ⋙
        (evaluation (Opens X)ᵒᵖ (ModuleCat.{u} R)).obj (op W) :=
  (NatIso.rightDerived (supportedSubmoduleSectionsRepresentableIso (R := R) S W) n).symm ≪≫
    rightDerivedLinearCoyonedaIsoExt R
    ((S.supportedFreeModuleSheafFunctor R).obj W) n

/-- The derived comparison is the transport of the canonical derived Hom-to-Ext
comparison along the supported-section representation. This characterizes its normalization. -/
@[reassoc (attr := simp)]
lemma rightDerivedSupportedSubmoduleSectionsIso_hom_comp (n : ℕ) :
    (supportedSubmoduleSectionsRepresentableIso (R := R) S W).hom.rightDerived n ≫
        (rightDerivedSupportedSubmoduleSectionsIso (R := R) S W n).hom =
      (rightDerivedLinearCoyonedaIsoExt R
        ((S.supportedFreeModuleSheafFunctor R).obj W) n).hom := by
  have h :=
    (NatIso.rightDerived (supportedSubmoduleSectionsRepresentableIso S W) n).hom_inv_id_assoc
      (rightDerivedLinearCoyonedaIsoExt R ((S.supportedFreeModuleSheafFunctor R).obj W) n).hom
  rw [NatIso.rightDerived_hom] at h
  exact h

/-- The derived supported-section-to-Ext comparison commutes with restriction in every
cohomological degree, naturally in the coefficient sheaf. -/
@[reassoc]
lemma rightDerivedSupportedSubmoduleSectionsIso_hom_restrict {W' W : Opens X}
    (i : W' ⟶ W) (n : ℕ) :
    (supportedSubmoduleSectionsRestrict (R := R) S i).rightDerived n ≫
        (rightDerivedSupportedSubmoduleSectionsIso (R := R) S W' n).hom =
      (rightDerivedSupportedSubmoduleSectionsIso (R := R) S W n).hom ≫
        Functor.whiskerLeft (supportedModuleHPresheafFunctor S n)
          ((evaluation (Opens X)ᵒᵖ (ModuleCat.{u} R)).map i.op) := by
  have : IsIso ((supportedSubmoduleSectionsRepresentableIso (R := R) S W).hom.rightDerived n) := by
    rw [← NatIso.rightDerived_hom]
    infer_instance
  apply (cancel_epi
    ((supportedSubmoduleSectionsRepresentableIso (R := R) S W).hom.rightDerived n)).1
  rw [← Category.assoc, ← NatTrans.rightDerived_comp,
    ← supportedSubmoduleSectionsRepresentableIso_hom_restrict,
    NatTrans.rightDerived_comp, Category.assoc,
    rightDerivedSupportedSubmoduleSectionsIso_hom_comp,
    rightDerivedSupportedSubmoduleSectionsIso_hom_comp_assoc]
  exact rightDerivedLinearCoyonedaIsoExt_hom_naturality_left R _
    ((S.supportedFreeModuleSheafFunctor R).map i) n

section Presheaf

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
      simp only [NatTrans.comp_app, Functor.whiskerLeft_app] at he
      simp only [Iso.trans_hom, Iso.app_hom]
      rw [evaluation_map_app] at he
      rw [reassoc_of% he, hr, evaluation_map_app, Category.assoc]))
    (fun f ↦ by
      apply NatTrans.ext
      funext W
      simp only [NatTrans.comp_app, NatIso.ofComponents_hom_app, Iso.trans_hom, Iso.app_hom,
        Category.assoc]
      have he := ((P).rightDerivedEvaluationIso n W).hom.naturality f
      have hr := (rightDerivedSupportedSubmoduleSectionsIso (R := R) S W.unop n).hom.naturality f
      have rightDerived_congr {E E' : Sheaf J A ⥤ A} [E.Additive] [E'.Additive] (h : E = E') :
          E.rightDerived n = E'.rightDerived n := by
        subst E'
        rfl
      have hEval := rightDerived_congr
        (supportedSubmoduleSectionsFunctor_eq_evaluation (R := R) S W).symm
      have hMap := eq_of_heq (Functor.hcongr_hom hEval f)
      simp only [Functor.comp_map, evaluation_obj_map] at he hr
      rw [hMap] at he
      rw [reassoc_of% he, hr])

/-- The presheaf comparison on an open is evaluation followed by the Ext comparison
for supported sections on that open. -/
@[simp]
lemma rightDerivedSupportedSubmodulePresheafIso_hom_app_app (n : ℕ) (F : Sheaf J A)
    (W : (Opens X)ᵒᵖ) :
    ((rightDerivedSupportedSubmodulePresheafIso S n).hom.app F).app W =
      ((P).rightDerivedEvaluationIso n W).hom.app F ≫
        (rightDerivedSupportedSubmoduleSectionsIso S W.unop n).hom.app F :=
  (rfl)

section BoundedBelow

open DerivedCategory

variable [HasDerivedCategory.{w} (Sheaf (Opens.grothendieckTopology X) (ModuleCat.{u} R))]
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

/-- The bounded below comparison on an open is the classical supported Ext comparison
after identifying the bounded below cohomology with the classical derived functors. -/
@[reassoc]
lemma rightDerivedFunctorPlusSupportedSubmoduleSectionsHomologyIso_hom (W : Opens X) (n : ℕ) :
    (rightDerivedFunctorPlusSupportedSubmoduleSectionsHomologyIso (R := R) S W n).hom =
      ((supportedSubmoduleSectionsFunctor (R := R) S W).rightDerivedFunctorPlusHomologyIso n).hom ≫
        (rightDerivedSupportedSubmoduleSectionsIso S W n).hom :=
  (rfl)

/-- The bounded below supported-section comparison intertwines derived restriction on
supported sections with restriction on supported Ext. -/
@[reassoc]
lemma rightDerivedFunctorPlusSupportedSubmoduleSectionsHomologyIso_hom_restrict
    {W' W : Opens X} (i : W' ⟶ W) (n : ℕ) :
    Functor.whiskerLeft (Plus.singleFunctor (Sheaf J (ModuleCat.{u} R)) 0)
      (Functor.whiskerRight
        (supportedSubmoduleSectionsRestrict (R := R) S i).rightDerivedFunctorPlus
        (Plus.homologyFunctor (ModuleCat.{u} R) n)) ≫
      (rightDerivedFunctorPlusSupportedSubmoduleSectionsHomologyIso S W' n).hom =
    (rightDerivedFunctorPlusSupportedSubmoduleSectionsHomologyIso S W n).hom ≫
      Functor.whiskerLeft (supportedModuleHPresheafFunctor S n) ((ev).map i.op) := by
  rw [rightDerivedFunctorPlusSupportedSubmoduleSectionsHomologyIso_hom,
    rightDerivedFunctorPlusSupportedSubmoduleSectionsHomologyIso_hom, ← Category.assoc,
    Functor.rightDerivedFunctorPlusHomologyIso_hom_naturality, Category.assoc,
    rightDerivedSupportedSubmoduleSectionsIso_hom_restrict, ← Category.assoc]

end BoundedBelow

end Presheaf

end

end CategoryTheory.Sheaf
