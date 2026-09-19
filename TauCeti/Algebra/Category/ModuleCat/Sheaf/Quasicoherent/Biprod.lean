/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Basic.Finite.Sum
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Quasicoherent.Refinement
public import TauCeti.Algebra.Category.ModuleCat.Sheaf.Restriction
public import TauCeti.CategoryTheory.Limits.Shapes.Biproduct
public import TauCeti.CategoryTheory.Sites.CoversTop

/-!
# Direct sums of quasi-coherent and locally free sheaves of modules

Let `R` be a sheaf of rings on a site with pullbacks. This file shows that the binary biproduct
(direct sum) `M ⊞ N` of two sheaves of `R`-modules is quasi-coherent, of finite type, finitely
presented, or locally free as soon as `M` and `N` are. In particular, direct sums of finite
locally free sheaves (locally free and finitely presented) are finite locally free.

The local input is that generating sections, and presentations, of `M` and `N` give generating
sections, and a presentation, of `M ⊞ N`: the free sheaf on `I ⊕ I'` is `free I ⊞ free I'`
(`SheafOfModules.freeBiprodIso`), and the biproduct of two cokernels is a cokernel
(`CategoryTheory.Limits.CokernelCofork.isColimitBiprod`). Restriction to a slice site is additive,
so it commutes with direct sums (`SheafOfModules.overBiprodIso`), and the local data of `M` and `N`
are compared on a common refinement of their covers.

The common-refinement construction follows the tensor-product closure formalization in
`SheafOfModules.QuasicoherentData.tensor`.

## Main declarations

* `SheafOfModules.GeneratingSections.biprod` and `SheafOfModules.Presentation.biprod`: the
  generating sections and the presentation of `M ⊞ N` built from those of `M` and `N`;
* `SheafOfModules.LocalGeneratorsData.biprod` and `SheafOfModules.QuasicoherentData.biprod`: their
  local versions, on a common refinement of the two covers;
* `TauCeti.SheafOfModules.isQuasicoherent_biprod`, `TauCeti.SheafOfModules.isFiniteType_biprod`,
  `TauCeti.SheafOfModules.isFinitePresentation_biprod` and
  `TauCeti.SheafOfModules.isLocallyFree_biprod`.
-/

public section

open CategoryTheory Limits

namespace TauCeti

universe u v₁ u₁

noncomputable section

namespace SheafOfModules

open _root_.SheafOfModules

section Global

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The direct sum of the free sheaves of modules on `I` and on `I'` is the free sheaf of modules
on `I ⊕ I'`. -/
def freeBiprodIso (I I' : Type u) : free (R := R) I ⊞ free I' ≅ free (I ⊕ I') :=
  biprod.isoCoprod _ _ ≪≫ freeSumIso I I'

@[reassoc (attr := simp)]
theorem inl_freeBiprodIso_hom (I I' : Type u) :
    biprod.inl ≫ (freeBiprodIso (R := R) I I').hom = freeMap Sum.inl := by
  simp [freeBiprodIso]

@[reassoc (attr := simp)]
theorem inr_freeBiprodIso_hom (I I' : Type u) :
    biprod.inr ≫ (freeBiprodIso (R := R) I I').hom = freeMap Sum.inr := by
  simp [freeBiprodIso]

@[reassoc (attr := simp)]
theorem freeMap_inl_freeBiprodIso_inv (I I' : Type u) :
    freeMap (R := R) Sum.inl ≫ (freeBiprodIso I I').inv = biprod.inl := by
  rw [← cancel_mono (freeBiprodIso I I').hom]
  simp

@[reassoc (attr := simp)]
theorem freeMap_inr_freeBiprodIso_inv (I I' : Type u) :
    freeMap (R := R) Sum.inr ≫ (freeBiprodIso I I').inv = biprod.inr := by
  rw [← cancel_mono (freeBiprodIso I I').hom]
  simp

variable {M N : SheafOfModules.{u} R}

/-- Generating sections of `M` and of `N` give generating sections of `M ⊞ N`, indexed by the
disjoint union of the two index types. -/
@[expose]
def _root_.SheafOfModules.GeneratingSections.biprod (G : M.GeneratingSections)
    (H : N.GeneratingSections) : (M ⊞ N).GeneratingSections where
  I := G.I ⊕ H.I
  s := (M ⊞ N).freeHomEquiv ((freeBiprodIso _ _).inv ≫ biprod.map G.π H.π)
  epi := by
    rw [Equiv.symm_apply_apply]
    infer_instance

@[simp]
theorem _root_.SheafOfModules.GeneratingSections.biprod_I (G : M.GeneratingSections)
    (H : N.GeneratingSections) : (G.biprod H).I = (G.I ⊕ H.I) :=
  (rfl)

/-- The generating morphism of `G.biprod H` is the direct sum of the generating morphisms, read
through `freeBiprodIso`. -/
@[simp]
theorem _root_.SheafOfModules.GeneratingSections.biprod_π (G : M.GeneratingSections)
    (H : N.GeneratingSections) :
    (G.biprod H).π = (freeBiprodIso _ _).inv ≫ biprod.map G.π H.π :=
  (M ⊞ N).freeHomEquiv.symm_apply_apply _

instance _root_.SheafOfModules.GeneratingSections.isFiniteType_biprod
    (G : M.GeneratingSections) (H : N.GeneratingSections) [hG : G.IsFiniteType]
    [hH : H.IsFiniteType] : (G.biprod H).IsFiniteType where
  finite :=
    have := hG.finite
    have := hH.finite
    inferInstanceAs (Finite (G.I ⊕ H.I))

instance _root_.SheafOfModules.GeneratingSections.isIso_biprod_π (G : M.GeneratingSections)
    (H : N.GeneratingSections) [hG : IsIso G.π] [hH : IsIso H.π] :
    IsIso (G.biprod H).π := by
  rw [GeneratingSections.biprod_π]
  exact IsIso.comp_isIso' (Iso.isIso_inv _)
    (biprod.mapIso (@asIso _ _ _ _ _ hG) (@asIso _ _ _ _ _ hH)).isIso_hom

/-- Presentations of `M` and of `N` give a presentation of `M ⊞ N`: its generators and its
relations are indexed by the disjoint unions of those of `M` and `N`. -/
@[expose]
def _root_.SheafOfModules.Presentation.biprod (P : M.Presentation) (Q : N.Presentation) :
    (M ⊞ N).Presentation :=
  presentationOfIsCokernelFree
    ((freeBiprodIso _ _).inv ≫
      biprod.map ((freeHomEquiv _).symm P.relations.s ≫ kernel.ι _)
        ((freeHomEquiv _).symm Q.relations.s ≫ kernel.ι _) ≫ (freeBiprodIso _ _).hom)
    ((freeBiprodIso _ _).inv ≫ biprod.map P.generators.π Q.generators.π)
    (by
      have h : Limits.biprod.map ((freeHomEquiv _).symm P.relations.s ≫ kernel.ι _)
          ((freeHomEquiv _).symm Q.relations.s ≫ kernel.ι _) ≫
            Limits.biprod.map P.generators.π Q.generators.π = 0 := by
        apply biprod.hom_ext' <;> simp
      simp [h]) <|
  IsCokernel.ofIso _ (CokernelCofork.isColimitBiprod P.isColimit Q.isColimit) _
    (freeBiprodIso _ _) (freeBiprodIso _ _) (Iso.refl _) (by simp) (by simp)

@[simp]
theorem _root_.SheafOfModules.Presentation.biprod_generators (P : M.Presentation)
    (Q : N.Presentation) : (P.biprod Q).generators = P.generators.biprod Q.generators :=
  (rfl)

@[simp]
theorem _root_.SheafOfModules.Presentation.biprod_relations_I (P : M.Presentation)
    (Q : N.Presentation) : (P.biprod Q).relations.I = (P.relations.I ⊕ Q.relations.I) :=
  (rfl)

private theorem relationsOfIsCokernelFree_π {M : SheafOfModules.{u} R} {ι σ : Type u}
    (f : free ι ⟶ free σ) (g : free σ ⟶ M) (H : f ≫ g = 0)
    (H' : IsColimit (CokernelCofork.ofπ g H)) :
    (relationsOfIsCokernelFree f g H H').π =
      kernel.lift (generatorsOfIsCokernelFree f g H H').π f
        (by rw [generatorsOfIsCokernelFree_π]; exact H) :=
  (kernel (generatorsOfIsCokernelFree f g H H').π).freeHomEquiv.symm_apply_apply _

private theorem relationsOfIsCokernelFree_π_kernel_ι {M : SheafOfModules.{u} R}
    {ι σ : Type u} (f : free ι ⟶ free σ) (g : free σ ⟶ M) (H : f ≫ g = 0)
    (H' : IsColimit (CokernelCofork.ofπ g H)) :
    (relationsOfIsCokernelFree f g H H').π ≫
      kernel.ι (generatorsOfIsCokernelFree f g H H').π = f := by
  rw [relationsOfIsCokernelFree_π]
  apply kernel.lift_ι

/-- The relation morphism of the direct-sum presentation is the direct sum of the two relation
morphisms, read through the free-sheaf biproduct isomorphisms. -/
@[simp]
theorem _root_.SheafOfModules.Presentation.biprod_relations_π (P : M.Presentation)
    (Q : N.Presentation) :
    (P.biprod Q).relations.π ≫ kernel.ι (P.biprod Q).generators.π =
      (freeBiprodIso _ _).inv ≫
        biprod.map (P.relations.π ≫ kernel.ι P.generators.π)
          (Q.relations.π ≫ kernel.ι Q.generators.π) ≫ (freeBiprodIso _ _).hom := by
  unfold Presentation.biprod
  apply relationsOfIsCokernelFree_π_kernel_ι

/-- The direct sum of two finite presentations is finite. -/
instance (P : M.Presentation) (Q : N.Presentation) [P.IsFinite] [Q.IsFinite] :
    (P.biprod Q).IsFinite where
  isFiniteType_generators := by rw [Presentation.biprod_generators]; infer_instance
  isFiniteType_relations := ⟨by rw [Presentation.biprod_relations_I]; infer_instance⟩

end Global

section Local

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M N : SheafOfModules.{u} R}

variable (M N) in
/-- Restriction to a slice site commutes with direct sums. -/
def _root_.SheafOfModules.overBiprodIso (X : C) : (M ⊞ N).over X ≅ M.over X ⊞ N.over X :=
  have := preservesBinaryBiproducts_of_preservesBiproducts (overFunctor.{u} R X)
  (overFunctor R X).mapBiprod M N

@[reassoc (attr := simp)]
theorem inl_overBiprodIso_inv (X : C) :
    biprod.inl ≫ (overBiprodIso M N X).inv = (biprod.inl : M ⟶ M ⊞ N).over X := by
  simp only [overBiprodIso, Functor.mapBiprod_inv]
  exact biprod.inl_desc _ _

@[reassoc (attr := simp)]
theorem inr_overBiprodIso_inv (X : C) :
    biprod.inr ≫ (overBiprodIso M N X).inv = (biprod.inr : N ⟶ M ⊞ N).over X := by
  simp only [overBiprodIso, Functor.mapBiprod_inv]
  exact biprod.inr_desc _ _

@[reassoc (attr := simp)]
theorem overBiprodIso_hom_fst (X : C) :
    (overBiprodIso M N X).hom ≫ biprod.fst = (biprod.fst : M ⊞ N ⟶ M).over X := by
  simp only [overBiprodIso, Functor.mapBiprod_hom]
  exact biprod.lift_fst _ _

@[reassoc (attr := simp)]
theorem overBiprodIso_hom_snd (X : C) :
    (overBiprodIso M N X).hom ≫ biprod.snd = (biprod.snd : M ⊞ N ⟶ N).over X := by
  simp only [overBiprodIso, Functor.mapBiprod_hom]
  exact biprod.lift_snd _ _

variable [HasPullbacks C]

/-- Local generators of `M` and of `N` give local generators of `M ⊞ N`. Its cover is the common
refinement of the two covers, and over each of its members the generators are the direct sum of
the restricted generators of `M` and `N`. -/
@[expose, simps I X generators]
def _root_.SheafOfModules.LocalGeneratorsData.biprod (qM : M.LocalGeneratorsData)
    (qN : N.LocalGeneratorsData) : (M ⊞ N).LocalGeneratorsData :=
  let r := GrothendieckTopology.CoversTop.commonRefinement qM.coversTop qN.coversTop
  { I := r.I
    X := r.X
    coversTop := r.coversTop
    generators i := GeneratingSections.equivOfIso (overBiprodIso M N (r.X i)).symm
      (((qM.ofRefinement r.X r.coversTop r.leftIndex r.left).generators i).biprod
        ((qN.ofRefinement r.X r.coversTop r.rightIndex r.right).generators i)) }

/-- The direct sum of locally free data is locally free data. -/
instance (qM : M.LocalGeneratorsData) (qN : N.LocalGeneratorsData) [qM.IsLocallyFreeData]
    [qN.IsLocallyFreeData] : (qM.biprod qN).IsLocallyFreeData where
  -- The index is taken in the common refinement, so that the refined generators of `M` and `N`
  -- are indexed by it syntactically; their invertibility is supplied explicitly.
  isIso := fun (i : (qM.coversTop.commonRefinement qN.coversTop).I) ↦
    GeneratingSections.isIso_equivOfIso_π _ _
      (hσ := GeneratingSections.isIso_biprod_π _ _
        (hG := LocalGeneratorsData.IsLocallyFreeData.isIso (q := qM.ofRefinement _ _ _ _) i)
        (hH := LocalGeneratorsData.IsLocallyFreeData.isIso (q := qN.ofRefinement _ _ _ _) i))

/-- The direct sum of local generators of finite type is of finite type. -/
instance (qM : M.LocalGeneratorsData) (qN : N.LocalGeneratorsData) [qM.IsFiniteType]
    [qN.IsFiniteType] : (qM.biprod qN).IsFiniteType where
  isFiniteType := fun (i : (qM.coversTop.commonRefinement qN.coversTop).I) ↦
    GeneratingSections.isFiniteType_equivOfIso _ _
      (hσ := GeneratingSections.isFiniteType_biprod _ _
        (hG := LocalGeneratorsData.IsFiniteType.isFiniteType (p := qM.ofRefinement _ _ _ _) i)
        (hH := LocalGeneratorsData.IsFiniteType.isFiniteType (p := qN.ofRefinement _ _ _ _) i))

/-- Quasi-coherent data for `M` and for `N` give quasi-coherent data for `M ⊞ N`. Its cover is the
common refinement of the two covers, and over each of its members the presentation is the direct
sum of the restricted presentations of `M` and `N`. -/
@[expose, simps I X presentation]
def _root_.SheafOfModules.QuasicoherentData.biprod (qM : M.QuasicoherentData)
    (qN : N.QuasicoherentData) : (M ⊞ N).QuasicoherentData :=
  let r := GrothendieckTopology.CoversTop.commonRefinement qM.coversTop qN.coversTop
  { I := r.I
    X := r.X
    coversTop := r.coversTop
    presentation i :=
      (((qM.ofRefinement r.X r.coversTop r.leftIndex r.left).presentation i).biprod
        ((qN.ofRefinement r.X r.coversTop r.rightIndex r.right).presentation i)).ofIsIso
        (overBiprodIso M N (r.X i)).inv }

/-- The direct sum of finite quasi-coherent data is finite. -/
instance (qM : M.QuasicoherentData) (qN : N.QuasicoherentData) [qM.IsFinitePresentation]
    [qN.IsFinitePresentation] : (qM.biprod qN).IsFinitePresentation where
  isFinite_presentation := fun (i : (qM.coversTop.commonRefinement qN.coversTop).I) ↦
    let r := qM.coversTop.commonRefinement qN.coversTop
    -- Restricting and transporting a presentation keep its index types, and the direct sum of
    -- two presentations is indexed by the disjoint unions of their index types, by construction.
    { isFiniteType_generators := ⟨inferInstanceAs (Finite
        ((qM.presentation (r.leftIndex i)).generators.I ⊕
          (qN.presentation (r.rightIndex i)).generators.I))⟩
      isFiniteType_relations := ⟨inferInstanceAs (Finite
        ((qM.presentation (r.leftIndex i)).relations.I ⊕
          (qN.presentation (r.rightIndex i)).relations.I))⟩ }

/-- The direct sum of two locally free sheaves of modules is locally free. -/
instance isLocallyFree_biprod [M.IsLocallyFree] [N.IsLocallyFree] : (M ⊞ N).IsLocallyFree := by
  obtain ⟨qM, _⟩ := IsLocallyFree.exists_isLocallyFreeData (M := M)
  obtain ⟨qN, _⟩ := IsLocallyFree.exists_isLocallyFreeData (M := N)
  exact (qM.biprod qN).isLocallyFree

/-- The direct sum of two sheaves of modules of finite type is of finite type. -/
instance isFiniteType_biprod [M.IsFiniteType] [N.IsFiniteType] : (M ⊞ N).IsFiniteType := by
  obtain ⟨qM, _⟩ := IsFiniteType.exists_localGeneratorsData M
  obtain ⟨qN, _⟩ := IsFiniteType.exists_localGeneratorsData N
  exact ⟨qM.biprod qN, inferInstance⟩

/-- The direct sum of two quasi-coherent sheaves of modules is quasi-coherent. -/
instance isQuasicoherent_biprod [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⊞ N).IsQuasicoherent :=
  ((IsQuasicoherent.nonempty_quasicoherentData (M := M)).some.biprod
    (IsQuasicoherent.nonempty_quasicoherentData (M := N)).some).isQuasicoherent

/-- The direct sum of two finitely presented sheaves of modules is finitely presented. -/
instance isFinitePresentation_biprod [M.IsFinitePresentation] [N.IsFinitePresentation] :
    (M ⊞ N).IsFinitePresentation := by
  obtain ⟨qM, _⟩ := IsFinitePresentation.exists_quasicoherentData M
  obtain ⟨qN, _⟩ := IsFinitePresentation.exists_quasicoherentData N
  exact ⟨qM.biprod qN, inferInstance⟩

end Local

end SheafOfModules

end

end TauCeti
