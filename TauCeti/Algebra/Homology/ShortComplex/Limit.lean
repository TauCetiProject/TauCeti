/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import TauCeti.Algebra.Homology.ShortComplex.PreservesHomology

/-!
# Homology and exact limits

This file proves that homology of short complexes, and hence homology of homological complexes,
commutes with limits of every shape whose limits are exact. Consequently a limit of
quasi-isomorphisms is a quasi-isomorphism when limits of that shape are exact.

## Main results

* `TauCeti.shortComplexHomologyFunctor_preservesLimitsOfShape`: homology of short complexes
  preserves limits of any exact shape.
* `TauCeti.homologicalComplexShortComplexFunctor_preservesLimitsOfShape`: the short complex
  associated to a homological complex preserves all existing limits.
* `TauCeti.homologicalComplexHomologyFunctor_preservesLimitsOfShape`: homology of homological
  complexes preserves limits of any exact shape.
* `TauCeti.quasiIso_limMap`: a limit of quasi-isomorphisms of homological complexes is a
  quasi-isomorphism when limits of that shape are exact.
* `TauCeti.quasiIso_pi_map`: a product of quasi-isomorphisms of homological complexes is a
  quasi-isomorphism when products of that shape are exact.

## Implementation notes

A diagram `F : J ⥤ ShortComplex C` corresponds under `ShortComplex.functorEquivalence` to a short
complex `S` of diagrams. The limiting cone used here is the image of `S` under
`lim : (J ⥤ C) ⥤ C`, with legs assembled from the counit of that equivalence. Working with the
counit rather than with the definitional identification of this cone with `ShortComplex.limitCone`
keeps every intermediate statement well typed for `rw` and `simp`: in a general category, unlike in
a concrete one, neither the unit laws nor associativity hold definitionally, so the composites
appearing here cannot be manipulated by `rfl` alone.

Exactness of `J`-shaped limits makes `lim` preserve homology, identifying the homology of this cone
with the chosen limit of the pointwise homology diagram.

## Sources

This file is the exact-limit dual of `TauCeti/Algebra/Homology/ShortComplex/Colimit`, and follows
that file's exact-colimit construction step for step. The formal inputs are Joël Riou's short
complex API in Mathlib — `ShortComplex.functorEquivalence` in
`Mathlib/Algebra/Homology/ShortComplex/FunctorEquivalence`, `ShortComplex.isLimitOfIsLimitπ` in
`Mathlib/Algebra/Homology/ShortComplex/Limits`, `ShortComplex.mapHomologyIso` and
`NatTrans.app_homology` in `Mathlib/Algebra/Homology/ShortComplex/PreservesHomology` and
`Mathlib/Algebra/Homology/ShortComplex/HomologicalComplex` — together with the exactness class
`HasExactLimitsOfShape` of Dagur Asgeirsson, Isaac Hernando, Coleton Kotch and Adam Topaz in
`Mathlib/CategoryTheory/Abelian/GrothendieckAxioms/Basic`.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v w w'

variable {C : Type u} [Category.{v} C]

section

variable {J : Type w} [Category.{w'} J] [HasLimitsOfShape J C]

section HasZeroMorphisms

variable [HasZeroMorphisms C]

private theorem lim_π_comp_mapNatTrans_evaluation
    (F : J ⥤ ShortComplex C) {X Y : J} (f : X ⟶ Y) :
    ((ShortComplex.functorEquivalence J C).inverse.obj F).mapNatTrans (lim.π X) ≫
        ((ShortComplex.functorEquivalence J C).inverse.obj F).mapNatTrans
          ((evaluation J C).map f) =
      ((ShortComplex.functorEquivalence J C).inverse.obj F).mapNatTrans (lim.π Y) := by
  ext <;>
    simp only [ShortComplex.comp_τ₁, ShortComplex.comp_τ₂, ShortComplex.comp_τ₃,
      ShortComplex.mapNatTrans_τ₁, ShortComplex.mapNatTrans_τ₂, ShortComplex.mapNatTrans_τ₃,
      evaluation_map_app, lim.π_app] <;>
    exact limit.w _ f

/-- The cone on `F : J ⥤ ShortComplex C` obtained by applying `lim` to the associated short
complex of diagrams. -/
private noncomputable def shortComplexLimCone (F : J ⥤ ShortComplex C) : Cone F where
  pt := ((ShortComplex.functorEquivalence J C).inverse.obj F).map lim
  π :=
    { app := fun j ↦
        ((ShortComplex.functorEquivalence J C).inverse.obj F).mapNatTrans (lim.π j) ≫
          (ShortComplex.diagramEvaluationIso F j).hom
      naturality := fun _ _ f ↦ by
        dsimp
        rw [Category.id_comp, Category.assoc,
          ← ShortComplex.diagramEvaluationIso_hom_naturality,
          ← Category.assoc, lim_π_comp_mapNatTrans_evaluation] }

/-- The cone `shortComplexLimCone F` is limiting: each of its three components is the chosen limit
cone of the corresponding diagram in `C`, up to the identities contributed by the counit of
`ShortComplex.functorEquivalence`. -/
private noncomputable def isLimitShortComplexLimCone (F : J ⥤ ShortComplex C) :
    IsLimit (shortComplexLimCone F) :=
  ShortComplex.isLimitOfIsLimitπ _
    (IsLimit.ofIsoLimit (limit.isLimit (F ⋙ ShortComplex.π₁))
      (Cone.ext (Iso.refl _) fun _ ↦ by
        dsimp [shortComplexLimCone, ShortComplex.π₁]
        rw [ShortComplex.diagramEvaluationIso_hom_τ₁]
        exact (Category.comp_id _).symm.trans (Category.id_comp _).symm))
    (IsLimit.ofIsoLimit (limit.isLimit (F ⋙ ShortComplex.π₂))
      (Cone.ext (Iso.refl _) fun _ ↦ by
        dsimp [shortComplexLimCone, ShortComplex.π₂]
        rw [ShortComplex.diagramEvaluationIso_hom_τ₂]
        exact (Category.comp_id _).symm.trans (Category.id_comp _).symm))
    (IsLimit.ofIsoLimit (limit.isLimit (F ⋙ ShortComplex.π₃))
      (Cone.ext (Iso.refl _) fun _ ↦ by
        dsimp [shortComplexLimCone, ShortComplex.π₃]
        rw [ShortComplex.diagramEvaluationIso_hom_τ₃]
        exact (Category.comp_id _).symm.trans (Category.id_comp _).symm))

end HasZeroMorphisms

variable [Abelian C] [HasExactLimitsOfShape J C]

private theorem shortComplex_mapHomologyIso_limit (F : J ⥤ ShortComplex C) (j : J) :
    (((ShortComplex.functorEquivalence J C).inverse.obj F).mapHomologyIso lim).inv ≫
        ShortComplex.homologyMap
          (((ShortComplex.functorEquivalence J C).inverse.obj F).mapNatTrans (lim.π j)) =
      limit.π ((ShortComplex.functorEquivalence J C).inverse.obj F).homology j ≫
        (((ShortComplex.functorEquivalence J C).inverse.obj F).mapHomologyIso
          ((evaluation J C).obj j)).inv := by
  -- Since `(lim.π j).app G = limit.π G j`, the projection on the right is the component of
  -- `NatTrans.app_homology (lim.π j)` on `(ShortComplex.functorEquivalence J C).inverse.obj F`.
  rw [Iso.eq_comp_inv, Category.assoc]
  exact (NatTrans.app_homology (lim.π j)
    ((ShortComplex.functorEquivalence J C).inverse.obj F)).symm

private theorem shortComplexHomologyLimit_compatibility
    (F : J ⥤ ShortComplex C) (j : J) :
    limit.π ((ShortComplex.functorEquivalence J C).inverse.obj F).homology j ≫
        ((((ShortComplex.functorEquivalence J C).inverse.obj F).mapHomologyIso
             ((evaluation J C).obj j)).inv ≫
          ShortComplex.homologyMap (ShortComplex.diagramEvaluationIso F j).hom) =
      (((ShortComplex.functorEquivalence J C).inverse.obj F).mapHomologyIso lim).inv ≫
        ShortComplex.homologyMap
          (((ShortComplex.functorEquivalence J C).inverse.obj F).mapNatTrans (lim.π j) ≫
            (ShortComplex.diagramEvaluationIso F j).hom) := by
  rw [ShortComplex.homologyMap_comp, ← Category.assoc, ← Category.assoc,
    shortComplex_mapHomologyIso_limit]

/-- Homology of the limit cone `shortComplexLimCone F` is the chosen limit of the pointwise
homology diagram of `F`. -/
private noncomputable def shortComplexHomologyLimitConeIso (F : J ⥤ ShortComplex C) :
    (Cone.postcompose (ShortComplex.homologyDiagramIso F).inv).obj
        (limit.cone ((ShortComplex.functorEquivalence J C).inverse.obj F).homology) ≅
      (ShortComplex.homologyFunctor C).mapCone (shortComplexLimCone F) :=
  Cone.ext (((ShortComplex.functorEquivalence J C).inverse.obj F).mapHomologyIso lim).symm
    (fun j ↦ by
      dsimp [shortComplexLimCone, ShortComplex.homologyFunctor]
      rw [ShortComplex.homologyDiagramIso_inv_app, shortComplexHomologyLimit_compatibility])

/-- Homology of short complexes preserves limits of any exact shape. -/
instance shortComplexHomologyFunctor_preservesLimitsOfShape :
    PreservesLimitsOfShape J (ShortComplex.homologyFunctor C) where
  preservesLimit {F} :=
    preservesLimit_of_preserves_limit_cone
      (isLimitShortComplexLimCone F)
      ((IsLimit.equivOfNatIsoOfIso
        (ShortComplex.homologyDiagramIso F).symm
        (limit.cone ((ShortComplex.functorEquivalence J C).inverse.obj F).homology)
        ((ShortComplex.homologyFunctor C).mapCone (shortComplexLimCone F))
        (shortComplexHomologyLimitConeIso F)) (limit.isLimit _))

variable {I D : Type*} [Category D] [HasZeroMorphisms D] [HasLimitsOfShape J D]
  (c : ComplexShape I) (q : I)

/-- Sending a homological complex to its short complex at one degree preserves all existing
limits. -/
instance homologicalComplexShortComplexFunctor_preservesLimitsOfShape :
    PreservesLimitsOfShape J
      (HomologicalComplex.shortComplexFunctor D c q) where
  preservesLimit {F} := by
    apply preservesLimit_of_preserves_limit_cone (limit.isLimit F)
    apply ShortComplex.isLimitOfIsLimitπ
    · exact isLimitOfPreserves (HomologicalComplex.eval D c (c.prev q))
        (limit.isLimit F)
    · exact isLimitOfPreserves (HomologicalComplex.eval D c q)
        (limit.isLimit F)
    · exact isLimitOfPreserves (HomologicalComplex.eval D c (c.next q))
        (limit.isLimit F)

/-- Homology in any degree of a homological complex preserves limits of any exact shape. -/
instance homologicalComplexHomologyFunctor_preservesLimitsOfShape :
    PreservesLimitsOfShape J
      (HomologicalComplex.homologyFunctor C c q) := by
  exact preservesLimitsOfShape_of_natIso
    (HomologicalComplex.homologyFunctorIso C c q).symm

variable {c}

/-- **Limits of quasi-isomorphisms.** If limits of shape `J` are exact, a morphism of `J`-shaped
diagrams of homological complexes which is a quasi-isomorphism at every index induces a
quasi-isomorphism on limits: homology commutes with these limits. -/
theorem quasiIso_limMap {F G : J ⥤ HomologicalComplex C c} (φ : F ⟶ G)
    (hφ : ∀ j, QuasiIso (φ.app j)) : QuasiIso (limMap φ) := by
  rw [quasiIso_iff]
  intro q
  rw [quasiIsoAt_iff_isIso_homologyMap]
  let H := HomologicalComplex.homologyFunctor C c q
  have (j : J) : IsIso ((Functor.whiskerRight φ H).app j) :=
    (quasiIsoAt_iff_isIso_homologyMap (φ.app j) q).mp ((hφ j).quasiIsoAt q)
  have : IsIso (Functor.whiskerRight φ H) := NatIso.isIso_of_isIso_app _
  have : IsIso (H.map (limMap φ) ≫ limit.post G H) := by
    rw [limit.map_post]
    infer_instance
  exact IsIso.of_isIso_comp_right (H.map (limMap φ)) (limit.post G H)

end

/-- **Products of quasi-isomorphisms.** If products indexed by `β` are exact, the product of a
family of quasi-isomorphisms of homological complexes is a quasi-isomorphism. -/
theorem quasiIso_pi_map [Abelian C] {I : Type*} {c : ComplexShape I}
    {β : Type w} [HasLimitsOfShape (Discrete β) C]
    [HasExactLimitsOfShape (Discrete β) C] {K L : β → HomologicalComplex C c}
    (φ : ∀ b, K b ⟶ L b) (hφ : ∀ b, QuasiIso (φ b)) : QuasiIso (Limits.Pi.map φ) :=
  quasiIso_limMap (F := Discrete.functor K) (G := Discrete.functor L)
    (Discrete.natTrans fun b ↦ φ b.as) fun b ↦ hφ b.as

end TauCeti
