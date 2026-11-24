/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Topology.Sheaves.Skyscraper
public import TauCeti.Topology.Category.TopCat.Opens

/-!
# Skyscraper sheaves: restriction maps and the stalk adjunction unit

Let `A` be an object of a category with a terminal object `⊤_ C`, and suppose that the unique
morphism `A ⟶ ⊤_ C` is a split epimorphism, that is, that there is some morphism `⊤_ C ⟶ A`. This
holds for every `A` when `C` has a zero object. Then every restriction map of a skyscraper
presheaf with value `A` is a split epimorphism
(`TauCeti.Topology.isSplitEpi_skyscraperPresheaf_map`): it is an identity when its target
contains the point, and a morphism to a terminal object otherwise. Mathlib's
`isFlasque_skyscraperSheaf_of_epi_from` proves the weaker statement that these maps are
epimorphisms; split epimorphisms are moreover preserved by products of any size, which is what
makes products of skyscraper sheaves, such as Godement sheaves, flasque. A restriction map
from `U` to `V ≤ U` is moreover an isomorphism when `V` contains the point whenever `U` does
(`TauCeti.Topology.isIso_skyscraperPresheaf_map`).

The unit of Mathlib's adjunction `stalkSkyscraperSheafAdjunction x` between the stalk at `x` and
the skyscraper sheaf at `x` sends a section over an open containing `x` to its germ at `x`
(`TauCeti.Topology.stalkSkyscraperSheafAdjunction_unit_app_hom_app`), and on an open containing
`p₀`, `skyscraperSheafFunctor p₀` acts on a morphism by conjugating it with the canonical
identifications of the section objects
(`TauCeti.Topology.skyscraperSheafFunctor_map_hom_app_of_mem`).

Restricting the skyscraper presheaf at `f y` along an injective open map `f` gives the
skyscraper presheaf at `y`, naturally in its coefficient object
(`IsOpenMap.skyscraperPresheafFunctorCompWhiskeringLeftIso`). In particular, the restriction to
an open subset `U` of the skyscraper sheaf at a point `x` of `U` is the skyscraper sheaf at `x`
on `U` (`TopologicalSpace.Opens.skyscraperSheafFunctorCompSheafRestrictIso`). Together with the
adjunction between stalks and skyscraper sheaves, this computes the stalks of a left adjoint of
restriction, such as extension by zero.
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace TauCeti.Topology

/-- Global sections of the skyscraper sheaf at `p₀` are its coefficient object. -/
noncomputable def skyscraperSheafGlobalSectionsIso {X : TopCat} (p₀ : X)
    [∀ U : Opens X, Decidable (p₀ ∈ U)] {C : Type*} [Category* C] [HasTerminal C] (A : C) :
    (skyscraperSheaf p₀ A).obj.obj (op ⊤) ≅ A :=
  eqToIso ((skyscraperSheaf_obj_obj p₀ A (op ⊤)).trans
    (ite_eq_left (show p₀ ∈ (⊤ : Opens X) from trivial)))

/-- The global-section identification is the canonical transport from the value on `⊤`. -/
@[simp]
theorem skyscraperSheafGlobalSectionsIso_hom {X : TopCat} (p₀ : X)
    [∀ U : Opens X, Decidable (p₀ ∈ U)] {C : Type*} [Category* C] [HasTerminal C] (A : C) :
    (skyscraperSheafGlobalSectionsIso p₀ A).hom =
      eqToHom ((skyscraperSheaf_obj_obj p₀ A (op ⊤)).trans
        (ite_eq_left (show p₀ ∈ (⊤ : Opens X) from trivial))) := by rfl

/-- On an open set `U` containing `p₀`, the skyscraper sheaf functor acts on a morphism `f : A ⟶ B`
by `f` conjugated by the canonical identifications with `A` and `B`. -/
@[simp]
theorem skyscraperSheafFunctor_map_hom_app_of_mem {X : TopCat} (p₀ : X)
    [∀ U : Opens X, Decidable (p₀ ∈ U)] {C : Type*} [Category* C] [HasTerminal C]
    {A B : C} (f : A ⟶ B) {U : Opens X} (hU : p₀ ∈ U) :
    ((skyscraperSheafFunctor p₀).map f).hom.app (op U) =
      eqToHom (show ((skyscraperSheafFunctor p₀).obj A).obj.obj (op U) = A from ite_eq_left hU) ≫
        f ≫
        eqToHom (show B = ((skyscraperSheafFunctor p₀).obj B).obj.obj (op U)
          from (ite_eq_left hU).symm) :=
  -- By definition `((skyscraperSheafFunctor p₀).map f).hom` is
  -- `SkyscraperPresheafFunctor.map' p₀ f`.
  (SkyscraperPresheafFunctor.map'_app p₀ f (op U)).trans (dite_eq_left hU)

/-- If the unique morphism `A ⟶ ⊤_ C` is a split epimorphism, then the restriction maps of a
skyscraper presheaf with value `A` are split epimorphisms: each is an identity or a morphism to a
terminal object. -/
instance isSplitEpi_skyscraperPresheaf_map {X : TopCat} (p₀ : X)
    [∀ U : Opens X, Decidable (p₀ ∈ U)] {C : Type*} [Category* C] [HasTerminal C] (A : C)
    [IsSplitEpi (terminalIsTerminal.from A)] {U V : (Opens X)ᵒᵖ} (i : U ⟶ V) :
    IsSplitEpi ((skyscraperPresheaf p₀ A).map i) := by
  by_cases hV : p₀ ∈ unop V
  · have hU : p₀ ∈ unop U := leOfHom i.unop hV
    refine ⟨⟨eqToHom (by simp [hU, hV]), ?_⟩⟩
    simp only [skyscraperPresheaf_map, dite_eq_left hV]
    -- The composite passes through `(skyscraperPresheaf p₀ A).obj U`, which is `A` only up to
    -- unfolding, so the two `eqToHom`s are composed as a term.
    exact (eqToHom_trans _ _).trans (eqToHom_refl _ _)
  · -- The target is terminal, so any morphism into the source is a section.
    have s : ⊤_ C ⟶ (skyscraperPresheaf p₀ A).obj U := by
      by_cases hU : p₀ ∈ unop U
      · exact section_ (terminalIsTerminal.from A) ≫ eqToHom (ite_eq_left hU).symm
      · exact eqToHom (ite_eq_right hU).symm
    exact ⟨⟨terminal.from _ ≫ s, ((ite_eq_right hV).symm.ndrec terminalIsTerminal).hom_ext _ _⟩⟩

/-- A restriction map of a skyscraper presheaf is an isomorphism as soon as the smaller open
contains the point whenever the larger one does: it is then an identity, or a morphism between
terminal objects. -/
theorem isIso_skyscraperPresheaf_map {X : TopCat} (p₀ : X) [∀ U : Opens X, Decidable (p₀ ∈ U)]
    {C : Type*} [Category* C] [HasTerminal C] (A : C) {U V : (Opens X)ᵒᵖ} (i : U ⟶ V)
    (h : p₀ ∈ unop U → p₀ ∈ unop V) : IsIso ((skyscraperPresheaf p₀ A).map i) := by
  by_cases hV : p₀ ∈ unop V
  · rw [skyscraperPresheaf_map, dite_eq_left hV]
    exact Iso.isIso_hom (eqToIso (by simp [hV, leOfHom i.unop hV]))
  · exact isIso_of_isTerminal ((ite_eq_right (mt h hV)).symm.ndrec terminalIsTerminal)
      ((ite_eq_right hV).symm.ndrec terminalIsTerminal) _

/-- The unit of the adjunction between the stalk at `x` and the skyscraper sheaf at `x` sends a
section over an open `U` containing `x` to its germ at `x`. -/
@[simp]
theorem stalkSkyscraperSheafAdjunction_unit_app_hom_app {C : Type*}
    [Category.{u} C] [HasTerminal C] [HasColimits C] {X : TopCat.{u}} (x : X)
    [∀ U : Opens X, Decidable (x ∈ U)]
    (F : X.Sheaf C) {U : Opens X} (hx : x ∈ U) :
    ((stalkSkyscraperSheafAdjunction x).unit.app F).hom.app (op U) =
      F.presheaf.germ U x hx ≫ eqToHom (ite_eq_left hx).symm := by
  -- The unit of the sheaf adjunction is that of the presheaf adjunction on underlying presheaves.
  change ((StalkSkyscraperPresheafAdjunctionAuxs.unit x).app F.presheaf).app (op U) = _
  simp only [StalkSkyscraperPresheafAdjunctionAuxs.unit_app,
    StalkSkyscraperPresheafAdjunctionAuxs.toSkyscraperPresheaf_app, Functor.id_obj,
    Functor.comp_obj, TopCat.Presheaf.stalkFunctor_obj, Category.id_comp]
  exact dite_eq_left hx

end TauCeti.Topology

namespace IsOpenMap

variable {X Y : TopCat.{u}} {f : Y ⟶ X} (hf : IsOpenMap f) (hf' : Function.Injective f) (y : Y)
  {C : Type*} [Category* C] [HasTerminal C]
  [∀ V : Opens X, Decidable (f y ∈ V)] [∀ V : Opens Y, Decidable (y ∈ V)]

variable (C) in
/-- Restricting the skyscraper presheaf at `f y` along an injective open map `f` gives the
skyscraper presheaf at `y`, naturally in the coefficient object. -/
noncomputable def skyscraperPresheafFunctorCompWhiskeringLeftIso :
    skyscraperPresheafFunctor (C := C) (f y) ⋙ (Functor.whiskeringLeft _ _ C).obj hf.functor.op ≅
      skyscraperPresheafFunctor y :=
  NatIso.ofComponents (fun M ↦
    NatIso.ofComponents (F := hf.functor.op ⋙ skyscraperPresheaf (f y) M)
      (G := skyscraperPresheaf y M)
    (fun V ↦ eqToIso (by simp [hf.apply_mem_functor_obj_iff hf']))
    (fun {V W} i ↦ by
      by_cases hW : y ∈ W.unop
      · simp only [Functor.comp_obj, Functor.op_obj, Functor.comp_map, Functor.op_map,
          skyscraperPresheaf_map, hf.apply_mem_functor_obj_iff hf', hW, ↓reduceDIte, eqToIso.hom]
        -- Both sides are composites of canonical identifications. Their middle objects agree only
        -- after unfolding `skyscraperPresheaf`, so `simp` cannot merge them; `eqToHom_trans`
        -- merges each side as a term, and the results agree by proof irrelevance.
        exact (eqToHom_trans _ _).trans (eqToHom_trans _ _).symm
      · exact ((ite_eq_right hW).symm.ndrec terminalIsTerminal).hom_ext _ _))
    (fun g ↦ by
      ext V
      by_cases hV : y ∈ V.unop
      · dsimp only [Functor.comp_map, Functor.whiskeringLeft_obj_map, NatTrans.comp_app,
          Functor.whiskerLeft_app, NatIso.ofComponents_hom_app]
        simp only [Functor.comp_obj, Functor.whiskeringLeft_obj_obj, Functor.op_obj,
          skyscraperPresheafFunctor_map, SkyscraperPresheafFunctor.map'_app,
          hf.apply_mem_functor_obj_iff hf', hV, ↓reduceDIte, eqToIso.hom]
        -- Both sides are `g` conjugated by canonical identifications, which, as above, are merged
        -- by `eqToHom_trans` as terms.
        exact ((Category.assoc _ _ _).trans (congrArg (eqToHom _ ≫ ·)
          ((Category.assoc _ _ _).trans (congrArg (g ≫ ·) (eqToHom_trans _ _))))).trans
          (eqToHom_trans_assoc _ _ _).symm
      · exact ((ite_eq_right hV).symm.ndrec terminalIsTerminal).hom_ext _ _)

/-- The components of `IsOpenMap.skyscraperPresheafFunctorCompWhiskeringLeftIso` are the canonical
identifications of the section objects. -/
@[simp]
theorem skyscraperPresheafFunctorCompWhiskeringLeftIso_hom_app_app (M : C) (V : (Opens Y)ᵒᵖ) :
    ((hf.skyscraperPresheafFunctorCompWhiskeringLeftIso hf' y C).hom.app M).app V =
      eqToHom (by simp [hf.apply_mem_functor_obj_iff hf']) := by
  rfl

end IsOpenMap

namespace TopologicalSpace.Opens

variable {X : TopCat.{u}} (U : Opens X) (C : Type*) [Category.{u} C] [HasTerminal C] (x : U)
  [∀ V : Opens X, Decidable ((x : X) ∈ V)] [∀ V : Opens U, Decidable (x ∈ V)]

/- The inclusion of `U` is written with source the space `U` itself, so that skyscraper presheaves
on `U` and the image functor along the inclusion are indexed by the same type. -/
private lemma isOpenMap_ofHom_val :
    IsOpenMap (TopCat.ofHom (X := U) (Y := X) ⟨Subtype.val, continuous_subtypeVal⟩) :=
  U.isOpenEmbedding'.isOpenMap

/-- The restriction to an open subset `U` of the skyscraper sheaf at a point `x` of `U` is the
skyscraper sheaf at `x` on `U`, naturally in the coefficient object. -/
noncomputable def skyscraperSheafFunctorCompSheafRestrictIso :
    skyscraperSheafFunctor (C := C) (x : X) ⋙ U.sheafRestrict ≅
      skyscraperSheafFunctor (X := TopCat.of U) x :=
  NatIso.ofComponents
    (fun M ↦ ObjectProperty.isoMk _
      ((U.isOpenMap_ofHom_val.skyscraperPresheafFunctorCompWhiskeringLeftIso
        Subtype.val_injective x C).app M))
    (fun g ↦ by
      ext1
      exact (U.isOpenMap_ofHom_val.skyscraperPresheafFunctorCompWhiskeringLeftIso
        Subtype.val_injective x C).hom.naturality g)

/-- The components of `TopologicalSpace.Opens.skyscraperSheafFunctorCompSheafRestrictIso` are the
canonical identifications of the section objects. -/
@[simp]
theorem skyscraperSheafFunctorCompSheafRestrictIso_hom_app_hom_app (M : C) (V : (Opens U)ᵒᵖ) :
    ((U.skyscraperSheafFunctorCompSheafRestrictIso C x).hom.app M).hom.app V =
      eqToHom (if_congr (U.isOpenEmbedding'.isOpenMap.apply_mem_functor_obj_iff
        Subtype.val_injective) rfl rfl) := by
  rfl

end TopologicalSpace.Opens
