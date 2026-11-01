/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Skyscraper sheaves: split restriction maps and the stalk adjunction unit

Let `A` be an object of a category with a terminal object `⊤_ C`, and suppose that the unique
morphism `A ⟶ ⊤_ C` is a split epimorphism, that is, that there is some morphism `⊤_ C ⟶ A`. This
holds for every `A` when `C` has a zero object. Then every restriction map of a skyscraper
presheaf with value `A` is a split epimorphism
(`TauCeti.Topology.isSplitEpi_skyscraperPresheaf_map`): it is an identity when its target
contains the point, and a morphism to a terminal object otherwise. Mathlib's
`isFlasque_skyscraperSheaf_of_epi_from` proves the weaker statement that these maps are
epimorphisms; split epimorphisms are moreover preserved by products of any size, which is what
makes products of skyscraper sheaves, such as Godement sheaves, flasque.

The unit of Mathlib's adjunction `stalkSkyscraperSheafAdjunction x` between the stalk at `x` and
the skyscraper sheaf at `x` sends a section over an open containing `x` to its germ at `x`
(`TauCeti.Topology.stalkSkyscraperSheafAdjunction_unit_app_hom_app`).
-/

public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace TauCeti.Topology

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
