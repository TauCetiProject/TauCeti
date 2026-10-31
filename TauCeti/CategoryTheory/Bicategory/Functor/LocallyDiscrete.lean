/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete

/-!
# Prelax functors and locally discrete bicategories

In a locally discrete bicategory every `2`-morphism `η : f ⟶ g` forces `f = g`, so a prelax
functor (in particular a pseudofunctor) sends `η` to an `eqToHom`. This lets the coherence
data of a pseudofunctor out of `LocallyDiscrete B₀`, such as `F.map₂ (α_ f g h).hom`, be
computed componentwise.

Dually, the unit and composition comparisons of a pseudofunctor `P` into a locally discrete
bicategory are determined by equalities of `1`-morphisms. So the comparisons of a composite
`P.comp F` are the flexible comparisons `F.mapId'` and `F.mapComp'` of `F` at the images of
`P`, for instance for `P = Functor.toPseudofunctor ψ` induced by a functor of categories.
-/

@[expose] public section

namespace CategoryTheory.PrelaxFunctor

open Bicategory

/-- A prelax functor out of a locally discrete bicategory sends every `2`-morphism to an
`eqToHom`. -/
lemma map₂_eq_eqToHom {B C : Type*} [Bicategory B] [IsLocallyDiscrete B] [Bicategory C]
    (F : PrelaxFunctor B C) {a b : B} {f g : a ⟶ b} (η : f ⟶ g) :
    F.map₂ η = eqToHom (by rw [obj_ext_of_isDiscrete η]) := by
  obtain rfl := obj_ext_of_isDiscrete η
  rw [Subsingleton.elim η (𝟙 f)]
  simp

/-- A prelax functor out of a locally discrete bicategory sends a composite of two `2`-morphisms
to the image of any `2`-morphism with the same source and target. -/
@[reassoc]
lemma map₂_comp_map₂ {B C : Type*} [Bicategory B] [IsLocallyDiscrete B] [Bicategory C]
    (F : PrelaxFunctor B C) {a b : B} {f g h : a ⟶ b} (η : f ⟶ g) (θ : g ⟶ h) (ι : f ⟶ h) :
    F.map₂ η ≫ F.map₂ θ = F.map₂ ι := by
  simp [map₂_eq_eqToHom]

end CategoryTheory.PrelaxFunctor

namespace CategoryTheory.Pseudofunctor

open Bicategory

variable {B₀ : Type*} [Bicategory B₀] {B₁ : Type*} [Bicategory B₁] [IsLocallyDiscrete B₁]
  {C : Type*} [Bicategory C] (P : B₀ ⥤ᵖ B₁) (F : B₁ ⥤ᵖ C)

/-- The unit comparison of the composite of a pseudofunctor `P` into a locally discrete
bicategory with `F` is the unit comparison of `F` at the `1`-morphism `P.map (𝟙 a)`, which
equals `𝟙 (P.obj a)`. -/
lemma comp_mapId_eq_mapId' (a : B₀) :
    (P.comp F).mapId a = F.mapId' (P.map (𝟙 a)) (obj_ext_of_isDiscrete (P.mapId a).hom) := by
  have h : P.mapId a = eqToIso (obj_ext_of_isDiscrete (P.mapId a).hom) :=
    Iso.ext (Subsingleton.elim _ _)
  rw [comp_mapId, h]
  -- `F.mapId' u hu` is by definition `F.map₂Iso (eqToIso _) ≪≫ F.mapId _`.
  rfl

/-- The composition comparison of the composite of a pseudofunctor `P` into a locally discrete
bicategory with `F` is the composition comparison of `F` at the factorization
`P.map f ≫ P.map g = P.map (f ≫ g)`. -/
lemma comp_mapComp_eq_mapComp' {a b c : B₀} (f : a ⟶ b) (g : b ⟶ c) :
    (P.comp F).mapComp f g = F.mapComp' (P.map f) (P.map g) (P.map (f ≫ g))
      (obj_ext_of_isDiscrete (P.mapComp f g).hom).symm := by
  have h : P.mapComp f g = eqToIso (obj_ext_of_isDiscrete (P.mapComp f g).hom) :=
    Iso.ext (Subsingleton.elim _ _)
  rw [comp_mapComp, h]
  -- `F.mapComp' u v w huv` is by definition `F.map₂Iso (eqToIso _) ≪≫ F.mapComp u v`.
  rfl

end CategoryTheory.Pseudofunctor
