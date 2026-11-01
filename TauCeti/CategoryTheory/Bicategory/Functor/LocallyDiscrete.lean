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
Consequently, pulling `F : LocallyDiscrete Λ ⥤ᵖ C` back along the identity functor, or along a
composite `f ⋙ g` instead of first along `g` and then along `f`, does not change its unit and
composition comparisons.
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

/-- The flexible unit comparison of the composite of a pseudofunctor `P` into a locally discrete
bicategory with `F`, at a `1`-morphism `u` equal to an identity, is the flexible unit comparison
of `F` at `P.map u`. -/
lemma comp_mapId'_eq_mapId' {a : B₀} (u : a ⟶ a) (hu : u = 𝟙 a) :
    (P.comp F).mapId' u hu =
      F.mapId' (P.map u) (by subst hu; exact obj_ext_of_isDiscrete (P.mapId a).hom) := by
  subst hu
  rw [mapId'_eq_mapId, comp_mapId_eq_mapId']

/-- The flexible composition comparison of the composite of a pseudofunctor `P` into a locally
discrete bicategory with `F` is the flexible composition comparison of `F` at the images under
`P`. -/
lemma comp_mapComp'_eq_mapComp' {a b c : B₀} (u : a ⟶ b) (v : b ⟶ c) (uv : a ⟶ c)
    (huv : u ≫ v = uv) :
    (P.comp F).mapComp' u v uv huv = F.mapComp' (P.map u) (P.map v) (P.map uv)
      (by subst huv; exact (obj_ext_of_isDiscrete (P.mapComp u v).hom).symm) := by
  subst huv
  rw [mapComp'_eq_mapComp, comp_mapComp_eq_mapComp']

/-! ### Pulling back along identities and composites of functors -/

section ToPseudofunctor

variable {Γ : Type*} [Category Γ] {Λ : Type*} [Category Λ] {Λ' : Type*} [Category Λ']
  {C : Type*} [Bicategory C]

-- The two sides of the following four lemmas have definitionally equal, but not syntactically
-- equal, types: `((𝟭 Γ).toPseudofunctor.comp F).obj x` unfolds to `F.obj x`, and similarly for
-- the composite functor.

/-- Pulling back along the identity functor does not change the unit comparisons. -/
lemma toPseudofunctor_id_comp_mapId (F : LocallyDiscrete Γ ⥤ᵖ C) (x : LocallyDiscrete Γ) :
    ((𝟭 Γ).toPseudofunctor.comp F).mapId x = F.mapId x := by
  rw [comp_mapId_eq_mapId']
  exact F.mapId'_eq_mapId x

/-- Pulling back along the identity functor does not change the composition comparisons. -/
lemma toPseudofunctor_id_comp_mapComp (F : LocallyDiscrete Γ ⥤ᵖ C) {x y z : LocallyDiscrete Γ}
    (φ : x ⟶ y) (ψ : y ⟶ z) :
    ((𝟭 Γ).toPseudofunctor.comp F).mapComp φ ψ = F.mapComp φ ψ := by
  rw [comp_mapComp_eq_mapComp']
  exact F.mapComp'_eq_mapComp φ ψ

/-- Pulling back along a composite functor `f ⋙ g` has the same unit comparisons as pulling back
along `g` and then along `f`. -/
lemma toPseudofunctor_comp_comp_mapId (f : Γ ⥤ Λ) (g : Λ ⥤ Λ') (F : LocallyDiscrete Λ' ⥤ᵖ C)
    (x : LocallyDiscrete Γ) :
    ((f ⋙ g).toPseudofunctor.comp F).mapId x =
      (f.toPseudofunctor.comp (g.toPseudofunctor.comp F)).mapId x := by
  rw [comp_mapId_eq_mapId', comp_mapId_eq_mapId', comp_mapId'_eq_mapId']
  -- Both sides are `F.mapId'` at the same arrow `(g.map (f.map (𝟙 x.as))).toLoc`.
  rfl

/-- Pulling back along a composite functor `f ⋙ g` has the same composition comparisons as
pulling back along `g` and then along `f`. -/
lemma toPseudofunctor_comp_comp_mapComp (f : Γ ⥤ Λ) (g : Λ ⥤ Λ') (F : LocallyDiscrete Λ' ⥤ᵖ C)
    {x y z : LocallyDiscrete Γ} (φ : x ⟶ y) (ψ : y ⟶ z) :
    ((f ⋙ g).toPseudofunctor.comp F).mapComp φ ψ =
      (f.toPseudofunctor.comp (g.toPseudofunctor.comp F)).mapComp φ ψ := by
  rw [comp_mapComp_eq_mapComp', comp_mapComp_eq_mapComp', comp_mapComp'_eq_mapComp']
  -- Both sides are `F.mapComp'` at the same arrows of `LocallyDiscrete Λ'`.
  rfl

end ToPseudofunctor

end CategoryTheory.Pseudofunctor
