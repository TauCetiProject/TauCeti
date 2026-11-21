/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.Quasicategory.CatInfty
public import TauCeti.AlgebraicTopology.Quasicategory.FullyFaithful
public import TauCeti.AlgebraicTopology.Quasicategory.Spaces.Basic
public import TauCeti.AlgebraicTopology.SimplicialNerve.FullSubcategory

/-!
# Comparison between `Spaces` and `Cat∞`

Because every simplex of a function complex `Fun(A, B)` into a Kan complex `B` lies in its core
(`SSet.core_sHom_eq_top`), the identity on underlying simplicial sets upgrades to a simplicial
functor `SSet.SpacesΔ.toCatInftyΔ : EnrichedFunctor SSet SpacesΔ CatInftyΔ` that is injective on
objects and an isomorphism on every mapping simplicial set (`SSet.SpacesΔ.isIso_toCatInftyΔ_map`).

Passing to simplicial nerves via `CategoryTheory.SimplicialNerve.fullSubcategoryIso` produces the
inclusion `SSet.spacesToCatInfty : SSet.spaces ⟶ SSet.catInfty`, which identifies `SSet.spaces`
with the full enhanced subcategory of `SSet.catInfty` spanned by the Kan complexes
(`SSet.spacesIsoFullSubcategory` and `SSet.range_spacesToCatInfty`). In particular,
`SSet.spacesToCatInfty` is a monomorphism, an inner fibration, and fully faithful (inducing
isomorphisms on all right mapping spaces).

## Main definitions

* `SSet.SpacesΔ.toCatInftyΔ`: the canonical simplicial functor from `SSet.SpacesΔ` to
  `SSet.CatInftyΔ`.
* `SSet.spacesToCatInfty`: the induced map of quasicategories `SSet.spaces ⟶ SSet.catInfty`.
* `SSet.spacesIsoFullSubcategory`: the isomorphism identifying `SSet.spaces` with the full
  enhanced subcategory of `SSet.catInfty` spanned by the Kan complexes.

## Main results

* `SSet.SpacesΔ.toCatInftyΔ_obj_obj`, `SSet.SpacesΔ.toCatInftyΔ_obj_toSSet`,
  `SSet.SpacesΔ.toCatInftyΔ_obj_injective`, `SSet.SpacesΔ.toCatInftyΔ_map_ι`,
  `SSet.SpacesΔ.ι_toCatInftyΔ_map`, `SSet.SpacesΔ.isIso_toCatInftyΔ_map`: projection,
  injectivity, and invertibility properties of `SSet.SpacesΔ.toCatInftyΔ`.
* `SSet.spacesToCatInfty_app`, `SSet.vertexEquiv_spacesToCatInfty_app`: action of
  `SSet.spacesToCatInfty` on simplices and vertices.
* `SSet.spacesIsoFullSubcategory_hom_ι`, `SSet.range_spacesToCatInfty`: the isomorphism
  `SSet.spacesIsoFullSubcategory` intertwines the full enhanced subcategory inclusion with
  `SSet.spacesToCatInfty`, and the range of `SSet.spacesToCatInfty` is the full enhanced
  subcategory on Kan complexes.
* `SSet.mono_spacesToCatInfty`, `SSet.innerFibration_spacesToCatInfty`,
  `SSet.isIso_rightMappingSpace_map_spacesToCatInfty`, `SSet.isFullyFaithful_spacesToCatInfty`:
  `SSet.spacesToCatInfty` is a monomorphism, an inner fibration, and fully faithful.

## References

* J. Lurie, *Higher Topos Theory*, Definition 1.2.16.1 and §1.2.11.
-/

public section

open CategoryTheory MonoidalCategory MonoidalClosed EnrichedCategory SimplicialCategory Opposite
  Simplicial

universe u

namespace SSet

namespace SpacesΔ

private lemma range_id_le_core (A B : SpacesΔ.{u}) :
    Subcomplex.range (𝟙 (sHom A.obj B.obj)) ≤ (sHom A.obj B.obj).core := by
  have := B.property
  rw [core_sHom_eq_top]
  exact le_top

/-- The canonical simplicial functor from `SpacesΔ` to `CatInftyΔ`, viewing each Kan complex as a
quasicategory and lifting `Fun(A, B)` along `Fun(A, B)^≃ = Fun(A, B)`. -/
noncomputable def toCatInftyΔ : EnrichedFunctor SSet.{u} SpacesΔ.{u} CatInftyΔ.{u} where
  obj A := ⟨CoreEnriched.of A.obj, have := A.property; inferInstance⟩
  map A B := Subcomplex.lift (𝟙 (sHom A.obj B.obj)) (range_id_le_core A B)
  map_id A := by
    rw [← cancel_mono (Subcomplex.ι _)]
    simp only [Category.assoc, Subcomplex.lift_ι, ObjectProperty.FullSubcategory.eId_eq]
    rw [CoreEnriched.eId_ι]
    exact Category.comp_id _
  map_comp A B C := by
    rw [← cancel_mono (Subcomplex.ι _)]
    simp only [Category.assoc, Subcomplex.lift_ι, ObjectProperty.FullSubcategory.eComp_eq]
    rw [CoreEnriched.eComp_ι, tensorHom_comp_tensorHom_assoc, Subcomplex.lift_ι, Subcomplex.lift_ι]
    have hL : eComp SSet A.obj B.obj C.obj ≫ 𝟙 (sHom A.obj C.obj) =
        eComp SSet A.obj B.obj C.obj := Category.comp_id _
    have hR : (𝟙 (sHom A.obj B.obj) ⊗ₘ 𝟙 (sHom B.obj C.obj)) ≫
          eComp SSet A.obj B.obj C.obj = eComp SSet A.obj B.obj C.obj :=
      (congrArg (· ≫ eComp SSet A.obj B.obj C.obj) (id_tensorHom_id _ _)).trans
        (Category.id_comp _)
    exact hL.trans hR.symm

/-- `SpacesΔ.toCatInftyΔ` sends a Kan complex `A` to `CoreEnriched.of A.obj` in `CatInftyΔ`. -/
@[simp]
lemma toCatInftyΔ_obj_obj (A : SpacesΔ.{u}) :
    (toCatInftyΔ.obj A).obj = CoreEnriched.of A.obj :=
  (rfl)

/-- `SpacesΔ.toCatInftyΔ` preserves underlying simplicial sets on objects. -/
lemma toCatInftyΔ_obj_toSSet (A : SpacesΔ.{u}) :
    (toCatInftyΔ.obj A).obj.toSSet = A.obj :=
  (rfl)

/-- `SpacesΔ.toCatInftyΔ` is injective on objects. -/
lemma toCatInftyΔ_obj_injective : Function.Injective toCatInftyΔ.{u}.obj :=
  fun _ _ h ↦ ObjectProperty.FullSubcategory.ext (congrArg (fun X ↦ X.obj.toSSet) h)

private lemma toCatInftyΔ_map_ι_eq (A B : SpacesΔ.{u}) :
    toCatInftyΔ.map A B ≫
        (sHom (toCatInftyΔ.obj A).obj.toSSet (toCatInftyΔ.obj B).obj.toSSet).core.ι =
      Subcomplex.lift (𝟙 (sHom A.obj B.obj)) (range_id_le_core A B) ≫
        (sHom A.obj B.obj).core.ι :=
  rfl

/-- Composing `toCatInftyΔ.map A B` with the core inclusion gives the identity on `Fun(A, B)`, up
to the object identification `toCatInftyΔ_obj_toSSet`. -/
@[reassoc (attr := simp)]
lemma toCatInftyΔ_map_ι (A B : SpacesΔ.{u}) :
    toCatInftyΔ.map A B ≫
        (sHom (toCatInftyΔ.obj A).obj.toSSet (toCatInftyΔ.obj B).obj.toSSet).core.ι =
      eqToHom (by rw [toCatInftyΔ_obj_toSSet, toCatInftyΔ_obj_toSSet]; exact (rfl)) := by
  rw [toCatInftyΔ_map_ι_eq, Subcomplex.lift_ι]
  exact (eqToHom_refl _ _).symm

/-- Composing the core inclusion with `toCatInftyΔ.map A B` gives the identity on `Fun(A, B)^≃`. -/
@[reassoc (attr := simp)]
lemma ι_toCatInftyΔ_map (A B : SpacesΔ.{u}) :
    (sHom (toCatInftyΔ.obj A).obj.toSSet (toCatInftyΔ.obj B).obj.toSSet).core.ι ≫
        eqToHom (by rw [toCatInftyΔ_obj_toSSet, toCatInftyΔ_obj_toSSet]; exact (rfl)) ≫
          toCatInftyΔ.map A B =
      𝟙 ((sHom (toCatInftyΔ.obj A).obj.toSSet (toCatInftyΔ.obj B).obj.toSSet).core : SSet.{u}) := by
  rw [← cancel_mono (Subcomplex.ι _)]
  simp

/-- The simplicial functor `SpacesΔ.toCatInftyΔ` induces isomorphisms on all mapping simplicial
sets. -/
instance isIso_toCatInftyΔ_map (A B : SpacesΔ.{u}) : IsIso (toCatInftyΔ.map A B) :=
  ⟨⟨(sHom (toCatInftyΔ.obj A).obj.toSSet (toCatInftyΔ.obj B).obj.toSSet).core.ι ≫
      eqToHom (by rw [toCatInftyΔ_obj_toSSet, toCatInftyΔ_obj_toSSet]; exact (rfl)),
    by simp, by rw [Category.assoc]; exact ι_toCatInftyΔ_map A B⟩⟩

end SpacesΔ

/-- The canonical map of quasicategories from `Spaces` to `Cat∞`, induced on simplicial nerves by
`SpacesΔ.toCatInftyΔ`. -/
noncomputable def spacesToCatInfty : spaces.{u} ⟶ catInfty.{u} :=
  simplicialNerveMap SpacesΔ.toCatInftyΔ

/-- On arbitrary simplices, `spacesToCatInfty` acts by postcomposition with
`SpacesΔ.toCatInftyΔ`. -/
@[simp]
lemma spacesToCatInfty_app (n : SimplexCategoryᵒᵖ) (G : spaces.{u}.obj n) :
    spacesToCatInfty.app n G = EnrichedFunctor.comp SSet G SpacesΔ.toCatInftyΔ :=
  simplicialNerveMap_app _ _ _

/-- On vertices, `spacesToCatInfty` preserves the underlying simplicial set. -/
@[simp↓]
lemma vertexEquiv_spacesToCatInfty_app (x : spaces.{u} _⦋0⦌) :
    (SimplicialNerve.vertexEquiv CatInftyΔ.{u} (spacesToCatInfty.app (op ⦋0⦌) x)).obj.toSSet =
      (SimplicialNerve.vertexEquiv SpacesΔ.{u} x).obj := by
  rw [SimplicialNerve.vertexEquiv_apply, SimplicialNerve.vertexEquiv_apply,
    spacesToCatInfty_app]
  dsimp only [EnrichedFunctor.comp]
  exact SpacesΔ.toCatInftyΔ_obj_toSSet _

private lemma kanComplex_iff_mem_range_toCatInftyΔ (A : CatInftyΔ.{u}) :
    KanComplex A.obj.toSSet ↔ A ∈ Set.range SpacesΔ.toCatInftyΔ.{u}.obj :=
  ⟨fun h ↦ ⟨⟨A.obj.toSSet, h⟩, ObjectProperty.FullSubcategory.ext rfl⟩,
    by rintro ⟨B, rfl⟩; exact B.property⟩

/-- The quasicategory `Spaces` of small Kan complexes is isomorphic to the full enhanced
subcategory of `Cat∞` spanned by the Kan complexes. -/
noncomputable def spacesIsoFullSubcategory :
    spaces.{u} ≅
      (catInfty.{u}.fullEnhancedSubcategory
        fun x ↦ KanComplex (SimplicialNerve.vertexEquiv CatInftyΔ.{u} x).obj.toSSet :
          SSet.{u + 1}) :=
  SimplicialNerve.fullSubcategoryIso SpacesΔ.toCatInftyΔ.{u}
    SpacesΔ.toCatInftyΔ_obj_injective (fun A ↦ KanComplex A.obj.toSSet)
    kanComplex_iff_mem_range_toCatInftyΔ

/-- Under `spacesIsoFullSubcategory`, the full enhanced subcategory inclusion corresponds to
`spacesToCatInfty`. -/
@[reassoc (attr := simp)]
lemma spacesIsoFullSubcategory_hom_ι :
    spacesIsoFullSubcategory.{u}.hom ≫ Subcomplex.ι _ = spacesToCatInfty.{u} :=
  SimplicialNerve.fullSubcategoryIso_hom_ι _ _ _ _

/-- The range of `spacesToCatInfty` is the full enhanced subcategory of `Cat∞` spanned by the Kan
complexes. -/
@[simp]
lemma range_spacesToCatInfty :
    Subcomplex.range spacesToCatInfty.{u} =
      catInfty.{u}.fullEnhancedSubcategory
        fun x ↦ KanComplex (SimplicialNerve.vertexEquiv CatInftyΔ.{u} x).obj.toSSet :=
  SimplicialNerve.range_simplicialNerveMap SpacesΔ.toCatInftyΔ.{u}
    SpacesΔ.toCatInftyΔ_obj_injective (fun A ↦ KanComplex A.obj.toSSet)
    kanComplex_iff_mem_range_toCatInftyΔ

/-- The inclusion `Spaces ⟶ Cat∞` is a monomorphism of simplicial sets. -/
instance mono_spacesToCatInfty : Mono spacesToCatInfty.{u} := by
  rw [← spacesIsoFullSubcategory_hom_ι]
  exact mono_comp _ _

/-- The inclusion `Spaces ⟶ Cat∞` is an inner fibration. -/
instance innerFibration_spacesToCatInfty : InnerFibration spacesToCatInfty.{u} :=
  ⟨by
    rw [← spacesIsoFullSubcategory_hom_ι]
    exact innerFibrations.comp_mem _ _ (innerFibrations.of_isIso _) InnerFibration.mem⟩

/-- The inclusion `Spaces ⟶ Cat∞` induces isomorphisms on all right mapping spaces. -/
instance isIso_rightMappingSpace_map_spacesToCatInfty (x y : spaces.{u} _⦋0⦌) :
    IsIso (rightMappingSpace.map x y spacesToCatInfty) := by
  rw [← spacesIsoFullSubcategory_hom_ι, rightMappingSpace.map_comp]
  exact inferInstance

/-- The inclusion `Spaces ⟶ Cat∞` is fully faithful. -/
instance isFullyFaithful_spacesToCatInfty : IsFullyFaithful spacesToCatInfty.{u} :=
  IsFullyFaithful.of_isIso_map _ inferInstance

end SSet
