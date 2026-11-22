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
  `SSet.SpacesΔ.toCatInftyΔ_obj_injective`, `SSet.SpacesΔ.toCatInftyΔ_sHom_eq`,
  `SSet.SpacesΔ.toCatInftyΔ_map`, `SSet.SpacesΔ.toCatInftyΔ_map_ι`,
  `SSet.SpacesΔ.ι_toCatInftyΔ_map`, `SSet.SpacesΔ.isIso_toCatInftyΔ_map`: projection,
  injectivity, hom-identification, and invertibility properties of `SSet.SpacesΔ.toCatInftyΔ`.
* `SSet.spacesToCatInfty_def`, `SSet.spacesToCatInfty_app`,
  `SSet.vertexEquiv_spacesToCatInfty_app`, `SSet.mem_range_toCatInftyΔ_iff`:
  characterization of `SSet.spacesToCatInfty` as a simplicial nerve map, its action on simplices
  and vertices, and the characterization of the object range of `SSet.SpacesΔ.toCatInftyΔ`.
* `SSet.spacesIsoFullSubcategory_hom_ι`, `SSet.spacesIsoFullSubcategory_hom_app_val`,
  `SSet.range_spacesToCatInfty`: the isomorphism `SSet.spacesIsoFullSubcategory` intertwines the
  full enhanced subcategory inclusion with `SSet.spacesToCatInfty`, acts on simplices by
  postcomposition, and identifies the range of `SSet.spacesToCatInfty` with the full enhanced
  subcategory on Kan complexes.
* `SSet.mono_spacesToCatInfty`, `SSet.innerFibration_spacesToCatInfty`,
  `SSet.isIso_rightMappingSpace_map_spacesToCatInfty`, `SSet.isFullyFaithful_spacesToCatInfty`:
  `SSet.spacesToCatInfty` is a monomorphism, an inner fibration, and fully faithful.

## References

* J. Lurie, *Higher Topos Theory*, Definition 1.2.16.1 and §1.2.11.
-/

public section

open CategoryTheory MonoidalCategory EnrichedCategory SimplicialCategory Opposite
  Simplicial

universe u

namespace SSet

namespace SpacesΔ

private def toCatInftyΔObj (A : SpacesΔ.{u}) : CatInftyΔ.{u} :=
  ⟨CoreEnriched.of A.obj, have := A.property; inferInstance⟩

private lemma toCatInftyΔObj_sHom_eq_core (A B : SpacesΔ.{u}) :
    sHom (toCatInftyΔObj A) (toCatInftyΔObj B) = ((sHom A.obj B.obj).core : SSet.{u}) :=
  (ObjectProperty.FullSubcategory.eHom_eq SSet (toCatInftyΔObj A) (toCatInftyΔObj B)).trans
    (CoreEnriched.sHom_eq (toCatInftyΔObj A).obj (toCatInftyΔObj B).obj)

private lemma toCatInftyΔObj_sHom_eq (A B : SpacesΔ.{u}) :
    sHom (toCatInftyΔObj A) (toCatInftyΔObj B) = ((sHom A B).core : SSet.{u}) :=
  (toCatInftyΔObj_sHom_eq_core A B).trans
    (congrArg coreFunctor.obj (ObjectProperty.FullSubcategory.eHom_eq SSet A B).symm)

private lemma toCatInftyΔObj_eqToHom_comp_ι (A B : SpacesΔ.{u}) :
    eqToHom (toCatInftyΔObj_sHom_eq A B) ≫ (sHom A B).core.ι =
      eqToHom (toCatInftyΔObj_sHom_eq_core A B) ≫
        (sHom A.obj B.obj).core.ι ≫
        eqToHom (ObjectProperty.FullSubcategory.eHom_eq SSet A B).symm := by
  calc eqToHom (toCatInftyΔObj_sHom_eq A B) ≫ (sHom A B).core.ι
      = eqToHom (toCatInftyΔObj_sHom_eq_core A B) ≫
          core.map (eqToHom (ObjectProperty.FullSubcategory.eHom_eq SSet A B).symm) ≫
          (sHom A B).core.ι := by
        refine congrArg (· ≫ _) ?_
        refine (eqToHom_trans (toCatInftyΔObj_sHom_eq_core A B)
          (congrArg coreFunctor.obj
            (ObjectProperty.FullSubcategory.eHom_eq SSet A B).symm)).symm.trans ?_
        exact congrArg (_ ≫ ·) (eqToHom_map coreFunctor _).symm
    _ = _ := congrArg (_ ≫ ·) (core.map_ι _)

private lemma toCatInftyΔObj_eComp_ι (A B C : SpacesΔ.{u}) :
    (eqToHom (toCatInftyΔObj_sHom_eq A B).symm ⊗ₘ
        eqToHom (toCatInftyΔObj_sHom_eq B C).symm) ≫
      eComp SSet (toCatInftyΔObj A) (toCatInftyΔObj B) (toCatInftyΔObj C) ≫
      eqToHom (toCatInftyΔObj_sHom_eq A C) ≫ (sHom A C).core.ι =
    ((sHom A B).core.ι ⊗ₘ (sHom B C).core.ι) ≫ eComp SSet A B C := by
  have hsymm (X Y : SpacesΔ.{u}) :
      eqToHom (toCatInftyΔObj_sHom_eq X Y).symm =
        core.map (eqToHom (ObjectProperty.FullSubcategory.eHom_eq SSet X Y)) ≫
          eqToHom (toCatInftyΔObj_sHom_eq_core X Y).symm :=
    (eqToHom_trans (congrArg coreFunctor.obj
      (ObjectProperty.FullSubcategory.eHom_eq SSet X Y))
      (toCatInftyΔObj_sHom_eq_core X Y).symm).symm.trans
      (congrArg (· ≫ _) (eqToHom_map coreFunctor _).symm)
  have hCoreComp :
      (eqToHom (toCatInftyΔObj_sHom_eq_core A B).symm ⊗ₘ
          eqToHom (toCatInftyΔObj_sHom_eq_core B C).symm) ≫
        eComp SSet (toCatInftyΔObj A) (toCatInftyΔObj B) (toCatInftyΔObj C) ≫
        eqToHom (toCatInftyΔObj_sHom_eq_core A C) =
      eComp SSet (CoreEnriched.of A.obj) (CoreEnriched.of B.obj) (CoreEnriched.of C.obj) := by
    rw [ObjectProperty.FullSubcategory.eComp_eq SSet (toCatInftyΔObj A) (toCatInftyΔObj B)
      (toCatInftyΔObj C)]
    rfl
  rw [hsymm A B, hsymm B C, toCatInftyΔObj_eqToHom_comp_ι A C,
    ← tensorHom_comp_tensorHom_assoc, reassoc_of% hCoreComp,
    CoreEnriched.eComp_ι_assoc]
  dsimp only
  rw [tensorHom_comp_tensorHom_assoc, core.map_ι, core.map_ι,
    ← tensorHom_comp_tensorHom_assoc, ← ObjectProperty.FullSubcategory.eComp_eq SSet A B C]
  simp only [eqToHom_refl, id_tensorHom_id, Category.id_comp, Category.comp_id]

/-- The canonical simplicial functor from `SpacesΔ` to `CatInftyΔ`, viewing each Kan complex as a
quasicategory and inverting the core inclusion `Fun(A, B)^≃ ⟶ Fun(A, B)`. -/
noncomputable def toCatInftyΔ : EnrichedFunctor SSet.{u} SpacesΔ.{u} CatInftyΔ.{u} where
  obj := toCatInftyΔObj
  map A B := inv (sHom A B).core.ι ≫ eqToHom (toCatInftyΔObj_sHom_eq A B).symm
  map_id A := by
    rw [← cancel_mono (eqToHom (toCatInftyΔObj_sHom_eq A A) ≫ (sHom A A).core.ι)]
    have hId :
        eId SSet (toCatInftyΔObj A) ≫ eqToHom (toCatInftyΔObj_sHom_eq A A) ≫ (sHom A A).core.ι =
          eId SSet A := by
      rw [toCatInftyΔObj_eqToHom_comp_ι,
        ObjectProperty.FullSubcategory.eId_eq SSet (toCatInftyΔObj A),
        ObjectProperty.FullSubcategory.eId_eq SSet A]
      simp only [eqToHom_refl, Category.comp_id]
      exact CoreEnriched.eId_ι (CoreEnriched.of A.obj)
    simp [hId]
  map_comp A B C := by
    rw [← cancel_mono (eqToHom (toCatInftyΔObj_sHom_eq A C) ≫ (sHom A C).core.ι)]
    simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp,
      IsIso.inv_hom_id, Category.comp_id]
    rw [← tensorHom_comp_tensorHom_assoc, toCatInftyΔObj_eComp_ι,
      tensorHom_comp_tensorHom_assoc]
    simp

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

/-- The mapping simplicial sets of `SpacesΔ.toCatInftyΔ` coincide with the cores of the
mapping simplicial sets of `SpacesΔ`. -/
lemma toCatInftyΔ_sHom_eq (A B : SpacesΔ.{u}) :
    sHom (toCatInftyΔ.obj A) (toCatInftyΔ.obj B) = ((sHom A B).core : SSet.{u}) :=
  toCatInftyΔObj_sHom_eq A B

/-- On mapping simplicial sets, `SpacesΔ.toCatInftyΔ` is the inverse of the core inclusion
transported along `toCatInftyΔ_sHom_eq`. -/
lemma toCatInftyΔ_map (A B : SpacesΔ.{u}) :
    toCatInftyΔ.map A B =
      inv (sHom A B).core.ι ≫ eqToHom (toCatInftyΔ_sHom_eq A B).symm :=
  (rfl)

/-- Composing `toCatInftyΔ.map A B` with the core inclusion on `Fun(A, B)` gives the identity on
`Fun(A, B)`. -/
@[reassoc (attr := simp)]
lemma toCatInftyΔ_map_ι (A B : SpacesΔ.{u}) :
    toCatInftyΔ.map A B ≫ eqToHom (toCatInftyΔ_sHom_eq A B) ≫ (sHom A B).core.ι =
      𝟙 (sHom A B) := by
  simp [toCatInftyΔ_map]

/-- Composing the core inclusion on `Fun(A, B)` with `toCatInftyΔ.map A B` gives the identity on
the mapping simplicial set of `CatInftyΔ`. -/
@[reassoc (attr := simp)]
lemma ι_toCatInftyΔ_map (A B : SpacesΔ.{u}) :
    eqToHom (toCatInftyΔ_sHom_eq A B) ≫ (sHom A B).core.ι ≫ toCatInftyΔ.map A B =
      𝟙 (sHom (toCatInftyΔ.obj A) (toCatInftyΔ.obj B)) := by
  simp [toCatInftyΔ_map]

/-- The simplicial functor `SpacesΔ.toCatInftyΔ` induces isomorphisms on all mapping simplicial
sets. -/
instance isIso_toCatInftyΔ_map (A B : SpacesΔ.{u}) : IsIso (toCatInftyΔ.map A B) :=
  ⟨⟨eqToHom (toCatInftyΔ_sHom_eq A B) ≫ (sHom A B).core.ι,
    toCatInftyΔ_map_ι A B, ι_toCatInftyΔ_map A B⟩⟩

end SpacesΔ

/-- The canonical map of quasicategories from `Spaces` to `Cat∞`, induced on simplicial nerves by
`SpacesΔ.toCatInftyΔ`. -/
noncomputable def spacesToCatInfty : spaces.{u} ⟶ catInfty.{u} :=
  simplicialNerveMap SpacesΔ.toCatInftyΔ

/-- `spacesToCatInfty` is the map on simplicial nerves induced by `SpacesΔ.toCatInftyΔ`. -/
lemma spacesToCatInfty_def :
    spacesToCatInfty.{u} = simplicialNerveMap SpacesΔ.toCatInftyΔ.{u} :=
  (rfl)

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
  rw [spacesToCatInfty_def, SimplicialNerve.vertexEquiv_simplicialNerveMap_app]
  exact SpacesΔ.toCatInftyΔ_obj_toSSet _

/-- An object of `CatInftyΔ` lies in the object range of `SpacesΔ.toCatInftyΔ` if and only if its
underlying simplicial set is a Kan complex. -/
@[simp↓]
lemma mem_range_toCatInftyΔ_iff (A : CatInftyΔ.{u}) :
    A ∈ Set.range SpacesΔ.toCatInftyΔ.{u}.obj ↔ KanComplex A.obj.toSSet :=
  ⟨by rintro ⟨B, rfl⟩; exact B.property,
    fun h ↦ ⟨⟨A.obj.toSSet, h⟩, ObjectProperty.FullSubcategory.ext rfl⟩⟩

/-- The quasicategory `Spaces` of small Kan complexes is isomorphic to the full enhanced
subcategory of `Cat∞` spanned by the Kan complexes. -/
noncomputable def spacesIsoFullSubcategory :
    spaces.{u} ≅
      (catInfty.{u}.fullEnhancedSubcategory
        fun x ↦ KanComplex (SimplicialNerve.vertexEquiv CatInftyΔ.{u} x).obj.toSSet :
          SSet.{u + 1}) :=
  SimplicialNerve.fullSubcategoryIso SpacesΔ.toCatInftyΔ.{u}
    SpacesΔ.toCatInftyΔ_obj_injective (fun A ↦ KanComplex A.obj.toSSet)
    fun A ↦ (mem_range_toCatInftyΔ_iff A).symm

/-- Under `spacesIsoFullSubcategory`, the full enhanced subcategory inclusion corresponds to
`spacesToCatInfty`. -/
@[reassoc (attr := simp)]
lemma spacesIsoFullSubcategory_hom_ι :
    spacesIsoFullSubcategory.{u}.hom ≫ Subcomplex.ι _ = spacesToCatInfty.{u} :=
  SimplicialNerve.fullSubcategoryIso_hom_ι _ _ _ _

/-- On arbitrary simplices, the underlying simplex of `spacesIsoFullSubcategory.hom` is
postcomposition with `SpacesΔ.toCatInftyΔ`. -/
@[simp]
lemma spacesIsoFullSubcategory_hom_app_val (n : SimplexCategoryᵒᵖ) (G : spaces.{u}.obj n) :
    dsimp% (spacesIsoFullSubcategory.{u}.hom.app n G).val =
      EnrichedFunctor.comp SSet G SpacesΔ.toCatInftyΔ :=
  SimplicialNerve.fullSubcategoryIso_hom_app_val _ _ _ _ n G

/-- The range of `spacesToCatInfty` is the full enhanced subcategory of `Cat∞` spanned by the Kan
complexes. -/
@[simp]
lemma range_spacesToCatInfty :
    Subcomplex.range spacesToCatInfty.{u} =
      catInfty.{u}.fullEnhancedSubcategory
        fun x ↦ KanComplex (SimplicialNerve.vertexEquiv CatInftyΔ.{u} x).obj.toSSet :=
  SimplicialNerve.range_simplicialNerveMap SpacesΔ.toCatInftyΔ.{u}
    (fun A ↦ KanComplex A.obj.toSSet) fun A ↦ (mem_range_toCatInftyΔ_iff A).symm

/-- The inclusion `Spaces ⟶ Cat∞` is a monomorphism of simplicial sets. -/
instance mono_spacesToCatInfty : Mono spacesToCatInfty.{u} :=
  SimplicialNerve.mono_simplicialNerveMap SpacesΔ.toCatInftyΔ
    SpacesΔ.toCatInftyΔ_obj_injective

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
