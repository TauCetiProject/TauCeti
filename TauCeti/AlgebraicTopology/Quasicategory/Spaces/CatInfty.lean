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
  `SSet.SpacesΔ.ι_toCatInftyΔ_map`, `SSet.SpacesΔ.isIso_toCatInftyΔ_map`,
  `SSet.SpacesΔ.eHomEquiv_symm_toCatInftyΔ_map`,
  `SSet.SpacesΔ.mem_range_toCatInftyΔ_obj_iff`: projection, injectivity, hom-identification,
  invertibility, underlying-morphism, and object-range properties of `SSet.SpacesΔ.toCatInftyΔ`.
* `SSet.spacesToCatInfty_def`, `SSet.spacesToCatInfty_app`,
  `SSet.vertexEquiv_spacesToCatInfty_app`, `SSet.edgeMk_map_spacesToCatInfty`,
  `SSet.homEquiv_ofEq_map_spacesToCatInfty`: characterization of `SSet.spacesToCatInfty` as a
  simplicial nerve map and its action on simplices, vertices, and edges.
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

private lemma toCatInftyΔObj_obj (A : SpacesΔ.{u}) :
    (toCatInftyΔObj A).obj = CoreEnriched.of A.obj :=
  rfl

private lemma toCatInftyΔObj_toSSet (A : SpacesΔ.{u}) :
    (toCatInftyΔObj A).obj.toSSet = A.obj :=
  rfl

private lemma toCatInftyΔObj_sHom_eq_core (A B : SpacesΔ.{u}) :
    sHom (toCatInftyΔObj A) (toCatInftyΔObj B) = ((sHom A.obj B.obj).core : SSet.{u}) := by
  refine (ObjectProperty.FullSubcategory.eHom_eq SSet
    (toCatInftyΔObj A) (toCatInftyΔObj B)).trans ?_
  refine (CoreEnriched.sHom_eq (toCatInftyΔObj A).obj (toCatInftyΔObj B).obj).trans ?_
  rw [toCatInftyΔObj_toSSet, toCatInftyΔObj_toSSet]

private lemma toCatInftyΔObj_sHom_eq (A B : SpacesΔ.{u}) :
    sHom (toCatInftyΔObj A) (toCatInftyΔObj B) = ((sHom A B).core : SSet.{u}) :=
  (toCatInftyΔObj_sHom_eq_core A B).trans
    (congrArg coreFunctor.obj (ObjectProperty.FullSubcategory.eHom_eq SSet A B).symm)

private noncomputable def toCatInftyΔHomToSpaces (A B : SpacesΔ.{u}) :
    sHom (toCatInftyΔObj A) (toCatInftyΔObj B) ⟶ sHom A B :=
  eqToHom (toCatInftyΔObj_sHom_eq A B) ≫ (sHom A B).core.ι

private instance (A B : SpacesΔ.{u}) : IsIso (toCatInftyΔHomToSpaces A B) := by
  dsimp [toCatInftyΔHomToSpaces]
  infer_instance

private lemma toCatInftyΔHomToSpaces_eq_core (A B : SpacesΔ.{u}) :
    toCatInftyΔHomToSpaces A B =
      eqToHom (toCatInftyΔObj_sHom_eq_core A B) ≫ (sHom A.obj B.obj).core.ι ≫
        eqToHom (ObjectProperty.FullSubcategory.eHom_eq SSet A B).symm := by
  have h := eqToHom_trans_assoc (toCatInftyΔObj_sHom_eq_core A B)
    (congrArg (fun Z : SSet.{u} ↦ (Z.core : SSet.{u}))
      (ObjectProperty.FullSubcategory.eHom_eq SSet A B).symm)
    (sHom A B).core.ι
  exact h.symm.trans (by
    rw [eqToHom_core_ι (ObjectProperty.FullSubcategory.eHom_eq SSet A B).symm])

private lemma eId_comp_toCatInftyΔHomToSpaces (A : SpacesΔ.{u}) :
    eId SSet (toCatInftyΔObj A) ≫ toCatInftyΔHomToSpaces A A = eId SSet A := by
  have h : eId SSet (CoreEnriched.of A.obj) ≫ (sHom A.obj A.obj).core.ι = eId SSet A.obj :=
    CoreEnriched.eId_ι (CoreEnriched.of A.obj)
  simp [ObjectProperty.FullSubcategory.eId_eq, toCatInftyΔHomToSpaces_eq_core,
    eId_comp_eqToHom_assoc (toCatInftyΔObj_obj A), h]

private lemma eComp_comp_toCatInftyΔHomToSpaces (A B C : SpacesΔ.{u}) :
    eComp SSet (toCatInftyΔObj A) (toCatInftyΔObj B) (toCatInftyΔObj C) ≫
        toCatInftyΔHomToSpaces A C =
      (toCatInftyΔHomToSpaces A B ⊗ₘ toCatInftyΔHomToSpaces B C) ≫ eComp SSet A B C := by
  have h :
      eComp SSet (CoreEnriched.of A.obj) (CoreEnriched.of B.obj) (CoreEnriched.of C.obj) ≫
          (sHom A.obj C.obj).core.ι =
        ((sHom A.obj B.obj).core.ι ⊗ₘ (sHom B.obj C.obj).core.ι) ≫
          eComp SSet A.obj B.obj C.obj :=
    CoreEnriched.eComp_ι _ _ _
  simp [ObjectProperty.FullSubcategory.eComp_eq, toCatInftyΔHomToSpaces_eq_core,
    ← tensorHom_eqToHom_comp_eComp_assoc (toCatInftyΔObj_obj A)
      (toCatInftyΔObj_obj B) (toCatInftyΔObj_obj C),
    h, ← tensorHom_comp_tensorHom_assoc]

private lemma eHomEquiv_comp_toCatInftyΔHomToSpaces {A B : SpacesΔ.{u}} (f : A ⟶ B) :
    eHomEquiv SSet (ObjectProperty.homMk (InducedCategory.homMk
        (eqToHom (toCatInftyΔObj_toSSet A) ≫ f.hom ≫
          eqToHom (toCatInftyΔObj_toSSet B).symm)) :
        toCatInftyΔObj A ⟶ toCatInftyΔObj B) ≫ toCatInftyΔHomToSpaces A B =
      eHomEquiv SSet f := by
  have h :
      sHom (toCatInftyΔObj A).obj.toSSet (toCatInftyΔObj B).obj.toSSet = sHom A.obj B.obj := by
    rw [toCatInftyΔObj_toSSet, toCatInftyΔObj_toSSet]
  simp [ObjectProperty.FullSubcategory.eHomEquiv_eq, toCatInftyΔHomToSpaces_eq_core,
    eqToHom_core_ι h, CoreEnriched.eHomEquiv_ι_assoc,
    eHomEquiv_comp_eqToHom (toCatInftyΔObj_toSSet A) (toCatInftyΔObj_toSSet B)]

/-- The canonical simplicial functor from `SpacesΔ` to `CatInftyΔ`, viewing each Kan complex as a
quasicategory and inverting the core inclusion `Fun(A, B)^≃ ⟶ Fun(A, B)`. -/
noncomputable def toCatInftyΔ : EnrichedFunctor SSet.{u} SpacesΔ.{u} CatInftyΔ.{u} where
  obj := toCatInftyΔObj
  map A B := inv (toCatInftyΔHomToSpaces A B)
  map_id A := by
    rw [← cancel_mono (toCatInftyΔHomToSpaces A A)]
    simp [eId_comp_toCatInftyΔHomToSpaces]
  map_comp A B C := by
    rw [← cancel_mono (toCatInftyΔHomToSpaces A C)]
    simp [eComp_comp_toCatInftyΔHomToSpaces]

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

private lemma toCatInftyΔHomToSpaces_eq (A B : SpacesΔ.{u}) :
    toCatInftyΔHomToSpaces A B = eqToHom (toCatInftyΔ_sHom_eq A B) ≫ (sHom A B).core.ι :=
  rfl

/-- On mapping simplicial sets, `SpacesΔ.toCatInftyΔ` is the inverse of the core inclusion
transported along `toCatInftyΔ_sHom_eq`. -/
lemma toCatInftyΔ_map (A B : SpacesΔ.{u}) :
    toCatInftyΔ.map A B =
      inv (sHom A B).core.ι ≫ eqToHom (toCatInftyΔ_sHom_eq A B).symm := by
  dsimp [toCatInftyΔ, toCatInftyΔHomToSpaces]
  rw [IsIso.inv_comp]
  simp

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

/-- On underlying morphisms, `SpacesΔ.toCatInftyΔ` sends a map of Kan complexes to itself viewed
as a morphism in `CatInftyΔ`. -/
@[simp]
lemma eHomEquiv_symm_toCatInftyΔ_map {A B : SpacesΔ.{u}} (f : A ⟶ B) :
    (eHomEquiv SSet).symm (eHomEquiv SSet f ≫ toCatInftyΔ.map A B) =
      ObjectProperty.homMk (InducedCategory.homMk
        (eqToHom (toCatInftyΔ_obj_toSSet A) ≫ f.hom ≫
          eqToHom (toCatInftyΔ_obj_toSSet B).symm)) := by
  apply (eHomEquiv SSet).injective
  rw [Equiv.apply_symm_apply,
    ← cancel_mono (eqToHom (toCatInftyΔ_sHom_eq A B) ≫ (sHom A B).core.ι)]
  have hL :
      (eHomEquiv SSet f ≫ toCatInftyΔ.map A B) ≫
          eqToHom (toCatInftyΔ_sHom_eq A B) ≫ (sHom A B).core.ι =
        eHomEquiv SSet f := by
    simp only [Category.assoc, toCatInftyΔ_map_ι, Category.comp_id]
  exact hL.trans (by
    rw [← toCatInftyΔHomToSpaces_eq]
    exact (eHomEquiv_comp_toCatInftyΔHomToSpaces f).symm)

/-- An object of `CatInftyΔ` lies in the object range of `SpacesΔ.toCatInftyΔ` if and only if its
underlying simplicial set is a Kan complex. -/
@[simp↓]
lemma mem_range_toCatInftyΔ_obj_iff (A : CatInftyΔ.{u}) :
    A ∈ Set.range toCatInftyΔ.{u}.obj ↔ KanComplex A.obj.toSSet :=
  ⟨by rintro ⟨B, rfl⟩; exact B.property,
    fun h ↦ ⟨⟨A.obj.toSSet, h⟩, ObjectProperty.FullSubcategory.ext rfl⟩⟩

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

/-- `spacesToCatInfty` sends the vertex `(SimplicialNerve.vertexEquiv SpacesΔ).symm A` to
`(SimplicialNerve.vertexEquiv CatInftyΔ).symm (SpacesΔ.toCatInftyΔ.obj A)`. -/
@[simp↓]
lemma spacesToCatInfty_app_vertexEquiv_symm (A : SpacesΔ.{u}) :
    spacesToCatInfty.{u}.app (op ⦋0⦌) ((SimplicialNerve.vertexEquiv SpacesΔ.{u}).symm A) =
      (SimplicialNerve.vertexEquiv CatInftyΔ.{u}).symm (SpacesΔ.toCatInftyΔ.obj A) :=
  SimplicialNerve.simplicialNerveMap_app_vertexEquiv_symm SpacesΔ.toCatInftyΔ A

/-- On edges, `spacesToCatInfty` preserves the underlying map of simplicial sets. -/
@[simp]
lemma edgeMk_map_spacesToCatInfty {A B : SpacesΔ.{u}} (f : A ⟶ B) :
    (SimplicialNerve.edgeMk f).map spacesToCatInfty.{u} =
      (SimplicialNerve.edgeMk (ObjectProperty.homMk (InducedCategory.homMk
          (eqToHom (SpacesΔ.toCatInftyΔ_obj_toSSet A) ≫ f.hom ≫
            eqToHom (SpacesΔ.toCatInftyΔ_obj_toSSet B).symm)) :
          SpacesΔ.toCatInftyΔ.obj A ⟶ SpacesΔ.toCatInftyΔ.obj B)).ofEq
        (spacesToCatInfty_app_vertexEquiv_symm A).symm
        (spacesToCatInfty_app_vertexEquiv_symm B).symm := by
  refine SSet.Edge.ext ?_
  calc
    ((SimplicialNerve.edgeMk f).map spacesToCatInfty.{u}).edge
      = ((SimplicialNerve.edgeMk f).map (simplicialNerveMap SpacesΔ.toCatInftyΔ.{u})).edge :=
        congrArg (fun g ↦ ((SimplicialNerve.edgeMk f).map g).edge) spacesToCatInfty_def
    _ = ((SimplicialNerve.edgeMk
          ((eHomEquiv SSet).symm (eHomEquiv SSet f ≫ SpacesΔ.toCatInftyΔ.map A B))).ofEq
          (SimplicialNerve.simplicialNerveMap_app_vertexEquiv_symm
            SpacesΔ.toCatInftyΔ A).symm
          (SimplicialNerve.simplicialNerveMap_app_vertexEquiv_symm
            SpacesΔ.toCatInftyΔ B).symm).edge :=
        congrArg SSet.Edge.edge
          (SimplicialNerve.edgeMk_map_simplicialNerveMap SpacesΔ.toCatInftyΔ f)
    _ = (SimplicialNerve.edgeMk
          ((eHomEquiv SSet).symm (eHomEquiv SSet f ≫ SpacesΔ.toCatInftyΔ.map A B))).edge :=
        SSet.Edge.ofEq_edge _ _ _
    _ = (SimplicialNerve.edgeMk (ObjectProperty.homMk (InducedCategory.homMk
          (eqToHom (SpacesΔ.toCatInftyΔ_obj_toSSet A) ≫ f.hom ≫
            eqToHom (SpacesΔ.toCatInftyΔ_obj_toSSet B).symm)) :
          SpacesΔ.toCatInftyΔ.obj A ⟶ SpacesΔ.toCatInftyΔ.obj B)).edge := by
        rw [SpacesΔ.eHomEquiv_symm_toCatInftyΔ_map]
    _ = _ := (SSet.Edge.ofEq_edge _ _ _).symm

/-- On arbitrary edges, `spacesToCatInfty` preserves the underlying map of simplicial sets. -/
@[simp]
lemma homEquiv_ofEq_map_spacesToCatInfty {A B : SpacesΔ.{u}}
    (e : spaces.{u}.Edge ((SimplicialNerve.vertexEquiv SpacesΔ.{u}).symm A)
      ((SimplicialNerve.vertexEquiv SpacesΔ.{u}).symm B)) :
    SimplicialNerve.homEquiv
      ((e.map spacesToCatInfty.{u}).ofEq
        (spacesToCatInfty_app_vertexEquiv_symm A)
        (spacesToCatInfty_app_vertexEquiv_symm B)) =
      ObjectProperty.homMk (InducedCategory.homMk
        (eqToHom (SpacesΔ.toCatInftyΔ_obj_toSSet A) ≫ (SimplicialNerve.homEquiv e).hom ≫
          eqToHom (SpacesΔ.toCatInftyΔ_obj_toSSet B).symm)) :=
  (SimplicialNerve.homEquiv_ofEq_map_simplicialNerveMap SpacesΔ.toCatInftyΔ e).trans
    (SpacesΔ.eHomEquiv_symm_toCatInftyΔ_map _)

/-- The quasicategory `Spaces` of small Kan complexes is isomorphic to the full enhanced
subcategory of `Cat∞` spanned by the Kan complexes. -/
noncomputable def spacesIsoFullSubcategory :
    spaces.{u} ≅
      (catInfty.{u}.fullEnhancedSubcategory
        fun x ↦ KanComplex (SimplicialNerve.vertexEquiv CatInftyΔ.{u} x).obj.toSSet :
          SSet.{u + 1}) :=
  SimplicialNerve.fullSubcategoryIso SpacesΔ.toCatInftyΔ.{u}
    SpacesΔ.toCatInftyΔ_obj_injective (fun A ↦ KanComplex A.obj.toSSet)
    fun A ↦ (SpacesΔ.mem_range_toCatInftyΔ_obj_iff A).symm

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
    (fun A ↦ KanComplex A.obj.toSSet) fun A ↦ (SpacesΔ.mem_range_toCatInftyΔ_obj_iff A).symm

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
