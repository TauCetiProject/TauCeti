/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.ContractedProduct
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Torsor.Automorphisms

/-!
# Extension of the structure group as a functor

For a homomorphism `φ : G ⟶ H` of sheaves of groups, `Torsor.mapFunctor φ` extends the
structure group of torsors. Its action on morphisms is characterized by the naturality of
`Torsor.toMap`, using the universal property `Torsor.mapLift` of the contracted product.

This functor allows lifting problems for torsors to be expressed as costructured arrows.
The contracted product convention is that of Giraud, *Cohomologie non abélienne*, III §1.3.
-/

public noncomputable section

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory.Sheaf.Torsor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]
  {G H : Sheaf J GrpCat.{w}}

/-- Extension of an equivariant morphism along a homomorphism of sheaves of groups. -/
def mapHom (φ : G ⟶ H) {P Q : Torsor G} (f : P ⟶ Q) : P.map φ ⟶ Q.map φ :=
  P.mapLift (f.hom ≫ Q.toMap φ) fun U g p ↦ by simp [f.map_smul]

/-- The map to the contracted product is natural in the torsor. -/
@[reassoc (attr := simp)]
lemma toMap_mapHom (φ : G ⟶ H) {P Q : Torsor G} (f : P ⟶ Q) :
    P.toMap φ ≫ (mapHom φ f).hom = f.hom ≫ Q.toMap φ :=
  P.toMap_mapLift _ _

@[simp]
lemma mapHom_id (φ : G ⟶ H) (P : Torsor G) : mapHom φ (𝟙 P) = 𝟙 (P.map φ) := by
  apply map_hom_ext
  simp

@[simp]
lemma mapHom_comp (φ : G ⟶ H) {P Q R : Torsor G} (f : P ⟶ Q) (g : Q ⟶ R) :
    mapHom φ (f ≫ g) = mapHom φ f ≫ mapHom φ g := by
  apply map_hom_ext
  simp [Category.assoc]

/-- Extension of the structure group, as a functor on the groupoids of torsors.

The body is exposed so that the objects of its costructured-arrow fibres have structure
isomorphisms with source `P.map φ`. -/
@[expose] def mapFunctor (φ : G ⟶ H) : Torsor G ⥤ Torsor H where
  obj P := P.map φ
  map f := mapHom φ f

@[simp]
lemma mapFunctor_obj (φ : G ⟶ H) (P : Torsor G) : (mapFunctor φ).obj P = P.map φ :=
  (rfl)

@[simp]
lemma mapFunctor_map (φ : G ⟶ H) {P Q : Torsor G} (f : P ⟶ Q) :
    (mapFunctor φ).map f = mapHom φ f :=
  (rfl)

/-- A translation by a section killed by `φ` extends to the identity. -/
lemma mapHom_translationHom_eq_id [∀ U, IsMulCommutative (G.obj.obj U)]
    (φ : G ⟶ H) (P : Torsor G) (s : (G.obj ⋙ forget GrpCat).sections)
    (hs : ∀ U, φ.hom.app U (GrpCat.sectionsπMonoidHom G.obj U s) = 1) :
    mapHom φ (P.translationHom s) = 𝟙 (P.map φ) := by
  apply map_hom_ext
  rw [toMap_mapHom]
  ext U p
  exact (congrArg ((P.toMap φ).hom.app U) (P.translationHom_hom_app s U p)).trans
    ((Torsor.toMap_smul φ P (GrpCat.sectionsπMonoidHom G.obj U s) p).trans (by
      rw [hs U]
      exact one_smul _ _))

end CategoryTheory.Sheaf.Torsor
