/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Enriched.Basic
public import TauCeti.AlgebraicTopology.SimplicialSet.PiZero

/-!
# The homotopy category of a simplicially enriched category

For a category `C` enriched over simplicial sets, the homotopy category `hC` has the same objects,
and its morphisms from `X` to `Y` are the connected components of the mapping simplicial set
`X ⟶[SSet] Y`. Composition is induced by the enriched composition: the connected components of a
product of simplicial sets are the pairs of connected components (`SSet.π₀ProdEquiv`), so
`SSet.π₀Functor` is monoidal and transports the enrichment to an enrichment in types, that is, to
an ordinary category. Every vertex `f` of `X ⟶[SSet] Y` gives a morphism
`SimplicialHomotopyCategory.homMk f`, every morphism arises this way, and two vertices give the same
morphism exactly when they are joined by a zigzag of edges.

An enriched functor `F` induces a functor `F.mapHomotopyCategory` of homotopy categories. Up to
canonical isomorphisms, the identity enriched functor induces the identity functor
(`CategoryTheory.EnrichedFunctor.mapHomotopyCategoryId`) and composites induce composites
(`F.mapHomotopyCategoryComp G`). The homotopy category is the
invariant on which Dwyer–Kan equivalences of simplicial categories are required to be essentially
surjective.

## Main definitions

* `TauCeti.SimplicialHomotopyCategory C`: the homotopy category of a simplicially enriched
  category `C`.
* `TauCeti.SimplicialHomotopyCategory.homEquiv`: its morphisms are the connected components of
  the mapping simplicial sets.
* `TauCeti.SimplicialHomotopyCategory.homMk`: the morphism given by a vertex of a mapping
  simplicial set.
* `CategoryTheory.EnrichedFunctor.mapHomotopyCategory`: the functor of homotopy categories
  induced by an enriched functor.

## Main results

* `TauCeti.SimplicialHomotopyCategory.homMk_eId` and
  `TauCeti.SimplicialHomotopyCategory.homMk_comp_homMk`: identities and composites are the
  components of the enriched identities and composites.
* `CategoryTheory.EnrichedFunctor.mapHomotopyCategoryId` and
  `CategoryTheory.EnrichedFunctor.mapHomotopyCategoryComp`: functoriality.

## References

* J. Lurie, *Higher Topos Theory*, §1.1.4, where the homotopy category `hC` of a simplicial
  category is enriched in the homotopy category of spaces; its underlying category, obtained by
  taking path components, is the category constructed here.
* J. E. Bergner, *A model category structure on the category of simplicial categories*,
  Trans. Amer. Math. Soc. 359 (2007), the category `π₀ C`.
-/

public section

open CategoryTheory MonoidalCategory Opposite Simplicial

universe v u u' u''

namespace TauCeti

noncomputable section

variable (C : Type u) [EnrichedCategory SSet.{v} C]

/-- The homotopy category of a category enriched over simplicial sets: it has the objects of `C`,
and its morphisms are the connected components of the mapping simplicial sets. -/
structure SimplicialHomotopyCategory where
  /-- An object of `C` as an object of its homotopy category. -/
  of ::
  /-- The object of `C` underlying an object of its homotopy category. -/
  as : C

namespace SimplicialHomotopyCategory

/-- The enrichment in types obtained by transporting the enrichment of `C` along the monoidal
functor `SSet.π₀Functor`. -/
instance : EnrichedCategory (Type v) (SimplicialHomotopyCategory C) where
  Hom X Y := SSet.π₀ (X.as ⟶[SSet.{v}] Y.as)
  id X := eId (Type v) (C := TransportEnrichment SSet.π₀Functor.{v} C) X.as
  comp X Y Z := eComp (Type v) (C := TransportEnrichment SSet.π₀Functor.{v} C) X.as Y.as Z.as
  id_comp X Y := e_id_comp (Type v) (C := TransportEnrichment SSet.π₀Functor.{v} C) X.as Y.as
  comp_id X Y := e_comp_id (Type v) (C := TransportEnrichment SSet.π₀Functor.{v} C) X.as Y.as
  assoc W X Y Z :=
    e_assoc (Type v) (C := TransportEnrichment SSet.π₀Functor.{v} C) W.as X.as Y.as Z.as

/-- The category structure is the one of the type-enriched category obtained by transporting the
enrichment of `C` along the monoidal functor `SSet.π₀Functor`. -/
instance : Category.{v} (SimplicialHomotopyCategory C) :=
  categoryOfEnrichedCategoryType _

variable {C}

/-- The morphisms of the homotopy category are the connected components of the mapping simplicial
sets. -/
def homEquiv {X Y : SimplicialHomotopyCategory C} : (X ⟶ Y) ≃ SSet.π₀ (X.as ⟶[SSet.{v}] Y.as) :=
  Equiv.refl _

/-- The identity of the homotopy category is the image of the unit of `SSet.π₀Functor` under the
map of connected components of the enriched identity. -/
lemma id_def (X : SimplicialHomotopyCategory C) :
    𝟙 X = homEquiv.symm
      (SSet.mapπ₀ (eId SSet.{v} X.as) (Functor.LaxMonoidal.ε SSet.π₀Functor PUnit.unit)) :=
  (rfl)

/-- Composition in the homotopy category is the tensorator of `SSet.π₀Functor` followed by the map
of connected components of the enriched composition. -/
lemma comp_def {X Y Z : SimplicialHomotopyCategory C} (f : X ⟶ Y) (g : Y ⟶ Z) :
    f ≫ g = homEquiv.symm (SSet.mapπ₀ (eComp SSet.{v} X.as Y.as Z.as)
      (Functor.LaxMonoidal.μ SSet.π₀Functor _ _ (homEquiv f, homEquiv g))) :=
  (rfl)

/-- The morphism of the homotopy category given by a vertex of a mapping simplicial set. -/
def homMk {X Y : C} (f : (X ⟶[SSet.{v}] Y) _⦋0⦌) : of X ⟶ of Y :=
  homEquiv.symm (SSet.π₀.mk f)

/-- The component of the morphism given by a vertex is the component of that vertex. -/
@[simp]
lemma homEquiv_homMk {X Y : C} (f : (X ⟶[SSet.{v}] Y) _⦋0⦌) :
    homEquiv (homMk f) = SSet.π₀.mk f :=
  (rfl)

/-- The morphism with the component of a vertex is the morphism given by that vertex. -/
@[simp]
lemma homEquiv_symm_mk {X Y : C} (f : (X ⟶[SSet.{v}] Y) _⦋0⦌) :
    homEquiv.symm (SSet.π₀.mk f) = homMk f :=
  (rfl)

/-- Every morphism of the homotopy category is given by a vertex of a mapping simplicial set. -/
lemma homMk_surjective {X Y : C} : Function.Surjective (homMk (X := X) (Y := Y)) :=
  homEquiv.symm.surjective.comp SSet.π₀.mk_surjective

/-- Two vertices give the same morphism of the homotopy category exactly when they are joined by a
zigzag of edges. -/
lemma homMk_eq_homMk_iff {X Y : C} (f g : (X ⟶[SSet.{v}] Y) _⦋0⦌) :
    homMk f = homMk g ↔ Relation.EqvGen SSet.π₀Rel f g := by
  rw [← SSet.π₀.mk_eq_mk_iff, ← homEquiv_homMk, ← homEquiv_homMk, homEquiv.apply_eq_iff_eq]

/-- Vertices joined by an edge give the same morphism of the homotopy category. -/
lemma homMk_eq_homMk {X Y : C} {f g : (X ⟶[SSet.{v}] Y) _⦋0⦌} (e : SSet.Edge f g) :
    homMk f = homMk g :=
  congrArg homEquiv.symm (SSet.π₀.sound e)

/-- The identity of the homotopy category is the component of the enriched identity. -/
lemma homMk_eId (X : C) : homMk ((eId SSet.{v} X).app (op ⦋0⦌) PUnit.unit) = 𝟙 (of X) := by
  rw [id_def, SSet.ε_π₀Functor_apply, SSet.mapπ₀_mk, homEquiv_symm_mk]

/-- Composition in the homotopy category is induced by the enriched composition. -/
@[simp]
lemma homMk_comp_homMk {X Y Z : C} (f : (X ⟶[SSet.{v}] Y) _⦋0⦌) (g : (Y ⟶[SSet.{v}] Z) _⦋0⦌) :
    homMk f ≫ homMk g = homMk ((eComp SSet.{v} X Y Z).app (op ⦋0⦌) (f, g)) := by
  rw [comp_def, homEquiv_homMk, homEquiv_homMk, SSet.μ_π₀Functor_mk]
  exact SSet.mapπ₀_mk _ _

end SimplicialHomotopyCategory

end

end TauCeti

namespace CategoryTheory.EnrichedFunctor

open TauCeti SimplicialHomotopyCategory

noncomputable section

variable {C : Type u} {D : Type u'} {E : Type u''} [EnrichedCategory SSet.{v} C]
  [EnrichedCategory SSet.{v} D] [EnrichedCategory SSet.{v} E]

/-- An enriched functor sends the enriched identity of `X`, as a vertex, to that of `F.obj X`. -/
lemma map_app_eId_app (F : EnrichedFunctor SSet.{v} C D) (X : C) :
    (F.map X X).app (op ⦋0⦌) ((eId SSet.{v} X).app (op ⦋0⦌) PUnit.unit) =
      (eId SSet.{v} (F.obj X)).app (op ⦋0⦌) PUnit.unit :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (F.map_id X) (op ⦋0⦌)) PUnit.unit

/-- An enriched functor sends the enriched composite of two vertices to the enriched composite of
their images. -/
lemma map_app_eComp_app (F : EnrichedFunctor SSet.{v} C D) {X Y Z : C}
    (f : (X ⟶[SSet.{v}] Y) _⦋0⦌) (g : (Y ⟶[SSet.{v}] Z) _⦋0⦌) :
    (F.map X Z).app (op ⦋0⦌) ((eComp SSet.{v} X Y Z).app (op ⦋0⦌) (f, g)) =
      (eComp SSet.{v} (F.obj X) (F.obj Y) (F.obj Z)).app (op ⦋0⦌)
        ((F.map X Y).app (op ⦋0⦌) f, (F.map Y Z).app (op ⦋0⦌) g) :=
  ConcreteCategory.congr_hom (NatTrans.congr_app (F.map_comp X Y Z) (op ⦋0⦌)) ⟨f, g⟩

/-- The functor of homotopy categories induced by a functor of simplicially enriched categories:
it acts on morphisms by the maps of connected components of the maps of mapping simplicial
sets. -/
-- Exposed so that `F.mapHomotopyCategory.obj X` unfolds to `of (F.obj X.as)`: the public statements
-- about its action on morphisms, such as `mapHomotopyCategory_map_homMk`, need this to typecheck.
@[expose]
def mapHomotopyCategory (F : EnrichedFunctor SSet.{v} C D) :
    SimplicialHomotopyCategory C ⥤ SimplicialHomotopyCategory D where
  obj X := of (F.obj X.as)
  map f := homEquiv.symm (SSet.mapπ₀ (F.map _ _) (homEquiv f))
  map_id := by
    rintro ⟨X⟩
    rw [← homMk_eId]
    exact (congrArg homMk (map_app_eId_app F X)).trans (homMk_eId _)
  map_comp := by
    rintro ⟨X⟩ ⟨Y⟩ ⟨Z⟩ f g
    obtain ⟨f, rfl⟩ := homMk_surjective (X := X) (Y := Y) f
    obtain ⟨g, rfl⟩ := homMk_surjective (X := Y) (Y := Z) g
    rw [homMk_comp_homMk]
    exact (congrArg homMk (map_app_eComp_app F f g)).trans (homMk_comp_homMk _ _).symm

variable (F : EnrichedFunctor SSet.{v} C D)

/-- The induced functor sends the object of `X` to the object of `F.obj X`. -/
@[simp]
lemma mapHomotopyCategory_obj_of (X : C) : F.mapHomotopyCategory.obj (of X) = of (F.obj X) :=
  (rfl)

/-- The induced functor acts on morphisms by the maps of connected components of the maps of
mapping simplicial sets. -/
lemma homEquiv_mapHomotopyCategory_map {X Y : SimplicialHomotopyCategory C} (f : X ⟶ Y) :
    homEquiv (F.mapHomotopyCategory.map f) = SSet.mapπ₀ (F.map X.as Y.as) (homEquiv f) :=
  (rfl)

/-- The induced functor sends the morphism given by a vertex `f` to the morphism given by its
image under the map of mapping simplicial sets. -/
@[simp]
lemma mapHomotopyCategory_map_homMk {X Y : C} (f : (X ⟶[SSet.{v}] Y) _⦋0⦌) :
    F.mapHomotopyCategory.map (homMk f) = homMk ((F.map X Y).app (op ⦋0⦌) f) :=
  (rfl)

/-- If the maps of mapping simplicial sets are injective on connected components, the induced
functor of homotopy categories is faithful. -/
lemma faithful_mapHomotopyCategory
    (h : ∀ X Y : C, Function.Injective (SSet.mapπ₀ (F.map X Y))) :
    F.mapHomotopyCategory.Faithful where
  map_injective {X Y} := homEquiv.symm.injective.comp ((h X.as Y.as).comp homEquiv.injective)

/-- If the maps of mapping simplicial sets are surjective on connected components, the induced
functor of homotopy categories is full. -/
lemma full_mapHomotopyCategory
    (h : ∀ X Y : C, Function.Surjective (SSet.mapπ₀ (F.map X Y))) :
    F.mapHomotopyCategory.Full where
  map_surjective {X Y} :=
    homEquiv.symm.surjective.comp ((h X.as Y.as).comp homEquiv.surjective)

/-- The identity enriched functor induces the identity of the homotopy category. -/
def mapHomotopyCategoryId : (EnrichedFunctor.id SSet.{v} C).mapHomotopyCategory ≅ 𝟭 _ :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun {X Y} f ↦ by
    obtain ⟨f, rfl⟩ := homMk_surjective (X := X.as) (Y := Y.as) f
    -- Both sides are `homMk f` up to the definition of the action on objects.
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The components of `mapHomotopyCategoryId` are identities. -/
@[simp]
lemma mapHomotopyCategoryId_hom_app (X : SimplicialHomotopyCategory C) :
    (mapHomotopyCategoryId (C := C)).hom.app X = 𝟙 X :=
  (rfl)

/-- The components of the inverse of `mapHomotopyCategoryId` are identities. -/
@[simp]
lemma mapHomotopyCategoryId_inv_app (X : SimplicialHomotopyCategory C) :
    (mapHomotopyCategoryId (C := C)).inv.app X = 𝟙 X :=
  (rfl)

/-- Composite enriched functors induce composite functors of homotopy categories. -/
def mapHomotopyCategoryComp (G : EnrichedFunctor SSet.{v} D E) :
    (EnrichedFunctor.comp SSet.{v} F G).mapHomotopyCategory ≅
      F.mapHomotopyCategory ⋙ G.mapHomotopyCategory :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun {X Y} f ↦ by
    obtain ⟨f, rfl⟩ := homMk_surjective (X := X.as) (Y := Y.as) f
    -- Both sides are `homMk (G.map (F.map f))` up to the definition of the action on objects.
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The components of `F.mapHomotopyCategoryComp G` are identities. -/
@[simp]
lemma mapHomotopyCategoryComp_hom_app (G : EnrichedFunctor SSet.{v} D E)
    (X : SimplicialHomotopyCategory C) :
    (F.mapHomotopyCategoryComp G).hom.app X = 𝟙 (of (G.obj (F.obj X.as))) :=
  (rfl)

/-- The components of the inverse of `F.mapHomotopyCategoryComp G` are identities. -/
@[simp]
lemma mapHomotopyCategoryComp_inv_app (G : EnrichedFunctor SSet.{v} D E)
    (X : SimplicialHomotopyCategory C) :
    (F.mapHomotopyCategoryComp G).inv.app X = 𝟙 (of (G.obj (F.obj X.as))) :=
  (rfl)

end

end CategoryTheory.EnrichedFunctor
