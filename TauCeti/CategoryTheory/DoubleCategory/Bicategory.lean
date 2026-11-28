/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.CatEnriched
public import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
public import TauCeti.CategoryTheory.DoubleCategory.Globular.Basic

/-!
# The globular strict bicategories of a double category

The horizontal edges and horizontal globular cells of a strict double category form a strict
bicategory. Its whiskering operations are horizontal pastings with identity cells; its
associators and unitors are induced by the equalities in the horizontal edge category.
Interchange supplies the exchange law. Applying the construction to the transpose gives the
vertical strict bicategory, with globular cells read from left to right.

Mathlib's `CatEnriched` construction supplies the `Bicategory` and `Bicategory.Strict`
instances from the globular hom-categories and horizontal pasting. Object wrappers keep the
two directions separate from the explicitly supplied edge category structures.
`StrictDoubleFunctor.mapHorizontalBicategory` sends a strict double functor to a strict
pseudofunctor, including its action on globular cells and coherence maps.

## References

* A. D. Fairbanks and M. Shulman, *Doubly weak double categories*, Applied Categorical
  Structures **34** (2026), article 26; arXiv:2506.23651, Definitions 3.1–3.3.
-/

public section

universe s u h v

namespace TauCeti.StrictDoubleCategory

open CategoryTheory DoubleCategoryStruct

variable {O : Type u} {H : Category.{h} O} {V : Category.{v} O}
  (D : StrictDoubleCategory.{s} O H V)

/-- The objects of the horizontal globular bicategory of `D`. Its 1-cells are horizontal
edges and its 2-cells are horizontal globular cells. -/
@[ext]
structure HorizontalBicategory (D : StrictDoubleCategory.{s} O H V) where
  /-- The underlying object of the double category. -/
  obj : O

namespace HorizontalBicategory

open HorizontalGlobular

/-- Horizontal globular hom-categories, enriched over categories by horizontal pasting. -/
instance : EnrichedCategory Cat.{s, h} D.HorizontalBicategory where
  Hom a b := Cat.of (D.HorizontalGlobular a.obj b.obj)
  id a := (Cat.fromChosenTerminalEquiv.symm
    (⟨edgeId H a.obj⟩ : D.HorizontalGlobular a.obj a.obj)).toCatHom
  comp _ _ _ := D.hCompFunctor.toCatHom
  id_comp a b := by
    apply Cat.Hom.ext
    -- Compute the terminal-category insertion before dependent functor extensionality.
    change D.hWhiskerLeft (edgeId H a.obj) = 𝟭 (D.HorizontalGlobular a.obj b.obj)
    refine CategoryTheory.Functor.ext
      (fun f ↦ HorizontalGlobular.ext (Category.id_comp (self := H) f.edge)) ?_
    intro f g α
    apply HorizontalGlobular.hom_ext
    rw [eqToHom_comp_eqToHom_cell]
    simp
  comp_id a b := by
    apply Cat.Hom.ext
    -- Compute the terminal-category insertion before dependent functor extensionality.
    change D.hWhiskerRight (edgeId H b.obj) = 𝟭 (D.HorizontalGlobular a.obj b.obj)
    refine CategoryTheory.Functor.ext
      (fun f ↦ HorizontalGlobular.ext (Category.comp_id (self := H) f.edge)) ?_
    intro f g α
    apply HorizontalGlobular.hom_ext
    rw [eqToHom_comp_eqToHom_cell]
    simp
  assoc a b c d := by
    apply Cat.Hom.ext
    refine CategoryTheory.Functor.ext (fun f ↦ HorizontalGlobular.ext
      (Category.assoc (self := H) f.1.edge f.2.1.edge f.2.2.edge)) ?_
    intro f g α
    apply HorizontalGlobular.hom_ext
    rw [eqToHom_comp_eqToHom_cell]
    -- Compute Cat's product associator and composition bifunctors at the cell level.
    change D.hComp (D.hComp α.1.cell α.2.1.cell) α.2.2.cell =
      (D.hComp α.1.cell (D.hComp α.2.1.cell α.2.2.cell)).cast _ _ rfl rfl
    exact D.hComp_assoc _ _ _

instance : CategoryStruct D.HorizontalBicategory where
  Hom a b := D.HorizontalGlobular a.obj b.obj
  id a := ⟨edgeId H a.obj⟩
  comp f g := ⟨edgeComp H f.edge g.edge⟩

instance homCategory (a b : D.HorizontalBicategory) : Category.{s} (a ⟶ b) :=
  D.instCategoryHorizontalGlobular a.obj b.obj

/-- Horizontal globular cells form the strict bicategory of the Cat-enriched structure. -/
instance : Bicategory.{s, h} D.HorizontalBicategory :=
  -- Keep edge and hom-category projections computable in boundary-indexed cell formulas.
  { (inferInstanceAs (Bicategory (CatEnriched D.HorizontalBicategory)) :
      Bicategory D.HorizontalBicategory) with
    toCategoryStruct := inferInstance
    homCategory := homCategory D }

/-- The coherence maps are induced by the strict edge-category laws. -/
instance : Bicategory.Strict D.HorizontalBicategory :=
  inferInstanceAs (Bicategory.Strict (CatEnriched D.HorizontalBicategory))

variable {D} {a b c d : D.HorizontalBicategory}

@[simp]
theorem id_edge (a : D.HorizontalBicategory) : (𝟙 a : a ⟶ a).edge = edgeId H a.obj :=
  rfl

@[simp]
theorem comp_edge (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).edge = edgeComp H f.edge g.edge :=
  rfl

open scoped Bicategory

/-- Left whiskering is horizontal pasting with a vertical identity cell. -/
@[simp]
theorem whiskerLeft_cell (f : a ⟶ b) {g h : b ⟶ c} (α : g ⟶ h) :
    (f ◁ α).cell = D.hComp (D.vId f.edge) α.cell :=
  (rfl)

/-- Right whiskering is horizontal pasting with a vertical identity cell. -/
@[simp]
theorem whiskerRight_cell {f g : a ⟶ b} (α : f ⟶ g) (h : b ⟶ c) :
    (α ▷ h).cell = D.hComp α.cell (D.vId h.edge) :=
  (rfl)

end HorizontalBicategory

/-- The vertical globular bicategory, obtained by applying the horizontal construction to the
transpose. Its 2-cells are read from left to right and composed by horizontal pasting in `D`. -/
abbrev VerticalBicategory := D.transpose.HorizontalBicategory

namespace VerticalBicategory

open scoped Bicategory

variable {D} {a b c : D.VerticalBicategory}

/-- Left whiskering of vertical globular cells pastes a horizontal identity cell above them. -/
@[simp high]
theorem whiskerLeft_cell (f : a ⟶ b) {g h : b ⟶ c} (α : g ⟶ h) :
    (f ◁ α).cell = D.vComp (D.hId f.edge) α.cell :=
  (HorizontalBicategory.whiskerLeft_cell f α).trans
    (DoubleCategoryStruct.transpose_hComp D.toDoubleCategoryStruct _ _)

/-- Right whiskering of vertical globular cells pastes a horizontal identity cell below them. -/
@[simp high]
theorem whiskerRight_cell {f g : a ⟶ b} (α : f ⟶ g) (h : b ⟶ c) :
    (α ▷ h).cell = D.vComp α.cell (D.hId h.edge) :=
  (HorizontalBicategory.whiskerRight_cell α h).trans
    (DoubleCategoryStruct.transpose_hComp D.toDoubleCategoryStruct _ _)

end VerticalBicategory

end TauCeti.StrictDoubleCategory

namespace TauCeti.StrictDoubleFunctor

open CategoryTheory TauCeti.StrictDoubleCategory TauCeti.DoubleCategoryStruct
open scoped Bicategory

universe s₁ s₂ s₃ u₁ u₂ u₃ h₁ h₂ h₃ v₁ v₂ v₃

variable {O₁ : Type u₁} {H₁ : Category.{h₁} O₁} {V₁ : Category.{v₁} O₁}
  {O₂ : Type u₂} {H₂ : Category.{h₂} O₂} {V₂ : Category.{v₂} O₂}
  {D₁ : StrictDoubleCategory.{s₁} O₁ H₁ V₁} {D₂ : StrictDoubleCategory.{s₂} O₂ H₂ V₂}

/-- A strict double functor induces a strict pseudofunctor of horizontal globular bicategories.
It acts on objects, horizontal edges and globular cells by their double-functor maps. -/
-- Exposure lets the object and edge maps compute in mapped-cell types.
@[expose]
def mapHorizontalBicategory (F : StrictDoubleFunctor D₁ D₂) :
    StrictPseudofunctor D₁.HorizontalBicategory D₂.HorizontalBicategory :=
  StrictPseudofunctor.mk'' {
    obj a := ⟨F.obj a.obj⟩
    map f := ⟨F.hMap f.edge⟩
    map₂ {a b} {_ _} α := (F.horizontalGlobularFunctor a.obj b.obj).map α
    map₂_id f := (F.horizontalGlobularFunctor _ _).map_id f
    map₂_comp α β := (F.horizontalGlobularFunctor _ _).map_comp α β
    map_id a := HorizontalGlobular.ext (F.hMap_id a.obj)
    map_comp f g := HorizontalGlobular.ext (F.hMap_comp f.edge g.edge)
    map₂_whisker_left f _ _ α := by
      dsimp only [horizontalGlobularFunctor]
      apply HorizontalGlobular.hom_ext
      rw [HorizontalGlobular.eqToHom_comp_eqToHom_cell,
        HorizontalBicategory.whiskerLeft_cell, HorizontalBicategory.whiskerLeft_cell]
      have hid := congrArg HorizontalGlobular.Hom.cell
        ((F.horizontalGlobularFunctor _ _).map_id f)
      dsimp only [horizontalGlobularFunctor, HorizontalGlobular.id_cell] at hid
      rw [← hid]
      simp only [map_hComp, hComp_cast_cast, Cell.cast_cast]
    map₂_whisker_right α g := by
      dsimp only [horizontalGlobularFunctor]
      apply HorizontalGlobular.hom_ext
      rw [HorizontalGlobular.eqToHom_comp_eqToHom_cell,
        HorizontalBicategory.whiskerRight_cell, HorizontalBicategory.whiskerRight_cell]
      have hid := congrArg HorizontalGlobular.Hom.cell
        ((F.horizontalGlobularFunctor _ _).map_id g)
      dsimp only [horizontalGlobularFunctor, HorizontalGlobular.id_cell] at hid
      rw [← hid]
      simp only [map_hComp, hComp_cast_cast, Cell.cast_cast] }

@[simp]
theorem mapHorizontalBicategory_obj_obj (F : StrictDoubleFunctor D₁ D₂)
    (a : D₁.HorizontalBicategory) :
    (F.mapHorizontalBicategory.obj a).obj = F.obj a.obj :=
  (rfl)

@[simp]
theorem mapHorizontalBicategory_map_edge (F : StrictDoubleFunctor D₁ D₂)
    {a b : D₁.HorizontalBicategory} (f : a ⟶ b) :
    (F.mapHorizontalBicategory.map f).edge = F.hMap f.edge :=
  (rfl)

@[simp]
theorem mapHorizontalBicategory_map₂_cell (F : StrictDoubleFunctor D₁ D₂)
    {a b : D₁.HorizontalBicategory} {f g : a ⟶ b} (α : f ⟶ g) :
    (F.mapHorizontalBicategory.map₂ α).cell =
      (F.map α.cell).cast rfl rfl (F.vMap_id a.obj) (F.vMap_id b.obj) :=
  (horizontalGlobularFunctor_map_cell F α)

/-- The identity double functor induces the identity strict pseudofunctor. -/
@[simp]
theorem id_mapHorizontalBicategory :
    (StrictDoubleFunctor.id D₁).mapHorizontalBicategory =
      StrictPseudofunctor.id D₁.HorizontalBicategory := by
  rfl

/-- The induced strict pseudofunctor preserves composition of double functors. -/
@[simp]
theorem comp_mapHorizontalBicategory {O₃ : Type u₃} {H₃ : Category.{h₃} O₃}
    {V₃ : Category.{v₃} O₃} {D₃ : StrictDoubleCategory.{s₃} O₃ H₃ V₃}
    (F : StrictDoubleFunctor D₁ D₂) (G : StrictDoubleFunctor D₂ D₃) :
    (F.comp G).mapHorizontalBicategory =
      F.mapHorizontalBicategory.comp G.mapHorizontalBicategory := by
  -- Compute the object and edge maps before comparing the dependent bundled data.
  dsimp only [mapHorizontalBicategory, StrictDoubleFunctor.comp,
    StrictPseudofunctor.mk'', StrictPseudofunctor.comp,
    StrictlyUnitaryPseudofunctor.comp, Pseudofunctor.comp, PrelaxFunctor.comp,
    PrelaxFunctorStruct.comp, horizontalGlobularFunctor]
  congr 3 <;> try exact proof_irrel_heq _ _
  · dsimp only [Prefunctor.comp]
    congr 2
    funext a b f g α
    apply HorizontalGlobular.hom_ext
    simp
  · funext a
    rw [PrelaxFunctor.map₂Iso_eqToIso]
    exact (eqToIso_trans _ _).symm
  · funext a b c f g
    rw [PrelaxFunctor.map₂Iso_eqToIso]
    exact (eqToIso_trans _ _).symm

end TauCeti.StrictDoubleFunctor
