/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.StrictPseudofunctor
public import TauCeti.CategoryTheory.DoubleCategory.Globular
public import TauCeti.CategoryTheory.DoubleCategory.Functor

/-!
# The globular strict bicategories of a double category

The horizontal edges and horizontal globular cells of a strict double category form a strict
bicategory. Its whiskering operations are horizontal pastings with identity cells; its
associators and unitors are induced by the equalities in the horizontal edge category.
Interchange supplies the exchange law. Applying the construction to the transpose gives the
vertical strict bicategory, with globular cells read from left to right.

For a double category with free path boundaries, this constructs the strict path 2-category
in which chosen representations compare paths with singleton generators. In particular its
coherence is derived from the double category laws, without extra coherence assumptions.

The construction uses Mathlib's `Bicategory` and `Bicategory.Strict`. Object wrappers keep the
two directions separate from the explicitly supplied edge category structures.
`StrictDoubleFunctor.toHorizontalBicategory` sends a strict double functor to a strict
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

instance : CategoryStruct D.HorizontalBicategory where
  Hom a b := D.HorizontalGlobular a.obj b.obj
  id a := ⟨edgeId H a.obj⟩
  comp f g := ⟨edgeComp H f.edge g.edge⟩

instance homCategory (a b : D.HorizontalBicategory) : Category.{s} (a ⟶ b) :=
  D.instCategoryHorizontalGlobular a.obj b.obj

variable {D} {a b c d : D.HorizontalBicategory}

@[simp]
theorem id_edge (a : D.HorizontalBicategory) : (𝟙 a : a ⟶ a).edge = edgeId H a.obj :=
  rfl

@[simp]
theorem comp_edge (f : a ⟶ b) (g : b ⟶ c) : (f ≫ g).edge = edgeComp H f.edge g.edge :=
  rfl

/-- Horizontal edges and horizontal globular cells form a bicategory. Coherence maps come from
edge equalities, and their laws follow from the strict double category laws. -/
instance : Bicategory.{s, h} D.HorizontalBicategory where
  toCategoryStruct := inferInstance
  homCategory := homCategory D
  whiskerLeft {_ _ _} f {_ _} α := ⟨D.hComp (D.vId f.edge) α.cell⟩
  whiskerRight α g := ⟨D.hComp α.cell (D.vId g.edge)⟩
  associator f g h := eqToIso
    (HorizontalGlobular.ext (Category.assoc (self := H) f.edge g.edge h.edge))
  leftUnitor f := eqToIso (HorizontalGlobular.ext (Category.id_comp (self := H) f.edge))
  rightUnitor f := eqToIso (HorizontalGlobular.ext (Category.comp_id (self := H) f.edge))
  whiskerLeft_id f g := (D.hWhiskerLeft f.edge).map_id g
  whiskerLeft_comp {_ _ _} f {_ _ _} α β := (D.hWhiskerLeft f.edge).map_comp α β
  id_whiskerRight f g := (D.hWhiskerRight g.edge).map_id f
  comp_whiskerRight α β g := (D.hWhiskerRight g.edge).map_comp α β
  id_whiskerLeft α := by
    apply HorizontalGlobular.hom_ext
    simp only [eqToIso.hom, eqToIso.inv]
    rw [eqToHom_comp_cell, comp_cell, eqToHom_cell]
    simp
  comp_whiskerLeft {_ _ _ _} f g {_ _} α := by
    apply HorizontalGlobular.hom_ext
    simp only [eqToIso.hom, eqToIso.inv]
    rw [eqToHom_comp_cell, comp_cell, eqToHom_cell]
    simp only [vComp_cast_bottom, vComp_vId, Cell.cast_cast]
    simp [D.vId_comp, D.hComp_assoc]
  whiskerRight_id α := by
    apply HorizontalGlobular.hom_ext
    simp only [eqToIso.hom, eqToIso.inv]
    rw [eqToHom_comp_cell, comp_cell, eqToHom_cell]
    simp
  whiskerRight_comp α g h := by
    apply HorizontalGlobular.hom_ext
    simp only [eqToIso.hom, eqToIso.inv]
    rw [eqToHom_comp_cell, comp_cell, eqToHom_cell]
    simp only [vComp_cast_bottom, vComp_vId, Cell.cast_cast]
    simp [D.vId_comp, D.hComp_assoc]
  whisker_assoc {_ _ _ _} f {_ _} α h := by
    apply HorizontalGlobular.hom_ext
    simp only [eqToIso.hom, eqToIso.inv]
    rw [eqToHom_comp_cell, comp_cell, eqToHom_cell]
    simp [D.hComp_assoc]
  whisker_exchange α β := by
    apply hom_ext
    rw [comp_cell, comp_cell]
    simp [D.interchange]
  pentagon f g h i := by
    simp only [eqToIso.hom]
    rw [HorizontalGlobular.hComp_eqToHom_vId, HorizontalGlobular.hComp_vId_eqToHom]
    simp only [eqToHom_trans]
  triangle f g := by
    simp only [eqToIso.hom]
    rw [HorizontalGlobular.hComp_eqToHom_vId, HorizontalGlobular.hComp_vId_eqToHom]
    simp only [eqToHom_trans]

/-- The horizontal globular bicategory is strict, including its specified coherence maps. -/
instance : Bicategory.Strict D.HorizontalBicategory where
  id_comp f := HorizontalGlobular.ext (Category.id_comp (self := H) f.edge)
  comp_id f := HorizontalGlobular.ext (Category.comp_id (self := H) f.edge)
  assoc f g h := HorizontalGlobular.ext (Category.assoc (self := H) f.edge g.edge h.edge)
  leftUnitor_eqToIso _ := rfl
  rightUnitor_eqToIso _ := rfl
  associator_eqToIso _ _ _ := rfl

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

/-- A strict double functor acts on horizontal globular hom-categories. Vertical identity
boundaries are identified using preservation of vertical identities. The body is exposed so
that the boundary types of its cell formulas compute. -/
@[expose]
def horizontalGlobularFunctor (F : StrictDoubleFunctor D₁ D₂) (a b : O₁) :
    D₁.HorizontalGlobular a b ⥤ D₂.HorizontalGlobular (F.obj a) (F.obj b) where
  obj p := ⟨F.hMap p.edge⟩
  map α := ⟨(F.map α.cell).cast rfl rfl (F.vMap_id a) (F.vMap_id b)⟩
  map_id p := by
    ext
    simp
  map_comp α β := by
    ext
    simp [HorizontalGlobular.comp_cell]

@[simp]
theorem horizontalGlobularFunctor_obj_edge (F : StrictDoubleFunctor D₁ D₂) (a b : O₁)
    (p : D₁.HorizontalGlobular a b) :
    ((F.horizontalGlobularFunctor a b).obj p).edge = F.hMap p.edge :=
  (rfl)

@[simp]
theorem horizontalGlobularFunctor_map_cell (F : StrictDoubleFunctor D₁ D₂) {a b : O₁}
    {p q : D₁.HorizontalGlobular a b} (α : p ⟶ q) :
    ((F.horizontalGlobularFunctor a b).map α).cell =
      (F.map α.cell).cast rfl rfl (F.vMap_id a) (F.vMap_id b) :=
  (rfl)

/-- A strict double functor induces a strict pseudofunctor of horizontal globular bicategories.
Mathlib's constructor for strict bicategories derives preservation of the coherence maps.
The body is exposed so that the object and edge maps compute in the types of mapped cells. -/
@[expose]
def toHorizontalBicategory (F : StrictDoubleFunctor D₁ D₂) :
    StrictPseudofunctor D₁.HorizontalBicategory D₂.HorizontalBicategory :=
  StrictPseudofunctor.mk'' {
    obj a := ⟨F.obj a.obj⟩
    map f := ⟨F.hMap f.edge⟩
    map₂ {a b} {_ _} α := ⟨(F.map α.cell).cast rfl rfl (F.vMap_id a.obj) (F.vMap_id b.obj)⟩
    map₂_id f := (F.horizontalGlobularFunctor _ _).map_id f
    map₂_comp α β := (F.horizontalGlobularFunctor _ _).map_comp α β
    map_id a := HorizontalGlobular.ext (F.hMap_id a.obj)
    map_comp f g := HorizontalGlobular.ext (F.hMap_comp f.edge g.edge)
    map₂_whisker_left f _ _ α := by
      apply HorizontalGlobular.hom_ext
      rw [HorizontalGlobular.eqToHom_comp_cell, HorizontalGlobular.comp_cell,
      HorizontalGlobular.eqToHom_cell]
      simp only [vComp_cast_bottom, vComp_vId, Cell.cast_cast,
        HorizontalBicategory.whiskerLeft_cell, map_hComp, map_vId]
      have hid : D₂.vId (F.hMap f.edge) = (F.map (D₁.vId f.edge)).cast rfl rfl
          (F.vMap_id _) (F.vMap_id _) := by simp
      rw [hid]
      simp only [hComp_cast_cast]
      simp only [Cell.cast_cast, Cell.cast_rfl]
    map₂_whisker_right α g := by
      apply HorizontalGlobular.hom_ext
      rw [HorizontalGlobular.eqToHom_comp_cell, HorizontalGlobular.comp_cell,
      HorizontalGlobular.eqToHom_cell]
      simp only [vComp_cast_bottom, vComp_vId, Cell.cast_cast,
        HorizontalBicategory.whiskerRight_cell, map_hComp, map_vId]
      have hid : D₂.vId (F.hMap g.edge) = (F.map (D₁.vId g.edge)).cast rfl rfl
          (F.vMap_id _) (F.vMap_id _) := by simp
      rw [hid]
      simp only [hComp_cast_cast]
      simp only [Cell.cast_cast, Cell.cast_rfl] }

@[simp]
theorem toHorizontalBicategory_obj_obj (F : StrictDoubleFunctor D₁ D₂)
    (a : D₁.HorizontalBicategory) :
    (F.toHorizontalBicategory.obj a).obj = F.obj a.obj :=
  (rfl)

@[simp]
theorem toHorizontalBicategory_map_edge (F : StrictDoubleFunctor D₁ D₂)
    {a b : D₁.HorizontalBicategory} (f : a ⟶ b) :
    (F.toHorizontalBicategory.map f).edge = F.hMap f.edge :=
  (rfl)

@[simp]
theorem toHorizontalBicategory_map₂_cell (F : StrictDoubleFunctor D₁ D₂)
    {a b : D₁.HorizontalBicategory} {f g : a ⟶ b} (α : f ⟶ g) :
    (F.toHorizontalBicategory.map₂ α).cell =
      (F.map α.cell).cast rfl rfl (F.vMap_id a.obj) (F.vMap_id b.obj) :=
  (rfl)

/-- The identity double functor acts identically on each globular hom-category. -/
@[simp]
theorem horizontalGlobularFunctor_id (a b : O₁) :
    (StrictDoubleFunctor.id D₁).horizontalGlobularFunctor a b =
      𝟭 (D₁.HorizontalGlobular a b) :=
  (rfl)

/-- The identity double functor induces the identity strict pseudofunctor. -/
@[simp]
theorem toHorizontalBicategory_id :
    (StrictDoubleFunctor.id D₁).toHorizontalBicategory =
      StrictPseudofunctor.id D₁.HorizontalBicategory := by
  rfl

/-- The action on globular hom-categories preserves composition of double functors. -/
@[simp]
theorem horizontalGlobularFunctor_comp {O₃ : Type u₃} {H₃ : Category.{h₃} O₃}
    {V₃ : Category.{v₃} O₃} {D₃ : StrictDoubleCategory.{s₃} O₃ H₃ V₃}
    (F : StrictDoubleFunctor D₁ D₂) (G : StrictDoubleFunctor D₂ D₃) (a b : O₁) :
    (F.comp G).horizontalGlobularFunctor a b =
      F.horizontalGlobularFunctor a b ⋙ G.horizontalGlobularFunctor (F.obj a) (F.obj b) := by
  -- Compute the object maps before applying dependent functor extensionality.
  dsimp only [horizontalGlobularFunctor, StrictDoubleFunctor.comp]
  refine Functor.ext ?_ ?_
  · intro p
    rfl
  · intro p q α
    apply HorizontalGlobular.hom_ext
    simp

end TauCeti.StrictDoubleFunctor
