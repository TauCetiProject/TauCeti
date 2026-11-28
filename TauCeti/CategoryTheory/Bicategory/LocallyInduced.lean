/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Bicategory.Functor.Pseudofunctor
public import Mathlib.CategoryTheory.InducedCategory

/-!
# Bicategories locally induced by chosen composites

Suppose a quiver of generating arrows maps to a bicategory, with a chosen unit and binary
composition of generators. Invertible comparisons from the images of these choices to the
ambient identity and composite induce a bicategory on the generators: its 2-cells are the
ambient 2-cells between their images. All coherence laws follow from those in the ambient
bicategory, without further assumptions on the chosen comparisons.

The construction is the bicategorical counterpart of the locally faithful transport used by
Kim Morrison's `CategoryTheory.Monoidal.induced` in `Mathlib.CategoryTheory.Monoidal.Transport`.
It differs from Mathlib's object-induced bicategory: the generating arrows can be a proper
subset of the ambient arrows, and composition is preserved up to the specified comparisons.
-/

public section

universe w v u u' v'

namespace TauCeti

open CategoryTheory
open scoped Bicategory

/-- Chosen units and composites of a quiver mapped into a bicategory, together with
invertible comparisons to the ambient units and composites. No coherence laws are assumed. -/
structure BicategoryInductionData (B : Type u) [Bicategory.{w, v} B]
    (O : Type u') (H : Quiver.{v'} O) where
  /-- The map on objects. -/
  obj : O → B
  /-- The image of each generating arrow. -/
  map {a b : O} : @Quiver.Hom O H a b → (obj a ⟶ obj b)
  /-- The chosen identity generator. -/
  unit (a : O) : @Quiver.Hom O H a a
  /-- The chosen binary composite of generators. -/
  mul {a b c : O} : @Quiver.Hom O H a b → @Quiver.Hom O H b c → @Quiver.Hom O H a c
  /-- Comparison of the chosen unit with the ambient identity. -/
  mapUnit (a : O) : map (unit a) ≅ 𝟙 (obj a)
  /-- Comparison of the chosen composite with ambient composition. -/
  mapMul {a b c : O} (f : @Quiver.Hom O H a b) (g : @Quiver.Hom O H b c) :
    map (mul f g) ≅ map f ≫ map g

namespace BicategoryInductionData

variable {B : Type u} [Bicategory.{w, v} B] {O : Type u'} {H : Quiver.{v'} O}

/-- Objects of the locally induced bicategory. -/
@[ext]
structure Obj (I : BicategoryInductionData B O H) where
  /-- The underlying object. -/
  obj : O

variable (I : BicategoryInductionData B O H)

instance : CategoryStruct.{v'} I.Obj where
  Hom a b := InducedCategory (I.obj a.obj ⟶ I.obj b.obj) (fun f ↦ I.map f)
  id a := I.unit a.obj
  comp f g := I.mul f g

instance homCategory (a b : I.Obj) : Category.{w} (a ⟶ b) :=
  inferInstanceAs (Category (InducedCategory (I.obj a.obj ⟶ I.obj b.obj) (fun f ↦ I.map f)))

private def leftWhisker {a b c : I.Obj} (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    f ≫ g ⟶ f ≫ h :=
  InducedCategory.homMk ((I.mapMul f g).hom ≫ I.map f ◁ η.hom ≫ (I.mapMul f h).inv)

private def rightWhisker {a b c : I.Obj} {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    f ≫ h ⟶ g ≫ h :=
  InducedCategory.homMk ((I.mapMul f h).hom ≫ η.hom ▷ I.map h ≫ (I.mapMul g h).inv)

private def assocIso {a b c d : I.Obj} (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (f ≫ g) ≫ h ≅ f ≫ g ≫ h :=
  InducedCategory.isoMk (I.mapMul (f ≫ g) h ≪≫ (I.mapMul f g ▷ᵢ I.map h) ≪≫
    α_ (I.map f) (I.map g) (I.map h) ≪≫ (I.map f ◁ᵢ (I.mapMul g h).symm) ≪≫
    (I.mapMul f (g ≫ h)).symm)

private def leftUnitIso {a b : I.Obj} (f : a ⟶ b) : 𝟙 a ≫ f ≅ f :=
  InducedCategory.isoMk (I.mapMul (𝟙 a) f ≪≫ (I.mapUnit a.obj ▷ᵢ I.map f) ≪≫ λ_ (I.map f))

private def rightUnitIso {a b : I.Obj} (f : a ⟶ b) : f ≫ 𝟙 b ≅ f :=
  InducedCategory.isoMk (I.mapMul f (𝟙 b) ≪≫ (I.map f ◁ᵢ I.mapUnit b.obj) ≪≫ ρ_ (I.map f))

private theorem induced_whiskerLeft_id {a b c : I.Obj} (f : a ⟶ b) (g : b ⟶ c) :
    leftWhisker I f (𝟙 g) = 𝟙 (f ≫ g) := by
  apply InducedCategory.hom_ext
  dsimp only [leftWhisker,
    InducedCategory.isoMk, InducedCategory.homMk,
    CategoryStruct.comp, CategoryStruct.id]
  simp

private theorem induced_whiskerLeft_comp {a b c : I.Obj} (f : a ⟶ b) {g h i : b ⟶ c}
    (η : g ⟶ h) (θ : h ⟶ i) :
    leftWhisker I f (η ≫ θ) = leftWhisker I f η ≫ leftWhisker I f θ := by
  apply InducedCategory.hom_ext
  dsimp only [leftWhisker,
    InducedCategory.isoMk, InducedCategory.homMk,
    CategoryStruct.comp, CategoryStruct.id]
  simp

private theorem induced_id_whiskerRight {a b c : I.Obj} (f : a ⟶ b) (g : b ⟶ c) :
    rightWhisker I (𝟙 f) g = 𝟙 (f ≫ g) := by
  apply InducedCategory.hom_ext
  dsimp only [rightWhisker,
    InducedCategory.isoMk, InducedCategory.homMk,
    CategoryStruct.comp, CategoryStruct.id]
  simp

private theorem induced_comp_whiskerRight {a b c : I.Obj} {f g h : a ⟶ b}
    (η : f ⟶ g) (θ : g ⟶ h) (i : b ⟶ c) :
    rightWhisker I (η ≫ θ) i = rightWhisker I η i ≫ rightWhisker I θ i := by
  apply InducedCategory.hom_ext
  dsimp only [rightWhisker,
    InducedCategory.isoMk, InducedCategory.homMk,
    CategoryStruct.comp, CategoryStruct.id]
  simp

private theorem induced_id_whiskerLeft {a b : I.Obj} {f g : a ⟶ b} (η : f ⟶ g) :
    leftWhisker I (𝟙 a) η = (leftUnitIso I f).hom ≫ η ≫ (leftUnitIso I g).inv := by
  apply InducedCategory.hom_ext
  dsimp only [leftWhisker, leftUnitIso,
    InducedCategory.isoMk, InducedCategory.homMk,
    CategoryStruct.comp, CategoryStruct.id]
  simp only [Iso.trans_hom, Bicategory.whiskerRightIso_hom, Iso.trans_inv,
    Bicategory.whiskerRightIso_inv, Category.assoc, Iso.cancel_iso_hom_left]
  rw [← Bicategory.id_whiskerLeft_assoc, ← Bicategory.whisker_exchange_assoc]
  simp

private theorem induced_whiskerRight_id {a b : I.Obj} {f g : a ⟶ b} (η : f ⟶ g) :
    rightWhisker I η (𝟙 b) = (rightUnitIso I f).hom ≫ η ≫ (rightUnitIso I g).inv := by
  apply InducedCategory.hom_ext
  dsimp only [rightWhisker, rightUnitIso,
    InducedCategory.isoMk, InducedCategory.homMk,
    CategoryStruct.comp, CategoryStruct.id]
  simp only [Iso.trans_hom, Bicategory.whiskerLeftIso_hom, Iso.trans_inv,
    Bicategory.whiskerLeftIso_inv, Category.assoc, Iso.cancel_iso_hom_left]
  rw [← Bicategory.whiskerRight_id_assoc, Bicategory.whisker_exchange_assoc]
  simp

private theorem induced_comp_whiskerLeft {a b c d : I.Obj} (f : a ⟶ b) (g : b ⟶ c)
    {h h1 : c ⟶ d} (η : h ⟶ h1) :
    leftWhisker I (f ≫ g) η = (assocIso I f g h).hom ≫
      leftWhisker I f (leftWhisker I g η) ≫ (assocIso I f g h1).inv := by
  apply InducedCategory.hom_ext
  dsimp only [leftWhisker, assocIso,
    InducedCategory.isoMk, InducedCategory.homMk,
    CategoryStruct.comp, CategoryStruct.id]
  simp only [Iso.trans_hom, Bicategory.whiskerRightIso_hom,
    Bicategory.whiskerLeftIso_hom, Iso.symm_hom, Bicategory.whiskerLeft_comp, Category.assoc,
    Iso.trans_inv, Iso.symm_inv, Bicategory.whiskerLeftIso_inv, Bicategory.whiskerRightIso_inv,
    Iso.inv_hom_id_assoc, Bicategory.whiskerLeft_inv_hom_assoc, Iso.cancel_iso_hom_left]
  rw [← Bicategory.comp_whiskerLeft_assoc, ← Bicategory.whisker_exchange_assoc]
  simp

private theorem induced_whiskerRight_comp {a b c d : I.Obj} {f f1 : a ⟶ b} (η : f ⟶ f1)
    (g : b ⟶ c) (h : c ⟶ d) :
    rightWhisker I η (g ≫ h) = (assocIso I f g h).inv ≫
      rightWhisker I (rightWhisker I η g) h ≫ (assocIso I f1 g h).hom := by
  apply InducedCategory.hom_ext
  dsimp only [rightWhisker, assocIso,
    InducedCategory.isoMk, InducedCategory.homMk,
    CategoryStruct.comp, CategoryStruct.id]
  simp only [Iso.trans_inv, Iso.symm_inv, Bicategory.whiskerLeftIso_inv,
    Category.assoc, Bicategory.whiskerRightIso_inv, Bicategory.comp_whiskerRight,
    Iso.trans_hom, Bicategory.whiskerRightIso_hom, Bicategory.whiskerLeftIso_hom, Iso.symm_hom,
    Iso.inv_hom_id_assoc, Bicategory.inv_hom_whiskerRight_assoc, Iso.cancel_iso_hom_left]
  rw [← Bicategory.whiskerRight_comp_assoc, Bicategory.whisker_exchange_assoc]
  simp

private theorem induced_whisker_assoc {a b c d : I.Obj} (f : a ⟶ b) {g g1 : b ⟶ c}
    (η : g ⟶ g1) (h : c ⟶ d) :
    rightWhisker I (leftWhisker I f η) h = (assocIso I f g h).hom ≫
      leftWhisker I f (rightWhisker I η h) ≫ (assocIso I f g1 h).inv := by
  apply InducedCategory.hom_ext
  dsimp only [leftWhisker, rightWhisker, assocIso,
    InducedCategory.isoMk, InducedCategory.homMk,
    CategoryStruct.comp, CategoryStruct.id]
  simp

private theorem induced_whisker_exchange {a b c : I.Obj} {f g : a ⟶ b} {h i : b ⟶ c}
    (η : f ⟶ g) (θ : h ⟶ i) :
    leftWhisker I f θ ≫ rightWhisker I η i = rightWhisker I η h ≫ leftWhisker I g θ := by
  apply InducedCategory.hom_ext
  dsimp only [leftWhisker, rightWhisker,
    InducedCategory.isoMk, InducedCategory.homMk,
    CategoryStruct.comp, CategoryStruct.id]
  simp [Bicategory.whisker_exchange_assoc]

private theorem induced_pentagon {a b c d e : I.Obj} (f : a ⟶ b) (g : b ⟶ c)
    (h : c ⟶ d) (i : d ⟶ e) :
    rightWhisker I (assocIso I f g h).hom i ≫ (assocIso I f (g ≫ h) i).hom ≫
      leftWhisker I f (assocIso I g h i).hom =
        (assocIso I (f ≫ g) h i).hom ≫ (assocIso I f g (h ≫ i)).hom := by
  apply InducedCategory.hom_ext
  dsimp only [leftWhisker, rightWhisker, assocIso,
    InducedCategory.isoMk, InducedCategory.homMk,
    CategoryStruct.comp, CategoryStruct.id]
  simp [Bicategory.whisker_exchange_assoc]

private theorem induced_triangle {a b c : I.Obj} (f : a ⟶ b) (g : b ⟶ c) :
    (assocIso I f (𝟙 b) g).hom ≫ leftWhisker I f (leftUnitIso I g).hom =
      rightWhisker I (rightUnitIso I f).hom g := by
  apply InducedCategory.hom_ext
  dsimp only [leftWhisker, rightWhisker, assocIso, leftUnitIso, rightUnitIso,
    InducedCategory.isoMk, InducedCategory.homMk,
    CategoryStruct.comp, CategoryStruct.id]
  simp

/-- The locally induced bicategory. All coherence follows from the ambient bicategory. -/
instance : Bicategory.{w, v'} I.Obj where
  toCategoryStruct := inferInstance
  homCategory := homCategory I
  whiskerLeft {_ _ _} f {g h} η :=
    InducedCategory.homMk ((I.mapMul f g).hom ≫ I.map f ◁ η.hom ≫ (I.mapMul f h).inv)
  whiskerRight {_ _ _} {f g} η h :=
    InducedCategory.homMk ((I.mapMul f h).hom ≫ η.hom ▷ I.map h ≫ (I.mapMul g h).inv)
  associator f g h :=
    InducedCategory.isoMk (I.mapMul (f ≫ g) h ≪≫ (I.mapMul f g ▷ᵢ I.map h) ≪≫
      α_ (I.map f) (I.map g) (I.map h) ≪≫ (I.map f ◁ᵢ (I.mapMul g h).symm) ≪≫
      (I.mapMul f (g ≫ h)).symm)
  leftUnitor {a _} f :=
    InducedCategory.isoMk (I.mapMul (𝟙 a) f ≪≫ (I.mapUnit a.obj ▷ᵢ I.map f) ≪≫ λ_ (I.map f))
  rightUnitor {_ b} f :=
    InducedCategory.isoMk (I.mapMul f (𝟙 b) ≪≫ (I.map f ◁ᵢ I.mapUnit b.obj) ≪≫ ρ_ (I.map f))
  whiskerLeft_id := by exact induced_whiskerLeft_id I
  whiskerLeft_comp := by exact induced_whiskerLeft_comp I
  id_whiskerRight := by exact induced_id_whiskerRight I
  comp_whiskerRight := by exact induced_comp_whiskerRight I
  id_whiskerLeft := by exact induced_id_whiskerLeft I
  whiskerRight_id := by exact induced_whiskerRight_id I
  comp_whiskerLeft := by exact induced_comp_whiskerLeft I
  whiskerRight_comp := by exact induced_whiskerRight_comp I
  whisker_assoc := by exact induced_whisker_assoc I
  whisker_exchange := by exact induced_whisker_exchange I
  pentagon := by exact induced_pentagon I
  triangle := by exact induced_triangle I

/-- The inclusion into the ambient bicategory, with the specified unit and composition
comparisons. It is fully faithful on every hom-category. Its body is exposed so the
object and arrow maps compute in the types of its hom-functors. -/
@[expose, simps obj map map₂ mapId mapComp]
def inclusion : I.Obj ⥤ᵖ B where
  obj a := I.obj a.obj
  map f := I.map f
  map₂ η := η.hom
  map₂_id _ := rfl
  map₂_comp _ _ := rfl
  mapId a := I.mapUnit a.obj
  mapComp f g := I.mapMul f g
  map₂_whisker_left := by intros; rfl
  map₂_whisker_right _ _ := rfl
  map₂_associator _ _ _ := rfl
  map₂_left_unitor _ := rfl
  map₂_right_unitor _ := rfl

instance (a b : I.Obj) : (I.inclusion.mapFunctor a b).Full :=
  (fullyFaithfulInducedFunctor (fun f : a ⟶ b ↦ I.map f)).full

instance (a b : I.Obj) : (I.inclusion.mapFunctor a b).Faithful :=
  (fullyFaithfulInducedFunctor (fun f : a ⟶ b ↦ I.map f)).faithful

variable {I} {a b c d : I.Obj}

/-- The identity 1-cell is the chosen unit generator. -/
@[simp]
theorem id_eq (a : I.Obj) : (𝟙 a : a ⟶ a) = I.unit a.obj := (rfl)

/-- Composition of 1-cells is the chosen binary composite. -/
@[simp]
theorem comp_eq (f : a ⟶ b) (g : b ⟶ c) : f ≫ g = I.mul f g := (rfl)

/-- Left whiskering is conjugation of ambient left whiskering by the comparisons. -/
@[simp]
theorem whiskerLeft_hom (f : a ⟶ b) {g h : b ⟶ c} (η : g ⟶ h) :
    (f ◁ η).hom = (I.mapMul f g).hom ≫ I.map f ◁ η.hom ≫ (I.mapMul f h).inv := (rfl)

/-- Right whiskering is conjugation of ambient right whiskering by the comparisons. -/
@[simp]
theorem whiskerRight_hom {f g : a ⟶ b} (η : f ⟶ g) (h : b ⟶ c) :
    (η ▷ h).hom = (I.mapMul f h).hom ≫ η.hom ▷ I.map h ≫ (I.mapMul g h).inv := (rfl)

/-- The associator compares the two binary reductions, through the ambient associator. -/
@[simp]
theorem associator_hom_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (α_ f g h).hom.hom = (I.mapMul (f ≫ g) h).hom ≫ (I.mapMul f g).hom ▷ I.map h ≫
      (α_ (I.map f) (I.map g) (I.map h)).hom ≫ I.map f ◁ (I.mapMul g h).inv ≫
      (I.mapMul f (g ≫ h)).inv := (rfl)

/-- The inverse associator reverses the two binary reductions. -/
@[simp]
theorem associator_inv_hom (f : a ⟶ b) (g : b ⟶ c) (h : c ⟶ d) :
    (α_ f g h).inv.hom = (I.mapMul f (g ≫ h)).hom ≫ I.map f ◁ (I.mapMul g h).hom ≫
      (α_ (I.map f) (I.map g) (I.map h)).inv ≫ (I.mapMul f g).inv ▷ I.map h ≫
      (I.mapMul (f ≫ g) h).inv := by
  simp only [Bicategory.associator, InducedCategory.isoMk_inv,
    InducedCategory.homMk_hom, Iso.trans_inv, Iso.symm_inv,
    Bicategory.whiskerLeftIso_inv, Bicategory.whiskerRightIso_inv, Category.assoc]

/-- The left unitor uses the chosen nullary comparison. -/
@[simp]
theorem leftUnitor_hom_hom (f : a ⟶ b) :
    (λ_ f).hom.hom = (I.mapMul (𝟙 a) f).hom ≫ (I.mapUnit a.obj).hom ▷ I.map f ≫
      (λ_ (I.map f)).hom := (rfl)

/-- The inverse left unitor inserts the chosen nullary comparison. -/
@[simp]
theorem leftUnitor_inv_hom (f : a ⟶ b) :
    (λ_ f).inv.hom = (λ_ (I.map f)).inv ≫ (I.mapUnit a.obj).inv ▷ I.map f ≫
      (I.mapMul (𝟙 a) f).inv := by
  simp only [Bicategory.leftUnitor, InducedCategory.isoMk_inv,
    InducedCategory.homMk_hom, Iso.trans_inv, Bicategory.whiskerRightIso_inv, Category.assoc]

/-- The right unitor uses the chosen nullary comparison. -/
@[simp]
theorem rightUnitor_hom_hom (f : a ⟶ b) :
    (ρ_ f).hom.hom = (I.mapMul f (𝟙 b)).hom ≫ I.map f ◁ (I.mapUnit b.obj).hom ≫
      (ρ_ (I.map f)).hom := (rfl)

/-- The inverse right unitor inserts the chosen nullary comparison. -/
@[simp]
theorem rightUnitor_inv_hom (f : a ⟶ b) :
    (ρ_ f).inv.hom = (ρ_ (I.map f)).inv ≫ I.map f ◁ (I.mapUnit b.obj).inv ≫
      (I.mapMul f (𝟙 b)).inv := by
  simp only [Bicategory.rightUnitor, InducedCategory.isoMk_inv,
    InducedCategory.homMk_hom, Iso.trans_inv, Bicategory.whiskerLeftIso_inv, Category.assoc]

end BicategoryInductionData

end TauCeti
