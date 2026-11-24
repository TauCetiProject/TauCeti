/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Dagger.Functor
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation

/-!
# Dagger monoidal categories and dagger tensor functors

A native monoidal structure on a dagger category is dagger compatible when whiskering commutes
with taking daggers and the associators and unitors are unitary. Daggers then commute with
tensor products of arrows, and tensor products and whiskerings of unitary arrows are unitary.

A lax monoidal structure on a functor into a dagger category is unitary when its unit and
tensor comparison morphisms are unitary; such a structure is automatically strong, its oplax
comparison morphisms are the daggers of the lax ones, and these structures are stable under
identities and composition with dagger-preserving functors. A dagger tensor functor is a
dagger-preserving lax monoidal functor with unitary comparison morphisms. Dagger tensor functors
form a full subcategory of Mathlib's category `LaxMonoidalFunctor` of lax monoidal functors and
monoidal natural transformations. The pointwise dagger of a monoidal natural transformation
between them is again monoidal, so this category is itself a dagger category, whose unitary
arrows are exactly the monoidal natural transformations with unitary components.

## Implementation notes

The bundled category `DaggerTensorFunctor` follows Mathlib's `CategoryTheory.LaxBraidedFunctor`
in `Mathlib/CategoryTheory/Monoidal/Braided/Basic.lean`.

## References

* P. Selinger, *Dagger compact closed categories and completely positive maps*,
  Electron. Notes Theor. Comput. Sci. 170 (2007), 139–163, §2.
* D. Penneys, *Unitary dual functors for unitary multitensor categories*,
  Higher Structures 4 (2020), 22–56, §2.
-/

public section

open CategoryTheory MonoidalCategory

universe v₁ v₂ v₃ u₁ u₂ u₃

namespace TauCeti

/-- Dagger compatibility of a native monoidal structure: whiskering commutes with taking
daggers, and the associators and unitors are unitary. -/
class DaggerMonoidalCategory (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C]
    [DaggerCategory C] : Prop where
  /-- Left whiskering commutes with taking daggers. -/
  dagger_whiskerLeft : ∀ (X : C) {Y Z : C} (f : Y ⟶ Z), dagger (X ◁ f) = X ◁ dagger f
  /-- Right whiskering commutes with taking daggers. -/
  dagger_whiskerRight : ∀ {X Y : C} (f : X ⟶ Y) (Z : C), dagger (f ▷ Z) = dagger f ▷ Z
  /-- The associators are unitary. -/
  isUnitary_associator : ∀ X Y Z : C, IsUnitary (α_ X Y Z).hom
  /-- The left unitors are unitary. -/
  isUnitary_leftUnitor : ∀ X : C, IsUnitary (λ_ X).hom
  /-- The right unitors are unitary. -/
  isUnitary_rightUnitor : ∀ X : C, IsUnitary (ρ_ X).hom

export DaggerMonoidalCategory (dagger_whiskerLeft dagger_whiskerRight isUnitary_associator
  isUnitary_leftUnitor isUnitary_rightUnitor)

attribute [simp, grind =] dagger_whiskerLeft dagger_whiskerRight
attribute [simp] isUnitary_associator isUnitary_leftUnitor isUnitary_rightUnitor

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [DaggerCategory C]
  [DaggerMonoidalCategory C]

/-- Taking daggers commutes with tensor products of arrows. -/
@[simp, grind =] theorem dagger_tensorHom {X₁ Y₁ X₂ Y₂ : C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    dagger (f ⊗ₘ g) = dagger f ⊗ₘ dagger g := by
  rw [tensorHom_def, dagger_comp, dagger_whiskerLeft, dagger_whiskerRight, tensorHom_def']

/-- The dagger of an associator is its inverse. -/
@[simp, grind =] theorem dagger_associator_hom (X Y Z : C) :
    dagger (α_ X Y Z).hom = (α_ X Y Z).inv :=
  (α_ X Y Z).dagger_hom_eq_inv_of_isUnitary (isUnitary_associator X Y Z)

/-- The dagger of an inverse associator is the associator. -/
@[simp, grind =] theorem dagger_associator_inv (X Y Z : C) :
    dagger (α_ X Y Z).inv = (α_ X Y Z).hom := by
  rw [← dagger_associator_hom, dagger_dagger]

/-- The dagger of a left unitor is its inverse. -/
@[simp, grind =] theorem dagger_leftUnitor_hom (X : C) : dagger (λ_ X).hom = (λ_ X).inv :=
  (λ_ X).dagger_hom_eq_inv_of_isUnitary (isUnitary_leftUnitor X)

/-- The dagger of an inverse left unitor is the left unitor. -/
@[simp, grind =] theorem dagger_leftUnitor_inv (X : C) : dagger (λ_ X).inv = (λ_ X).hom := by
  rw [← dagger_leftUnitor_hom, dagger_dagger]

/-- The dagger of a right unitor is its inverse. -/
@[simp, grind =] theorem dagger_rightUnitor_hom (X : C) : dagger (ρ_ X).hom = (ρ_ X).inv :=
  (ρ_ X).dagger_hom_eq_inv_of_isUnitary (isUnitary_rightUnitor X)

/-- The dagger of an inverse right unitor is the right unitor. -/
@[simp, grind =] theorem dagger_rightUnitor_inv (X : C) : dagger (ρ_ X).inv = (ρ_ X).hom := by
  rw [← dagger_rightUnitor_hom, dagger_dagger]

/-- Inverse associators are unitary. -/
@[simp] theorem isUnitary_associator_inv (X Y Z : C) : IsUnitary (α_ X Y Z).inv := by
  simpa using (isUnitary_associator X Y Z).dagger

/-- Inverse left unitors are unitary. -/
@[simp] theorem isUnitary_leftUnitor_inv (X : C) : IsUnitary (λ_ X).inv := by
  simpa using (isUnitary_leftUnitor X).dagger

/-- Inverse right unitors are unitary. -/
@[simp] theorem isUnitary_rightUnitor_inv (X : C) : IsUnitary (ρ_ X).inv := by
  simpa using (isUnitary_rightUnitor X).dagger

end TauCeti

namespace CategoryTheory

open TauCeti

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [DaggerCategory C]
  [DaggerMonoidalCategory C]

/-- Tensoring on the left preserves daggers. -/
instance (X : C) : (tensorLeft X).PreservesDagger where
  map_dagger f := by simp

/-- Tensoring on the right preserves daggers. -/
instance (X : C) : (tensorRight X).PreservesDagger where
  map_dagger f := by simp

end CategoryTheory

namespace TauCeti

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [DaggerCategory C]
  [DaggerMonoidalCategory C]

namespace IsUnitary

variable {X Y Z : C}

/-- Left whiskering preserves unitary arrows. -/
theorem whiskerLeft (X : C) {f : Y ⟶ Z} (hf : IsUnitary f) : IsUnitary (X ◁ f) := by
  simpa using (tensorLeft X).map_isUnitary hf

/-- Right whiskering preserves unitary arrows. -/
theorem whiskerRight {f : X ⟶ Y} (hf : IsUnitary f) (Z : C) : IsUnitary (f ▷ Z) := by
  simpa using (tensorRight Z).map_isUnitary hf

/-- Tensor products of unitary arrows are unitary. -/
theorem tensorHom {X₁ Y₁ X₂ Y₂ : C} {f : X₁ ⟶ Y₁} {g : X₂ ⟶ Y₂} (hf : IsUnitary f)
    (hg : IsUnitary g) : IsUnitary (f ⊗ₘ g) := by
  rw [tensorHom_def]
  exact (hf.whiskerRight X₂).comp (hg.whiskerLeft Y₁)

end IsUnitary

end TauCeti

namespace CategoryTheory.Functor

open TauCeti Functor.LaxMonoidal Functor.OplaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [DaggerCategory D]
variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [DaggerCategory E]

/-- A lax monoidal structure on a functor into a dagger category is unitary when its unit and
tensor comparison morphisms are unitary. Such a structure is automatically strong. -/
class IsUnitaryMonoidal (F : C ⥤ D) [F.LaxMonoidal] : Prop where
  /-- The unit comparison morphism is unitary. -/
  isUnitary_ε (F) : IsUnitary (ε F)
  /-- The tensor comparison morphisms are unitary. -/
  isUnitary_μ (F) : ∀ X Y : C, IsUnitary (μ F X Y)

export IsUnitaryMonoidal (isUnitary_ε isUnitary_μ)

attribute [simp] isUnitary_ε isUnitary_μ

section

variable (F : C ⥤ D) [F.LaxMonoidal] [F.IsUnitaryMonoidal]

/-- The unit comparison morphism of a unitary lax monoidal structure is invertible. -/
instance : IsIso (ε F) := (isUnitary_ε F).isIso

/-- The tensor comparison morphisms of a unitary lax monoidal structure are invertible. -/
instance (X Y : C) : IsIso (μ F X Y) := (isUnitary_μ F X Y).isIso

end

namespace IsUnitaryMonoidal

/-- The identity functor is unitary monoidal. -/
instance [DaggerCategory C] : (𝟭 C).IsUnitaryMonoidal where
  isUnitary_ε := by simp
  isUnitary_μ _ _ := by simp

/-- The composite of unitary monoidal functors, the second preserving daggers, is unitary
monoidal. -/
instance (F : C ⥤ D) (G : D ⥤ E) [F.LaxMonoidal] [G.LaxMonoidal] [F.IsUnitaryMonoidal]
    [G.IsUnitaryMonoidal] [G.PreservesDagger] : (F ⋙ G).IsUnitaryMonoidal where
  isUnitary_ε := by
    rw [LaxMonoidal.comp_ε]
    exact (isUnitary_ε G).comp (G.map_isUnitary (isUnitary_ε F))
  isUnitary_μ X Y := by
    rw [LaxMonoidal.comp_μ]
    exact (isUnitary_μ G _ _).comp (G.map_isUnitary (isUnitary_μ F X Y))

end IsUnitaryMonoidal

namespace Monoidal

variable (F : C ⥤ D) [F.Monoidal]

/-- A strong monoidal structure is unitary exactly when its oplax comparison morphisms are the
daggers of its lax comparison morphisms. -/
theorem isUnitaryMonoidal_iff :
    F.IsUnitaryMonoidal ↔ dagger (ε F) = η F ∧ ∀ X Y : C, dagger (μ F X Y) = δ F X Y := by
  constructor
  · intro h
    exact ⟨(εIso F).dagger_hom_eq_inv_of_isUnitary (isUnitary_ε F),
      fun X Y => (μIso F X Y).dagger_hom_eq_inv_of_isUnitary (isUnitary_μ F X Y)⟩
  · rintro ⟨hε, hμ⟩
    exact ⟨(εIso F).isUnitary_hom_iff.mpr hε,
      fun X Y => (μIso F X Y).isUnitary_hom_iff.mpr (hμ X Y)⟩

variable [F.IsUnitaryMonoidal]

/-- The dagger of the unit comparison morphism of a unitary monoidal functor is its oplax unit
comparison morphism. -/
@[simp, grind =] theorem dagger_ε : dagger (ε F) = η F :=
  ((isUnitaryMonoidal_iff F).mp inferInstance).1

/-- The dagger of the tensor comparison morphism of a unitary monoidal functor is its oplax
tensor comparison morphism. -/
@[simp, grind =] theorem dagger_μ (X Y : C) : dagger (μ F X Y) = δ F X Y :=
  ((isUnitaryMonoidal_iff F).mp inferInstance).2 X Y

/-- The dagger of the oplax unit comparison morphism of a unitary monoidal functor is its unit
comparison morphism. -/
@[simp, grind =] theorem dagger_η : dagger (η F) = ε F := by
  rw [← dagger_ε, dagger_dagger]

/-- The dagger of the oplax tensor comparison morphism of a unitary monoidal functor is its
tensor comparison morphism. -/
@[simp, grind =] theorem dagger_δ (X Y : C) : dagger (δ F X Y) = μ F X Y := by
  rw [← dagger_μ, dagger_dagger]

end Monoidal

end CategoryTheory.Functor

namespace CategoryTheory.NatTrans

open TauCeti Functor.LaxMonoidal

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [DaggerCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [DaggerCategory D]
  [DaggerMonoidalCategory D]
variable {F G : C ⥤ D} [F.LaxMonoidal] [G.LaxMonoidal] [F.IsUnitaryMonoidal]
  [G.IsUnitaryMonoidal] [F.PreservesDagger] [G.PreservesDagger]

/-- The pointwise dagger of a monoidal natural transformation between dagger-preserving unitary
monoidal functors is monoidal. -/
instance IsMonoidal.dagger (α : F ⟶ G) [α.IsMonoidal] : α.dagger.IsMonoidal where
  unit := by
    rw [← cancel_mono (TauCeti.dagger (ε F))]
    simp only [dagger_app, Category.assoc, ← TauCeti.dagger_comp]
    simp
  tensor X Y := by
    rw [← cancel_mono (TauCeti.dagger (μ F X Y))]
    simp only [dagger_app, Category.assoc, ← TauCeti.dagger_comp]
    simp

end CategoryTheory.NatTrans

namespace TauCeti

open Functor.LaxMonoidal

variable (C : Type u₁) [Category.{v₁} C] [MonoidalCategory C] [DaggerCategory C]
variable (D : Type u₂) [Category.{v₂} D] [MonoidalCategory D] [DaggerCategory D]

/-- A dagger tensor functor between dagger monoidal categories: a dagger-preserving lax monoidal
functor whose unit and tensor comparison morphisms are unitary, hence strong monoidal. -/
structure DaggerTensorFunctor [DaggerMonoidalCategory C] [DaggerMonoidalCategory D] extends
    LaxMonoidalFunctor C D where
  preservesDagger : toFunctor.PreservesDagger := by infer_instance
  isUnitaryMonoidal : toFunctor.IsUnitaryMonoidal := by infer_instance

namespace DaggerTensorFunctor

attribute [instance] preservesDagger isUnitaryMonoidal

variable {C D} [DaggerMonoidalCategory C] [DaggerMonoidalCategory D]

/-- Bundle a dagger-preserving functor with a unitary lax monoidal structure as a dagger tensor
functor. -/
def of (F : C ⥤ D) [F.LaxMonoidal] [F.PreservesDagger] [F.IsUnitaryMonoidal] :
    DaggerTensorFunctor C D where
  toFunctor := F

/-- The underlying functor of `of F` is `F`. -/
@[simp]
lemma of_toFunctor (F : C ⥤ D) [F.LaxMonoidal] [F.PreservesDagger] [F.IsUnitaryMonoidal] :
    (of F).toFunctor = F := (rfl)

/-- Dagger tensor functors form a full subcategory of lax monoidal functors, with monoidal
natural transformations as morphisms. -/
instance : Category (DaggerTensorFunctor C D) :=
  inferInstanceAs (Category (InducedCategory _ toLaxMonoidalFunctor))

/-- The underlying natural transformation of an identity morphism is the identity. -/
@[simp]
lemma id_hom (F : DaggerTensorFunctor C D) :
    LaxMonoidalFunctor.Hom.hom (InducedCategory.Hom.hom (𝟙 F)) = 𝟙 _ := (rfl)

/-- The underlying morphism of lax monoidal functors of a composite is the composite. -/
@[reassoc, simp]
lemma comp_hom {F G H : DaggerTensorFunctor C D} (α : F ⟶ G) (β : G ⟶ H) :
    (α ≫ β).hom = α.hom ≫ β.hom := (rfl)

/-- Morphisms of dagger tensor functors are determined by their underlying natural
transformations. -/
@[ext]
lemma hom_ext {F G : DaggerTensorFunctor C D} {α β : F ⟶ G} (h : α.hom.hom = β.hom.hom) :
    α = β :=
  InducedCategory.hom_ext (LaxMonoidalFunctor.hom_ext h)

/-- Constructor for morphisms of dagger tensor functors from monoidal natural
transformations. -/
def homMk {F G : DaggerTensorFunctor C D} (f : F.toFunctor ⟶ G.toFunctor)
    [NatTrans.IsMonoidal f] : F ⟶ G :=
  InducedCategory.homMk (LaxMonoidalFunctor.homMk f)

/-- The underlying natural transformation of `homMk f` is `f`. -/
@[simp]
lemma homMk_hom_hom {F G : DaggerTensorFunctor C D} (f : F.toFunctor ⟶ G.toFunctor)
    [NatTrans.IsMonoidal f] : (homMk f).hom.hom = f := (rfl)

/-- The forgetful functor from dagger tensor functors to lax monoidal functors. -/
@[expose] def forget : DaggerTensorFunctor C D ⥤ LaxMonoidalFunctor C D :=
  inducedFunctor _

/-- The forgetful functor sends a dagger tensor functor to its lax monoidal functor. -/
@[simp]
lemma forget_obj (F : DaggerTensorFunctor C D) : forget.obj F = F.toLaxMonoidalFunctor := (rfl)

/-- The forgetful functor sends a morphism to its morphism of lax monoidal functors. -/
@[simp]
lemma forget_map {F G : DaggerTensorFunctor C D} (α : F ⟶ G) : forget.map α = α.hom := (rfl)

/-- The forgetful functor from dagger tensor functors to lax monoidal functors is fully
faithful. -/
def fullyFaithfulForget : (forget (C := C) (D := D)).FullyFaithful :=
  fullyFaithfulInducedFunctor _

/-- The category of dagger tensor functors is a dagger category under pointwise daggers. -/
instance : DaggerCategory (DaggerTensorFunctor C D) where
  dagger α := homMk α.hom.hom.dagger
  dagger_id F := by ext; simp
  dagger_comp α β := by ext; simp
  dagger_dagger α := by ext; simp

/-- The underlying natural transformation of the dagger of a morphism of dagger tensor
functors is the pointwise dagger. -/
@[simp, grind =]
lemma dagger_hom_hom {F G : DaggerTensorFunctor C D} (α : F ⟶ G) :
    (dagger α).hom.hom = α.hom.hom.dagger := (rfl)

/-- A morphism of dagger tensor functors is unitary exactly when all its components are
unitary: the unitary arrows are the unitary monoidal natural isomorphisms. -/
theorem isUnitary_iff_isUnitary_app {F G : DaggerTensorFunctor C D} (α : F ⟶ G) :
    IsUnitary α ↔ ∀ X : C, IsUnitary (α.hom.hom.app X) := by
  constructor
  · intro h X
    rw [TauCeti.isUnitary_iff]
    exact ⟨by simpa using congrArg (fun β => β.hom.hom.app X) h.hom_dagger_id,
      by simpa using congrArg (fun β => β.hom.hom.app X) h.dagger_hom_id⟩
  · intro h
    rw [TauCeti.isUnitary_iff]
    constructor <;> ext X <;> simp [(h X).hom_dagger_id, (h X).dagger_hom_id]

end DaggerTensorFunctor

end TauCeti
