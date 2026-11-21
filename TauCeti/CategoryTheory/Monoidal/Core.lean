/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Core
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import TauCeti.CategoryTheory.Monoidal.Skeleton

/-!
# The monoidal structure on the core of a monoidal category

For a monoidal category `C`, the core `Core C` (the groupoid of objects of `C` and isomorphisms
between them) inherits a monoidal structure: the tensor product of two isomorphisms is an
isomorphism, and the associators and unitors of `C` are isomorphisms. All laws are inherited
along the faithful inclusion `Core.inclusion C : Core C ⥤ C`, which is strict monoidal. When `C`
is braided (resp. symmetric), so is `Core C`, and the inclusion is braided.

A (braided) strong monoidal functor `F : C ⥤ D` induces a (braided) strong monoidal functor
`F.core : Core C ⥤ Core D`, and the comparison isomorphisms `Functor.coreCompInclusionIso`,
`Functor.coreId` and `Functor.coreComp` are monoidal natural isomorphisms. For a groupoid `C`
the inclusion `Core C ⥤ C` is a braided monoidal equivalence.

Finally, since two objects are isomorphic in `Core C` exactly when they are isomorphic in `C`,
the inclusion identifies the monoid of isomorphism classes `Skeleton (Core C)` with
`Skeleton C` (`CategoryTheory.Core.skeletonMulEquiv`), naturally in strong monoidal functors.

This is the input to Quillen's group completion `S⁻¹S` of a symmetric monoidal category `S`,
which is formed from the symmetric monoidal groupoid `Core S`.

## References

* C. A. Weibel, *The K-book: An introduction to algebraic K-theory*, Graduate Studies in
  Mathematics 145, AMS, 2013, Chapter IV, Definition 4.1 and Examples 4.1.1.
-/

@[expose] public section

namespace CategoryTheory

open MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]

namespace Core

/-- The monoidal operations on `Core C`, computed in `C`. -/
instance instMonoidalCategoryStruct : MonoidalCategoryStruct (Core C) where
  tensorObj X Y := .mk (X.of ⊗ Y.of)
  whiskerLeft X _ _ f := .mk (whiskerLeftIso X.of f.iso)
  whiskerRight f Y := .mk (whiskerRightIso f.iso Y.of)
  tensorHom f g := .mk (f.iso ⊗ᵢ g.iso)
  tensorUnit := .mk (𝟙_ C)
  associator X Y Z := isoMk (α_ X.of Y.of Z.of)
  leftUnitor X := isoMk (λ_ X.of)
  rightUnitor X := isoMk (ρ_ X.of)

@[simp]
lemma tensorObj_of (X Y : Core C) : (X ⊗ Y).of = X.of ⊗ Y.of := rfl

@[simp]
lemma tensorUnit_of : (𝟙_ (Core C)).of = 𝟙_ C := rfl

@[simp]
lemma whiskerLeft_iso (X : Core C) {Y₁ Y₂ : Core C} (f : Y₁ ⟶ Y₂) :
    (X ◁ f).iso = whiskerLeftIso X.of f.iso := rfl

@[simp]
lemma whiskerRight_iso {X₁ X₂ : Core C} (f : X₁ ⟶ X₂) (Y : Core C) :
    (f ▷ Y).iso = whiskerRightIso f.iso Y.of := rfl

@[simp]
lemma tensorHom_iso {X₁ Y₁ X₂ Y₂ : Core C} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (f ⊗ₘ g).iso = f.iso ⊗ᵢ g.iso := rfl

@[simp]
lemma associator_hom_iso (X Y Z : Core C) : (α_ X Y Z).hom.iso = α_ X.of Y.of Z.of := rfl

@[simp]
lemma associator_inv_iso (X Y Z : Core C) : (α_ X Y Z).inv.iso = (α_ X.of Y.of Z.of).symm :=
  rfl

@[simp]
lemma leftUnitor_hom_iso (X : Core C) : (λ_ X).hom.iso = λ_ X.of := rfl

@[simp]
lemma leftUnitor_inv_iso (X : Core C) : (λ_ X).inv.iso = (λ_ X.of).symm := rfl

@[simp]
lemma rightUnitor_hom_iso (X : Core C) : (ρ_ X).hom.iso = ρ_ X.of := rfl

@[simp]
lemma rightUnitor_inv_iso (X : Core C) : (ρ_ X).inv.iso = (ρ_ X.of).symm := rfl

/-- The core of a monoidal category is monoidal, with the laws inherited along the faithful
inclusion `Core C ⥤ C`. -/
instance instMonoidalCategory : MonoidalCategory (Core C) :=
  Monoidal.induced (inclusion C)
    { μIso _ _ := Iso.refl _
      εIso := Iso.refl _ }

/-- The inclusion of the core is a strict monoidal functor. -/
instance instMonoidalInclusion : (inclusion C).Monoidal :=
  Functor.CoreMonoidal.toMonoidal
    { μIso _ _ := Iso.refl _
      εIso := Iso.refl _ }

@[simp]
lemma inclusion_ε : ε (inclusion C) = 𝟙 (𝟙_ C) := rfl

@[simp]
lemma inclusion_η : η (inclusion C) = 𝟙 (𝟙_ C) := rfl

@[simp]
lemma inclusion_μ (X Y : Core C) : μ (inclusion C) X Y = 𝟙 (X.of ⊗ Y.of) := rfl

@[simp]
lemma inclusion_δ (X Y : Core C) : δ (inclusion C) X Y = 𝟙 (X.of ⊗ Y.of) := rfl

section Braided

variable [BraidedCategory C]

/-- The core of a braided monoidal category is braided, with braiding computed in `C`. -/
instance instBraidedCategory : BraidedCategory (Core C) :=
  .ofFaithful (inclusion C) fun X Y ↦ isoMk (β_ X.of Y.of)

@[simp]
lemma braiding_hom_iso (X Y : Core C) : (β_ X Y).hom.iso = β_ X.of Y.of := rfl

@[simp]
lemma braiding_inv_iso (X Y : Core C) : (β_ X Y).inv.iso = (β_ X.of Y.of).symm := rfl

/-- The inclusion of the core of a braided monoidal category is braided. -/
instance instBraidedInclusion : (inclusion C).Braided where

end Braided

/-- The core of a symmetric monoidal category is symmetric. -/
instance instSymmetricCategory [SymmetricCategory C] : SymmetricCategory (Core C) :=
  .ofFaithful (inclusion C)

section Groupoid

variable [IsGroupoid C]

/-- In a groupoid every morphism is an isomorphism, so the inclusion of the core is full. -/
instance : (inclusion C).Full where
  map_surjective f := ⟨⟨asIso f⟩, rfl⟩

/-- The inclusion of the core is bijective on objects. -/
instance : (inclusion C).EssSurj where
  mem_essImage X := ⟨⟨X⟩, ⟨Iso.refl _⟩⟩

/-- The core of a groupoid is equivalent to the groupoid via the inclusion. Since the inclusion
is braided monoidal, this is a braided monoidal equivalence. -/
instance : (inclusion C).IsEquivalence where

end Groupoid

end Core

namespace Functor

variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
  {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E]

/-- A strong monoidal functor induces a strong monoidal functor on cores. -/
instance instMonoidalCore (F : C ⥤ D) [F.Monoidal] : F.core.Monoidal :=
  CoreMonoidal.toMonoidal
    { μIso X Y := Core.isoMk (Monoidal.μIso F X.of Y.of)
      εIso := Core.isoMk (Monoidal.εIso F)
      μIso_hom_natural_left f X := Core.hom_ext (μ_natural_left F f.iso.hom X.of)
      μIso_hom_natural_right X f := Core.hom_ext (μ_natural_right F X.of f.iso.hom)
      associativity X Y Z := Core.hom_ext (by simp)
      left_unitality X := Core.hom_ext (by simp)
      right_unitality X := Core.hom_ext (by simp) }

variable (F : C ⥤ D) [F.Monoidal]

@[simp]
lemma core_ε_iso : (ε F.core).iso = Monoidal.εIso F := rfl

@[simp]
lemma core_η_iso : (η F.core).iso = (Monoidal.εIso F).symm := rfl

@[simp]
lemma core_μ_iso (X Y : Core C) : (μ F.core X Y).iso = Monoidal.μIso F X.of Y.of := rfl

@[simp]
lemma core_δ_iso (X Y : Core C) : (δ F.core X Y).iso = (Monoidal.μIso F X.of Y.of).symm := rfl

/-- The comparison `F.core ⋙ Core.inclusion D ≅ Core.inclusion C ⋙ F` is monoidal. -/
instance : NatTrans.IsMonoidal (F.coreCompInclusionIso).hom where

/-- The comparison `(𝟭 C).core ≅ 𝟭 (Core C)` is monoidal. -/
instance : NatTrans.IsMonoidal (coreId C).hom where
  unit := Core.hom_ext (by simp)
  tensor X Y := Core.hom_ext (by simp)

/-- The comparison `(F ⋙ G).core ≅ F.core ⋙ G.core` is monoidal. -/
instance (G : D ⥤ E) [G.Monoidal] : NatTrans.IsMonoidal (F.coreComp G).hom where
  unit := Core.hom_ext (by simp)
  tensor X Y := Core.hom_ext (by simp)

end Functor

/-- A braided strong monoidal functor induces a braided functor on cores. -/
instance Functor.instBraidedCore {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
    [BraidedCategory C] [BraidedCategory D] (F : C ⥤ D) [F.Braided] : F.core.Braided where
  braided X Y := Core.hom_ext (by simp)

/-- A monoidal natural isomorphism of strong monoidal functors induces a monoidal natural
isomorphism of their cores. -/
instance Iso.instIsMonoidalCoreHom {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
    {F G : C ⥤ D} [F.Monoidal] [G.Monoidal] (α : F ≅ G) [NatTrans.IsMonoidal α.hom] :
    NatTrans.IsMonoidal α.core.hom where
  unit := Core.hom_ext (by simp)
  tensor X Y := Core.hom_ext (by simp)

namespace Core

/-- Two objects of `Core C` are isomorphic exactly when they are isomorphic in `C`, so the
inclusion identifies the monoid of isomorphism classes of `Core C` with that of `C`. -/
noncomputable def skeletonMulEquiv : Skeleton (Core C) ≃* Skeleton C :=
  .ofBijective (Skeleton.monoidHom (inclusion C)) <| by
    refine ⟨fun X Y h ↦ ?_, fun X ↦ ⟨toSkeleton ⟨(fromSkeleton C).obj X⟩, ?_⟩⟩
    · rw [← toSkeleton_fromSkeleton_obj X, ← toSkeleton_fromSkeleton_obj Y] at h ⊢
      obtain ⟨e⟩ := toSkeleton_eq_toSkeleton_iff.1 (by simpa using h)
      exact congr_toSkeleton_of_iso (isoMk e)
    · simp [toSkeleton_fromSkeleton_obj]

@[simp]
lemma skeletonMulEquiv_toSkeleton (X : Core C) :
    skeletonMulEquiv (toSkeleton X) = toSkeleton X.of :=
  Skeleton.monoidHom_toSkeleton (inclusion C) X

/-- The identification of the monoids of isomorphism classes of `Core C` and `C` is natural in
strong monoidal functors. -/
lemma skeletonMulEquiv_monoidHom_core {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] (X : Skeleton (Core C)) :
    skeletonMulEquiv (Skeleton.monoidHom F.core X) = Skeleton.monoidHom F (skeletonMulEquiv X) := by
  rw [← toSkeleton_fromSkeleton_obj X]
  simp

end Core

end CategoryTheory
