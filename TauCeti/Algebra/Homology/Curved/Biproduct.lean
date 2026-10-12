/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Curved.Duplex
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Constructions.FiniteProductsOfBinaryProducts

/-!
# Direct sums of curved duplexes

The componentwise biproduct of two curved duplexes has the same curvature. Its differentials
are the direct sums of the original differentials. The componentwise projections exhibit this
object as the categorical binary product; preadditivity makes it a biproduct. In particular,
finite-projective matrix factorizations inherit these sums.
-/

public section

namespace TauCeti.CurvedDuplex

open CategoryTheory CategoryTheory.Limits

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {R : Type w} [Semiring R] [Linear R C] [HasBinaryBiproducts C] {w₀ : R}

attribute [local instance] HasBinaryBiproducts.of_hasBinaryCoproducts

/-- The componentwise direct sum of two curved duplexes with the same curvature. -/
-- The component types of the public morphism formulas require the constructor to be exposed.
@[expose] noncomputable def biprod (X Y : CurvedDuplex C w₀) : CurvedDuplex C w₀ where
  X₀ := X.X₀ ⊞ Y.X₀
  X₁ := X.X₁ ⊞ Y.X₁
  d₀ := CategoryTheory.Limits.biprod.map X.d₀ Y.d₀
  d₁ := CategoryTheory.Limits.biprod.map X.d₁ Y.d₁
  d₀_comp_d₁ := by
    ext <;> simp
  d₁_comp_d₀ := by
    ext <;> simp

@[simp] theorem biprod_X₀ (X Y : CurvedDuplex C w₀) :
    (biprod X Y).X₀ = (X.X₀ ⊞ Y.X₀) := rfl

@[simp] theorem biprod_X₁ (X Y : CurvedDuplex C w₀) :
    (biprod X Y).X₁ = (X.X₁ ⊞ Y.X₁) := rfl

@[simp] theorem biprod_d₀ (X Y : CurvedDuplex C w₀) :
    (biprod X Y).d₀ = CategoryTheory.Limits.biprod.map X.d₀ Y.d₀ := rfl

@[simp] theorem biprod_d₁ (X Y : CurvedDuplex C w₀) :
    (biprod X Y).d₁ = CategoryTheory.Limits.biprod.map X.d₁ Y.d₁ := rfl

/-- Projection to the first curved duplex. -/
noncomputable def biprodFst (X Y : CurvedDuplex C w₀) : biprod X Y ⟶ X where
  f₀ := CategoryTheory.Limits.biprod.fst
  f₁ := CategoryTheory.Limits.biprod.fst
  comm₀ := by simp [biprod]
  comm₁ := by simp [biprod]

/-- Projection to the second curved duplex. -/
noncomputable def biprodSnd (X Y : CurvedDuplex C w₀) : biprod X Y ⟶ Y where
  f₀ := CategoryTheory.Limits.biprod.snd
  f₁ := CategoryTheory.Limits.biprod.snd
  comm₀ := by simp [biprod]
  comm₁ := by simp [biprod]

/-- A pair of maps into curved duplexes induces a map into their direct sum. -/
noncomputable def biprodLift {Z X Y : CurvedDuplex C w₀}
    (f : Z ⟶ X) (g : Z ⟶ Y) : Z ⟶ biprod X Y where
  f₀ := CategoryTheory.Limits.biprod.lift f.f₀ g.f₀
  f₁ := CategoryTheory.Limits.biprod.lift f.f₁ g.f₁
  comm₀ := by
    apply CategoryTheory.Limits.biprod.hom_ext <;> simp [biprod, Category.assoc, f.comm₀, g.comm₀]
  comm₁ := by
    apply CategoryTheory.Limits.biprod.hom_ext <;> simp [biprod, Category.assoc, f.comm₁, g.comm₁]

@[simp] theorem biprodFst_f₀ (X Y : CurvedDuplex C w₀) :
    (biprodFst X Y).f₀ = CategoryTheory.Limits.biprod.fst := (rfl)

@[simp] theorem biprodFst_f₁ (X Y : CurvedDuplex C w₀) :
    (biprodFst X Y).f₁ = CategoryTheory.Limits.biprod.fst := (rfl)

@[simp] theorem biprodSnd_f₀ (X Y : CurvedDuplex C w₀) :
    (biprodSnd X Y).f₀ = CategoryTheory.Limits.biprod.snd := (rfl)

@[simp] theorem biprodSnd_f₁ (X Y : CurvedDuplex C w₀) :
    (biprodSnd X Y).f₁ = CategoryTheory.Limits.biprod.snd := (rfl)

@[simp] theorem biprodLift_f₀ {Z X Y : CurvedDuplex C w₀}
    (f : Z ⟶ X) (g : Z ⟶ Y) :
    (biprodLift f g).f₀ = CategoryTheory.Limits.biprod.lift f.f₀ g.f₀ := (rfl)

@[simp] theorem biprodLift_f₁ {Z X Y : CurvedDuplex C w₀}
    (f : Z ⟶ X) (g : Z ⟶ Y) :
    (biprodLift f g).f₁ = CategoryTheory.Limits.biprod.lift f.f₁ g.f₁ := (rfl)

@[simp] theorem biprodLift_fst {Z X Y : CurvedDuplex C w₀}
    (f : Z ⟶ X) (g : Z ⟶ Y) : biprodLift f g ≫ biprodFst X Y = f := by
  ext <;> simp [biprodLift, biprodFst]

@[simp] theorem biprodLift_snd {Z X Y : CurvedDuplex C w₀}
    (f : Z ⟶ X) (g : Z ⟶ Y) : biprodLift f g ≫ biprodSnd X Y = g := by
  ext <;> simp [biprodLift, biprodSnd]

/-- Maps into a direct sum are determined by their projections. -/
theorem biprod_hom_ext {Z X Y : CurvedDuplex C w₀} {f g : Z ⟶ biprod X Y}
    (h₀ : f ≫ biprodFst X Y = g ≫ biprodFst X Y)
    (h₁ : f ≫ biprodSnd X Y = g ≫ biprodSnd X Y) : f = g := by
  apply hom_ext
  · apply CategoryTheory.Limits.biprod.hom_ext
    · simpa [biprodFst] using congrArg Hom.f₀ h₀
    · simpa [biprodSnd] using congrArg Hom.f₀ h₁
  · apply CategoryTheory.Limits.biprod.hom_ext
    · simpa [biprodFst] using congrArg Hom.f₁ h₀
    · simpa [biprodSnd] using congrArg Hom.f₁ h₁

/-- Inclusion of the first curved duplex into the componentwise direct sum. -/
noncomputable def biprodInl (X Y : CurvedDuplex C w₀) : X ⟶ biprod X Y where
  f₀ := CategoryTheory.Limits.biprod.inl
  f₁ := CategoryTheory.Limits.biprod.inl
  comm₀ := by simp [biprod]
  comm₁ := by simp [biprod]

/-- Inclusion of the second curved duplex into the componentwise direct sum. -/
noncomputable def biprodInr (X Y : CurvedDuplex C w₀) : Y ⟶ biprod X Y where
  f₀ := CategoryTheory.Limits.biprod.inr
  f₁ := CategoryTheory.Limits.biprod.inr
  comm₀ := by simp [biprod]
  comm₁ := by simp [biprod]

/-- Maps out of both summands induce a map out of their direct sum. -/
noncomputable def biprodDesc {X Y Z : CurvedDuplex C w₀}
    (f : X ⟶ Z) (g : Y ⟶ Z) : biprod X Y ⟶ Z where
  f₀ := CategoryTheory.Limits.biprod.desc f.f₀ g.f₀
  f₁ := CategoryTheory.Limits.biprod.desc f.f₁ g.f₁
  comm₀ := by
    apply CategoryTheory.Limits.biprod.hom_ext' <;>
      simp [biprod, f.comm₀, g.comm₀]
  comm₁ := by
    apply CategoryTheory.Limits.biprod.hom_ext' <;>
      simp [biprod, f.comm₁, g.comm₁]

@[simp] theorem biprodInl_f₀ (X Y : CurvedDuplex C w₀) :
    (biprodInl X Y).f₀ = CategoryTheory.Limits.biprod.inl := by simp only [biprodInl]; rfl

@[simp] theorem biprodInl_f₁ (X Y : CurvedDuplex C w₀) :
    (biprodInl X Y).f₁ = CategoryTheory.Limits.biprod.inl := by simp only [biprodInl]; rfl

@[simp] theorem biprodInr_f₀ (X Y : CurvedDuplex C w₀) :
    (biprodInr X Y).f₀ = CategoryTheory.Limits.biprod.inr := by simp only [biprodInr]; rfl

@[simp] theorem biprodInr_f₁ (X Y : CurvedDuplex C w₀) :
    (biprodInr X Y).f₁ = CategoryTheory.Limits.biprod.inr := by simp only [biprodInr]; rfl

@[simp] theorem biprodDesc_f₀ {X Y Z : CurvedDuplex C w₀} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (biprodDesc f g).f₀ = CategoryTheory.Limits.biprod.desc f.f₀ g.f₀ := by
  simp only [biprodDesc]
  rfl

@[simp] theorem biprodDesc_f₁ {X Y Z : CurvedDuplex C w₀} (f : X ⟶ Z) (g : Y ⟶ Z) :
    (biprodDesc f g).f₁ = CategoryTheory.Limits.biprod.desc f.f₁ g.f₁ := by
  simp only [biprodDesc]
  rfl

@[simp] theorem biprodInl_desc {X Y Z : CurvedDuplex C w₀} (f : X ⟶ Z) (g : Y ⟶ Z) :
    biprodInl X Y ≫ biprodDesc f g = f := by
  ext <;> simp

@[simp] theorem biprodInr_desc {X Y Z : CurvedDuplex C w₀} (f : X ⟶ Z) (g : Y ⟶ Z) :
    biprodInr X Y ≫ biprodDesc f g = g := by
  ext <;> simp

@[simp] theorem biprodInl_fst (X Y : CurvedDuplex C w₀) :
    biprodInl X Y ≫ biprodFst X Y = 𝟙 X := by
  ext <;> simp

@[simp] theorem biprodInl_snd (X Y : CurvedDuplex C w₀) :
    biprodInl X Y ≫ biprodSnd X Y = 0 := by
  ext <;> simp

@[simp] theorem biprodInr_fst (X Y : CurvedDuplex C w₀) :
    biprodInr X Y ≫ biprodFst X Y = 0 := by
  ext <;> simp

@[simp] theorem biprodInr_snd (X Y : CurvedDuplex C w₀) :
    biprodInr X Y ≫ biprodSnd X Y = 𝟙 Y := by
  ext <;> simp

/-- Maps from a direct sum are determined by their restrictions to both summands. -/
theorem biprod_hom_ext' {X Y Z : CurvedDuplex C w₀} {f g : biprod X Y ⟶ Z}
    (h₀ : biprodInl X Y ≫ f = biprodInl X Y ≫ g)
    (h₁ : biprodInr X Y ≫ f = biprodInr X Y ≫ g) : f = g := by
  apply hom_ext
  · apply CategoryTheory.Limits.biprod.hom_ext'
    · simpa using congrArg Hom.f₀ h₀
    · simpa using congrArg Hom.f₀ h₁
  · apply CategoryTheory.Limits.biprod.hom_ext'
    · simpa using congrArg Hom.f₁ h₀
    · simpa using congrArg Hom.f₁ h₁

/-- Curved duplexes have componentwise binary products. -/
instance hasBinaryProduct (X Y : CurvedDuplex C w₀) : HasBinaryProduct X Y :=
  HasLimit.mk ⟨BinaryFan.mk (biprodFst X Y) (biprodSnd X Y),
    BinaryFan.IsLimit.mk _ (fun f g ↦ biprodLift f g)
      (fun f g ↦ biprodLift_fst f g) (fun f g ↦ biprodLift_snd f g)
      (fun f g _ h₀ h₁ ↦ biprod_hom_ext
        (h₀.trans (biprodLift_fst f g).symm)
        (h₁.trans (biprodLift_snd f g).symm))⟩

/-- Curved duplexes have componentwise binary products. -/
instance hasBinaryProducts : HasBinaryProducts (CurvedDuplex C w₀) :=
  hasBinaryProducts_of_hasLimit_pair _

/-- Curved duplexes have binary biproducts. -/
instance hasBinaryBiproducts : HasBinaryBiproducts (CurvedDuplex C w₀) :=
  HasBinaryBiproducts.of_hasBinaryProducts

end TauCeti.CurvedDuplex

namespace TauCeti.CurvedDuplex

open CategoryTheory CategoryTheory.Limits
open ZeroObject

universe w v u

variable {C : Type u} [Category.{v} C] [Preadditive C]
  {R : Type w} [Semiring R] [Linear R C] {w₀ : R}

/-- A curved duplex with zero objects in both parities is a zero object. -/
theorem isZero_of_components (X : CurvedDuplex C w₀)
    (h₀ : IsZero X.X₀) (h₁ : IsZero X.X₁) : IsZero X := by
  refine ⟨fun Y ↦ ⟨?_⟩, fun Y ↦ ⟨?_⟩⟩
  · refine { default := 0, uniq := ?_ }
    intro f
    apply hom_ext
    · exact h₀.eq_of_src _ _
    · exact h₁.eq_of_src _ _
  · refine { default := 0, uniq := ?_ }
    intro f
    apply hom_ext
    · exact h₀.eq_of_tgt _ _
    · exact h₁.eq_of_tgt _ _

variable [HasZeroObject C]

/-- The curved duplex on two zero objects. -/
noncomputable def zero : CurvedDuplex C w₀ where
  X₀ := 0
  X₁ := 0
  d₀ := 0
  d₁ := 0
  d₀_comp_d₁ := by simp
  d₁_comp_d₀ := by simp

@[simp] theorem zero_X₀ : (zero (C := C) (w₀ := w₀)).X₀ = 0 := (rfl)

@[simp] theorem zero_X₁ : (zero (C := C) (w₀ := w₀)).X₁ = 0 := (rfl)

@[simp] theorem zero_d₀ : (zero (C := C) (w₀ := w₀)).d₀ = 0 := (rfl)

@[simp] theorem zero_d₁ : (zero (C := C) (w₀ := w₀)).d₁ = 0 := (rfl)

/-- The zero curved duplex is both initial and terminal. -/
theorem isZero_zero : IsZero (zero (C := C) (w₀ := w₀)) :=
  isZero_of_components _ (CategoryTheory.Limits.isZero_zero C)
    (CategoryTheory.Limits.isZero_zero C)

/-- Curved duplexes have a zero object whenever the base category does. -/
instance hasZeroObject : HasZeroObject (CurvedDuplex C w₀) :=
  ⟨⟨zero, isZero_zero⟩⟩

variable [HasBinaryBiproducts C]

/-- Curved duplexes have finite products. -/
instance hasFiniteProducts : HasFiniteProducts (CurvedDuplex C w₀) := by
  let : HasTerminal (CurvedDuplex C w₀) := HasZeroObject.hasTerminal
  exact CategoryTheory.hasFiniteProducts_of_has_binary_and_terminal

/-- Curved duplexes have finite biproducts. -/
instance hasFiniteBiproducts : HasFiniteBiproducts (CurvedDuplex C w₀) :=
  HasFiniteBiproducts.of_hasFiniteProducts

end TauCeti.CurvedDuplex
