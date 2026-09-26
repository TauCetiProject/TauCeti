/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.DG.HomotopyCategory

/-!
# Closed morphisms and the underlying category of a DG category

Mathlib's `ForgetEnrichment` regards a morphism of an enriched category as a map from the tensor
unit to a Hom object.  For a DG category, such a map is exactly a closed morphism of degree zero.
This file makes the comparison explicit and sends a closed morphism to its class in `H⁰`.

The underlying category is used rather than introducing a second category of cocycles.  This
allows Mathlib's enriched functors and natural transformations to act on closed morphisms without
copying their definitions.

## References

* B. Keller, *Deriving DG categories*, Section 1.
-/

public section

open CategoryTheory MonoidalCategory HomologicalComplex

namespace TauCeti

universe v u

variable (R : Type v) [CommRing R] {C : Type u} [DGCategory R C]

/-- The degree-zero component of a morphism in the underlying category of a DG category. -/
noncomputable def dgClosedHom
    {X Y : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C} (f : X ⟶ Y) :
    DGHom R 0 (ForgetEnrichment.to (CochainComplex (ModuleCat.{v} R) ℤ) X)
      (ForgetEnrichment.to (CochainComplex (ModuleCat.{v} R) ℤ) Y) :=
  ((ForgetEnrichment.homTo (CochainComplex (ModuleCat.{v} R) ℤ) f).f 0).hom
    ((singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).inv 1)

/-- The degree-zero component of an underlying morphism is closed. -/
theorem dgClosedHom_mem_dgCycles
    {X Y : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C} (f : X ⟶ Y) :
    dgClosedHom R f ∈ dgCycles R (ForgetEnrichment.to (CochainComplex (ModuleCat.{v} R) ℤ) X)
      (ForgetEnrichment.to (CochainComplex (ModuleCat.{v} R) ℤ) Y) := by
  rw [mem_dgCycles]
  have hu : (𝟙_ (CochainComplex (ModuleCat.{v} R) ℤ)).d 0 (0 + 1) = 0 :=
    HomologicalComplex.single_obj_d (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{v} R)) 0 (0 + 1)
  rw [dgClosedHom, ← ModuleCat.comp_apply,
    (ForgetEnrichment.homTo (CochainComplex (ModuleCat.{v} R) ℤ) f).comm 0 (0 + 1), hu,
    Limits.zero_comp]
  simp

/-- A closed degree-zero morphism, regarded as a morphism in Mathlib's underlying category of
the DG enrichment. -/
noncomputable def dgClosedHomOf {X Y : C} (f : DGHom R 0 X Y)
    (hf : f ∈ dgCycles R X Y) :
    (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) X) ⟶
      (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) Y) :=
  ForgetEnrichment.homOf _ <|
    mkHomFromSingle (ModuleCat.ofHom (LinearMap.toSpanSingleton R _ f)) fun k hk => by
      obtain rfl : k = 0 + 1 := hk.symm
      ext
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom,
        LinearMap.toSpanSingleton_apply_one, ModuleCat.hom_zero, LinearMap.zero_apply] using
        (mem_dgCycles R).mp hf

/-- Extracting the closed morphism from `dgClosedHomOf` recovers its input. -/
@[simp]
theorem dgClosedHom_dgClosedHomOf {X Y : C} (f : DGHom R 0 X Y)
    (hf : f ∈ dgCycles R X Y) : dgClosedHom R (dgClosedHomOf R f hf) = f := by
  rw [dgClosedHom, dgClosedHomOf, ForgetEnrichment.homTo_homOf, mkHomFromSingle_f]
  rw [← ModuleCat.comp_apply, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]
  exact LinearMap.toSpanSingleton_apply_one (R := R) (M := DGHom R 0 X Y) f

/-- Every underlying morphism of a DG category is determined by its closed degree-zero
component. -/
theorem dgClosedHom_injective {X Y : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C} :
    Function.Injective (dgClosedHom R : (X ⟶ Y) → _) := by
  intro f g h
  have hfg : ForgetEnrichment.homTo (CochainComplex (ModuleCat.{v} R) ℤ) f =
      ForgetEnrichment.homTo (CochainComplex (ModuleCat.{v} R) ℤ) g := by
    apply HomologicalComplex.from_single_hom_ext
    rw [← cancel_epi (singleObjXSelf (ComplexShape.up ℤ) 0 (𝟙_ (ModuleCat.{v} R))).inv]
    apply ModuleCat.hom_ext
    apply LinearMap.ext_ring
    exact h
  have := congrArg (ForgetEnrichment.homOf (CochainComplex (ModuleCat.{v} R) ℤ)) hfg
  simpa only [ForgetEnrichment.homOf_homTo] using this

/-- Constructing an underlying morphism from the closed component of an underlying morphism
recovers that morphism. -/
@[simp]
theorem dgClosedHomOf_dgClosedHom {X Y : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C}
    (f : X ⟶ Y) :
    dgClosedHomOf R (dgClosedHom R f) (dgClosedHom_mem_dgCycles R f) = f := by
  apply dgClosedHom_injective R
  exact dgClosedHom_dgClosedHomOf R _ _

/-- Morphisms in Mathlib's underlying category of a DG category are precisely the closed
degree-zero morphisms of its Hom complexes. -/
noncomputable def dgClosedHomEquiv
    (X Y : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) :
    (X ⟶ Y) ≃ dgCycles R (ForgetEnrichment.to (CochainComplex (ModuleCat.{v} R) ℤ) X)
      (ForgetEnrichment.to (CochainComplex (ModuleCat.{v} R) ℤ) Y) where
  toFun f := ⟨dgClosedHom R f, dgClosedHom_mem_dgCycles R f⟩
  invFun f := dgClosedHomOf (C := C) R f.1 f.2
  left_inv f := dgClosedHomOf_dgClosedHom R f
  right_inv f := Subtype.ext (dgClosedHom_dgClosedHomOf R f.1 f.2)

/-- The equivalence from underlying morphisms to cycles evaluates by taking the degree-zero
component. -/
@[simp]
theorem dgClosedHomEquiv_apply_coe
    {X Y : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C} (f : X ⟶ Y) :
    (dgClosedHomEquiv R X Y f).1 = dgClosedHom R f :=
  (rfl)

/-- The inverse equivalence constructs the underlying morphism represented by a cocycle. -/
@[simp]
theorem dgClosedHomEquiv_symm_apply
    {X Y : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C}
    (f : dgCycles R (ForgetEnrichment.to (CochainComplex (ModuleCat.{v} R) ℤ) X)
      (ForgetEnrichment.to (CochainComplex (ModuleCat.{v} R) ℤ) Y)) :
    (dgClosedHomEquiv R X Y).symm f = dgClosedHomOf R f.1 f.2 :=
  (rfl)

/-- The identity at an object of Mathlib's underlying category has the DG identity as its
closed component. -/
@[simp]
theorem dgClosedHom_id
    (X : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) :
    dgClosedHom R (𝟙 X) =
      dgId R (ForgetEnrichment.to (CochainComplex (ModuleCat.{v} R) ℤ) X) := by
  rw [dgClosedHom, ForgetEnrichment.homTo_id]
  exact (dgId_def R _).symm

/-- Composition in the underlying category is DG composition of closed degree-zero
morphisms. -/
@[simp]
theorem dgClosedHom_comp
    {X Y Z : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C}
    (f : X ⟶ Y) (g : Y ⟶ Z) :
    dgClosedHom R (f ≫ g) = dgCompZero R (dgClosedHom R f) (dgClosedHom R g) := by
  rw [dgCompZero_def]
  simp only [dgClosedHom, ForgetEnrichment.homTo_comp, HomologicalComplex.comp_f]
  rw [leftUnitor_inv_f, leftUnitor'_inv]
  simp only [Category.assoc, tensorHom_def, HomologicalComplex.comp_f,
    ι_whiskerRight_assoc, ι_whiskerLeft_assoc]
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
    ModuleCat.MonoidalCategory.whiskerRight_apply,
    ModuleCat.MonoidalCategory.whiskerLeft_apply,
    ModuleCat.MonoidalCategory.leftUnitor_inv_apply]
  rw [← ModuleCat.comp_apply, ← dgCompMap_def]
  exact dgCompMap_tmul R (by omega) _ _

/-- The underlying morphism constructed from the DG identity is the identity. -/
@[simp]
theorem dgClosedHomOf_dgId (X : C) :
    dgClosedHomOf R (dgId R X) ((mem_dgCycles R).mpr (dgDifferential_dgId R X)) =
      𝟙 (ForgetEnrichment.of (CochainComplex (ModuleCat.{v} R) ℤ) X) := by
  apply dgClosedHom_injective R
  simp

/-- The underlying morphism constructed from a composite of cocycles is their composite. -/
@[simp]
theorem dgClosedHomOf_dgCompZero {X Y Z : C} (f : DGHom R 0 X Y) (g : DGHom R 0 Y Z)
    (hf : f ∈ dgCycles R X Y) (hg : g ∈ dgCycles R Y Z) :
    dgClosedHomOf R (dgCompZero R f g) (dgCompZero_mem_dgCycles R hf hg) =
      dgClosedHomOf R f hf ≫ dgClosedHomOf R g hg := by
  apply dgClosedHom_injective R
  simp

/-- The canonical functor from closed degree-zero morphisms to their classes in `H⁰`.
It is the identity on the underlying objects. -/
@[expose]
noncomputable def dgClosedToHomotopy :
    ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C ⥤ DGHomotopyCategory R C where
  obj X := DGHomotopyCategory.of R
    (ForgetEnrichment.to (CochainComplex (ModuleCat.{v} R) ℤ) X)
  map f := DGHomotopyCategory.homOf R (dgClosedHom R f) (dgClosedHom_mem_dgCycles R f)
  map_id X := by
    simp only [dgClosedHom_id, DGHomotopyCategory.homOf_dgId]
  map_comp f g := by
    simpa only [dgClosedHom_comp] using
      (DGHomotopyCategory.homOf_comp R (dgClosedHom R f) (dgClosedHom R g)
        (dgClosedHom_mem_dgCycles R f) (dgClosedHom_mem_dgCycles R g)).symm

/-- The quotient functor fixes the objects of the DG category. -/
@[simp]
theorem dgClosedToHomotopy_obj
    (X : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C) :
    (dgClosedToHomotopy R).obj X =
      DGHomotopyCategory.of R
        (ForgetEnrichment.to (CochainComplex (ModuleCat.{v} R) ℤ) X) :=
  (rfl)

/-- The quotient functor takes an underlying morphism to the class of its closed component. -/
theorem dgClosedToHomotopy_map
    {X Y : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C} (f : X ⟶ Y) :
    (dgClosedToHomotopy R).map f =
      DGHomotopyCategory.homOf R (dgClosedHom R f) (dgClosedHom_mem_dgCycles R f) :=
  (rfl)

/-- The quotient functor sends a closed morphism to its homotopy class. -/
@[simp]
theorem dgClosedToHomotopy_map_dgClosedHomOf {X Y : C} (f : DGHom R 0 X Y)
    (hf : f ∈ dgCycles R X Y) :
    (dgClosedToHomotopy R).map (dgClosedHomOf R f hf) =
      DGHomotopyCategory.homOf R f hf := by
  rw [dgClosedToHomotopy_map]
  simp only [dgClosedHom_dgClosedHomOf]
  congr

/-- Every morphism in `H⁰(C)` has a representative in the underlying closed category. -/
instance full_dgClosedToHomotopy : (dgClosedToHomotopy (C := C) R).Full where
  map_surjective := by
    intro X Y c
    change DGHomotopyClass R
        (ForgetEnrichment.to (CochainComplex (ModuleCat.{v} R) ℤ) X)
        (ForgetEnrichment.to (CochainComplex (ModuleCat.{v} R) ℤ) Y) at c
    obtain ⟨f, hf, hfc⟩ := exists_dgHomotopyClass_eq (C := C) R c
    refine ⟨dgClosedHomOf (C := C) R f hf, ?_⟩
    exact (dgClosedToHomotopy_map_dgClosedHomOf (C := C) R f hf).trans (by
      rw [DGHomotopyCategory.homOf_def]
      exact hfc)

/-- Two underlying closed morphisms have the same class in `H⁰` precisely when their
difference is a boundary. -/
@[simp]
theorem dgClosedToHomotopy_map_eq_iff
    {X Y : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C} (f g : X ⟶ Y) :
    (dgClosedToHomotopy R).map f = (dgClosedToHomotopy R).map g ↔
      dgClosedHom R f - dgClosedHom R g ∈ dgBoundaries R
        (ForgetEnrichment.to (CochainComplex (ModuleCat.{v} R) ℤ) X)
        (ForgetEnrichment.to (CochainComplex (ModuleCat.{v} R) ℤ) Y) :=
  DGHomotopyCategory.homOf_eq_iff R
    (dgClosedHom_mem_dgCycles R f) (dgClosedHom_mem_dgCycles R g)

/-- A closed morphism becomes zero in `H⁰` exactly when it is a boundary. -/
@[simp]
theorem dgClosedToHomotopy_map_eq_zero_iff
    {X Y : ForgetEnrichment (CochainComplex (ModuleCat.{v} R) ℤ) C} (f : X ⟶ Y) :
    (dgClosedToHomotopy R).map f = 0 ↔
      dgClosedHom R f ∈ dgBoundaries R
        (ForgetEnrichment.to (CochainComplex (ModuleCat.{v} R) ℤ) X)
        (ForgetEnrichment.to (CochainComplex (ModuleCat.{v} R) ℤ) Y) :=
  DGHomotopyCategory.homOf_eq_zero_iff R (dgClosedHom_mem_dgCycles R f)

end TauCeti
