/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Preadditive.MorphismIdeal.Basic
public import Mathlib.CategoryTheory.Preadditive.Opposite

/-!
# Opposites of morphism ideals

Taking opposites reverses every morphism in a two-sided ideal. This operation is involutive, and
the quotient by the opposite ideal is canonically equivalent to the opposite of the quotient.
The equivalence identifies the class of an opposite morphism with the opposite of its class.

This lets constructions expressed as additive ideal quotients pass between a category and its
opposite. In particular, stable quotients defined using projective objects can be compared with
the corresponding quotients defined using injective objects on the opposite category.

## Main definitions

* `TauCeti.MorphismIdeal.op`: the opposite of a morphism ideal.
* `TauCeti.MorphismIdeal.unop`: the inverse operation on ideals of an opposite category.
* `TauCeti.MorphismIdeal.opQuotientFunctor`: the canonical functor from the quotient by the
  opposite ideal to the opposite quotient.
* `TauCeti.MorphismIdeal.opQuotientEquivalence`: the resulting equivalence of categories.

## References

* D. Happel, *Triangulated Categories in the Representation Theory of Finite Dimensional
  Algebras*, LMS Lecture Note Series 119, CUP (1988), Section I.2.
-/

public section

universe v u

namespace TauCeti

open CategoryTheory Opposite

namespace MorphismIdeal

variable {C : Type u} [Category.{v} C] [Preadditive C]

/-- The opposite ideal: a morphism of `Cᵒᵖ` belongs to `I.op` when its unopposite belongs to
`I`. -/
def op (I : MorphismIdeal C) : MorphismIdeal Cᵒᵖ where
  hom X Y := (I.hom Y.unop X.unop).comap (CategoryTheory.unopHom X Y)
  comp_mem_left := by
    intro X Y Z f g hg
    exact I.comp_mem_right f.unop hg
  comp_mem_right := by
    intro X Y Z f g hf
    exact I.comp_mem_left g.unop hf

/-- A morphism belongs to the opposite ideal exactly when its unopposite belongs to the original
ideal. -/
@[simp]
theorem mem_op_hom (I : MorphismIdeal C) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    f ∈ I.op.hom X Y ↔ f.unop ∈ I.hom Y.unop X.unop :=
  Iff.rfl

/-- Unopposite an ideal on an opposite category. -/
def unop (I : MorphismIdeal Cᵒᵖ) : MorphismIdeal C where
  hom X Y := (I.hom (Opposite.op Y) (Opposite.op X)).comap (CategoryTheory.opHom X Y)
  comp_mem_left := by
    intro X Y Z f g hg
    exact I.comp_mem_right f.op hg
  comp_mem_right := by
    intro X Y Z f g hf
    exact I.comp_mem_left g.op hf

/-- A morphism belongs to the unopposite ideal exactly when its opposite belongs to the original
ideal. -/
@[simp]
theorem mem_unop_hom (I : MorphismIdeal Cᵒᵖ) {X Y : C} (f : X ⟶ Y) :
    f ∈ I.unop.hom X Y ↔ f.op ∈ I.hom (Opposite.op Y) (Opposite.op X) :=
  Iff.rfl

/-- Taking the opposite and then the unopposite of an ideal recovers the ideal. -/
@[simp]
theorem op_unop (I : MorphismIdeal Cᵒᵖ) : I.unop.op = I := by
  ext X Y f
  simp

/-- Taking the unopposite and then the opposite of an ideal recovers the ideal. -/
@[simp]
theorem unop_op (I : MorphismIdeal C) : I.op.unop = I := by
  ext X Y f
  simp

/-- Taking opposites is injective on morphism ideals. -/
theorem op_injective : Function.Injective (op : MorphismIdeal C → MorphismIdeal Cᵒᵖ) := by
  intro I J h
  rw [← I.unop_op, ← J.unop_op, h]

/-- Taking unopposites is injective on morphism ideals. -/
theorem unop_injective : Function.Injective (unop : MorphismIdeal Cᵒᵖ → MorphismIdeal C) := by
  intro I J h
  rw [← I.op_unop, ← J.op_unop, h]

/-- Taking opposites preserves inclusions of morphism ideals. -/
theorem op_monotone {I J : MorphismIdeal C} (h : I ≤ J) : I.op ≤ J.op := by
  intro X Y f hf
  exact (J.mem_op_hom f).2 (h _ _ ((I.mem_op_hom f).1 hf))

/-- Taking unopposites preserves inclusions of morphism ideals. -/
theorem unop_monotone {I J : MorphismIdeal Cᵒᵖ} (h : I ≤ J) : I.unop ≤ J.unop := by
  intro X Y f hf
  exact (J.mem_unop_hom f).2 (h _ _ ((I.mem_unop_hom f).1 hf))

/-- Inclusion of opposite ideals is equivalent to inclusion of the original ideals. -/
@[simp]
theorem op_monotone_iff {I J : MorphismIdeal C} : I.op ≤ J.op ↔ I ≤ J :=
  ⟨unop_monotone, op_monotone⟩

/-- Inclusion of unopposite ideals is equivalent to inclusion of the original ideals. -/
@[simp]
theorem unop_monotone_iff {I J : MorphismIdeal Cᵒᵖ} : I.unop ≤ J.unop ↔ I ≤ J :=
  ⟨op_monotone, unop_monotone⟩

/-- Congruence modulo the opposite ideal is congruence modulo the original ideal after taking
unopposites. -/
@[simp]
theorem op_rel_iff (I : MorphismIdeal C) {X Y : Cᵒᵖ} {f g : X ⟶ Y} :
    I.op.rel f g ↔ I.rel f.unop g.unop := by
  simp only [rel_iff, mem_op_hom, CategoryTheory.unop_sub]

/-- Congruence modulo an unopposite ideal is congruence modulo the original ideal after taking
opposites. -/
@[simp]
theorem unop_rel_iff (I : MorphismIdeal Cᵒᵖ) {X Y : C} {f g : X ⟶ Y} :
    I.unop.rel f g ↔ I.rel f.op g.op := by
  simp only [rel_iff, mem_unop_hom, CategoryTheory.op_sub]

/-- The canonical functor from the quotient by the opposite ideal to the opposite of the quotient.
It sends the class of `f` to the opposite of the class of `f.unop`. -/
noncomputable abbrev opQuotientFunctor (I : MorphismIdeal C) :
    CategoryTheory.Functor I.op.Quotient I.Quotientᵒᵖ :=
  I.op.lift I.quotientFunctor.op fun X Y f hf ↦ by
    rw [CategoryTheory.Functor.mem_kerIdeal_hom]
    apply Quiver.Hom.unop_inj
    simpa using (I.quotientFunctor_map_eq_zero_iff).2 ((I.mem_op_hom f).mp hf)

@[simp]
theorem opQuotientFunctor_obj (I : MorphismIdeal C) (X : Cᵒᵖ) :
    I.opQuotientFunctor.obj (I.op.quotientFunctor.obj X) =
      Opposite.op (I.quotientFunctor.obj X.unop) :=
  rfl

/-- The canonical opposite-quotient functor has the expected value on a representative. -/
@[simp]
theorem opQuotientFunctor_map (I : MorphismIdeal C) {X Y : Cᵒᵖ} (f : X ⟶ Y) :
    I.opQuotientFunctor.map (I.op.quotientFunctor.map f) =
      (I.quotientFunctor.map f.unop).op :=
  rfl

instance (I : MorphismIdeal C) : I.opQuotientFunctor.Faithful where
  map_injective {X Y} f g h := by
    obtain ⟨f, rfl⟩ := I.op.quotientFunctor.map_surjective f
    obtain ⟨g, rfl⟩ := I.op.quotientFunctor.map_surjective g
    rw [I.opQuotientFunctor_map, I.opQuotientFunctor_map] at h
    rw [I.op.quotientFunctor_map_eq_iff, mem_op_hom, CategoryTheory.unop_sub]
    exact I.quotientFunctor_map_eq_iff.mp (Quiver.Hom.op_inj h)

instance (I : MorphismIdeal C) : I.opQuotientFunctor.Full where
  map_surjective {X Y} f := by
    obtain ⟨g, hg⟩ := I.quotientFunctor.map_surjective f.unop
    refine ⟨I.op.quotientFunctor.map g.op, ?_⟩
    rw [I.opQuotientFunctor_map]
    exact Quiver.Hom.unop_inj hg

instance (I : MorphismIdeal C) : I.opQuotientFunctor.EssSurj where
  mem_essImage := by
    rintro ⟨⟨X⟩⟩
    exact ⟨⟨Opposite.op X⟩, ⟨Iso.refl _⟩⟩

noncomputable instance (I : MorphismIdeal C) : I.opQuotientFunctor.IsEquivalence :=
  CategoryTheory.Functor.IsEquivalence.mk

/-- Quotienting the opposite category by the opposite ideal is canonically equivalent to taking
the opposite of the quotient category. -/
noncomputable abbrev opQuotientEquivalence (I : MorphismIdeal C) :
    I.op.Quotient ≌ I.Quotientᵒᵖ :=
  I.opQuotientFunctor.asEquivalence

@[simp]
theorem opQuotientEquivalence_functor (I : MorphismIdeal C) :
    I.opQuotientEquivalence.functor = I.opQuotientFunctor :=
  rfl

instance (I : MorphismIdeal C) : I.opQuotientEquivalence.functor.Additive := by
  rw [opQuotientEquivalence_functor]
  infer_instance

end MorphismIdeal

end TauCeti
