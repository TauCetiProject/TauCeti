/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Preadditive.SingleObj
public import TauCeti.CategoryTheory.Preadditive.Radical.Basic
public import TauCeti.RingTheory.VonNeumannRegular

/-!
# Von Neumann regular preadditive categories

A preadditive category is von Neumann regular if every morphism `f : X ⟶ Y` has an inner
inverse `g : Y ⟶ X` with `f ≫ g ≫ f = f`. Regularity passes to endomorphism rings, is invariant
under passage to the opposite category, and forces the categorical Jacobson radical to vanish.
On a one-object category it agrees with ring regularity.

See Simson, *On pure global dimension of locally finitely presented Grothendieck categories*,
§1, before Proposition 1.2.
-/

public section

namespace TauCeti

open CategoryTheory

/-- A preadditive category is von Neumann regular if every morphism has an inner inverse. -/
class IsVonNeumannRegularCategory (C : Type*) [Category* C] [Preadditive C] : Prop where
  exists_comp_comp_eq_self ⦃X Y : C⦄ (f : X ⟶ Y) : ∃ g : Y ⟶ X, f ≫ g ≫ f = f

namespace IsVonNeumannRegularCategory

variable {C : Type*} [Category* C] [Preadditive C]

/-- Von Neumann regularity is invariant under passing to the opposite category. -/
@[simp]
theorem op_iff : IsVonNeumannRegularCategory Cᵒᵖ ↔ IsVonNeumannRegularCategory C := by
  constructor
  · intro h
    constructor
    intro X Y f
    obtain ⟨g, hg⟩ := h.exists_comp_comp_eq_self f.op
    refine ⟨g.unop, ?_⟩
    simpa only [unop_comp, Quiver.Hom.unop_op, Category.assoc]
      using congrArg Quiver.Hom.unop hg
  · intro h
    constructor
    intro X Y f
    obtain ⟨g, hg⟩ := h.exists_comp_comp_eq_self f.unop
    exact ⟨g.op, Quiver.Hom.unop_inj (by simpa only [unop_comp, Quiver.Hom.unop_op,
      Category.assoc] using hg)⟩

/-- Endomorphism rings in a von Neumann regular category are von Neumann regular. -/
instance [IsVonNeumannRegularCategory C] (X : C) : IsVonNeumannRegularRing (End X) where
  exists_mul_mul_eq_self f := by
    obtain ⟨g, hg⟩ := exists_comp_comp_eq_self f.asHom
    exact ⟨End.of g, End.ext (by simpa only [End.mul_asHom, Category.assoc] using hg)⟩

/-- A von Neumann regular category has zero Jacobson radical. -/
theorem jacobsonRadicalIdeal_eq_bot [IsVonNeumannRegularCategory C] :
    jacobsonRadicalIdeal C = ⊥ := by
  refine eq_bot_iff.mpr (MorphismIdeal.le_def.mpr fun X Y f hf ↦ MorphismIdeal.mem_bot.mpr ?_)
  rw [jacobsonRadicalIdeal_hom] at hf
  obtain ⟨g, hg⟩ := exists_comp_comp_eq_self f
  have := mem_jacobsonRadical_iff_isIso_id_sub_comp_right.mp hf g
  have hzero : (𝟙 X - f ≫ g) ≫ f = 0 := by
    simp [Preadditive.sub_comp, hg]
  exact (cancel_epi (𝟙 X - f ≫ g)).mp (by simpa using hzero)

end IsVonNeumannRegularCategory

/-- The one-object category of a ring is von Neumann regular exactly when the ring is. -/
@[simp]
theorem isVonNeumannRegularCategory_singleObj_iff (R : Type*) [Ring R] :
    IsVonNeumannRegularCategory (SingleObj R) ↔ IsVonNeumannRegularRing R := by
  constructor
  · intro h
    constructor
    intro a
    obtain ⟨b, hb⟩ := h.exists_comp_comp_eq_self
      (X := SingleObj.star R) (Y := SingleObj.star R) a
    exact ⟨b, by simpa only [SingleObj.comp_as_mul, mul_assoc] using hb⟩
  · intro h
    constructor
    intro X Y f
    obtain ⟨g, hg⟩ := h.exists_mul_mul_eq_self f
    exact ⟨g, by simpa only [SingleObj.comp_as_mul, mul_assoc] using hg⟩

end TauCeti
