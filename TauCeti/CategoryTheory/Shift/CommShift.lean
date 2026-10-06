/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Algebra.Group.Int.Defs

/-!
# Checking shift compatibility of natural transformations at a generator

For integral shifts, a natural transformation between functors commuting with shifts is
compatible with every shift as soon as it is compatible with the shift by one. Compatibility
is closed under addition by Mathlib's `NatTrans.CommShiftCore.add`; cancellation of a shift
gives compatibility with negative integers.
-/

public section

namespace TauCeti

open CategoryTheory CategoryTheory.Functor

open CategoryTheory.NatTrans

variable {C D : Type*} [Category* C] [Category* D]
variable {A : Type*} [AddMonoid A] [HasShift C A] [HasShift D A]
variable {F G : C ⥤ D} [F.CommShift A] [G.CommShift A] {τ : F ⟶ G}

/-- Compatibility with shifts by `b` and `a + b` is equivalent to compatibility with shifts
by `b` and `a`. It suffices that the target shift by `b` is faithful; in particular this holds
for group shifts. -/
lemma natTrans_commShiftCore_add_right_iff {a b : A} [(shiftFunctor D b).Faithful] :
    CommShiftCore τ b ∧ CommShiftCore τ (a + b) ↔ CommShiftCore τ b ∧ CommShiftCore τ a := by
  constructor
  · rintro ⟨hb, hab⟩
    refine ⟨hb, ?_⟩
    constructor
    ext X
    apply (shiftFunctor D b).map_injective
    have h := hab.shift_app_comm τ X
    rw [F.commShiftIso_add, G.commShiftIso_add,
      Functor.CommShift.isoAdd_hom_app, Functor.CommShift.isoAdd_hom_app] at h
    rw [← τ.naturality_assoc ((shiftFunctorAdd C a b).hom.app X)] at h
    have hn := (shiftFunctorAdd D a b).inv.naturality (τ.app X)
    dsimp at hn
    simp only [Category.assoc] at h
    rw [← hn] at h
    rw [cancel_epi (F.map ((shiftFunctorAdd C a b).hom.app X))] at h
    simp only [← Category.assoc] at h
    rw [cancel_mono ((shiftFunctorAdd D a b).inv.app (G.obj X))] at h
    simp only [Category.assoc] at h
    dsimp only [Functor.comp_obj] at h
    rw [← hb.shift_app_comm_assoc τ (X⟦a⟧)] at h
    rw [cancel_epi ((F.commShiftIso b).hom.app (X⟦a⟧))] at h
    simpa only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
      Functor.map_comp] using h
  · rintro ⟨hb, ha⟩
    exact ⟨hb, ha.add hb⟩

/-- A natural transformation is compatible with all integral shifts if and only if it is
compatible with the shift by one. -/
lemma natTrans_commShift_iff_one {F G : C ⥤ D} [HasShift C ℤ] [HasShift D ℤ]
    [F.CommShift ℤ] [G.CommShift ℤ] {τ : F ⟶ G} :
    CommShift τ ℤ ↔ CommShiftCore τ (1 : ℤ) := by
  constructor
  · intro h
    exact ⟨h.shift_comm 1⟩
  · intro h
    apply CommShift.of_core
    intro n
    have hneg : CommShiftCore τ (-1 : ℤ) :=
      (natTrans_commShiftCore_add_right_iff.mp
        ⟨h, by simpa using (CommShiftCore.zero (τ := τ) ℤ)⟩).2
    induction n using Int.induction_on with
    | zero => exact CommShiftCore.zero (τ := τ) ℤ
    | succ n ih => exact ih.add h
    | pred n ih => simpa only [sub_eq_add_neg] using ih.add hneg

end TauCeti
