/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Shift.CommShift
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Algebra.Ring.NegOnePow
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Preadditive.FunctorCategory

/-!
# Shift compatibility of natural transformations and of shift functors

For integral shifts, a natural transformation between functors commuting with shifts is
compatible with every shift as soon as it is compatible with the shift by one. Compatibility
is closed under addition by Mathlib's `NatTrans.CommShiftCore.add`; cancellation of a shift
gives compatibility with negative integers.

In a preadditive category with an additive shift by `ℤ`, each shift functor `⟦n⟧` commutes with
the shifts through the isomorphisms `X⟦a⟧⟦n⟧ ≅ X⟦n⟧⟦a⟧` of `shiftFunctorComm` multiplied by the
sign `(-1)^(a * n)` (`TauCeti.shiftFunctorCommShift`). The sign is a homomorphism in `a`, so the
twisted isomorphisms still satisfy the coherence conditions of `Functor.CommShift`. With it, the
shifted mapping cocone `(mappingCone φ)⟦-1⟧` of a morphism of cochain complexes commutes with
the shifts so that its projection to the source of `φ` does.
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

section ShiftFunctor

variable (C : Type*) [Category* C]

/-- The isomorphism `X⟦a + b⟧⟦n⟧ ≅ X⟦n⟧⟦a + b⟧` is obtained from those for `a` and `b`. -/
lemma shiftFunctorComm_hom_app_add {M : Type*} [AddCommMonoid M] [HasShift C M] (a b n : M)
    (X : C) :
    (shiftFunctorComm C (a + b) n).hom.app X =
      ((shiftFunctorAdd C a b).hom.app X)⟦n⟧' ≫ (shiftFunctorComm C b n).hom.app (X⟦a⟧) ≫
        ((shiftFunctorComm C a n).hom.app X)⟦b⟧' ≫ (shiftFunctorAdd C a b).inv.app (X⟦n⟧) := by
  rw [← shiftFunctorComm_symm C n (a + b), ← shiftFunctorComm_symm C n a,
    ← shiftFunctorComm_symm C n b, Iso.symm_hom, Iso.symm_hom, Iso.symm_hom,
    ← cancel_epi ((shiftFunctorComm C n (a + b)).hom.app X), Iso.hom_inv_id_app,
    shiftFunctorComm_hom_app_comp_shift_shiftFunctorAdd_hom_app_assoc]
  simp [← Functor.map_comp_assoc]

variable [Preadditive C] [HasShift C ℤ] [∀ a : ℤ, (shiftFunctor C a).Additive]

/-- The shift functor `⟦n⟧` commutes with the shifts through the isomorphisms
`X⟦a⟧⟦n⟧ ≅ X⟦n⟧⟦a⟧` of `shiftFunctorComm` multiplied by the sign `(-1)^(a * n)`. This is not an
instance: without the sign, `shiftFunctorComm` gives another such structure. -/
@[instance_reducible]
noncomputable def shiftFunctorCommShift (n : ℤ) : (shiftFunctor C n).CommShift ℤ where
  commShiftIso a := (a * n).negOnePow • shiftFunctorComm C a n
  commShiftIso_zero := by
    ext X
    rw [Functor.CommShift.isoZero_hom_app, Preadditive.smul_iso_hom, NatTrans.app_units_zsmul,
      zero_mul, Int.negOnePow_zero, one_smul, ← shiftFunctorComm_symm C n 0, Iso.symm_hom,
      ← cancel_epi ((shiftFunctorComm C n 0).hom.app X), Iso.hom_inv_id_app,
      shiftFunctorComm_zero_hom_app]
    simp [← Functor.map_comp_assoc]
  commShiftIso_add a b := by
    ext X
    simp [shiftFunctorComm_hom_app_add, mul_add, Int.negOnePow_add, smul_smul, mul_comm,
      Functor.map_units_smul, Linear.comp_units_smul, Linear.units_smul_comp]

lemma shiftFunctorCommShift_commShiftIso_hom_app (n a : ℤ) (X : C) :
    letI := shiftFunctorCommShift C n
    ((shiftFunctor C n).commShiftIso a).hom.app X =
      (a * n).negOnePow • (shiftFunctorComm C a n).hom.app X :=
  (rfl)

end ShiftFunctor

end TauCeti
