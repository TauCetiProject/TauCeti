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
public import Mathlib.CategoryTheory.Triangulated.Functor

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
the shifts so that its projection to the source of `φ` does. For this structure, the image of a
triangle by `⟦n⟧` is isomorphic to its shift by `n` in the category of triangles
(`TauCeti.shiftFunctorMapTriangleIso`).
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
  simp only [← shiftFunctorComm_symm C n, Iso.symm_hom]
  rw [← cancel_epi ((shiftFunctorComm C n (a + b)).hom.app X), Iso.hom_inv_id_app,
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
    simp only [Functor.CommShift.isoZero_hom_app, Preadditive.smul_iso_hom, zero_mul,
      Int.negOnePow_zero, one_smul, ← shiftFunctorComm_symm C n 0, Iso.symm_hom]
    rw [← cancel_epi ((shiftFunctorComm C n 0).hom.app X), Iso.hom_inv_id_app,
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

open Pretriangulated in
/-- With the commutation with the shifts `TauCeti.shiftFunctorCommShift`, the image of a
triangle by `⟦n⟧` is isomorphic to its shift `Triangle.shiftFunctor C n`, in which the three
morphisms carry the sign `(-1)^n`. The isomorphism is the identity on the first and third objects
and `(-1)^n` on the second. -/
noncomputable def shiftFunctorMapTriangleIso (n : ℤ) (T : Triangle C) :
    letI := shiftFunctorCommShift C n
    (shiftFunctor C n).mapTriangle.obj T ≅ (Triangle.shiftFunctor C n).obj T :=
  letI := shiftFunctorCommShift C n
  -- The triangles are given explicitly so that the morphisms agree up to reducible unfolding.
  Triangle.isoMk
    (Triangle.mk (T.mor₁⟦n⟧') (T.mor₂⟦n⟧')
      (T.mor₃⟦n⟧' ≫ ((shiftFunctor C n).commShiftIso 1).hom.app T.obj₁))
    (Triangle.mk (n.negOnePow • T.mor₁⟦n⟧') (n.negOnePow • T.mor₂⟦n⟧')
      (n.negOnePow • T.mor₃⟦n⟧' ≫ (shiftFunctorComm C 1 n).hom.app T.obj₁))
    (Iso.refl _) (n.negOnePow • Iso.refl _) (Iso.refl _) (by simp [Preadditive.smul_iso_hom])
    (by simp [Preadditive.smul_iso_hom, smul_smul])
    (by simp [shiftFunctorCommShift_commShiftIso_hom_app])

section MapTriangle

open Pretriangulated

@[simp]
lemma shiftFunctorMapTriangleIso_hom_hom₁ (n : ℤ) (T : Triangle C) :
    (shiftFunctorMapTriangleIso C n T).hom.hom₁ = 𝟙 _ :=
  (rfl)

@[simp]
lemma shiftFunctorMapTriangleIso_hom_hom₂ (n : ℤ) (T : Triangle C) :
    (shiftFunctorMapTriangleIso C n T).hom.hom₂ = n.negOnePow • 𝟙 _ :=
  (rfl)

@[simp]
lemma shiftFunctorMapTriangleIso_hom_hom₃ (n : ℤ) (T : Triangle C) :
    (shiftFunctorMapTriangleIso C n T).hom.hom₃ = 𝟙 _ :=
  (rfl)

@[simp]
lemma shiftFunctorMapTriangleIso_inv_hom₁ (n : ℤ) (T : Triangle C) :
    (shiftFunctorMapTriangleIso C n T).inv.hom₁ = 𝟙 _ :=
  (rfl)

@[simp]
lemma shiftFunctorMapTriangleIso_inv_hom₂ (n : ℤ) (T : Triangle C) :
    (shiftFunctorMapTriangleIso C n T).inv.hom₂ = n.negOnePow • 𝟙 _ := by
  simp only [shiftFunctorMapTriangleIso, Triangle.isoMk_inv, Triangle.homMk_hom₂,
    Preadditive.smul_iso_inv, Int.units_inv_eq_self, Iso.refl_inv]
  -- Both sides are now `n.negOnePow • 𝟙 (T.obj₂⟦n⟧)`; they differ only in how the object
  -- `T.obj₂⟦n⟧` is written in the type of the scalar action, which `simp` cannot rewrite.
  rfl

@[simp]
lemma shiftFunctorMapTriangleIso_inv_hom₃ (n : ℤ) (T : Triangle C) :
    (shiftFunctorMapTriangleIso C n T).inv.hom₃ = 𝟙 _ :=
  (rfl)

end MapTriangle

end ShiftFunctor

end TauCeti
