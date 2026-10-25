/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Class
public import TauCeti.LinearAlgebra.IntegralLattice.Isometry.Group
import TauCeti.Algebra.Module.Lattice
import TauCeti.LinearAlgebra.Reflection

/-!
# Proper isometries and proper classes of integral lattices

An isometry `e : L ≅ M` between two integral lattices in the same rational space `V` is
**proper** when its ambient linear equivalence of `V` has positive determinant, that is, when it
preserves the orientations of `V`. For a self-isometry of `L` the ambient determinant is the
determinant of its restriction to the carrier, so the proper self-isometries are exactly the
elements of `SO(L)`. When the form is nondegenerate the ambient determinant of every isometry is
`±1`, and proper means determinant one; positivity is the condition that still compares
orientations when the form is degenerate.

Proper isometry is an equivalence relation, and its classes are the **proper classes**
`cls⁺ L`. Every proper class lies in a single class `cls L`, and each class consists of one or
two proper classes. In positive rank, it is one proper class exactly when `L` has an improper
self-isometry, so that `[O(L) : SO(L)] = 2`, and two proper classes when `O(L) = SO(L)`; in
either case the number of proper classes in the class of `L` times `[O(L) : SO(L)]` is `2`.
In rank zero every isometry is proper, and the class of `L` is a single proper class.

## Main definitions

* `TauCeti.IntegralLattice.Isometry.IsProper`: an isometry whose ambient equivalence has positive
  determinant.
* `TauCeti.IntegralLattice.properIsometrySetoid`: proper isometry of integral lattices in `V`.
* `TauCeti.IntegralLattice.ProperIsometryQuotient`: the proper classes of integral lattices in
  `V`, and `TauCeti.IntegralLattice.properIsometryClass`: the proper class `cls⁺ L` of a lattice.
* `TauCeti.IntegralLattice.ProperIsometryQuotient.toIsometryQuotient`: the class containing a
  proper class.
* `TauCeti.IntegralLattice.properIsometryQuotientEquiv`: transport of proper classes along an
  ambient linear equivalence.

## Main results

* `TauCeti.IntegralLattice.Isometry.isProper_iff_det_eq_one`: a self-isometry is proper exactly
  when it lies in `SO(L)`.
* `TauCeti.IntegralLattice.Isometry.isProper_trans_iff`: a composite of isometries is proper
  exactly when both factors are proper or both are improper.
* `TauCeti.IntegralLattice.properIsometryClass_eq_properIsometryClass_iff_of_index_eq_two`: when
  `L` has an improper self-isometry, the proper class of `L` is its class.
* `TauCeti.IntegralLattice.natCard_preimage_toIsometryQuotient_mul_index`: in positive rank, the
  number of proper classes in the class of `L`, times `[O(L) : SO(L)]`, is `2`.
* `TauCeti.IntegralLattice.preimage_toIsometryQuotient_eq_singleton_of_index_eq_two` and
  `TauCeti.IntegralLattice.preimage_toIsometryQuotient_eq_singleton_of_finrank_eq_zero`: the class
  of `L` is the single proper class of `L` when `L` has an improper self-isometry, and in rank
  zero.

## References

* O. T. O'Meara, *Introduction to Quadratic Forms*, §102A, for classes and proper classes of
  lattices.
* J. W. S. Cassels, *Rational Quadratic Forms*, Chapter 9, §1.
-/

public section

open Module

namespace TauCeti.IntegralLattice

universe u v

variable {V : Type u} {W : Type v} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]

namespace Isometry

section IsProper

variable {L M N : IntegralLattice V}

/-- An isometry between integral lattices in the same rational space is *proper* when its ambient
linear equivalence has positive determinant, that is, preserves the orientations of `V`. -/
def IsProper (e : Isometry L M) : Prop :=
  0 < (LinearEquiv.det (e : V ≃ₗ[ℚ] V) : ℚ)

theorem isProper_iff (e : Isometry L M) :
    e.IsProper ↔ 0 < (LinearEquiv.det (e : V ≃ₗ[ℚ] V) : ℚ) :=
  Iff.rfl

/-- An isometry is improper exactly when its ambient determinant is negative. -/
theorem not_isProper_iff (e : Isometry L M) :
    ¬ e.IsProper ↔ (LinearEquiv.det (e : V ≃ₗ[ℚ] V) : ℚ) < 0 := by
  rw [isProper_iff, not_lt]
  exact (Units.ne_zero _).le_iff_lt

/-- An isometry whose ambient equivalence is the identity is proper. -/
theorem isProper_of_coe_eq_refl (e : Isometry L M)
    (h : (e : V ≃ₗ[ℚ] V) = LinearEquiv.refl ℚ V) : e.IsProper := by
  simp [isProper_iff, h]

/-- The identity isometry is proper. -/
@[simp]
theorem isProper_refl (L : IntegralLattice V) : (refl L).IsProper :=
  isProper_of_coe_eq_refl _ (LinearEquiv.ext fun x ↦ refl_apply L x)

/-- A composite of isometries is proper exactly when both factors are proper or both are
improper. -/
theorem isProper_trans_iff (e : Isometry L M) (f : Isometry M N) :
    (e.trans f).IsProper ↔ (e.IsProper ↔ f.IsProper) := by
  have h : ((e.trans f : Isometry L N) : V ≃ₗ[ℚ] V) =
      (e : V ≃ₗ[ℚ] V).trans (f : V ≃ₗ[ℚ] V) := by
    ext x
    simp
  rw [isProper_iff, h, LinearEquiv.det_trans, Units.val_mul, mul_pos_iff]
  simp only [← isProper_iff, ← not_isProper_iff]
  tauto

/-- A composite of proper isometries is proper. -/
theorem IsProper.trans {e : Isometry L M} {f : Isometry M N} (he : e.IsProper)
    (hf : f.IsProper) : (e.trans f).IsProper :=
  (isProper_trans_iff e f).mpr (iff_of_true he hf)

/-- The inverse of an isometry is proper exactly when the isometry is. -/
@[simp]
theorem isProper_symm_iff (e : Isometry L M) : e.symm.IsProper ↔ e.IsProper := by
  have h := isProper_trans_iff e e.symm
  rw [self_trans_symm] at h
  have h' := h.mp (isProper_refl L)
  exact h'.symm

/-- The inverse of a proper isometry is proper. -/
theorem IsProper.symm {e : Isometry L M} (he : e.IsProper) : e.symm.IsProper :=
  (isProper_symm_iff e).mpr he

/-- The ambient determinant of a self-isometry is its determinant on the carrier. -/
theorem coe_det_toLinearEquiv (e : Isometry L L) :
    (LinearEquiv.det (e : V ≃ₗ[ℚ] V) : ℚ) = ((det L e : ℤ) : ℚ) := by
  rw [LinearEquiv.coe_det, coe_det]
  exact LinearMap.det_eq_algebraMap_det_of_isLattice _ _ fun x ↦ (coe_carrierEquiv_apply e x).symm

/-- A self-isometry is proper exactly when it lies in `SO(L)`, that is, has determinant one. -/
theorem isProper_iff_det_eq_one (e : Isometry L L) : e.IsProper ↔ det L e = 1 := by
  rw [isProper_iff, coe_det_toLinearEquiv]
  rcases det_eq_one_or_neg_one e with h | h <;> simp [h]

/-- A self-isometry is improper exactly when it has determinant `-1`. -/
theorem det_eq_neg_one_iff_not_isProper (e : Isometry L L) : det L e = -1 ↔ ¬ e.IsProper := by
  rw [isProper_iff_det_eq_one]
  rcases det_eq_one_or_neg_one e with h | h <;> simp [h]

/-- A self-isometry is proper exactly when it lies in `SO(L)`. -/
theorem isProper_iff_mem_specialOrthogonalGroup (e : Isometry L L) :
    e.IsProper ↔ e ∈ specialOrthogonalGroup L := by
  rw [mem_specialOrthogonalGroup_iff, isProper_iff_det_eq_one]

/-- The canonical isometry to a transported lattice is proper exactly when the ambient
equivalence has positive determinant. -/
theorem isProper_transportIsometry_iff (L : IntegralLattice V) (g : V ≃ₗ[ℚ] V) :
    (L.transportIsometry g).IsProper ↔ 0 < (LinearEquiv.det g : ℚ) := by
  have h : ((L.transportIsometry g : Isometry L (L.transport g)) : V ≃ₗ[ℚ] V) = g := by
    ext x
    exact transportIsometry_apply L g x
  rw [isProper_iff, h]

end IsProper

end Isometry

section ProperIsometryQuotient

open Isometry

variable (V) in
/-- Proper isometry of integral lattices in a fixed rational space, as an equivalence relation. -/
def properIsometrySetoid : Setoid (IntegralLattice V) where
  r L M := ∃ e : Isometry L M, e.IsProper
  iseqv := ⟨fun L ↦ ⟨refl L, isProper_refl L⟩, fun ⟨e, he⟩ ↦ ⟨e.symm, he.symm⟩,
    fun ⟨e, he⟩ ⟨f, hf⟩ ↦ ⟨e.trans f, he.trans hf⟩⟩

/-- Two lattices are related by `properIsometrySetoid` exactly when they are properly
isometric. -/
theorem properIsometrySetoid_apply {L M : IntegralLattice V} :
    properIsometrySetoid V L M ↔ ∃ e : Isometry L M, e.IsProper :=
  Iff.rfl

variable (V) in
/-- The proper classes of integral lattices in a rational space `V`. -/
abbrev ProperIsometryQuotient : Type u := Quotient (properIsometrySetoid V)

/-- The proper class `cls⁺ L` of an integral lattice. -/
def properIsometryClass (L : IntegralLattice V) : ProperIsometryQuotient V :=
  Quotient.mk _ L

/-- Two lattices have the same proper class exactly when they are properly isometric. -/
@[simp]
theorem properIsometryClass_eq_properIsometryClass_iff {L M : IntegralLattice V} :
    L.properIsometryClass = M.properIsometryClass ↔ ∃ e : Isometry L M, e.IsProper :=
  Quotient.eq

/-- Properly isometric lattices have the same proper class. -/
theorem Isometry.IsProper.properIsometryClass_eq {L M : IntegralLattice V} {e : Isometry L M}
    (he : e.IsProper) : L.properIsometryClass = M.properIsometryClass :=
  properIsometryClass_eq_properIsometryClass_iff.mpr ⟨e, he⟩

/-- Every proper class is the proper class of a lattice. -/
theorem properIsometryClass_surjective :
    Function.Surjective (properIsometryClass : IntegralLattice V → ProperIsometryQuotient V) :=
  Quotient.mk_surjective

/-- The class containing a proper class. -/
def ProperIsometryQuotient.toIsometryQuotient :
    ProperIsometryQuotient V → IsometryQuotient V :=
  Quotient.lift isometryClass fun _ _ ⟨e, _⟩ ↦ e.isometryClass_eq

/-- The proper class of `L` lies in the class of `L`. -/
@[simp]
theorem ProperIsometryQuotient.toIsometryQuotient_properIsometryClass (L : IntegralLattice V) :
    L.properIsometryClass.toIsometryQuotient = L.isometryClass :=
  (rfl)

/-- Every class contains a proper class. -/
theorem ProperIsometryQuotient.toIsometryQuotient_surjective :
    Function.Surjective (toIsometryQuotient : ProperIsometryQuotient V → IsometryQuotient V) := by
  intro c
  obtain ⟨L, rfl⟩ := isometryClass_surjective c
  exact ⟨L.properIsometryClass, rfl⟩

open ProperIsometryQuotient

/-- **A class with an improper automorphism is a single proper class.** If `L` has an improper
self-isometry, so that `[O(L) : SO(L)] = 2`, then the lattices properly isometric to `L` are
exactly those isometric to `L`. -/
theorem properIsometryClass_eq_properIsometryClass_iff_of_index_eq_two {L M : IntegralLattice V}
    (h : (specialOrthogonalGroup L).index = 2) :
    L.properIsometryClass = M.properIsometryClass ↔ L.isometryClass = M.isometryClass := by
  refine ⟨fun hLM ↦ by rw [← toIsometryQuotient_properIsometryClass, hLM,
    toIsometryQuotient_properIsometryClass], fun hLM ↦ ?_⟩
  obtain ⟨e⟩ := isometryClass_eq_isometryClass_iff.mp hLM
  by_cases he : e.IsProper
  · exact he.properIsometryClass_eq
  obtain ⟨a, ha⟩ := (index_specialOrthogonalGroup_eq_two_iff L).mp h
  have ha' : ¬ a.IsProper := (det_eq_neg_one_iff_not_isProper a).mp ha
  exact ((isProper_trans_iff a e).mpr (iff_of_false ha' he)).properIsometryClass_eq

/-- When `L` has an improper self-isometry, its class is the single proper class of `L`. -/
theorem preimage_toIsometryQuotient_eq_singleton_of_index_eq_two {L : IntegralLattice V}
    (h : (specialOrthogonalGroup L).index = 2) :
    toIsometryQuotient ⁻¹' {L.isometryClass} = {L.properIsometryClass} := by
  ext c
  obtain ⟨M, rfl⟩ := properIsometryClass_surjective c
  simp only [Set.mem_preimage, toIsometryQuotient_properIsometryClass, Set.mem_singleton_iff]
  rw [eq_comm, ← properIsometryClass_eq_properIsometryClass_iff_of_index_eq_two h, eq_comm]

/-- In positive rank the proper classes in the class of `L` are the proper class of `L` and the
proper class of its transport along any orientation-reversing equivalence. -/
private theorem preimage_toIsometryQuotient_eq_pair {L : IntegralLattice V} {g : V ≃ₗ[ℚ] V}
    (hg : (LinearEquiv.det g : ℚ) < 0) :
    toIsometryQuotient ⁻¹' {L.isometryClass} =
      {L.properIsometryClass, (L.transport g).properIsometryClass} := by
  have ht : ¬ (L.transportIsometry g).IsProper := by
    rw [isProper_transportIsometry_iff, not_lt]
    exact hg.le
  ext c
  obtain ⟨M, rfl⟩ := properIsometryClass_surjective c
  simp only [Set.mem_preimage, toIsometryQuotient_properIsometryClass, Set.mem_singleton_iff,
    Set.mem_insert_iff]
  constructor
  · intro hLM
    obtain ⟨e⟩ := isometryClass_eq_isometryClass_iff.mp hLM.symm
    by_cases he : e.IsProper
    · exact Or.inl he.properIsometryClass_eq.symm
    · refine Or.inr ((isProper_trans_iff (L.transportIsometry g).symm e).mpr
        (iff_of_false ((isProper_symm_iff _).not.mpr ht) he)).properIsometryClass_eq.symm
  · rintro (h | h)
    · simpa using congrArg toIsometryQuotient h
    · simpa [(L.transportIsometry g).isometryClass_eq] using congrArg toIsometryQuotient h

/-- In positive rank, the proper class of `L` and that of its transport along an
orientation-reversing equivalence agree exactly when `L` has an improper self-isometry. -/
private theorem properIsometryClass_transport_eq_iff {L : IntegralLattice V} {g : V ≃ₗ[ℚ] V}
    (hg : (LinearEquiv.det g : ℚ) < 0) :
    L.properIsometryClass = (L.transport g).properIsometryClass ↔
      (specialOrthogonalGroup L).index = 2 := by
  have ht : ¬ (L.transportIsometry g).IsProper := by
    rw [isProper_transportIsometry_iff, not_lt]
    exact hg.le
  rw [index_specialOrthogonalGroup_eq_two_iff, properIsometryClass_eq_properIsometryClass_iff]
  constructor
  · rintro ⟨e, he⟩
    refine ⟨e.trans (L.transportIsometry g).symm, ?_⟩
    rw [det_eq_neg_one_iff_not_isProper, isProper_trans_iff, isProper_symm_iff]
    exact fun h ↦ ht (h.mp he)
  · rintro ⟨a, ha⟩
    have ha' : ¬ a.IsProper := (det_eq_neg_one_iff_not_isProper a).mp ha
    exact ⟨a.trans (L.transportIsometry g), (isProper_trans_iff _ _).mpr (iff_of_false ha' ht)⟩

/-- **The class of a lattice of positive rank splits into `2 / [O(L) : SO(L)]` proper classes.**
It is one proper class when `L` has an improper self-isometry, and two proper classes when
`O(L) = SO(L)`. -/
theorem natCard_preimage_toIsometryQuotient_mul_index (L : IntegralLattice V)
    (hV : 0 < finrank ℚ V) :
    Nat.card (toIsometryQuotient ⁻¹' {L.isometryClass}) *
      (specialOrthogonalGroup L).index = 2 := by
  rcases index_specialOrthogonalGroup_eq_one_or_two L with h | h
  · have := L.finiteDimensional
    obtain ⟨g, hg⟩ := Module.exists_det_eq_neg_one hV
    replace hg : (LinearEquiv.det g : ℚ) < 0 := by simp [hg]
    have hne : L.properIsometryClass ≠ (L.transport g).properIsometryClass := by
      rw [Ne, properIsometryClass_transport_eq_iff hg, h]
      decide
    rw [preimage_toIsometryQuotient_eq_pair hg, h, Nat.card_coe_set_eq, Set.ncard_pair hne]
  · rw [preimage_toIsometryQuotient_eq_singleton_of_index_eq_two h, h, Nat.card_unique]

/-- **In rank zero a class is a single proper class**: every isometry of the zero space is
proper. -/
theorem preimage_toIsometryQuotient_eq_singleton_of_finrank_eq_zero (L : IntegralLattice V)
    (hV : finrank ℚ V = 0) :
    toIsometryQuotient ⁻¹' {L.isometryClass} = {L.properIsometryClass} := by
  have := L.finiteDimensional
  have : Subsingleton V := Module.finrank_zero_iff.mp hV
  have hproper {M N : IntegralLattice V} (e : Isometry M N) : e.IsProper :=
    isProper_of_coe_eq_refl e (LinearEquiv.ext fun _ ↦ Subsingleton.elim _ _)
  ext c
  obtain ⟨M, rfl⟩ := properIsometryClass_surjective c
  simp only [Set.mem_preimage, toIsometryQuotient_properIsometryClass, Set.mem_singleton_iff,
    isometryClass_eq_isometryClass_iff, properIsometryClass_eq_properIsometryClass_iff]
  exact ⟨fun ⟨e⟩ ↦ ⟨e, hproper e⟩, fun ⟨e, _⟩ ↦ ⟨e⟩⟩

/-- In rank zero a class contains exactly one proper class. -/
theorem natCard_preimage_toIsometryQuotient_of_finrank_eq_zero (L : IntegralLattice V)
    (hV : finrank ℚ V = 0) :
    Nat.card (toIsometryQuotient ⁻¹' {L.isometryClass}) = 1 := by
  rw [preimage_toIsometryQuotient_eq_singleton_of_finrank_eq_zero L hV, Nat.card_unique]

/-- Each class contains finitely many proper classes. -/
theorem finite_preimage_toIsometryQuotient (c : IsometryQuotient V) :
    (toIsometryQuotient ⁻¹' {c} : Set (ProperIsometryQuotient V)).Finite := by
  obtain ⟨L, rfl⟩ := isometryClass_surjective c
  refine Set.finite_coe_iff.mp (Nat.finite_of_card_ne_zero ?_)
  rcases (finrank ℚ V).eq_zero_or_pos with hV | hV
  · rw [natCard_preimage_toIsometryQuotient_of_finrank_eq_zero L hV]
    exact one_ne_zero
  · intro h
    have := natCard_preimage_toIsometryQuotient_mul_index L hV
    rw [h, zero_mul] at this
    exact absurd this (by decide)

/-- Each class contains at most two proper classes. -/
theorem natCard_preimage_toIsometryQuotient_le_two (c : IsometryQuotient V) :
    Nat.card (toIsometryQuotient ⁻¹' {c} : Set (ProperIsometryQuotient V)) ≤ 2 := by
  obtain ⟨L, rfl⟩ := isometryClass_surjective c
  rcases (finrank ℚ V).eq_zero_or_pos with hV | hV
  · rw [natCard_preimage_toIsometryQuotient_of_finrank_eq_zero L hV]
    exact one_le_two
  · have h := natCard_preimage_toIsometryQuotient_mul_index L hV
    have h₀ := (inferInstance : (specialOrthogonalGroup L).FiniteIndex).index_ne_zero
    calc _ ≤ Nat.card (toIsometryQuotient ⁻¹' {L.isometryClass}) *
          (specialOrthogonalGroup L).index := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h₀)
      _ = 2 := h

/-- Conjugating an isometry of lattices in `V` by the transport isometries along `f : V ≃ W`
gives an isometry of the transported lattices in `W`, which is proper exactly when the original
one is: conjugation does not change the determinant of an ambient equivalence. -/
theorem isProper_transportIsometry_symm_trans_trans_iff (f : V ≃ₗ[ℚ] W)
    {M N : IntegralLattice V} (e : Isometry M N) :
    (((M.transportIsometry f).symm.trans e).trans (N.transportIsometry f)).IsProper ↔
      e.IsProper := by
  have h : ((((M.transportIsometry f).symm.trans e).trans (N.transportIsometry f) :
      Isometry (M.transport f) (N.transport f)) : W ≃ₗ[ℚ] W) =
      (f.symm.trans (e : V ≃ₗ[ℚ] V)).trans f := by
    ext x
    simp
  rw [isProper_iff, isProper_iff, h, LinearEquiv.det_conj]

/-- Transport along a rational linear equivalence `V ≃ W` identifies the proper classes of
integral lattices in `V` with those in `W`. -/
noncomputable def properIsometryQuotientEquiv (f : V ≃ₗ[ℚ] W) :
    ProperIsometryQuotient V ≃ ProperIsometryQuotient W where
  toFun := Quotient.map (·.transport f) fun _ _ ⟨e, he⟩ ↦
    ⟨_, (isProper_transportIsometry_symm_trans_trans_iff f e).mpr he⟩
  invFun := Quotient.map (·.transport f.symm) fun _ _ ⟨e, he⟩ ↦
    ⟨_, (isProper_transportIsometry_symm_trans_trans_iff f.symm e).mpr he⟩
  left_inv c := by
    obtain ⟨M, rfl⟩ := properIsometryClass_surjective c
    refine (isProper_of_coe_eq_refl
      ((M.transportIsometry f).trans ((M.transport f).transportIsometry f.symm))
      ?_).properIsometryClass_eq.symm
    ext x
    simp
  right_inv c := by
    obtain ⟨M, rfl⟩ := properIsometryClass_surjective c
    refine (isProper_of_coe_eq_refl
      ((M.transportIsometry f.symm).trans ((M.transport f.symm).transportIsometry f))
      ?_).properIsometryClass_eq.symm
    ext x
    simp

/-- `properIsometryQuotientEquiv f` sends the proper class of `M` to the proper class of its
transport along `f`. -/
@[simp]
theorem properIsometryQuotientEquiv_properIsometryClass (f : V ≃ₗ[ℚ] W) (M : IntegralLattice V) :
    properIsometryQuotientEquiv f M.properIsometryClass = (M.transport f).properIsometryClass :=
  (rfl)

/-- The inverse of `properIsometryQuotientEquiv f` sends the proper class of `M` to the proper
class of its transport along `f.symm`. -/
@[simp]
theorem properIsometryQuotientEquiv_symm_properIsometryClass (f : V ≃ₗ[ℚ] W)
    (M : IntegralLattice W) :
    (properIsometryQuotientEquiv f).symm M.properIsometryClass =
      (M.transport f.symm).properIsometryClass :=
  (rfl)

/-- Transport of proper classes covers transport of classes. -/
theorem toIsometryQuotient_properIsometryQuotientEquiv (f : V ≃ₗ[ℚ] W)
    (c : ProperIsometryQuotient V) :
    (properIsometryQuotientEquiv f c).toIsometryQuotient =
      isometryQuotientEquiv f c.toIsometryQuotient := by
  obtain ⟨M, rfl⟩ := properIsometryClass_surjective c
  simp

end ProperIsometryQuotient

end TauCeti.IntegralLattice
