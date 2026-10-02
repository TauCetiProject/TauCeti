/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.InformationTheory.Coding.DirectSum

/-!
# Direct sums of additive codes

An additive code is an additive subgroup of a word space. Its direct sum with another code lives
on the disjoint union of the coordinate types: membership is determined by the two restrictions.
The direct sum is additively equivalent to the product of the codes, so their cardinalities
multiply. This supplies the disjoint-coordinate construction used in additive-code distance
calculations.

The alphabet is an arbitrary commutative additive group, with no finiteness or field assumption.
The construction uses Mathlib's identification of additive subgroups with integer submodules to
reuse the module-alphabet direct sum.

The conventions follow Huffman and Pless, *Fundamentals of Error-Correcting Codes*, §1.6.
-/

public section

namespace TauCeti

open AddSubgroup

variable {A ι κ : Type*} [AddCommGroup A]

/-- The direct sum of additive codes on the disjoint union of their coordinate types. -/
def _root_.AddSubgroup.directSum (C : AddSubgroup (ι → A)) (D : AddSubgroup (κ → A)) :
    AddSubgroup (ι ⊕ κ → A) :=
  (C.toIntSubmodule.directSum D.toIntSubmodule).toAddSubgroup

/-- An additive direct sum is the underlying subgroup of the integer-module direct sum. -/
theorem _root_.AddSubgroup.directSum_def (C : AddSubgroup (ι → A))
    (D : AddSubgroup (κ → A)) :
    C.directSum D = (C.toIntSubmodule.directSum D.toIntSubmodule).toAddSubgroup := (rfl)

/-- Passing to integer submodules commutes with the direct sum of additive codes. -/
@[simp]
theorem _root_.AddSubgroup.toIntSubmodule_directSum (C : AddSubgroup (ι → A))
    (D : AddSubgroup (κ → A)) :
    (C.directSum D).toIntSubmodule = C.toIntSubmodule.directSum D.toIntSubmodule := by
  rw [directSum_def, Submodule.toAddSubgroup_toIntSubmodule]

/-- A word belongs to an additive direct sum exactly when its restrictions belong to the two
constituent codes. -/
@[simp]
theorem _root_.AddSubgroup.mem_directSum_iff {C : AddSubgroup (ι → A)}
    {D : AddSubgroup (κ → A)} {x : ι ⊕ κ → A} :
    x ∈ C.directSum D ↔ (fun i ↦ x (.inl i)) ∈ C ∧ (fun j ↦ x (.inr j)) ∈ D := by
  rw [directSum_def, Submodule.mem_toAddSubgroup, Submodule.mem_directSum_iff]
  simp only [← SetLike.mem_coe, AddSubgroup.coe_toIntSubmodule]

/-- A word from the first code extended by zero belongs to the direct sum. -/
theorem _root_.AddSubgroup.sumElim_zero_right_mem_directSum {C : AddSubgroup (ι → A)}
    (D : AddSubgroup (κ → A)) {x : ι → A} (hx : x ∈ C) :
    Sum.elim x (0 : κ → A) ∈ C.directSum D :=
  mem_directSum_iff.mpr ⟨hx, D.zero_mem⟩

/-- A word from the second code extended by zero belongs to the direct sum. -/
theorem _root_.AddSubgroup.sumElim_zero_left_mem_directSum (C : AddSubgroup (ι → A))
    {D : AddSubgroup (κ → A)} {y : κ → A} (hy : y ∈ D) :
    Sum.elim (0 : ι → A) y ∈ C.directSum D :=
  mem_directSum_iff.mpr ⟨C.zero_mem, hy⟩

/-- An additive direct sum is additively equivalent to the product of its constituent codes. -/
def _root_.AddSubgroup.directSumEquivProd (C : AddSubgroup (ι → A))
    (D : AddSubgroup (κ → A)) : C.directSum D ≃+ C × D :=
  (Submodule.directSumEquivProd C.toIntSubmodule D.toIntSubmodule).toAddEquiv

@[simp]
theorem _root_.AddSubgroup.directSumEquivProd_apply_fst (C : AddSubgroup (ι → A))
    (D : AddSubgroup (κ → A)) (x : C.directSum D) (i : ι) :
    (C.directSumEquivProd D x).1.1 i = x.1 (.inl i) :=
  Submodule.directSumEquivProd_apply_fst _ _ _ _

@[simp]
theorem _root_.AddSubgroup.directSumEquivProd_apply_snd (C : AddSubgroup (ι → A))
    (D : AddSubgroup (κ → A)) (x : C.directSum D) (j : κ) :
    (C.directSumEquivProd D x).2.1 j = x.1 (.inr j) :=
  Submodule.directSumEquivProd_apply_snd _ _ _ _

@[simp]
theorem _root_.AddSubgroup.directSumEquivProd_symm_apply_inl (C : AddSubgroup (ι → A))
    (D : AddSubgroup (κ → A)) (x : C) (y : D) (i : ι) :
    ((C.directSumEquivProd D).symm (x, y)).1 (.inl i) = x.1 i :=
  Submodule.directSumEquivProd_symm_apply_inl _ _ _ _ _

@[simp]
theorem _root_.AddSubgroup.directSumEquivProd_symm_apply_inr (C : AddSubgroup (ι → A))
    (D : AddSubgroup (κ → A)) (x : C) (y : D) (j : κ) :
    ((C.directSumEquivProd D).symm (x, y)).1 (.inr j) = y.1 j :=
  Submodule.directSumEquivProd_symm_apply_inr _ _ _ _ _

/-- The cardinality of an additive direct sum is the product of the two code cardinalities. -/
@[simp↓]
theorem _root_.AddSubgroup.natCard_directSum (C : AddSubgroup (ι → A))
    (D : AddSubgroup (κ → A)) : Nat.card (C.directSum D) = Nat.card C * Nat.card D := by
  rw [Nat.card_congr (C.directSumEquivProd D).toEquiv, Nat.card_prod]

/-- Inclusion of additive direct sums is equivalent to inclusion in each summand. -/
@[simp]
theorem _root_.AddSubgroup.directSum_le_directSum_iff {C C' : AddSubgroup (ι → A)}
    {D D' : AddSubgroup (κ → A)} :
    C.directSum D ≤ C'.directSum D' ↔ C ≤ C' ∧ D ≤ D' := by
  rw [← AddSubgroup.toIntSubmodule.le_iff_le, toIntSubmodule_directSum,
    toIntSubmodule_directSum, Submodule.directSum_le_directSum_iff]
  rfl

/-- The direct sum of two zero codes is zero. -/
@[simp]
theorem _root_.AddSubgroup.bot_directSum_bot :
    (⊥ : AddSubgroup (ι → A)).directSum (⊥ : AddSubgroup (κ → A)) = ⊥ := by
  ext x
  simp only [mem_directSum_iff, AddSubgroup.mem_bot, funext_iff, Pi.zero_apply]
  exact ⟨fun h i ↦ Sum.rec h.1 h.2 i, fun h ↦ ⟨fun i ↦ h (.inl i), fun j ↦ h (.inr j)⟩⟩

/-- Forgetting scalar closure commutes with the direct sum of linear codes. -/
@[simp]
theorem _root_.Submodule.toAddSubgroup_directSum {R : Type*} [Ring R] [Module R A]
    (C : Submodule R (ι → A)) (D : Submodule R (κ → A)) :
    (C.directSum D).toAddSubgroup = C.toAddSubgroup.directSum D.toAddSubgroup := by
  ext x
  simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_directSum_iff,
    Submodule.mem_directSum_iff]

end TauCeti
