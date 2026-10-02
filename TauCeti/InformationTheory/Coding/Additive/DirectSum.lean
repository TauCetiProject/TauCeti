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

Hamming weight and distance split as sums over the two coordinate blocks. Canonical reindexings
by the commutativity and associativity equivalences for `Sum` give the corresponding code
identities, using Mathlib's `AddEquiv.arrowCongr`.

The alphabet is an arbitrary additive group, with no finiteness or field assumption.
The construction transports Mathlib's `AddSubgroup.prod` along `Equiv.sumArrowEquivProdArrow`,
and its product equivalence uses `AddSubgroup.prodEquiv`. For commutative
alphabets, the construction agrees with the direct sum of the corresponding integer submodules.

The conventions follow Huffman and Pless, *Fundamentals of Error-Correcting Codes*, §1.6.
-/

public section

namespace TauCeti

open AddSubgroup

variable {A ι κ ν : Type*}

section AddGroup

variable [AddGroup A]

/-- The direct sum of additive codes on the disjoint union of their coordinate types. -/
def _root_.AddSubgroup.directSum (C : AddSubgroup (ι → A)) (D : AddSubgroup (κ → A)) :
    AddSubgroup (ι ⊕ κ → A) :=
  let e : (ι ⊕ κ → A) ≃+ (ι → A) × (κ → A) :=
    { Equiv.sumArrowEquivProdArrow ι κ A with map_add' := fun _ _ ↦ rfl }
  (C.prod D).comap e.toAddMonoidHom

/-- A word belongs to an additive direct sum exactly when its restrictions belong to the two
constituent codes. -/
@[simp]
theorem _root_.AddSubgroup.mem_directSum_iff {C : AddSubgroup (ι → A)}
    {D : AddSubgroup (κ → A)} {x : ι ⊕ κ → A} :
    x ∈ C.directSum D ↔ (fun i ↦ x (.inl i)) ∈ C ∧ (fun j ↦ x (.inr j)) ∈ D := (Iff.rfl)

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
  ({ (Equiv.sumArrowEquivProdArrow ι κ A).subtypeEquiv
      (fun _ ↦ mem_directSum_iff) with map_add' := fun _ _ ↦ rfl } :
      C.directSum D ≃+ C.prod D).trans (C.prodEquiv D)

private theorem directSumEquivProd_apply_eq (C : AddSubgroup (ι → A))
    (D : AddSubgroup (κ → A)) (x : C.directSum D) :
    C.directSumEquivProd D x =
      (⟨fun i ↦ x.1 (.inl i), (mem_directSum_iff.mp x.2).1⟩,
        ⟨fun j ↦ x.1 (.inr j), (mem_directSum_iff.mp x.2).2⟩) := by
  simp only [directSumEquivProd, AddSubgroup.prodEquiv, Equiv.Set.prod,
    Equiv.sumArrowEquivProdArrow]
  rfl

@[simp]
theorem _root_.AddSubgroup.directSumEquivProd_apply_fst (C : AddSubgroup (ι → A))
    (D : AddSubgroup (κ → A)) (x : C.directSum D) (i : ι) :
    (C.directSumEquivProd D x).1.1 i = x.1 (.inl i) := by
  exact congrArg (fun y : C × D ↦ y.1.1 i) (directSumEquivProd_apply_eq C D x)

@[simp]
theorem _root_.AddSubgroup.directSumEquivProd_apply_snd (C : AddSubgroup (ι → A))
    (D : AddSubgroup (κ → A)) (x : C.directSum D) (j : κ) :
    (C.directSumEquivProd D x).2.1 j = x.1 (.inr j) := by
  exact congrArg (fun y : C × D ↦ y.2.1 j) (directSumEquivProd_apply_eq C D x)

@[simp]
theorem _root_.AddSubgroup.directSumEquivProd_symm_apply_inl (C : AddSubgroup (ι → A))
    (D : AddSubgroup (κ → A)) (x : C) (y : D) (i : ι) :
    ((C.directSumEquivProd D).symm (x, y)).1 (.inl i) = x.1 i := by
  have h := directSumEquivProd_apply_eq C D ((C.directSumEquivProd D).symm (x, y))
  rw [AddEquiv.apply_symm_apply] at h
  exact (congrArg (fun z : C × D ↦ z.1.1 i) h).symm

@[simp]
theorem _root_.AddSubgroup.directSumEquivProd_symm_apply_inr (C : AddSubgroup (ι → A))
    (D : AddSubgroup (κ → A)) (x : C) (y : D) (j : κ) :
    ((C.directSumEquivProd D).symm (x, y)).1 (.inr j) = y.1 j := by
  have h := directSumEquivProd_apply_eq C D ((C.directSumEquivProd D).symm (x, y))
  rw [AddEquiv.apply_symm_apply] at h
  exact (congrArg (fun z : C × D ↦ z.2.1 j) h).symm

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
  constructor
  · intro h
    exact ⟨fun x hx ↦ (mem_directSum_iff.mp (h (sumElim_zero_right_mem_directSum D hx))).1,
      fun y hy ↦ (mem_directSum_iff.mp (h (sumElim_zero_left_mem_directSum C hy))).2⟩
  · rintro ⟨hC, hD⟩ x hx
    exact mem_directSum_iff.mpr ⟨hC (mem_directSum_iff.mp hx).1, hD (mem_directSum_iff.mp hx).2⟩

/-- Direct sum is monotone in both constituent additive codes. -/
@[gcongr]
theorem _root_.AddSubgroup.directSum_mono {C C' : AddSubgroup (ι → A)}
    {D D' : AddSubgroup (κ → A)} (hC : C ≤ C') (hD : D ≤ D') :
    C.directSum D ≤ C'.directSum D' :=
  directSum_le_directSum_iff.mpr ⟨hC, hD⟩

/-- Two additive direct sums are equal exactly when their constituent codes are equal. -/
@[simp]
theorem _root_.AddSubgroup.directSum_inj {C C' : AddSubgroup (ι → A)}
    {D D' : AddSubgroup (κ → A)} :
    C.directSum D = C'.directSum D' ↔ C = C' ∧ D = D' := by
  simp only [le_antisymm_iff, directSum_le_directSum_iff]
  tauto

/-- Reindexing an additive direct sum by swapping the coordinate summands swaps the two codes. -/
@[simp↓]
theorem _root_.AddSubgroup.map_directSum_sumComm (C : AddSubgroup (ι → A))
    (D : AddSubgroup (κ → A)) :
    (C.directSum D).map
        (AddEquiv.arrowCongr (Equiv.sumComm ι κ) (AddEquiv.refl A)).toAddMonoidHom =
      D.directSum C := by
  ext x
  rw [mem_map_equiv, mem_directSum_iff, mem_directSum_iff]
  exact and_comm

/-- Reindexing an iterated additive direct sum by associating its coordinate summands associates
the three codes in the same way. -/
@[simp↓]
theorem _root_.AddSubgroup.map_directSum_sumAssoc (C : AddSubgroup (ι → A))
    (D : AddSubgroup (κ → A)) (E : AddSubgroup (ν → A)) :
    ((C.directSum D).directSum E).map
        (AddEquiv.arrowCongr (Equiv.sumAssoc ι κ ν) (AddEquiv.refl A)).toAddMonoidHom =
      C.directSum (D.directSum E) := by
  ext x
  simp only [mem_map_equiv, mem_directSum_iff]
  exact and_assoc

/-- The direct sum of two zero codes is zero. -/
@[simp]
theorem _root_.AddSubgroup.bot_directSum_bot :
    (⊥ : AddSubgroup (ι → A)).directSum (⊥ : AddSubgroup (κ → A)) = ⊥ := by
  ext x
  simp only [mem_directSum_iff, AddSubgroup.mem_bot, funext_iff, Pi.zero_apply]
  exact ⟨fun h i ↦ Sum.rec h.1 h.2 i, fun h ↦ ⟨fun i ↦ h (.inl i), fun j ↦ h (.inr j)⟩⟩

section Hamming

variable [DecidableEq A] [Fintype ι] [Fintype κ]

/-- Hamming weight is additive on words in an additive direct sum. -/
@[simp]
theorem _root_.AddSubgroup.hammingNorm_directSumEquivProd_symm (C : AddSubgroup (ι → A))
    (D : AddSubgroup (κ → A)) (x : C) (y : D) :
    hammingNorm ((C.directSumEquivProd D).symm (x, y) : ι ⊕ κ → A) =
      hammingNorm x.1 + hammingNorm y.1 := by
  rw [← hammingNorm_sumElim x.1 y.1]
  apply congrArg hammingNorm
  funext i
  cases i <;> simp

/-- Hamming distance is additive on pairs of words in an additive direct sum. -/
@[simp]
theorem _root_.AddSubgroup.hammingDist_directSumEquivProd_symm (C : AddSubgroup (ι → A))
    (D : AddSubgroup (κ → A)) (x x' : C) (y y' : D) :
    hammingDist ((C.directSumEquivProd D).symm (x, y) : ι ⊕ κ → A)
        ((C.directSumEquivProd D).symm (x', y') : ι ⊕ κ → A) =
      hammingDist x.1 x'.1 + hammingDist y.1 y'.1 := by
  rw [← hammingDist_sumElim x.1 x'.1 y.1 y'.1]
  apply congrArg₂ hammingDist
  · funext i
    cases i <;> simp
  · funext i
    cases i <;> simp

end Hamming

end AddGroup

section AddCommGroup

variable [AddCommGroup A]

/-- An additive direct sum is the underlying subgroup of the integer-module direct sum. -/
theorem _root_.AddSubgroup.directSum_def (C : AddSubgroup (ι → A))
    (D : AddSubgroup (κ → A)) :
    C.directSum D = (C.toIntSubmodule.directSum D.toIntSubmodule).toAddSubgroup := by
  ext x
  rw [mem_directSum_iff, Submodule.mem_toAddSubgroup, Submodule.mem_directSum_iff]
  simp only [← SetLike.mem_coe, AddSubgroup.coe_toIntSubmodule]

/-- Passing to integer submodules commutes with the direct sum of additive codes. -/
@[simp]
theorem _root_.AddSubgroup.toIntSubmodule_directSum (C : AddSubgroup (ι → A))
    (D : AddSubgroup (κ → A)) :
    (C.directSum D).toIntSubmodule = C.toIntSubmodule.directSum D.toIntSubmodule := by
  rw [directSum_def, Submodule.toAddSubgroup_toIntSubmodule]

/-- Forgetting scalar closure commutes with the direct sum of linear codes. -/
@[simp]
theorem _root_.Submodule.toAddSubgroup_directSum {R : Type*} [Ring R] [Module R A]
    (C : Submodule R (ι → A)) (D : Submodule R (κ → A)) :
    (C.directSum D).toAddSubgroup = C.toAddSubgroup.directSum D.toAddSubgroup := by
  ext x
  simp only [Submodule.mem_toAddSubgroup, AddSubgroup.mem_directSum_iff,
    Submodule.mem_directSum_iff]

end AddCommGroup

end TauCeti
