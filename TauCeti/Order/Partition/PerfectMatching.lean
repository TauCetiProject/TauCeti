/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Enumerative.PerfectMatching
public import TauCeti.Order.Partition.Finpartition
public import TauCeti.Order.Partition.Pairing

/-!
# Perfect matchings and pair partitions

A fixed-point-free involution and a partition into two-element blocks encode the same
matching. `TauCeti.PerfectMatching.pairingEquiv` converts between these encodings on any
finite type. Its forward map is the orbit partition, with block `{a, D.val a}` at `a`;
its inverse sends a point to the unique other point of its block.

The conversion and its characteristic block formulas require no order on the underlying
finite type. Noncrossing compatibility is developed in
`TauCeti/Combinatorics/NoncrossingPartition/PerfectMatching.lean`.
-/

public section

open Finset

namespace Finpartition

variable {α : Type*} [DecidableEq α] {s : Finset α} {P : Finpartition s}

/-- In a pair partition, each point has a unique distinct partner in its block. -/
theorem IsPairing.existsUnique_mem_part_ne (hP : P.IsPairing) {a : α} (ha : a ∈ s) :
    ∃! b, b ∈ P.part a ∧ b ≠ a := by
  obtain ⟨x, y, hxy, hpart⟩ := card_eq_two.mp (isPairing_iff.mp hP _ (P.part_mem.mpr ha))
  have ha' := P.mem_part ha
  rw [hpart] at ha' ⊢
  rcases (by simpa only [mem_insert, mem_singleton] using ha' : a = x ∨ a = y) with rfl | rfl
  · exact ⟨y, by simp [hxy.symm], by simp_all⟩
  · exact ⟨x, by simp [hxy], by simp_all⟩

variable [Fintype α] {P : Finpartition (univ : Finset α)}

/-- The perfect matching associated to a pair partition sends each point to the other
point of its block. The unique-partner search is computable. -/
@[expose]
def IsPairing.toPerfectMatching (hP : P.IsPairing) : TauCeti.PerfectMatching α := by
  let f (a : α) := (P.part a).choose (· ≠ a) (hP.existsUnique_mem_part_ne (mem_univ a))
  have hf (a : α) : f a ∈ P.part a ∧ f a ≠ a :=
    choose_spec _ _ _
  have hinv : Function.Involutive f := by
    intro a
    have hpart : P.part (f a) = P.part a :=
      (P.mem_part_iff_part_eq_part (mem_univ _) (mem_univ _)).mp (hf a).1
    exact (hP.existsUnique_mem_part_ne (mem_univ (f a))).unique
      (hf (f a)) ⟨hpart ▸ P.mem_part (mem_univ a), (hf a).2.symm⟩
  exact ⟨Function.Involutive.toPerm f hinv,
    TauCeti.isPerfectMatching_iff.mpr ⟨hinv, fun a => (hf a).2⟩⟩

/-- The partner determined by a pair partition is characterized by distinct membership
in the same block. -/
@[simp]
theorem IsPairing.toPerfectMatching_apply_eq_iff (hP : P.IsPairing) (a b : α) :
    hP.toPerfectMatching.val a = b ↔ b ∈ P.part a ∧ b ≠ a := by
  exact choose_eq_iff (· ≠ a) (P.part a) _

/-- The block through a point consists of that point and its partner. -/
theorem IsPairing.part_eq_pair (hP : P.IsPairing) (a : α) :
    P.part a = {a, hP.toPerfectMatching.val a} := by
  ext b
  have hf := (hP.toPerfectMatching_apply_eq_iff a _).mp rfl
  by_cases hba : b = a
  · simp [hba]
  · simp only [mem_insert, mem_singleton]
    exact ⟨fun hb => Or.inr ((hP.toPerfectMatching_apply_eq_iff a b).mpr ⟨hb, hba⟩).symm,
      fun hb => hb.elim (fun h => (hba h).elim) (fun h => h ▸ hf.1)⟩

end Finpartition

namespace TauCeti.PerfectMatching

section Finite

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The partition into the two-element orbits of a perfect matching. -/
@[expose]
def toFinpartition (D : PerfectMatching α) : Finpartition (univ : Finset α) :=
  letI : DecidableRel (Equiv.Perm.SameCycle.setoid D.val) :=
    inferInstanceAs (DecidableRel D.val.SameCycle)
  Finpartition.ofSetoid (Equiv.Perm.SameCycle.setoid D.val)

/-- Two points are in the same block precisely when they are equal or matched. -/
theorem mem_part_toFinpartition (D : PerfectMatching α) (a b : α) :
    b ∈ D.toFinpartition.part a ↔ a = b ∨ a = D.val b := by
  simp only [toFinpartition, Finpartition.mem_part_ofSetoid_iff_rel]
  exact D.prop.involutive.sameCycle_iff a b

/-- The block through `a` is the pair consisting of `a` and its partner. -/
@[simp]
theorem part_toFinpartition (D : PerfectMatching α) (a : α) :
    D.toFinpartition.part a = {a, D.val a} := by
  ext b
  rw [mem_part_toFinpartition]
  simp only [mem_insert, mem_singleton]
  constructor <;> rintro (h | h)
  · exact Or.inl h.symm
  · exact Or.inr ((D.apply_eq_comm).mpr h.symm).symm
  · exact Or.inl h.symm
  · exact Or.inr ((D.apply_eq_comm).mp h.symm).symm

/-- Every block of the orbit partition of a perfect matching has two elements. -/
theorem isPairing_toFinpartition (D : PerfectMatching α) : D.toFinpartition.IsPairing := by
  rw [Finpartition.isPairing_iff_part]
  intro a _
  simp [Ne.symm (D.apply_ne a)]

/-- Reconstructing the partners of the orbit partition recovers the matching. -/
@[simp]
theorem toPerfectMatching_toFinpartition (D : PerfectMatching α) :
    D.isPairing_toFinpartition.toPerfectMatching = D := by
  apply Subtype.ext
  apply Equiv.ext
  intro a
  exact (D.isPairing_toFinpartition.toPerfectMatching_apply_eq_iff a _).mpr
    ⟨by simp, D.apply_ne a⟩

/-- Taking the orbit partition of the matching of a pair partition recovers the partition. -/
@[simp]
theorem _root_.Finpartition.IsPairing.toFinpartition_toPerfectMatching
    {P : Finpartition (univ : Finset α)} (hP : P.IsPairing) :
    hP.toPerfectMatching.toFinpartition = P := by
  apply Finpartition.ext_of_part
  intro a _
  rw [part_toFinpartition, hP.part_eq_pair]

/-- Perfect matchings are equivalent to partitions into pairs, with no ordering required
on the finite underlying type. -/
@[expose]
def pairingEquiv : PerfectMatching α ≃ {P : Finpartition (univ : Finset α) // P.IsPairing} where
  toFun D := ⟨D.toFinpartition, D.isPairing_toFinpartition⟩
  invFun P := P.2.toPerfectMatching
  left_inv := toPerfectMatching_toFinpartition
  right_inv P := Subtype.ext P.2.toFinpartition_toPerfectMatching

/-- The forward conversion of the equivalence is the orbit partition. -/
@[simp]
theorem pairingEquiv_apply_coe (D : PerfectMatching α) :
    (pairingEquiv D).val = D.toFinpartition := rfl

/-- The inverse conversion sends each point to its distinct block partner. -/
@[simp]
theorem pairingEquiv_symm_apply_val (P : {P : Finpartition (univ : Finset α) // P.IsPairing}) :
    (pairingEquiv.symm P).val = P.2.toPerfectMatching.val := rfl

end Finite

end TauCeti.PerfectMatching
