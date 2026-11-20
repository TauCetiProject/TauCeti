/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.FinThree.Basic
public import Mathlib.Data.SetLike.Fintype

/-!
# The subgroup lattice of the symmetric group on three points

The six subgroups of `S₃` are the trivial subgroup, the three point stabilizers,
the alternating subgroup, and the whole group. This enumeration allows sums over
subgroups, such as the integral coefficients in Artin induction, to be evaluated explicitly.
It also identifies the complements of the alternating subgroup: they are the three point
stabilizers, so `A₃` has exactly three complements in `S₃`, one for each point.
-/

public section

namespace Subgroup

/-- Every subgroup of `S₃` is trivial, a point stabilizer, alternating, or the whole group. -/
theorem fin_three_cases (H : Subgroup (Equiv.Perm (Fin 3))) :
    H = ⊥ ∨ H = MulAction.stabilizer (Equiv.Perm (Fin 3)) (0 : Fin 3) ∨
      H = MulAction.stabilizer (Equiv.Perm (Fin 3)) (1 : Fin 3) ∨
      H = MulAction.stabilizer (Equiv.Perm (Fin 3)) (2 : Fin 3) ∨
      H = alternatingGroup (Fin 3) ∨ H = ⊤ := by
  have key : ∀ s : Finset (Equiv.Perm (Fin 3)), 1 ∈ s ∧ (∀ a ∈ s, ∀ b ∈ s, a * b ∈ s) →
      s ∈ ({ {1}, {1, Equiv.swap 1 2}, {1, Equiv.swap 2 0},
        {1, Equiv.swap 0 1}, {1, finRotate 3, (finRotate 3)⁻¹}, Finset.univ } :
          Finset (Finset (Equiv.Perm (Fin 3)))) := by decide
  have halt : (alternatingGroup (Fin 3) : Set (Equiv.Perm (Fin 3))) =
      {1, finRotate 3, (finRotate 3)⁻¹} := by
    ext g
    simp only [SetLike.mem_coe, Equiv.Perm.mem_alternatingGroup, Set.mem_insert_iff,
      Set.mem_singleton_iff]
    revert g
    decide
  classical
  have h := key (H : Set (Equiv.Perm (Fin 3))).toFinset
    ⟨by simp, by simpa using fun a ha b hb ↦ H.mul_mem ha hb⟩
  have h0 := TauCeti.coe_stabilizer_perm_fin_three 0
  have h1 := TauCeti.coe_stabilizer_perm_fin_three 1
  have h2 := TauCeti.coe_stabilizer_perm_fin_three 2
  norm_num at h0 h1 h2
  simpa only [Finset.mem_insert, Finset.mem_singleton, ← Finset.coe_inj,
    Set.coe_toFinset, Finset.coe_singleton,
    Finset.coe_insert, Finset.coe_univ, ← coe_bot, ← coe_top,
    ← h0, ← h1, ← h2, ← halt, SetLike.coe_set_eq] using h

/-- A sum over the subgroups of `S₃` has exactly six terms. -/
theorem finsum_fin_three {A : Type*} [AddCommMonoid A]
    (f : Subgroup (Equiv.Perm (Fin 3)) → A) :
    ∑ᶠ H, f H = f ⊥ + f (MulAction.stabilizer (Equiv.Perm (Fin 3)) (0 : Fin 3)) +
      f (MulAction.stabilizer (Equiv.Perm (Fin 3)) (1 : Fin 3)) +
      f (MulAction.stabilizer (Equiv.Perm (Fin 3)) (2 : Fin 3)) +
      f (alternatingGroup (Fin 3)) + f ⊤ := by
  classical
  have hg : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  have hne : ∀ a : Fin 3,
      MulAction.stabilizer (Equiv.Perm (Fin 3)) a ≠ ⊥ ∧
      MulAction.stabilizer (Equiv.Perm (Fin 3)) a ≠ ⊤ ∧
      MulAction.stabilizer (Equiv.Perm (Fin 3)) a ≠ alternatingGroup (Fin 3) := by
    intro a
    have hs := TauCeti.card_stabilizer_perm_fin_three a
    have ha := TauCeti.card_alternatingGroup_fin_three
    refine ⟨?_, ?_, ?_⟩ <;> intro h <;>
      have _ := congrArg (fun H : Subgroup (Equiv.Perm (Fin 3)) ↦ Nat.card H) h <;>
      simp_all only [card_bot, card_top] <;> omega
  have hstab := TauCeti.stabilizer_perm_fin_three_injective
  have hAlt : alternatingGroup (Fin 3) ≠ ⊥ ∧ alternatingGroup (Fin 3) ≠ ⊤ := by
    have ha := TauCeti.card_alternatingGroup_fin_three
    constructor <;> intro h <;>
      have _ := congrArg (fun H : Subgroup (Equiv.Perm (Fin 3)) ↦ Nat.card H) h <;>
      simp_all only [card_bot, card_top] <;> omega
  have huniv : (Finset.univ : Finset (Subgroup (Equiv.Perm (Fin 3)))) =
      {⊥, MulAction.stabilizer (Equiv.Perm (Fin 3)) (0 : Fin 3),
        MulAction.stabilizer (Equiv.Perm (Fin 3)) (1 : Fin 3),
        MulAction.stabilizer (Equiv.Perm (Fin 3)) (2 : Fin 3), alternatingGroup (Fin 3), ⊤} := by
    ext H
    simpa using fin_three_cases H
  rw [finsum_eq_sum_of_fintype, huniv]
  simp_all [Finset.sum_insert, hstab.eq_iff, ne_comm, add_assoc]

end Subgroup

namespace TauCeti

/-- **The complements of `A₃` in `S₃` are the three point stabilizers**, the subgroups of order
two. -/
theorem isComplement'_alternatingGroup_fin_three_iff (D : Subgroup (Equiv.Perm (Fin 3))) :
    (alternatingGroup (Fin 3)).IsComplement' D ↔
      ∃ a : Fin 3, MulAction.stabilizer (Equiv.Perm (Fin 3)) a = D := by
  refine ⟨fun h ↦ ?_, fun ⟨a, ha⟩ ↦ ha ▸ isComplement'_alternatingGroup_stabilizer_perm_fin_three a⟩
  have hcard := h.card_mul_card
  have hg : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
    norm_num [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]
  rw [card_alternatingGroup_fin_three, hg] at hcard
  rcases Subgroup.fin_three_cases D with rfl | rfl | rfl | rfl | rfl | rfl
  · simp at hcard
  · exact ⟨0, rfl⟩
  · exact ⟨1, rfl⟩
  · exact ⟨2, rfl⟩
  · rw [card_alternatingGroup_fin_three] at hcard
    omega
  · rw [Subgroup.card_top, hg] at hcard
    omega

/-- **The complements of `A₃` in `S₃`, indexed by the points**: the point `a` corresponds to its
stabilizer, the subgroup generated by the transposition of the two other points. -/
noncomputable def alternatingGroupFinThreeComplementEquiv :
    Fin 3 ≃ {D : Subgroup (Equiv.Perm (Fin 3)) // (alternatingGroup (Fin 3)).IsComplement' D} :=
  Equiv.ofBijective
    (fun a ↦ ⟨MulAction.stabilizer (Equiv.Perm (Fin 3)) a,
      isComplement'_alternatingGroup_stabilizer_perm_fin_three a⟩)
    ⟨fun _ _ hab ↦ stabilizer_perm_fin_three_injective (congrArg Subtype.val hab),
      fun D ↦ ((isComplement'_alternatingGroup_fin_three_iff D.val).mp D.property).imp
        fun _ ha ↦ Subtype.ext ha⟩

/-- The complement of `A₃` indexed by the point `a` is the stabilizer of `a`. -/
@[simp]
theorem coe_alternatingGroupFinThreeComplementEquiv_apply (a : Fin 3) :
    (alternatingGroupFinThreeComplementEquiv a : Subgroup (Equiv.Perm (Fin 3))) =
      MulAction.stabilizer (Equiv.Perm (Fin 3)) a := (rfl)

/-- **`A₃` has exactly three complements in `S₃`.** -/
theorem card_isComplement'_alternatingGroup_fin_three :
    Nat.card {D : Subgroup (Equiv.Perm (Fin 3)) // (alternatingGroup (Fin 3)).IsComplement' D} =
      3 := by
  rw [← Nat.card_congr alternatingGroupFinThreeComplementEquiv, Nat.card_eq_fintype_card,
    Fintype.card_fin]

end TauCeti
