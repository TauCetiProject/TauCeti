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
      have hcard := congrArg (fun H : Subgroup (Equiv.Perm (Fin 3)) ↦ Nat.card H) h <;>
      simp_all only [Subgroup.card_bot, Subgroup.card_top] <;> omega
  have hstab : Function.Injective
      (fun a : Fin 3 ↦ MulAction.stabilizer (Equiv.Perm (Fin 3)) a) := by
    intro a b hab
    have h := congrArg (fun H : Subgroup (Equiv.Perm (Fin 3)) ↦
      Equiv.swap (a + 1) (a + 2) ∈ H) hab
    simp only [TauCeti.mem_stabilizer_perm_fin_three_iff] at h
    have key : ∀ a b : Fin 3,
        (Equiv.swap (a + 1) (a + 2) = 1 ∨
          Equiv.swap (a + 1) (a + 2) = Equiv.swap (b + 1) (b + 2)) → a = b := by
      decide
    exact key a b (h.mp (Or.inr trivial))
  have hAlt : alternatingGroup (Fin 3) ≠ ⊥ ∧ alternatingGroup (Fin 3) ≠ ⊤ := by
    have ha := TauCeti.card_alternatingGroup_fin_three
    constructor <;> intro h <;>
      have hcard := congrArg (fun H : Subgroup (Equiv.Perm (Fin 3)) ↦ Nat.card H) h <;>
      simp_all only [Subgroup.card_bot, Subgroup.card_top] <;> omega
  have huniv : (Finset.univ : Finset (Subgroup (Equiv.Perm (Fin 3)))) =
      {⊥, MulAction.stabilizer (Equiv.Perm (Fin 3)) (0 : Fin 3),
        MulAction.stabilizer (Equiv.Perm (Fin 3)) (1 : Fin 3),
        MulAction.stabilizer (Equiv.Perm (Fin 3)) (2 : Fin 3), alternatingGroup (Fin 3), ⊤} := by
    ext H
    simpa using fin_three_cases H
  rw [finsum_eq_sum_of_fintype, huniv]
  have h0 := hne 0
  have h1 := hne 1
  have h2 := hne 2
  simp_all [Finset.sum_insert, hstab.eq_iff, ne_comm, add_assoc]

end Subgroup
