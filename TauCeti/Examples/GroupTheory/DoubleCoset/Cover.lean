/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import TauCeti.GroupTheory.DoubleCoset.Cover
import Mathlib.GroupTheory.Perm.Sign
import Mathlib.Algebra.BigOperators.Fin

/-!
# A two-block double-coset cover of the symmetric group on three letters

Cover the cosets of the stabilizer of `0` by two double-coset blocks. Check the generator
transitions in these blocks and obtain the index bound `1 + 2 = 3`. The transition
witnesses are permutations in the actual group, not just a permutation action of an
unidentified presented group. A failed one-block cover tests the identity-only boundary.
-/

open Equiv
open scoped Pointwise

namespace TauCeti

/-- The two double-coset blocks of a point stabilizer in `S₃` certify index at most three. -/
example : (MulAction.stabilizer (Perm (Fin 3)) (0 : Fin 3)).index ≤ 3 := by
  let H := MulAction.stabilizer (Perm (Fin 3)) (0 : Fin 3)
  let w : Fin 2 → Perm (Fin 3) := fun i ↦ if i = 0 then 1 else swap 0 1
  have hw : w 0 = 1 := rfl
  have transitions : ∀ (s h : Perm (Fin 3)), s.IsSwap → h 0 = 0 → ∀ i : Fin 2,
      ∃ (j : Fin 2) (a b : Perm (Fin 3)),
        a 0 = 0 ∧ b 0 = 0 ∧ a * w j * b = s * h * w i := by
    unfold Perm.IsSwap
    decide +kernel
  have cover : ∀ g : Perm (Fin 3), ∃ i, g ∈ DoubleCoset.doubleCoset (w i) H H := by
    apply H.exists_mem_doubleCoset_of_generator_transitions w {s | s.IsSwap}
      Perm.closure_isSwap
    · exact ⟨0, DoubleCoset.mem_doubleCoset.mpr
        ⟨1, H.one_mem, 1, H.one_mem, by simp [hw]⟩⟩
    · intro s hs i h
      have hs' : s.IsSwap := by
        rcases hs with hs | hs
        · exact hs
        · obtain ⟨a, b, hab, heq⟩ := hs
          exact ⟨a, b, hab, by simpa using congrArg Inv.inv heq⟩
      obtain ⟨j, a, b, ha, hb, hab⟩ := transitions s h hs' h.property i
      exact ⟨j, DoubleCoset.mem_doubleCoset.mpr ⟨a, ha, b, hb, hab.symm⟩⟩
  have hcard : Nat.card H = 2 := by
    rw [Nat.card_eq_fintype_card]
    decide +kernel
  have bound := H.index_le_sum_of_doubleCoset_cover w cover
  have hzero : (ConjAct.toConjAct (w 0) • H).relIndex H = 1 := by
    simp [hw]
  have hone : (ConjAct.toConjAct (w 1) • H).relIndex H ≤ 2 :=
    (Nat.le_of_dvd Nat.card_pos (Subgroup.relIndex_dvd_card _ _)).trans hcard.le
  exact bound.trans (by simpa only [Fin.sum_univ_two, hzero] using Nat.add_le_add_left hone 1)

/-- Omitting the nonidentity block cannot satisfy all transposition transitions. -/
example : ¬ (∀ s : Perm (Fin 3), s.IsSwap → ∃ a b : Perm (Fin 3),
    a 0 = 0 ∧ b 0 = 0 ∧ a * 1 * b = s * 1 * 1) := by
  unfold Perm.IsSwap
  decide +kernel

end TauCeti
