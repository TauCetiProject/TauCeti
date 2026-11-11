/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.Fin.Rotate
import TauCeti.Data.Fin.Basic

/-!
# Cyclic rotation of concatenated blocks

Mathlib's `finSigmaFinEquiv` lists the positions of `m` consecutive blocks of lengths `n i` as
`Fin (∑ i, n i)`. This file describes the cyclic successor `finRotate` in these coordinates: inside
a block it moves to the next position of that block, and from the last position of a block it
moves to the first position of the cyclically next block.

This is the bookkeeping needed to replace each letter of a cyclic word by a nonempty block of
letters.
-/

public section

namespace TauCeti

variable {m : ℕ} {n : Fin m → ℕ}

/-- The total length of the blocks before the block `a`. -/
private def blockStart (n : Fin m → ℕ) (a : ℕ) : ℕ := ∑ k : Fin m, if (k : ℕ) < a then n k else 0

private theorem blockStart_zero : blockStart n 0 = 0 := by
  simp [blockStart]

private theorem blockStart_self : blockStart n m = ∑ k, n k := by
  simp [blockStart]

private theorem blockStart_succ (i : Fin m) : blockStart n (i + 1) = blockStart n i + n i := by
  have h : ∀ k : Fin m, (if (k : ℕ) < i + 1 then n k else 0) =
      (if (k : ℕ) < i then n k else 0) + if k = i then n k else 0 := fun k => by
    simp only [Fin.ext_iff]
    split_ifs <;> omega
  simp [blockStart, h, Finset.sum_add_distrib]

private theorem coe_finSigmaFinEquiv (i : Fin m) (j : Fin (n i)) :
    (finSigmaFinEquiv ⟨i, j⟩ : ℕ) = blockStart n i + j := by
  rw [finSigmaFinEquiv_apply, blockStart,
    Fin.sum_univ_eq_sum_castLE_add i (fun k => if (k : ℕ) < i then n k else 0)
      fun k hk => ite_eq_right_iff.2 fun h => absurd h (not_lt.2 hk.le)]
  simp

/-- Inside a block, the cyclic successor of a position is the next position of that block. -/
theorem finRotate_finSigmaFinEquiv_of_lt (i : Fin m) (j : Fin (n i)) (h : (j : ℕ) + 1 < n i) :
    finRotate _ (finSigmaFinEquiv ⟨i, j⟩) = finSigmaFinEquiv ⟨i, ⟨j + 1, h⟩⟩ := by
  apply Fin.ext
  have hlt := (finSigmaFinEquiv ⟨i, ⟨j + 1, h⟩⟩).is_lt
  rw [Fin.coe_finRotate_eq_ite, coe_finSigmaFinEquiv, coe_finSigmaFinEquiv]
  rw [coe_finSigmaFinEquiv] at hlt
  simp only at hlt ⊢
  split_ifs <;> omega

/-- The cyclic successor of the last position of a block is the first position of the cyclically
next block. -/
theorem finRotate_finSigmaFinEquiv_of_eq (i : Fin m) (j : Fin (n i)) (h : (j : ℕ) + 1 = n i)
    (j' : Fin (n (finRotate m i))) (hj' : (j' : ℕ) = 0) :
    finRotate _ (finSigmaFinEquiv ⟨i, j⟩) = finSigmaFinEquiv ⟨finRotate m i, j'⟩ := by
  apply Fin.ext
  have hlt := (finSigmaFinEquiv ⟨finRotate m i, j'⟩).is_lt
  have hstep := blockStart_succ (n := n) i
  rw [Fin.coe_finRotate_eq_ite, coe_finSigmaFinEquiv, coe_finSigmaFinEquiv]
  rw [coe_finSigmaFinEquiv] at hlt
  rw [Fin.coe_finRotate_eq_ite i] at hlt ⊢
  by_cases hi : (i : ℕ) + 1 = m
  · rw [hi, blockStart_self] at hstep
    simp only [hi, ite_true, blockStart_zero]
    split_ifs <;> omega
  · simp only [hi, ite_false] at hlt ⊢
    split_ifs <;> omega

end TauCeti
