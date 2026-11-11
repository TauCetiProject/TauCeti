/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Logic.Equiv.Fin.Rotate
import TauCeti.Algebra.BigOperators.Finset.PartialSum
import TauCeti.Data.Fin.Basic

/-!
# Cyclic rotation of concatenated blocks

Mathlib's `finSigmaFinEquiv` lists the positions of `m` consecutive blocks of lengths `n i` as
`Fin (∑ i, n i)`. This file describes the cyclic successor `finRotate` in these coordinates: inside
a block it moves to the next position of that block, and from the last position of a block it
moves to the first position of the cyclically next block. Positions are compared through the
prefix sums `TauCeti.prefixSum` of the block lengths.

This is the bookkeeping needed to replace each letter of a cyclic word by a nonempty block of
letters.
-/

public section

namespace Fin

open TauCeti

variable {m : ℕ} {n : Fin m → ℕ}

/-- The position of `⟨i, j⟩` in the concatenation is the total length of the blocks before `i`,
plus `j`. -/
private theorem coe_finSigmaFinEquiv (i : Fin m) (j : Fin (n i)) :
    (finSigmaFinEquiv ⟨i, j⟩ : ℕ) = prefixSum i n + j := by
  rw [finSigmaFinEquiv_apply, prefixSum_eq_sum_castLE i.2.le]

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
  have hstep : prefixSum (i + 1) n = prefixSum i n + n i := prefixSum_succ i.2 n
  rw [Fin.coe_finRotate_eq_ite, coe_finSigmaFinEquiv, coe_finSigmaFinEquiv]
  rw [coe_finSigmaFinEquiv] at hlt
  rw [Fin.coe_finRotate_eq_ite i] at hlt ⊢
  by_cases hi : (i : ℕ) + 1 = m
  · rw [hi, prefixSum_of_le le_rfl] at hstep
    simp only [hi, ite_true, prefixSum_zero]
    split_ifs <;> omega
  · simp only [hi, ite_false] at hlt ⊢
    split_ifs <;> omega

end Fin
