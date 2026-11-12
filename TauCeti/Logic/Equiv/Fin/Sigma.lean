/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.List.OfFn
public import Mathlib.Logic.Equiv.Fin.Rotate
import TauCeti.Algebra.BigOperators.Finset.PartialSum
import TauCeti.Data.Fin.Basic

/-!
# Cyclic rotation of concatenated blocks

Mathlib's `finSigmaFinEquiv` lists the positions of `m` consecutive blocks of lengths `n i` as
`Fin (∑ i, n i)`. This file describes the cyclic successor `finRotate` in these coordinates: inside
a block it moves to the next position of that block, and from the last position of a block it
moves to the first position of the cyclically next block, when that block is nonempty. It also
splits the list of values of a function on `Fin (∑ i, n i)` into the lists of its values on the
blocks (`List.ofFn_sum`), as `List.ofFn_mul` does for blocks of equal length.

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

/-- The cyclic successor of the last position of a block is the first position `j'` of the
cyclically next block; the existence of `j'` says that this block is nonempty. -/
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

namespace List

/-- The list of values of a function on the concatenation of blocks of lengths `n i` is the
concatenation of the lists of its values on the blocks. -/
theorem ofFn_sum {α : Type*} {m : ℕ} {n : Fin m → ℕ} (f : Fin (∑ i, n i) → α) :
    ofFn f = (ofFn fun i => ofFn fun j => f (finSigmaFinEquiv ⟨i, j⟩)).flatten := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ofFn_congr (Fin.sum_univ_castSucc n), ofFn_add, ofFn_succ', concat_eq_append,
      flatten_append, flatten_singleton, ih]
    congr 3 <;> funext i
    · congr 1
      funext j
      congr 1
      ext
      simp [finSigmaFinEquiv_apply]
    · congr 1
      ext
      simp [finSigmaFinEquiv_apply]
      -- The two sums agree term by term: `Fin.castSucc` and `Fin.castLE` keep the value.
      rfl

end List
