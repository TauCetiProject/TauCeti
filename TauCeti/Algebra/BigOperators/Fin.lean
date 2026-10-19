/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals
public import TauCeti.Logic.Equiv.Fin.Basic

/-!
# Telescoping finite vertex sequences

Successive differences along a finite sequence sum to the difference of its endpoints,
including the empty edge sequence. Reversing every difference reverses the endpoint difference.
The equivalence omitting the last index also reindexes sums by the preceding indices.
-/

public section

namespace Fin

/-- Successive differences telescope to the endpoint difference. -/
theorem sum_univ_succ_sub_castSucc {G : Type*} [AddCommGroup G] {n : ℕ}
    (f : Fin (n + 1) → G) :
    ∑ i : Fin n, (f i.succ - f i.castSucc) = f (last n) - f 0 := by
  cases n with
  | zero => simp
  | succ n =>
    have hIic : Finset.Iic (last n) = Finset.univ := Finset.Iic_top
    simpa only [hIic, succ_last] using sum_Iic_sub (last n) f

/-- Reversed successive differences telescope to the reversed endpoint difference. -/
theorem sum_univ_castSucc_sub_succ {G : Type*} [AddCommGroup G] {n : ℕ}
    (f : Fin (n + 1) → G) :
    ∑ i : Fin n, (f i.castSucc - f i.succ) = f 0 - f (last n) := by
  simpa only [neg_sub_neg] using sum_univ_succ_sub_castSucc (fun i ↦ -f i)

end Fin

namespace TauCeti

/-- Reindex a sum over all indices except the last by the preceding finite ordinal. -/
theorem sum_finSuccAboveEquiv_last {M : Type*} [AddCommMonoid M] (n : ℕ)
    (z : {i : Fin (n + 1) // i ≠ Fin.last n} → M) :
    ∑ i : Fin n, z ⟨i.castSucc, Fin.castSucc_ne_last i⟩ = ∑ j, z j := by
  simpa only [finSuccAboveEquiv_last_apply] using
    Equiv.sum_comp (finSuccAboveEquiv (Fin.last n)) z

end TauCeti
