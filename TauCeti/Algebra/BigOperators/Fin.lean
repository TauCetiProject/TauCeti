/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Intervals

/-!
# Telescoping finite vertex sequences

Successive differences along a finite sequence sum to the difference of its endpoints,
including the empty edge sequence. Reversing every difference reverses the endpoint difference.
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
