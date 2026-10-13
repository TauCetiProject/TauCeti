/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin

/-!
# Telescoping sums over finite vertex sequences

Successive differences indexed by `Fin N` telescope between the first and last members of a
sequence indexed by `Fin (N + 1)`.
-/

public section

namespace Fin

/-- Successive differences over a finite sequence telescope to the difference of its endpoints. -/
theorem sum_sub_succ {A : Type*} [AddCommGroup A] {N : ℕ}
    (f : Fin (N + 1) → A) :
    (∑ i : Fin N, (f i.succ - f i.castSucc)) = f (Fin.last N) - f 0 := by
  rw [Finset.sum_sub_distrib]
  have h₁ := Fin.sum_univ_succ f
  have h₂ := Fin.sum_univ_castSucc f
  have h : f 0 + (∑ i : Fin N, f i.succ) =
      (∑ i : Fin N, f i.castSucc) + f (Fin.last N) := h₁.symm.trans h₂
  exact (sub_eq_sub_iff_add_eq_add).mpr (by simpa only [add_comm] using h)

end Fin
