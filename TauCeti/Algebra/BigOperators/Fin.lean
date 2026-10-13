/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Fin

/-!
# Telescoping products and sums over finite vertex sequences

Successive quotients and differences indexed by `Fin N` telescope between the endpoints of a
sequence indexed by `Fin (N + 1)`.
-/

public section

namespace Fin

/-- Successive quotients over a finite sequence telescope to the quotient of its endpoints. -/
@[to_additive /-- Successive differences over a finite sequence telescope to the difference of
its endpoints. -/]
theorem prod_univ_succ_div_castSucc {A : Type*} [CommGroup A] {N : ℕ}
    (f : Fin (N + 1) → A) :
    (∏ i : Fin N, (f i.succ / f i.castSucc)) = f (Fin.last N) / f 0 := by
  rw [Finset.prod_div_distrib]
  have h₁ := Fin.prod_univ_succ f
  have h₂ := Fin.prod_univ_castSucc f
  have h : f 0 * (∏ i : Fin N, f i.succ) =
      (∏ i : Fin N, f i.castSucc) * f (Fin.last N) := h₁.symm.trans h₂
  exact div_eq_div_iff_mul_eq_mul.mpr (by simpa only [mul_comm] using h)

/-- The reversed successive quotients telescope with the reversed endpoint quotient. -/
@[to_additive /-- The reversed successive differences telescope with the reversed endpoint
difference. -/]
theorem prod_univ_castSucc_div_succ {A : Type*} [CommGroup A] {N : ℕ}
    (f : Fin (N + 1) → A) :
    (∏ i : Fin N, (f i.castSucc / f i.succ)) = f 0 / f (Fin.last N) := by
  simpa only [← Finset.prod_inv_distrib, inv_div] using
    congrArg Inv.inv (prod_univ_succ_div_castSucc f)

end Fin
