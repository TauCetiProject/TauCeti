/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas

/-!
# Squares and finite products

If all but the last entries of two finite families agree modulo squares, agreement of their
products modulo squares determines the last entry. This is useful when prescribing the last
coefficient of a diagonal quadratic form from its determinant.
-/

public section

namespace TauCeti

/-- Agreement modulo squares of two products, and of all their factors except the last,
forces agreement of the last factors. -/
theorem isSquare_div_last_of_isSquare_div_prod
    {G : Type*} [CommGroup G] {n : ℕ} {a b : Fin (n + 1) → G}
    (h : ∀ i : Fin n, IsSquare (a i.castSucc / b i.castSucc))
    (hp : IsSquare ((∏ i, a i) / ∏ i, b i)) :
    IsSquare (a (Fin.last n) / b (Fin.last n)) := by
  have hh := Finset.isSquare_prod (s := Finset.univ) _ (fun i _ => h i)
  convert hp.div hh using 1
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc, Finset.prod_div_distrib]
  simp only [mul_div_mul_comm, mul_div_cancel_left]

end TauCeti
