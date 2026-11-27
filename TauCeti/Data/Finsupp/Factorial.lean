/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Finsupp.Basic
public import Mathlib.Data.Nat.Factorial.Basic

/-!
# Products of multi-index factorials

Incrementing one coordinate of a finitely supported exponent vector changes only
the factorial at that coordinate.
-/

public section

namespace Finsupp

/-- Increasing one exponent multiplies the product of factorials by that exponent plus one. -/
theorem prod_factorial_add_single {σ R : Type*} [CommSemiring R]
    (d : σ →₀ ℕ) (i : σ) :
    ((d + Finsupp.single i 1).prod fun _ n ↦ (n.factorial : R)) =
      ((d i : R) + 1) * d.prod fun _ n ↦ (n.factorial : R) := by
  classical
  let weight : σ → ℕ → R := fun _ n ↦ n.factorial
  have hzero : ∀ j, weight j 0 = 1 := by simp [weight]
  calc
    (d + Finsupp.single i 1).prod weight =
        weight i ((d + Finsupp.single i 1 : σ →₀ ℕ) i) *
          ((d + Finsupp.single i 1).erase i).prod weight :=
      (Finsupp.mul_prod_erase' _ i _ hzero).symm
    _ = ((d i : R) + 1) * (weight i (d i) * (d.erase i).prod weight) := by
      simp [weight, Finsupp.add_apply, Finsupp.erase_add, Nat.factorial_succ, mul_assoc]
    _ = ((d i : R) + 1) * d.prod weight := by
      rw [Finsupp.mul_prod_erase' d i weight hzero]

end Finsupp
