/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharP.Defs
public import Mathlib.Algebra.Group.AddChar

/-!
# Additive characters

## Main results

* `AddChar.map_sum_eq_prod`: an additive character turns finite sums into products.
* `AddChar.pow_char_eq_one`: every additive character on a ring of characteristic `p`, such as
  `ZMod p`, takes values in the `p`-th roots of unity.
-/

public section

/-- An additive character on a ring of characteristic `p` takes values in the `p`-th roots of
unity; for instance every additive character on `ZMod p` does. -/
@[simp]
theorem AddChar.pow_char_eq_one {R M : Type*} [NonAssocSemiring R] (p : ℕ) [CharP R p]
    [Monoid M] (ψ : AddChar R M) (x : R) : ψ x ^ p = 1 := by
  simp [← AddChar.map_nsmul_eq_pow]

/-- An additive character turns a finite sum into the product of its values. -/
theorem AddChar.map_sum_eq_prod {ι A M : Type*} [AddCommMonoid A] [CommMonoid M]
    (ψ : AddChar A M) (s : Finset ι) (f : ι → A) : ψ (∑ i ∈ s, f i) = ∏ i ∈ s, ψ (f i) := by
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih => rw [Finset.sum_cons, map_add_eq_mul, ih, Finset.prod_cons]
