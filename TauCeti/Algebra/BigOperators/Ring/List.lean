/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Defs
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Varying one factor of a list product in a ring

In an `R`-algebra `A`, the product of a list is affine in each factor. In particular, shifting one
factor `a` by the scalar `algebraMap R A c` changes the product by `c` times the product of the
list with that factor deleted. This is the step that centres one letter of a word at a time.

An additive map `δ` of a possibly noncommutative ring obeying the Leibniz rule
`δ (a * b) = δ a * b + a * δ b` sends an ordered product `f 0 * ⋯ * f (n - 1)` to the sum, over the
positions `k`, of the same product with the factor `f k` replaced by `δ (f k)`. The rule covers
both a derivation of a commutative ring and the inner derivation `⁅a, -⁆` of an associative ring,
which is how the commutator with a Lie generator acts on a word in a universal enveloping algebra.

## Main results

* `List.prod_append_sub_algebraMap_cons`:
  `(l₁ ++ (a - algebraMap R A c) :: l₂).prod = (l₁ ++ a :: l₂).prod - c • (l₁ ++ l₂).prod`.
* `AddMonoidHom.map_prod_ofFn_of_leibniz`: the Leibniz rule for an ordered product of `n` factors.
-/

public section

namespace List

variable {R A : Type*} [CommSemiring R] [Ring A] [Algebra R A]

/-- Shifting the factor `a` of the product of `l₁ ++ a :: l₂` by the scalar `algebraMap R A c`
subtracts `c` times the product of `l₁ ++ l₂`. -/
theorem prod_append_sub_algebraMap_cons (l₁ l₂ : List A) (a : A) (c : R) :
    (l₁ ++ (a - algebraMap R A c) :: l₂).prod = (l₁ ++ a :: l₂).prod - c • (l₁ ++ l₂).prod := by
  simp only [prod_append, prod_cons, sub_mul, mul_sub, Algebra.smul_def, Algebra.left_comm _ c]

end List

namespace AddMonoidHom

variable {A : Type*} [Ring A]

/-- **The Leibniz rule for an ordered product.** An additive map `δ` with
`δ (a * b) = δ a * b + a * δ b` sends the product `f 0 * ⋯ * f (n - 1)` to the sum over `k` of the
same product with its `k`-th factor replaced by `δ (f k)`. The ring need not be commutative. -/
theorem map_prod_ofFn_of_leibniz (δ : A →+ A) (hδ : ∀ a b, δ (a * b) = δ a * b + a * δ b)
    {n : ℕ} (f : Fin n → A) :
    δ (List.ofFn f).prod = ∑ k, (List.ofFn (Function.update f k (δ (f k)))).prod := by
  induction n with
  | zero =>
    have h := hδ 1 1
    simp only [mul_one, one_mul, left_eq_add] at h
    simp [h]
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, hδ, ih, Fin.sum_univ_succ, Finset.mul_sum]
    congr 1
    · simp only [List.ofFn_succ, List.prod_cons, Function.update_self,
        Function.update_of_ne (Fin.succ_ne_zero _)]
    · refine Finset.sum_congr rfl fun k _ ↦ ?_
      rw [List.ofFn_succ, List.prod_cons, Function.update_of_ne (Fin.succ_ne_zero k).symm]
      congr 3
      funext i
      simp only [Function.update_apply, Fin.succ_inj]

end AddMonoidHom
