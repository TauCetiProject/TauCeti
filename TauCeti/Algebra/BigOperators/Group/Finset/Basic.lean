/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# Finite-product descent for scaling-closed predicates

Let `M` be a commutative monoid, `P : M → Prop` a predicate, and `f, g : ι → M` two families
indexed by a finite set `s : Finset ι`. Suppose that for every `k ∈ s`, `P` is closed under
multiplying by `g k` (`P a → P (a * g k)`) and satisfies the pairwise descent rule
`P (a * f k) → P (a * g k) → P a`. Then `P` holds at `c` whenever it holds at `c * ∏ k ∈ s, g k`
and at `c * f k` for every `k ∈ s`.

In a commutative ring, taking `f k = b k` and `g k = 1 - b k` recovers descent from the
complementary finite cover `c * ∏ k ∈ s, (1 - b k)` and `{c * b k | k ∈ s}` whenever `P` is closed
under scaling and glues `P (a * e)` with `P (a * (1 - e))`.

## Main results

* `TauCeti.of_mul_prod_of_forall_mul`: finite-product descent for a predicate on a commutative
  monoid.
* `TauCeti.of_add_sum_of_forall_add`: the additive counterpart for a finite sum in an additive
  commutative monoid.
-/

public section

namespace TauCeti

/-- **Finite-product descent for a predicate on a commutative monoid.** If for every `k ∈ s`, `P` is
closed under multiplying by `g k` (`P a → P (a * g k)`) and satisfies the pairwise descent rule
`P (a * f k) → P (a * g k) → P a`, then `P` holds at `c` whenever it holds at `c * ∏ k ∈ s, g k`
and at `c * f k` for every `k ∈ s`. -/
@[to_additive /-- **Finite-sum descent for a predicate on an additive commutative monoid.** If for
every `k ∈ s`, `P` is closed under adding `g k` (`P a → P (a + g k)`) and satisfies the pairwise
descent rule `P (a + f k) → P (a + g k) → P a`, then `P` holds at `c` whenever it holds at
`c + ∑ k ∈ s, g k` and at `c + f k` for every `k ∈ s`. -/]
theorem of_mul_prod_of_forall_mul {ι M : Type*} [CommMonoid M] {P : M → Prop}
    {s : Finset ι} {f g : ι → M}
    (hmul : ∀ {a k}, k ∈ s → P a → P (a * g k))
    (hjoin : ∀ {a k}, k ∈ s → P (a * f k) → P (a * g k) → P a)
    {c : M} (h0 : P (c * ∏ k ∈ s, g k)) (hk : ∀ k ∈ s, P (c * f k)) : P c := by
  classical
  induction s using Finset.induction_on generalizing c with
  | empty => rwa [Finset.prod_empty, mul_one] at h0
  | insert k s hks ihs =>
    rw [Finset.prod_insert hks, ← mul_assoc] at h0
    have hcg : P (c * g k) :=
      ihs (fun ht ↦ hmul (Finset.mem_insert_of_mem ht))
        (fun ht ↦ hjoin (Finset.mem_insert_of_mem ht))
        h0 fun t ht ↦ by
          have h := hmul (Finset.mem_insert_self k s) (hk t (Finset.mem_insert_of_mem ht))
          rwa [mul_right_comm] at h
    exact hjoin (Finset.mem_insert_self k s) (hk k (Finset.mem_insert_self k s)) hcg

end TauCeti
