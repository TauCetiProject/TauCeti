/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Finset.NoncommProd
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Nat.Factorial.Basic
public import TauCeti.Algebra.BigOperators.Finset.Powerset
public import TauCeti.Algebra.Ring.SquareZero
import Mathlib.Algebra.Module.NatInt

/-!
# Powers of a sum of commuting square-zero elements

Let `x i` be pairwise commuting elements of a semiring with `x i * x i = 0`. In the multinomial
expansion of `(∑ i ∈ s, x i) ^ n` every monomial with a repeated factor vanishes, and each
product of `n` distinct factors occurs `n !` times, once for each ordering. Hence

  `(∑ i ∈ s, x i) ^ n = n ! • ∑_{t ⊆ s, #t = n} ∏_{i ∈ t} x i`,

so `(∑ i ∈ s, x i) ^ n` is `n !` times an explicit element with no denominators: the elementary
symmetric sum is a divided power `(∑ i ∈ s, x i) ^ n / n !` over any base, including `ℤ`.

## Main results

* `Finset.sum_pow_of_commute_of_mul_self_eq_zero`: the displayed formula, with the product over
  `t` the noncommutative product `Finset.noncommProd` of the pairwise commuting family.
-/

public section

open scoped Function Nat

variable {R : Type*} [Semiring R]

namespace Finset

variable {ι : Type*}

/-- The multinomial theorem for square-zero elements, for a family commuting pairwise everywhere.
-/
private theorem sum_pow_of_pairwise_commute_of_mul_self_eq_zero (s : Finset ι) (x : ι → R)
    (hc : Pairwise (Commute on x)) (hx : ∀ i ∈ s, x i * x i = 0) (n : ℕ) :
    (∑ i ∈ s, x i) ^ n =
      n ! • ∑ t ∈ s.powersetCard n, t.noncommProd x (hc.set_pairwise _) := by
  classical
  induction s using Finset.induction_on generalizing n with
  | empty =>
    cases n with
    | zero => simp
    | succ n => simp [powersetCard_eq_empty.2 (by simp : (∅ : Finset ι).card < n + 1)]
  | insert a s ha ih =>
    have hxs : ∀ i ∈ s, x i * x i = 0 := fun i hi ↦ hx i (mem_insert_of_mem hi)
    have hcomm : Commute (x a) (∑ i ∈ s, x i) :=
      Commute.sum_right _ _ _ fun i hi ↦ hc (ne_of_mem_of_not_mem hi ha).symm
    cases n with
    | zero => simp
    | succ n =>
      have hins : ∀ t ∈ s.powersetCard n,
          (insert a t).noncommProd x (hc.set_pairwise _) =
            x a * t.noncommProd x (hc.set_pairwise _) := fun t ht ↦
        noncommProd_insert_of_notMem _ _ _ _ fun h ↦ ha ((mem_powersetCard.1 ht).1 h)
      rw [sum_insert ha, hcomm.add_pow_succ_of_mul_self_eq_zero (hx a (mem_insert_self a s)),
        ih hxs, ih hxs, sum_powersetCard_succ_insert ha, sum_congr rfl hins, ← mul_sum,
        mul_smul_comm, smul_smul, ← Nat.factorial_succ, smul_add]

/-- **Multinomial theorem for square-zero elements.** If the `x i` commute pairwise and square to
zero on `s`, then `(∑ i ∈ s, x i) ^ n` is `n !` times the sum, over the `n`-element subsets `t` of
`s`, of the products of the `x i` with `i ∈ t`. -/
theorem sum_pow_of_commute_of_mul_self_eq_zero (s : Finset ι) (x : ι → R)
    (hc : (s : Set ι).Pairwise (Commute on x)) (hx : ∀ i ∈ s, x i * x i = 0) (n : ℕ) :
    (∑ i ∈ s, x i) ^ n =
      n ! • ∑ t : s.powersetCard n,
        t.1.noncommProd x (hc.mono (coe_subset.2 (mem_powersetCard.1 t.2).1)) := by
  classical
  -- Extending `x` by zero outside `s` gives a family commuting pairwise everywhere.
  let y : ι → R := fun i ↦ if i ∈ s then x i else 0
  have hys : ∀ i ∈ s, y i = x i := fun i hi ↦ by simp [y, hi]
  have hyc : Pairwise (Commute on y) := fun i j hij ↦ by
    by_cases hi : i ∈ s
    · by_cases hj : j ∈ s
      · simpa [Function.onFun, y, hi, hj] using hc hi hj hij
      · simp [Function.onFun, y, hj]
    · simp [Function.onFun, y, hi]
  rw [sum_congr rfl fun i hi ↦ (hys i hi).symm,
    sum_pow_of_pairwise_commute_of_mul_self_eq_zero s y hyc (fun i hi ↦ by rw [hys i hi, hx i hi]),
    ← sum_coe_sort]
  exact congrArg _ (sum_congr rfl fun t _ ↦
    noncommProd_congr rfl (fun i hi ↦ hys i ((mem_powersetCard.1 t.2).1 hi)) _)

end Finset
