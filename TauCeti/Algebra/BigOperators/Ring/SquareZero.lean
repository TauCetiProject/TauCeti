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

/-- **Multinomial theorem for square-zero elements.** If the `x i` commute pairwise and square to
zero on `s`, then `(∑ i ∈ s, x i) ^ n` is `n !` times the sum, over the `n`-element subsets `t` of
`s`, of the products of the `x i` with `i ∈ t`. -/
theorem sum_pow_of_commute_of_mul_self_eq_zero (s : Finset ι) (x : ι → R)
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
      -- Split the `n + 1`-subsets of `insert a s` into those avoiding `a` and those of the form
      -- `insert a t` with `t` an `n`-subset of `s`.
      have hdisj : Disjoint (s.powersetCard (n + 1)) ((s.powersetCard n).image (insert a)) := by
        refine disjoint_left.2 fun t ht ht' ↦ ?_
        obtain ⟨u, -, rfl⟩ := mem_image.1 ht'
        exact ha ((mem_powersetCard.1 ht).1 (mem_insert_self a u))
      have hinj : Set.InjOn (insert a) (s.powersetCard n : Set (Finset ι)) := by
        intro u hu v hv huv
        have hau : a ∉ u := fun h ↦ ha ((mem_powersetCard.1 hu).1 h)
        have hav : a ∉ v := fun h ↦ ha ((mem_powersetCard.1 hv).1 h)
        rw [← erase_insert hau, huv, erase_insert hav]
      have hins : ∀ t ∈ s.powersetCard n,
          (insert a t).noncommProd x (hc.set_pairwise _) =
            x a * t.noncommProd x (hc.set_pairwise _) := fun t ht ↦
        noncommProd_insert_of_notMem _ _ _ _ fun h ↦ ha ((mem_powersetCard.1 ht).1 h)
      rw [sum_insert ha, hcomm.add_pow_succ_of_mul_self_eq_zero (hx a (mem_insert_self a s)),
        ih hxs, ih hxs, powersetCard_succ_insert ha, sum_union hdisj, sum_image hinj,
        sum_congr rfl hins, ← mul_sum, mul_smul_comm, smul_smul, ← Nat.factorial_succ, smul_add]

end Finset
