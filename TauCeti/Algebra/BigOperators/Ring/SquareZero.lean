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

These elementary symmetric sums `e k = ∑_{t ⊆ s, #t = k} ∏_{i ∈ t} x i` multiply like divided
powers, `e m * e n = (m + n).choose m • e (m + n)`, again with no division by factorials.

## Main results

* `Finset.sum_pow_of_commute_of_mul_self_eq_zero`: the displayed formula, with the product over
  `t` the noncommutative product `Finset.noncommProd` of the pairwise commuting family.
* `Finset.sum_pow_of_pairwise_commute_of_mul_self_eq_zero`: the same formula as a sum over
  `s.powersetCard n`, for a family commuting pairwise everywhere.
* `Finset.sum_noncommProd_powersetCard_mul_of_commute_of_mul_self_eq_zero`:
  `e m * e n = (m + n).choose m • e (m + n)`, and
  `Finset.sum_noncommProd_powersetCard_mul_of_pairwise_commute_of_mul_self_eq_zero`, the same
  identity as sums over `powersetCard` for a family commuting pairwise everywhere.
-/

public section

open scoped Function Nat

variable {R : Type*} [Semiring R]

namespace Finset

variable {ι : Type*}

/-- The multinomial theorem for square-zero elements, for a family commuting pairwise everywhere:
`(∑ i ∈ s, x i) ^ n` is `n !` times the sum, over the `n`-element subsets `t` of `s`, of the
products of the `x i` with `i ∈ t`. -/
theorem sum_pow_of_pairwise_commute_of_mul_self_eq_zero (s : Finset ι) (x : ι → R)
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
      rw [sum_insert ha, hcomm.add_pow_succ_of_mul_self_eq_zero (hx a (mem_insert_self a s)),
        sum_noncommProd_powersetCard_succ_insert_of_pairwise_commute ha x hc]
      simp only [ih hxs, mul_smul_comm, smul_smul, Nat.factorial_succ, smul_add]

/-- **Multinomial theorem for square-zero elements.** If the `x i` commute pairwise and square to
zero on `s`, then `(∑ i ∈ s, x i) ^ n` is `n !` times the sum, over the `n`-element subsets `t` of
`s`, of the products of the `x i` with `i ∈ t`. -/
theorem sum_pow_of_commute_of_mul_self_eq_zero (s : Finset ι) (x : ι → R)
    (hc : (s : Set ι).Pairwise (Commute on x)) (hx : ∀ i ∈ s, x i * x i = 0) (n : ℕ) :
    (∑ i ∈ s, x i) ^ n =
      n ! • ∑ t : s.powersetCard n,
        t.1.noncommProd x (hc.mono (coe_subset.2 (mem_powersetCard.1 t.2).1)) := by
  -- Extend `x` by zero outside `s`, to a family commuting pairwise everywhere.
  have hxs (i : ι) (hi : i ∈ s) : (s : Set ι).indicator x i = x i := Set.indicator_of_mem hi x
  rw [sum_noncommProd_powersetCard_eq_indicator subset_rfl x hc, ← sum_congr rfl hxs]
  exact sum_pow_of_pairwise_commute_of_mul_self_eq_zero s _ hc.pairwise_commute_indicator
    (fun i hi ↦ by rw [hxs i hi, hx i hi]) n

/-- Multiplication of elementary symmetric sums of square-zero elements, for a family commuting
pairwise everywhere: if the `x i` square to zero on `s`, then the sums `e k` of the products over
the `k`-element subsets of `s` satisfy `e m * e n = (m + n).choose m • e (m + n)`. -/
theorem sum_noncommProd_powersetCard_mul_of_pairwise_commute_of_mul_self_eq_zero (s : Finset ι)
    (x : ι → R) (hc : Pairwise (Commute on x)) (hx : ∀ i ∈ s, x i * x i = 0) (m n : ℕ) :
    (∑ t ∈ s.powersetCard m, t.noncommProd x (hc.set_pairwise _)) *
        ∑ t ∈ s.powersetCard n, t.noncommProd x (hc.set_pairwise _) =
      (m + n).choose m • ∑ t ∈ s.powersetCard (m + n), t.noncommProd x (hc.set_pairwise _) := by
  classical
  induction s using Finset.induction_on generalizing m n with
  | empty =>
    cases m with
    | zero => simp
    | succ m =>
      rw [powersetCard_eq_empty.2 (by simp), sum_empty, zero_mul,
        powersetCard_eq_empty.2 (by simp; omega), sum_empty, smul_zero]
  | insert a s ha ih =>
    have hxa : x a * x a = 0 := hx a (mem_insert_self a s)
    have hcomm (k : ℕ) :
        Commute (x a) (∑ t ∈ s.powersetCard k, t.noncommProd x (hc.set_pairwise _)) :=
      Commute.sum_right _ _ _ fun t _ ↦ noncommProd_commute _ _ _ _ fun i _ ↦ by
        obtain rfl | h := eq_or_ne a i
        exacts [Commute.refl _, hc h]
    have ih := ih fun i hi ↦ hx i (mem_insert_of_mem hi)
    cases m with
    | zero => simp
    | succ m =>
      cases n with
      | zero => simp
      | succ n =>
        -- Write the top degree as a successor, so that the recursion applies to each factor.
        rw [show m + 1 + (n + 1) = m + n + 1 + 1 by omega]
        simp only [sum_noncommProd_powersetCard_succ_insert_of_pairwise_commute ha x hc]
        -- Name the elementary symmetric sums `e k` of the family over `s`.
        obtain ⟨e, he⟩ : ∃ e : ℕ → R, ∀ k,
            ∑ t ∈ s.powersetCard k, t.noncommProd x (hc.set_pairwise _) = e k :=
          ⟨_, fun _ ↦ rfl⟩
        simp only [he] at hcomm ih ⊢
        -- The term with `x a` twice vanishes, and Pascal's rule combines the two terms with `x a`
        -- once.
        have hsq : x a * e m * (x a * e n) = 0 := by
          rw [mul_assoc, (hcomm m).symm.left_comm]
          simp [← mul_assoc, hxa]
        have hcross : x a * e m * e (n + 1) + e (m + 1) * (x a * e n) =
            (m + n + 1 + 1).choose (m + 1) • (x a * e (m + n + 1)) := by
          rw [(hcomm (m + 1)).symm.left_comm, mul_assoc, ih, ih, Nat.choose_succ_succ']
          -- Both products land in degree `m + n + 1`.
          simp only [Nat.add_right_comm m 1 n, ← add_assoc, mul_smul_comm, add_smul]
        simp only [add_mul, mul_add, hsq, add_zero, ih]
        rw [add_assoc, hcross, show m + 1 + (n + 1) = m + n + 1 + 1 by omega, smul_add]

/-- **Multiplication of elementary symmetric sums of square-zero elements.** If the `x i` commute
pairwise and square to zero on `s`, then the sums `e k` of the products over the `k`-element subsets
of `s` satisfy `e m * e n = (m + n).choose m • e (m + n)`: they are the divided powers of
`e 1 = ∑ i ∈ s, x i`, with no division by factorials. -/
theorem sum_noncommProd_powersetCard_mul_of_commute_of_mul_self_eq_zero (s : Finset ι)
    (x : ι → R) (hc : (s : Set ι).Pairwise (Commute on x)) (hx : ∀ i ∈ s, x i * x i = 0)
    (m n : ℕ) :
    (∑ t : s.powersetCard m,
        t.1.noncommProd x (hc.mono (coe_subset.2 (mem_powersetCard.1 t.2).1))) *
        ∑ t : s.powersetCard n,
          t.1.noncommProd x (hc.mono (coe_subset.2 (mem_powersetCard.1 t.2).1)) =
      (m + n).choose m • ∑ t : s.powersetCard (m + n),
        t.1.noncommProd x (hc.mono (coe_subset.2 (mem_powersetCard.1 t.2).1)) := by
  simp only [sum_noncommProd_powersetCard_eq_indicator subset_rfl x hc]
  exact sum_noncommProd_powersetCard_mul_of_pairwise_commute_of_mul_self_eq_zero s _
    hc.pairwise_commute_indicator (fun i hi ↦ by rw [Set.indicator_of_mem hi, hx i hi]) m n

end Finset
