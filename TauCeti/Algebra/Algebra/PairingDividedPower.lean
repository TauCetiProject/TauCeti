/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import TauCeti.Algebra.BigOperators.Ring.SquareZero
import Mathlib.Algebra.BigOperators.GroupWithZero.Action
import TauCeti.Algebra.BigOperators.GroupWithZero.Action

/-!
# Divided powers of quadratic elements in anticommuting generators

Let `ν i` be elements of an `R`-algebra `A` which anticommute, `ν i * ν j + ν j * ν i = 0`, and
square to zero, `ν i * ν i = 0`. Examples are the generators `ExteriorAlgebra.ι R (e i)` of an
exterior algebra and the degree-one classes in the integral cohomology ring of a torus. For
coefficients `a : ι × ι → R` and a finite set `P` of index pairs consider the quadratic element

  `u = ∑_{p ∈ P} a p • (ν p.1 * ν p.2)`,

for instance a two-form `∑_{i < j} a_{ij} ν_i ν_j`. Each product `ν i * ν j` commutes with every
`ν k`, so the summands of `u` commute pairwise and square to zero. By the multinomial theorem for
square-zero elements, `u ^ k = k ! • u^[k]`, where the `k`-th divided power

  `u^[k] = ∑_{t ⊆ P, #t = k} ∏_{p ∈ t} a p • (ν p.1 * ν p.2)`

involves no denominators. A product over `t` vanishes unless the `2 k` endpoints `p.1, p.2` of
the pairs `p ∈ t` are distinct, so `u^[k]` is the sum over the unordered sets of `k` pairwise
disjoint pairs, each contributing the product of its coefficients times its ordered monomial
`ν_{i₁} ν_{j₁} ⋯ ν_{i_k} ν_{j_k}`. Over `ℤ`, in a torsion-free ring, `u^[k]` is therefore the
integral class `u ^ k / k !`, obtained without dividing by `k !`.

Such divided powers of the two-form `u` on the integral cohomology of the Picard torus appear in
the wall-crossing formula for Seiberg–Witten invariants of four-manifolds with `b₂⁺ = 1`.

## Main definitions

* `TauCeti.pairDividedPower hν a P k`: the divided power `u^[k]`.

## Main results

* `TauCeti.commute_mul_of_anticommute`: `ν i * ν j` commutes with `ν k`.
* `TauCeti.smul_mul_mul_self_eq_zero`: each summand `a p • (ν p.1 * ν p.2)` squares to zero.
* `TauCeti.pairDividedPower_insert_succ`: the recursion for `u^[k + 1]` when a pair is added to
  `P`.
* `TauCeti.pairDividedPower_smul`, `TauCeti.pairDividedPower_neg`: `(c • u)^[k] = c ^ k • u^[k]`,
  in particular `(-u)^[k] = (-1) ^ k • u^[k]`.
* `TauCeti.factorial_smul_pairDividedPower`: `k ! • u^[k] = u ^ k`.
* `TauCeti.pairDividedPower_mul`: `u^[m] * u^[n] = (m + n).choose m • u^[m + n]`.
* `TauCeti.noncommProd_smul_mul_eq_zero_of_not_nodup`: the product over `t` vanishes when the
  endpoints of the pairs in `t` are not distinct.
* `TauCeti.pairDividedPower_eq_sum_filter_nodup`: `u^[k]` is the sum over the `k`-element sets of
  pairwise disjoint pairs.

## References

* C. Okonek and A. Teleman, *Seiberg–Witten invariants for manifolds with `b₊ = 1` and the
  universal wall crossing formula*, Internat. J. Math. 7 (1996), 811–832.
-/

public section

open scoped Function Nat

namespace TauCeti

variable {ι R A : Type*} [CommSemiring R] [Ring A] [Algebra R A] {ν : ι → A}

section Anticommute

variable (hν : ∀ i j, ν i * ν j + ν j * ν i = 0)
include hν

/-- A product of two anticommuting elements commutes with a third one. -/
theorem commute_mul_of_anticommute (i j k : ι) : Commute (ν i * ν j) (ν k) := by
  have hjk : ν j * ν k = -(ν k * ν j) := eq_neg_of_add_eq_zero_left (hν j k)
  have hik : ν i * ν k = -(ν k * ν i) := eq_neg_of_add_eq_zero_left (hν i k)
  rw [commute_iff_eq]
  calc ν i * ν j * ν k = -(ν i * ν k * ν j) := by simp [mul_assoc, hjk]
    _ = ν k * (ν i * ν j) := by simp [hik, mul_assoc]

/-- The summands `a p • (ν p.1 * ν p.2)` of a quadratic element commute pairwise. -/
theorem pairwise_commute_smul_mul (a : ι × ι → R) :
    Pairwise (Commute on fun p : ι × ι ↦ a p • (ν p.1 * ν p.2)) := fun p q _ ↦
  (((commute_mul_of_anticommute hν p.1 p.2 q.1).mul_right
    (commute_mul_of_anticommute hν p.1 p.2 q.2)).smul_left (a p)).smul_right (a q)

/-- The `k`-th divided power `u^[k]` of `u = ∑_{p ∈ P} a p • (ν p.1 * ν p.2)`: the sum, over the
`k`-element subsets `t` of `P`, of the products of the pairwise commuting summands indexed by
`t`. -/
def pairDividedPower (a : ι × ι → R) (P : Finset (ι × ι)) (k : ℕ) : A :=
  ∑ t ∈ P.powersetCard k,
    t.noncommProd (fun p ↦ a p • (ν p.1 * ν p.2)) ((pairwise_commute_smul_mul hν a).set_pairwise _)

theorem pairDividedPower_def (a : ι × ι → R) (P : Finset (ι × ι)) (k : ℕ) :
    pairDividedPower hν a P k =
      ∑ t ∈ P.powersetCard k, t.noncommProd (fun p ↦ a p • (ν p.1 * ν p.2))
        ((pairwise_commute_smul_mul hν a).set_pairwise _) :=
  (rfl)

/-- The zeroth divided power is `1`. -/
@[simp]
theorem pairDividedPower_zero (a : ι × ι → R) (P : Finset (ι × ι)) :
    pairDividedPower hν a P 0 = 1 := by
  simp [pairDividedPower_def]

/-- The first divided power of `u` is `u` itself. -/
@[simp]
theorem pairDividedPower_one (a : ι × ι → R) (P : Finset (ι × ι)) :
    pairDividedPower hν a P 1 = ∑ p ∈ P, a p • (ν p.1 * ν p.2) := by
  rw [pairDividedPower_def, Finset.powersetCard_one, Finset.sum_map]
  simp

/-- The divided power `u^[k]` vanishes when `k` exceeds the number of pairs in `P`. -/
@[simp]
theorem pairDividedPower_eq_zero_of_card_lt (a : ι × ι → R) {P : Finset (ι × ι)} {k : ℕ}
    (hk : P.card < k) : pairDividedPower hν a P k = 0 := by
  rw [pairDividedPower_def, Finset.powersetCard_eq_empty.2 hk, Finset.sum_empty]

/-- Adding a pair `p ∉ P` to `P` adds `a p • (ν p.1 * ν p.2) * u^[k]` to the divided power
`u^[k + 1]`. -/
theorem pairDividedPower_insert_succ [DecidableEq ι] (a : ι × ι → R) {P : Finset (ι × ι)}
    {p : ι × ι} (hp : p ∉ P) (k : ℕ) :
    pairDividedPower hν a (insert p P) (k + 1) =
      pairDividedPower hν a P (k + 1) + a p • (ν p.1 * ν p.2) * pairDividedPower hν a P k := by
  simp only [pairDividedPower_def]
  exact Finset.sum_noncommProd_powersetCard_succ_insert_of_pairwise_commute hp _
    (pairwise_commute_smul_mul hν a) k

/-- Scaling the coefficients by `c` scales the `k`-th divided power by `c ^ k`. -/
theorem pairDividedPower_smul (c : R) (a : ι × ι → R) (P : Finset (ι × ι)) (k : ℕ) :
    pairDividedPower hν (c • a) P k = c ^ k • pairDividedPower hν a P k := by
  rw [pairDividedPower_def, pairDividedPower_def, Finset.smul_sum]
  refine Finset.sum_congr rfl fun t ht ↦ ?_
  rw [← (Finset.mem_powersetCard.1 ht).2, Finset.smul_noncommProd]
  simp only [Pi.smul_apply, smul_eq_mul, mul_smul]

/-- Negating the coefficients multiplies the `k`-th divided power by `(-1) ^ k`. -/
theorem pairDividedPower_neg {S : Type*} [CommRing S] [Algebra S A] (a : ι × ι → S)
    (P : Finset (ι × ι)) (k : ℕ) :
    pairDividedPower hν (-a) P k = (-1 : S) ^ k • pairDividedPower hν a P k := by
  rw [← pairDividedPower_smul, neg_one_smul]

variable (hν₀ : ∀ i, ν i * ν i = 0)
include hν₀

/-- Left multiplication by `ν i` kills `ν j * ν k` when `i` is `j` or `k`. -/
theorem mul_mul_eq_zero_of_anticommute {i j k : ι} (h : i = j ∨ i = k) :
    ν i * (ν j * ν k) = 0 := by
  rcases h with rfl | rfl
  · rw [← mul_assoc, hν₀, zero_mul]
  · rw [← (commute_mul_of_anticommute hν j i i).eq, mul_assoc, hν₀, mul_zero]

/-- A summand `c • (ν i * ν j)` of a quadratic element squares to zero. -/
theorem smul_mul_mul_self_eq_zero (c : R) (i j : ι) : c • (ν i * ν j) * (c • (ν i * ν j)) = 0 := by
  rw [smul_mul_smul_comm, ← mul_assoc, (commute_mul_of_anticommute hν i j i).eq]
  simp [← mul_assoc, hν₀]

/-- **Divided powers without denominators.** The `k`-th power of the quadratic element
`u = ∑_{p ∈ P} a p • (ν p.1 * ν p.2)` is `k !` times its divided power `u^[k]`. -/
theorem factorial_smul_pairDividedPower (a : ι × ι → R) (P : Finset (ι × ι)) (k : ℕ) :
    k ! • pairDividedPower hν a P k = (∑ p ∈ P, a p • (ν p.1 * ν p.2)) ^ k :=
  (Finset.sum_pow_of_pairwise_commute_of_mul_self_eq_zero P _ (pairwise_commute_smul_mul hν a)
    (fun p _ ↦ smul_mul_mul_self_eq_zero hν hν₀ (a p) p.1 p.2) k).symm

/-- **Multiplication of divided powers.** `u^[m] * u^[n] = (m + n).choose m • u^[m + n]`, with no
division by factorials. -/
theorem pairDividedPower_mul (a : ι × ι → R) (P : Finset (ι × ι)) (m n : ℕ) :
    pairDividedPower hν a P m * pairDividedPower hν a P n =
      (m + n).choose m • pairDividedPower hν a P (m + n) :=
  Finset.sum_noncommProd_powersetCard_mul_of_pairwise_commute_of_mul_self_eq_zero P _
    (pairwise_commute_smul_mul hν a)
    (fun p _ ↦ smul_mul_mul_self_eq_zero hν hν₀ (a p) p.1 p.2) m n

/-- Left multiplication by `ν i` kills the product over a set `t` of pairs as soon as `i` is an
endpoint of a pair in `t`. -/
theorem mul_noncommProd_smul_mul_eq_zero (a : ι × ι → R) {t : Finset (ι × ι)} {i : ι}
    (hi : i ∈ t.val.bind fun p ↦ {p.1, p.2}) :
    ν i * t.noncommProd (fun p ↦ a p • (ν p.1 * ν p.2))
      ((pairwise_commute_smul_mul hν a).set_pairwise _) = 0 := by
  classical
  obtain ⟨p, hp, hip⟩ := Multiset.mem_bind.1 hi
  rw [← Finset.mul_noncommProd_erase t hp, ← mul_assoc, mul_smul_comm]
  simp [mul_mul_eq_zero_of_anticommute hν hν₀ (by simpa using hip : i = p.1 ∨ i = p.2)]

/-- The product over a set `t` of pairs vanishes unless the endpoints of the pairs in `t` are
distinct, that is, unless `t` consists of pairwise disjoint pairs with distinct endpoints. -/
theorem noncommProd_smul_mul_eq_zero_of_not_nodup (a : ι × ι → R) {t : Finset (ι × ι)}
    (ht : ¬ (t.val.bind fun p ↦ {p.1, p.2}).Nodup) :
    t.noncommProd (fun p ↦ a p • (ν p.1 * ν p.2))
      ((pairwise_commute_smul_mul hν a).set_pairwise _) = 0 := by
  classical
  induction t using Finset.induction_on with
  | empty => simp at ht
  | insert p t hp ih =>
    rw [Finset.noncommProd_insert_of_notMem _ _ _ _ hp]
    rw [Finset.insert_val_of_notMem hp, Multiset.cons_bind, Multiset.nodup_add] at ht
    simp only [not_and_or] at ht
    rcases ht with hpp | ht | ht
    · -- The pair `p` has equal endpoints, so its summand vanishes.
      have hpp : p.1 = p.2 := by simpa using hpp
      rw [hpp, hν₀, smul_zero, zero_mul]
    · rw [ih ht, mul_zero]
    · -- An endpoint `i` of `p` is an endpoint of a pair in `t`, so `ν i` kills the product.
      obtain ⟨i, hi, hit⟩ : ∃ i ∈ ({p.1, p.2} : Multiset ι),
          i ∈ t.val.bind fun p ↦ {p.1, p.2} := by
        by_contra! h
        exact ht (Multiset.disjoint_left.2 fun hi hit ↦ h _ hi hit)
      have hi : i = p.1 ∨ i = p.2 := by simpa using hi
      rw [smul_mul_assoc]
      rcases hi with rfl | rfl
      · rw [eq_neg_of_add_eq_zero_left (hν _ _)]
        simp [mul_assoc, mul_noncommProd_smul_mul_eq_zero hν hν₀ a hit]
      · simp [mul_assoc, mul_noncommProd_smul_mul_eq_zero hν hν₀ a hit]

/-- **The divided power as a sum over disjoint pairings.** The `k`-th divided power of
`u = ∑_{p ∈ P} a p • (ν p.1 * ν p.2)` is the sum, over the `k`-element sets `t ⊆ P` whose `2 k`
endpoints are distinct, of the products of the summands indexed by `t`. -/
theorem pairDividedPower_eq_sum_filter_nodup [DecidableEq ι] (a : ι × ι → R)
    (P : Finset (ι × ι)) (k : ℕ) :
    pairDividedPower hν a P k =
      ∑ t ∈ P.powersetCard k with (t.val.bind fun p ↦ {p.1, p.2}).Nodup,
        t.noncommProd (fun p ↦ a p • (ν p.1 * ν p.2))
          ((pairwise_commute_smul_mul hν a).set_pairwise _) := by
  rw [Finset.sum_filter_of_ne fun t _ h ↦ ?_, pairDividedPower_def]
  by_contra ht
  exact h (noncommProd_smul_mul_eq_zero_of_not_nodup hν hν₀ a ht)

end Anticommute

end TauCeti
