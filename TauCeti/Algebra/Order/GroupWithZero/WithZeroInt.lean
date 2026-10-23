/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.NormNum.Basic

/-!
# Discrete arithmetic in `ℤᵐ⁰`

The value group `ℤᵐ⁰` of a discrete valuation is discrete: an element below `1` is at most
`exp (-1)`. This file records consequences of that discreteness for products of integral values,
as they arise when the valuation of a norm is written as a product over the primes above a given
prime.

## Main results

* `TauCeti.lt_one_iff_le_exp_neg_one`: `t < 1 ↔ t ≤ exp (-1)`.
* `TauCeti.eq_one_of_exp_neg_one_le_sq`: an integral value whose square is at least `exp (-1)`
  is `1`.
* `TauCeti.eq_one_and_forall_eq_one_of_exp_neg_one_le_prod`: in a weighted product of integral
  values that is at least `exp (-1)`, at most one factor differs from `1`, and it has weight `1`.
* `TauCeti.two_dvd_log_iff`: a nonzero value has even logarithm if and only if it is a square.
* `TauCeti.two_dvd_log_of_prod_eq_sq`: in a weighted product of nonzero values equal to a square,
  a factor of weight `1` has even logarithm once all the other factors do.

## Provenance

The statements are adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0), revision `3bfe124`,
`EllipticCurves/SelmerGroup.lean`, section `WithZeroArith`, where they are proved for the critical
factor of a local étale algebra; here they are stated for an arbitrary finite weighted product.
-/

public section

open WithZero

namespace TauCeti

/-- In `ℤᵐ⁰`, an element is below `1` exactly when it is at most `exp (-1)`. -/
theorem lt_one_iff_le_exp_neg_one {t : ℤᵐ⁰} : t < 1 ↔ t ≤ exp (-1) := by
  rw [← lt_mul_exp_iff_le exp_ne_zero, ← exp_add, neg_add_cancel, exp_zero]

/-- The product of two elements of `ℤᵐ⁰` that are at most `exp (-1)` is below `exp (-1)`. -/
theorem mul_lt_exp_neg_one {s t : ℤᵐ⁰} (hs : s ≤ exp (-1)) (ht : t ≤ exp (-1)) :
    s * t < exp (-1) :=
  (mul_le_mul' hs ht).trans_lt <| by rw [← exp_add, exp_lt_exp]; norm_num

/-- An integral value in `ℤᵐ⁰` whose square is at least `exp (-1)` is `1`. -/
theorem eq_one_of_exp_neg_one_le_sq {t : ℤᵐ⁰} (h1 : t ≤ 1) (h2 : exp (-1) ≤ t ^ 2) : t = 1 := by
  by_contra ht
  have h := lt_one_iff_le_exp_neg_one.mp (h1.lt_of_ne ht)
  exact (mul_lt_exp_neg_one h h).not_ge (by rwa [← sq])

variable {I : Type*} [Fintype I]

/-- In a weighted product of integral values in `ℤᵐ⁰` that is at least `exp (-1)`, a factor
different from `1` has weight `1`, and all the other factors are `1`. -/
theorem eq_one_and_forall_eq_one_of_exp_neg_one_le_prod {t : I → ℤᵐ⁰} {e : I → ℕ}
    (ht : ∀ i, t i ≤ 1) (he : ∀ i, 1 ≤ e i) (hprod : exp (-1) ≤ ∏ i, t i ^ e i) {i₀ : I}
    (hi₀ : t i₀ ≠ 1) : e i₀ = 1 ∧ ∀ i ≠ i₀, t i = 1 := by
  classical
  have h₀ := lt_one_iff_le_exp_neg_one.mp ((ht i₀).lt_of_ne hi₀)
  have hrest (s : Finset I) : ∏ i ∈ s, t i ^ e i ≤ 1 :=
    Finset.prod_le_one fun i _ ↦ pow_le_one' (ht i) _
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀)] at hprod
  refine ⟨?_, fun j hj ↦ ?_⟩
  · -- a weight of at least `2` would put the product below `t i₀ ^ 2 < exp (-1)`
    by_contra hne
    have h2 : t i₀ ^ e i₀ ≤ t i₀ ^ 2 := pow_le_pow_right_of_le_one' (ht i₀) (by have := he i₀; lia)
    refine (mul_lt_exp_neg_one h₀ h₀).not_ge (hprod.trans ?_)
    rw [← sq]
    exact (mul_le_of_le_one_right' (hrest _)).trans h2
  · -- a second nontrivial factor would put the product below `t i₀ * t j < exp (-1)`
    by_contra hj'
    rw [← Finset.mul_prod_erase _ _ (Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩)] at hprod
    refine (mul_lt_exp_neg_one h₀ (lt_one_iff_le_exp_neg_one.mp ((ht j).lt_of_ne hj'))).not_ge
      (hprod.trans ?_)
    refine mul_le_mul' ((pow_le_pow_right_of_le_one' (ht i₀) (he i₀)).trans_eq (pow_one _)) ?_
    exact (mul_le_of_le_one_right' (hrest _)).trans
      ((pow_le_pow_right_of_le_one' (ht j) (he j)).trans_eq (pow_one _))

/-- A nonzero element of `ℤᵐ⁰` has even logarithm if and only if it is a square. -/
theorem two_dvd_log_iff {s : ℤᵐ⁰} (hs : s ≠ 0) : (2 : ℤ) ∣ log s ↔ ∃ c, s = c ^ 2 := by
  refine ⟨fun ⟨k, hk⟩ ↦ ⟨exp k, ?_⟩, fun ⟨c, hc⟩ ↦ ⟨log c, ?_⟩⟩
  · rw [← exp_log hs, hk, two_mul, exp_add, sq]
  · rw [hc, log_pow, two_nsmul, two_mul]

/-- In a weighted product of nonzero values in `ℤᵐ⁰` equal to a square, a factor of weight `1`
has even logarithm once all the other factors do. -/
theorem two_dvd_log_of_prod_eq_sq {s : I → ℤᵐ⁰} {e : I → ℕ} {c : ℤᵐ⁰} (hs : ∀ i, s i ≠ 0)
    {i₀ : I} (he : e i₀ = 1) (hev : ∀ i ≠ i₀, (2 : ℤ) ∣ log (s i))
    (hprod : ∏ i, s i ^ e i = c ^ 2) : (2 : ℤ) ∣ log (s i₀) := by
  classical
  -- the factors away from `i₀` are squares `d i ^ 2`, so their product is a square `D ^ 2`
  choose! d hd using fun i (hi : i ≠ i₀) ↦ (two_dvd_log_iff (hs i)).mp (hev i hi)
  set D := ∏ i ∈ Finset.univ.erase i₀, d i ^ e i
  have hD : ∏ i ∈ Finset.univ.erase i₀, s i ^ e i = D ^ 2 := by
    rw [← Finset.prod_pow]
    exact Finset.prod_congr rfl fun i hi ↦ by
      rw [hd i (Finset.ne_of_mem_erase hi), ← pow_mul, ← pow_mul, mul_comm]
  have hD0 : D ^ 2 ≠ 0 := hD ▸ Finset.prod_ne_zero_iff.mpr fun i _ ↦ pow_ne_zero _ (hs i)
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀), he, pow_one, hD, ← eq_div_iff hD0,
    ← div_pow] at hprod
  exact (two_dvd_log_iff (hs i₀)).mpr ⟨_, hprod⟩

end TauCeti
