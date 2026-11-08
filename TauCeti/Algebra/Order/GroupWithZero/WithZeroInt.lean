/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.GroupWithZero.Canonical
import Mathlib.Algebra.BigOperators.Group.Finset.Lemmas
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
* `TauCeti.two_dvd_log_iff`: a value has even logarithm if and only if it is a square.
* `TauCeti.two_dvd_log_of_prod_eq_sq`: in a weighted product of values equal to a square, a
  factor of weight `1` has even logarithm once all the other factors are nonzero with even
  logarithm.

## Provenance

The statements are adapted from Michael Stoll's `EllipticCurves` project
(`github.com/MichaelStollBayreuth/EllipticCurves`, Apache-2.0), revision `3bfe124`,
`EllipticCurves/SelmerGroup.lean`, section `WithZeroArith`, where they are proved for the critical
factor of a local étale algebra; here they are stated for a weighted product over any finset.
-/

public section

open WithZero

namespace TauCeti

/-- In `ℤᵐ⁰`, an element is below `1` exactly when it is at most `exp (-1)`. -/
theorem lt_one_iff_le_exp_neg_one {t : ℤᵐ⁰} : t < 1 ↔ t ≤ exp (-1) := by
  rw [← lt_mul_exp_iff_le exp_ne_zero, ← exp_add, neg_add_cancel, exp_zero]

/-- The product of two elements of `ℤᵐ⁰` below `1` is below `exp (-1)`. -/
theorem mul_lt_exp_neg_one {s t : ℤᵐ⁰} (hs : s < 1) (ht : t < 1) : s * t < exp (-1) :=
  (mul_le_mul' (lt_one_iff_le_exp_neg_one.mp hs) (lt_one_iff_le_exp_neg_one.mp ht)).trans_lt <| by
    simp [← exp_add]

/-- An integral value in `ℤᵐ⁰` whose square is at least `exp (-1)` is `1`. -/
theorem eq_one_of_exp_neg_one_le_sq {t : ℤᵐ⁰} (h1 : t ≤ 1) (h2 : exp (-1) ≤ t ^ 2) : t = 1 :=
  h1.eq_of_not_lt fun h ↦ (mul_lt_exp_neg_one h h).not_ge (sq t ▸ h2)

variable {I : Type*} {s : Finset I}

/-- In a weighted product of integral values in `ℤᵐ⁰` that is at least `exp (-1)`, a factor
different from `1` has weight `1`, and all the other factors are `1`. -/
theorem eq_one_and_forall_eq_one_of_exp_neg_one_le_prod {t : I → ℤᵐ⁰} {e : I → ℕ}
    (ht : ∀ i ∈ s, t i ≤ 1) (he : ∀ i ∈ s, 1 ≤ e i) (hprod : exp (-1) ≤ ∏ i ∈ s, t i ^ e i)
    {i₀ : I} (hi₀s : i₀ ∈ s) (hi₀ : t i₀ ≠ 1) : e i₀ = 1 ∧ ∀ i ∈ s, i ≠ i₀ → t i = 1 := by
  classical
  have h₀ := (ht i₀ hi₀s).lt_of_ne hi₀
  -- the product is at most its subproduct over any `u ⊆ s`, as all factors are at most `1`
  have hsub {u : Finset I} (hu : u ⊆ s) : ∏ i ∈ s, t i ^ e i ≤ ∏ i ∈ u, t i ^ e i :=
    Finset.prod_le_prod_of_subset_of_le_one hu fun i hi _ ↦ pow_le_one' (ht i hi) _
  have hpow {i : I} (hi : i ∈ s) : t i ^ e i ≤ t i :=
    (pow_le_pow_right_of_le_one' (ht i hi) (he i hi)).trans_eq (pow_one _)
  refine ⟨(he i₀ hi₀s).antisymm' ?_, fun j hj hji₀ ↦ ?_⟩
  · -- a weight of at least `2` would put the product below `t i₀ ^ 2 < exp (-1)`
    by_contra! h2
    refine (mul_lt_exp_neg_one h₀ h₀).not_ge <|
      hprod.trans <| (hsub (Finset.singleton_subset_iff.2 hi₀s)).trans ?_
    rw [Finset.prod_singleton, ← sq]
    exact pow_le_pow_right_of_le_one' (ht i₀ hi₀s) h2
  · -- a second nontrivial factor would put the product below `t i₀ * t j < exp (-1)`
    by_contra hj'
    refine (mul_lt_exp_neg_one h₀ ((ht j hj).lt_of_ne hj')).not_ge <|
      hprod.trans <| (hsub (Finset.insert_subset hi₀s (Finset.singleton_subset_iff.2 hj))).trans ?_
    rw [Finset.prod_pair hji₀.symm]
    exact mul_le_mul' (hpow hi₀s) (hpow hj)

/-- An element of `ℤᵐ⁰` has even logarithm if and only if it is a square. -/
theorem two_dvd_log_iff {x : ℤᵐ⁰} : (2 : ℤ) ∣ log x ↔ ∃ c, x = c ^ 2 := by
  obtain rfl | hx := eq_or_ne x 0
  · exact iff_of_true ⟨0, by simp⟩ ⟨0, by simp⟩
  refine ⟨fun ⟨k, hk⟩ ↦ ⟨exp k, ?_⟩, fun ⟨c, hc⟩ ↦ ⟨log c, ?_⟩⟩
  · rw [← exp_log hx, hk, two_mul, exp_add, sq]
  · rw [hc, log_pow, two_nsmul, two_mul]

/-- In a weighted product of values in `ℤᵐ⁰` equal to a square, a factor of weight `1` has even
logarithm once all the other factors are nonzero with even logarithm. -/
theorem two_dvd_log_of_prod_eq_sq {x : I → ℤᵐ⁰} {e : I → ℕ} {c : ℤᵐ⁰} {i₀ : I}
    (hx : ∀ i ∈ s, i ≠ i₀ → x i ≠ 0) (hi₀s : i₀ ∈ s) (he : e i₀ = 1)
    (hev : ∀ i ∈ s, i ≠ i₀ → (2 : ℤ) ∣ log (x i)) (hprod : ∏ i ∈ s, x i ^ e i = c ^ 2) :
    (2 : ℤ) ∣ log (x i₀) := by
  classical
  -- the factors away from `i₀` are squares, so their product is a square `D ^ 2`
  obtain ⟨D, hD⟩ := (Finset.isSquare_prod (s := s.erase i₀) (fun i ↦ x i ^ e i) fun i hi ↦
    ((isSquare_iff_exists_sq _).mpr <| two_dvd_log_iff.mp <|
      hev i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi)).pow _).exists_sq
  have hD0 : D ^ 2 ≠ 0 := hD ▸ Finset.prod_ne_zero_iff.mpr fun i hi ↦
    pow_ne_zero _ (hx i (Finset.mem_of_mem_erase hi) (Finset.ne_of_mem_erase hi))
  rw [← Finset.mul_prod_erase _ _ hi₀s, he, pow_one, hD, ← eq_div_iff hD0, ← div_pow] at hprod
  exact two_dvd_log_iff.mpr ⟨_, hprod⟩

end TauCeti
