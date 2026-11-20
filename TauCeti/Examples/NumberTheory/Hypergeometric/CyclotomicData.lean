/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Hypergeometric.CyclotomicData

/-!
# Examples of cyclotomic data

* `A = {2, 2}`, `B = {1, 1}`, the LMFDB family `A2.2_B1.1` of the Legendre curves: degree `2`,
  `Φ_A = (X + 1)²`, `Φ_B = (X - 1)²`, constant coefficients `1 = (-1)^0` and `1 = (-1)^2`.
* `A = {2, 2}`, `B = {2, 1}` has the common index `2`, and `A = {3}`, `B = {1}` has totient sums
  `2 ≠ 1`; neither is a cyclotomic datum.
* `A = {4}`, `B = {2, 1}`: `Φ_A = X² + 1` and `Φ_B = X² - 1` are coprime over `ℚ` but not over
  `ℤ`, since `Φ_A - Φ_B = 2`.
-/

public section

open Polynomial TauCeti.Hypergeometric

namespace TauCeti.Hypergeometric.Examples

/-- The datum `A = {2, 2}`, `B = {1, 1}` of the Legendre family. -/
def legendre : CyclotomicData where
  A := {2, 2}
  B := {1, 1}
  pos := by decide
  disjoint := Multiset.disjoint_left.2 (by simp)
  totient_sum_eq := by simp

example : legendre.degree = 2 := by
  simp [← CyclotomicData.sum_map_totient_A, legendre]

example : legendre.phiA ℤ = (X + 1) ^ 2 := by
  simp [CyclotomicData.phiA_def, legendre, cyclotomic_two, sq]

example : legendre.phiB ℤ = (X - 1) ^ 2 := by
  simp [CyclotomicData.phiB_def, legendre, sq]

example : legendre.multOneA = 0 ∧ legendre.multOneB = 2 := by
  simp [← CyclotomicData.count_one_A, ← CyclotomicData.count_one_B, legendre]

example : (legendre.phiA ℤ).coeff 0 = 1 ∧ (legendre.phiB ℤ).coeff 0 = 1 := by
  simp [← CyclotomicData.count_one_A, ← CyclotomicData.count_one_B, legendre]

-- `{2, 2}` and `{2, 1}` share the index `2`.
example : ¬ Disjoint ({2, 2} : Multiset ℕ) {2, 1} := by
  simp [Multiset.disjoint_left]

-- `{3}` and `{1}` have totient sums `2` and `1`.
example : (({3} : Multiset ℕ).map Nat.totient).sum ≠ (({1} : Multiset ℕ).map Nat.totient).sum := by
  simp [Nat.totient_prime Nat.prime_three]

/-- The datum `A = {4}`, `B = {2, 1}`, the cyclotomic form of the parameters
`TauCeti.Hypergeometric.Examples.quarter`. -/
def cyclotomicQuarter : CyclotomicData where
  A := {4}
  B := {2, 1}
  pos := by decide
  disjoint := Multiset.disjoint_left.2 (by simp)
  totient_sum_eq := by decide

theorem phiA_cyclotomicQuarter : cyclotomicQuarter.phiA ℤ = X ^ 2 + 1 := by
  have h : cyclotomic 4 ℤ = 1 + X ^ 2 := by
    simpa [Finset.sum_range_succ] using
      cyclotomic_prime_pow_eq_geom_sum (R := ℤ) Nat.prime_two (n := 1)
  simp [CyclotomicData.phiA_def, cyclotomicQuarter, h, add_comm]

theorem phiB_cyclotomicQuarter : cyclotomicQuarter.phiB ℤ = X ^ 2 - 1 := by
  simp [CyclotomicData.phiB_def, cyclotomicQuarter, cyclotomic_two]
  ring

-- Over `ℚ` the cyclotomic products of `cyclotomicQuarter` are coprime.
example : IsCoprime (cyclotomicQuarter.phiA ℚ) (cyclotomicQuarter.phiB ℚ) :=
  cyclotomicQuarter.isCoprime_phiA_phiB ℚ

-- Over `ℤ` they are not: evaluating a Bézout identity at `1` would give `2 * u(1) = 1`.
example : ¬ IsCoprime (cyclotomicQuarter.phiA ℤ) (cyclotomicQuarter.phiB ℤ) := by
  rintro ⟨u, v, h⟩
  have h1 := congrArg (eval 1) h
  simp only [phiA_cyclotomicQuarter, phiB_cyclotomicQuarter, eval_add, eval_mul, eval_pow, eval_X,
    eval_one, eval_sub, one_pow, sub_self, mul_zero, add_zero] at h1
  omega

end TauCeti.Hypergeometric.Examples
