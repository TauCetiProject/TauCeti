/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Hypergeometric.Pochhammer

/-!
# Examples of gamma vectors

* `A = {2, 2, 2, 2}`, `B = {1, 1, 1, 1}`, the LMFDB family `A2.2.2.2_B1.1.1.1`: `γ(2) = 4` and
  `γ(1) = -8`, so the gamma multiset is `[-1^8, 2^4]`. Reading `γ` from `B` instead would give
  `[1^8, -2^4]`.
* `A = {1}`, `B = {2}`: `Φ_1 / Φ_2 = (X - 1)² / (X² - 1)`, so `γ(1) = 2` and `γ(2) = -1`. This is
  read off from the defining identity `Φ_1 · (X² - 1) = Φ_2 · (X - 1)²` by uniqueness.
* `A = {30}`, `B = {5, 3, 2, 1}`, Bober's family, has scale `1007769600000`.
  Its gamma exponents give the factorial ratio `(30n)! n! / ((6n)! (10n)! (15n)!)`.
-/

public section

open Polynomial TauCeti.Hypergeometric

namespace TauCeti.Hypergeometric.Examples

/-- The datum `A = {2, 2, 2, 2}`, `B = {1, 1, 1, 1}` of the LMFDB family `A2.2.2.2_B1.1.1.1`. -/
def quartic : CyclotomicData where
  A := {2, 2, 2, 2}
  B := {1, 1, 1, 1}
  pos := by decide
  disjoint := Multiset.disjoint_left.2 (by simp)
  totient_sum_eq := by simp

theorem gamma_two_quartic : quartic.gamma 2 = 4 := by
  simp [CyclotomicData.gamma_def, quartic, Multiset.filter_singleton]

theorem gamma_one_quartic : quartic.gamma 1 = -8 := by
  simp [CyclotomicData.gamma_def, quartic, Multiset.filter_singleton,
    ArithmeticFunction.moebius_apply_prime Nat.prime_two]

-- The gamma multiset of `A2.2.2.2_B1.1.1.1` contains `2` four times and `-1` eight times.
example : quartic.gammaMultiset.count 2 = 4 ∧ quartic.gammaMultiset.count (-1) = 8 := by
  simp [gamma_two_quartic, gamma_one_quartic, Int.sign_eq_one_of_pos]

/-- The datum `A = {1}`, `B = {2}`. -/
def oneTwo : CyclotomicData where
  A := {1}
  B := {2}
  pos := by decide
  disjoint := Multiset.disjoint_left.2 (by simp)
  totient_sum_eq := by simp

/-- The gamma vector of `A = {1}`, `B = {2}` is `γ(1) = 2`, `γ(2) = -1`, read off from the
identity `Φ_1 · (X² - 1) = Φ_2 · (X - 1)²` by uniqueness. -/
theorem gamma_oneTwo : oneTwo.gamma = fun n ↦ if n = 1 then 2 else if n = 2 then -1 else 0 := by
  refine (oneTwo.eq_gamma_of_phiA_mul_prod_eq_phiB_mul_prod (R := ℚ) (I := {1, 2}) ?_ ?_).symm
  · intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    simp [hn.1, hn.2]
  · simp [CyclotomicData.phiA_def, CyclotomicData.phiB_def, oneTwo, cyclotomic_two]
    ring

example : quartic.gammaScale = 256 := by
  have hs : quartic.gammaSupport = {1, 2} := by
    rw [CyclotomicData.gammaSupport_eq_biUnion_divisors]
    decide
  norm_num [CyclotomicData.gammaScale_def, hs, gamma_two_quartic]

-- At n = 1 the quotient for parameters 1 and 1/2 is 2.
example : oneTwo.gammaScale = 1 / 4 ∧
    (oneTwo.toParameters.α.map fun a ↦ (ascPochhammer ℚ 1).eval (rep a)).prod /
      (oneTwo.toParameters.β.map fun b ↦ (ascPochhammer ℚ 1).eval (rep b)).prod = 2 := by
  have hs : oneTwo.gammaSupport = {1, 2} := by
    rw [CyclotomicData.gammaSupport_eq_biUnion_divisors]
    decide
  have hM : oneTwo.gammaScale = 1 / 4 := by
    norm_num [CyclotomicData.gammaScale_def, hs, gamma_oneTwo]
  refine ⟨hM, ?_⟩
  rw [oneTwo.prod_ascPochhammer_div_eq_mul_prod_factorial]
  norm_num [hM, hs, gamma_oneTwo, Nat.factorial]

/-- Bober's degree-eight datum `A = {30}`, `B = {5, 3, 2, 1}`. -/
def bober : CyclotomicData where
  A := {30}
  B := {5, 3, 2, 1}
  pos := by decide
  disjoint := Multiset.disjoint_left.2 (by simp)
  totient_sum_eq := by decide

/-- The divisor support of Bober's datum consists of the eight divisors of 30. -/
theorem gammaSupport_bober : bober.gammaSupport = {1, 2, 3, 5, 6, 10, 15, 30} := by
  rw [CyclotomicData.gammaSupport_eq_biUnion_divisors]
  decide

/-- On its divisor support Bober's gamma vector has two positive entries, at
`1` and `30`, and three negative entries, at `6`, `10`, and `15`. -/
theorem gamma_bober : bober.gamma = fun m ↦
    if m ∈ ({1, 30} : Finset ℕ) then 1 else if m ∈ ({6, 10, 15} : Finset ℕ) then -1 else 0 := by
  funext m
  by_cases hm : m ∈ bober.gammaSupport
  · rw [gammaSupport_bober] at hm
    fin_cases hm <;> rw [CyclotomicData.gamma_def] <;> decide +kernel
  · rw [bober.gamma_eq_zero_of_notMem hm]
    rw [gammaSupport_bober] at hm
    simp_all

theorem gammaScale_bober : bober.gammaScale = 1007769600000 := by
  norm_num [CyclotomicData.gammaScale_def, gammaSupport_bober, gamma_bober]

example : bober.gammaPosCount = 2 ∧ bober.gammaNegCount = 3 := by
  norm_num [CyclotomicData.gammaPosCount_eq_sum, CyclotomicData.gammaNegCount_eq_sum,
    gammaSupport_bober, gamma_bober]

-- The coefficient identity for Bober's family, with all five factorials visible.
example (n : ℕ) :
    (bober.toParameters.α.map fun a ↦ (ascPochhammer ℚ n).eval (rep a)).prod /
        (bober.toParameters.β.map fun b ↦ (ascPochhammer ℚ n).eval (rep b)).prod =
      (1007769600000 : ℚ) ^ (-(n : ℤ)) *
        ((30 * n).factorial * (n.factorial : ℚ) /
          ((6 * n).factorial * ((10 * n).factorial : ℚ) * (15 * n).factorial)) := by
  rw [bober.prod_ascPochhammer_div_eq_mul_prod_factorial, gammaScale_bober]
  congr 1
  norm_num [gammaSupport_bober, gamma_bober, div_eq_mul_inv]
  ring

end TauCeti.Hypergeometric.Examples
