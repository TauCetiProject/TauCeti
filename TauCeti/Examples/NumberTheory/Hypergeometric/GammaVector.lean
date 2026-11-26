/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Hypergeometric.GammaVector

/-!
# Examples of gamma vectors

* `A = {2, 2, 2, 2}`, `B = {1, 1, 1, 1}`, the LMFDB family `A2.2.2.2_B1.1.1.1`: `γ(2) = 4` and
  `γ(1) = -8`, so the gamma multiset is `[-1^8, 2^4]`. Reading `γ` from `B` instead would give
  `[1^8, -2^4]`.
* `A = {1}`, `B = {2}`: `Φ_1 / Φ_2 = (X - 1)² / (X² - 1)`, so `γ(1) = 2` and `γ(2) = -1`. This is
  read off from the defining identity `Φ_1 · (X² - 1) = Φ_2 · (X - 1)²` by uniqueness.
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

end TauCeti.Hypergeometric.Examples
