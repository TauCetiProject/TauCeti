/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum.Prime

/-!
# Small-prime splitting in the fifth cyclotomic field

In a fifth cyclotomic field, the primes `2`, `3`, and `7` are inert, `19` has two primes of
residue degree two, and `11` splits completely. Each statement gives the number of primes,
ramification index, and residue degree. The calculations use Mathlib's cyclotomic splitting
law and the Galois fundamental identity. Mathlib already gives total ramification at `5`.

## Reference

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 2.
-/

public section
noncomputable section

open Ideal NumberField
open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {5} ℚ K]

private theorem count_mul_order (p : ℕ) [Fact p.Prime] (hp : p ≠ 5) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard * orderOf (p : ZMod 5) = 4 := by
  have hp5 : ¬ p ∣ 5 := by
    intro h
    exact hp ((Nat.prime_dvd_prime_iff_eq Fact.out (by norm_num : Nat.Prime 5)).mp h)
  let _ : IsGalois ℚ K := IsCyclotomicExtension.isGalois {5} ℚ K
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn
    (span {(p : ℤ)}) (𝓞 K) Gal(K/ℚ)
  rw [IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd p K hp5,
    IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd p K hp5,
    IsGalois.card_aut_eq_finrank ℚ K, IsCyclotomicExtension.Rat.finrank 5 K,
    Nat.totient_prime (by norm_num : Nat.Prime 5)] at h
  simpa using h

private theorem orderOf_two : orderOf (2 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by omega)]
  constructor
  · decide
  · intro m _ _
    interval_cases m
    all_goals decide

private theorem orderOf_three : orderOf (3 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by omega)]
  constructor
  · decide
  · intro m _ _
    interval_cases m
    all_goals decide

private theorem orderOf_seven : orderOf (7 : ZMod 5) = 4 := by
  have h : (7 : ZMod 5) = 2 := by decide
  simpa only [h] using orderOf_two

private theorem orderOf_nineteen : orderOf (19 : ZMod 5) = 2 := by
  rw [orderOf_eq_iff (by omega)]
  constructor
  · decide
  · intro m _ _
    interval_cases m
    all_goals decide

private theorem orderOf_eleven : orderOf (11 : ZMod 5) = 1 := by
  rw [orderOf_eq_one_iff]
  decide

/-- In a fifth cyclotomic field, `2` is inert: it has one prime, with `e = 1` and `f = 4`. -/
theorem fifthCyclotomic_splitting_two :
    (primesOver (span {(2 : ℤ)}) (𝓞 K)).ncard = 1 ∧
      (span {(2 : ℤ)}).ramificationIdxIn (𝓞 K) = 1 ∧
      (span {(2 : ℤ)}).inertiaDegIn (𝓞 K) = 4 := by
  let _ : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  have hc := count_mul_order (K := K) 2 (by norm_num)
  norm_num only [Nat.cast_ofNat, orderOf_two] at hc
  refine ⟨by omega, ?_, ?_⟩
  · exact IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd (m := 5) 2 K (by norm_num)
  · simpa [orderOf_two] using
      (IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd (m := 5) 2 K (by norm_num))

/-- In a fifth cyclotomic field, `3` is inert: it has one prime, with `e = 1` and `f = 4`. -/
theorem fifthCyclotomic_splitting_three :
    (primesOver (span {(3 : ℤ)}) (𝓞 K)).ncard = 1 ∧
      (span {(3 : ℤ)}).ramificationIdxIn (𝓞 K) = 1 ∧
      (span {(3 : ℤ)}).inertiaDegIn (𝓞 K) = 4 := by
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hc := count_mul_order (K := K) 3 (by norm_num)
  norm_num only [Nat.cast_ofNat, orderOf_three] at hc
  refine ⟨by omega, ?_, ?_⟩
  · exact IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd (m := 5) 3 K (by norm_num)
  · simpa [orderOf_three] using
      (IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd (m := 5) 3 K (by norm_num))

/-- In a fifth cyclotomic field, `7` is inert: it has one prime, with `e = 1` and `f = 4`. -/
theorem fifthCyclotomic_splitting_seven :
    (primesOver (span {(7 : ℤ)}) (𝓞 K)).ncard = 1 ∧
      (span {(7 : ℤ)}).ramificationIdxIn (𝓞 K) = 1 ∧
      (span {(7 : ℤ)}).inertiaDegIn (𝓞 K) = 4 := by
  let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hc := count_mul_order (K := K) 7 (by norm_num)
  norm_num only [Nat.cast_ofNat, orderOf_seven] at hc
  refine ⟨by omega, ?_, ?_⟩
  · exact IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd (m := 5) 7 K (by norm_num)
  · simpa [orderOf_seven] using
      (IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd (m := 5) 7 K (by norm_num))

/-- In a fifth cyclotomic field, `19` has two primes, each with `e = 1` and `f = 2`. -/
theorem fifthCyclotomic_splitting_nineteen :
    (primesOver (span {(19 : ℤ)}) (𝓞 K)).ncard = 2 ∧
      (span {(19 : ℤ)}).ramificationIdxIn (𝓞 K) = 1 ∧
      (span {(19 : ℤ)}).inertiaDegIn (𝓞 K) = 2 := by
  let _ : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  have hc := count_mul_order (K := K) 19 (by norm_num)
  norm_num only [Nat.cast_ofNat, orderOf_nineteen] at hc
  refine ⟨by omega, ?_, ?_⟩
  · exact IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd (m := 5) 19 K (by norm_num)
  · simpa [orderOf_nineteen] using
      (IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd (m := 5) 19 K (by norm_num))

/-- In a fifth cyclotomic field, `11` splits completely into four primes of degree one. -/
theorem fifthCyclotomic_splitting_eleven :
    (primesOver (span {(11 : ℤ)}) (𝓞 K)).ncard = 4 ∧
      (span {(11 : ℤ)}).ramificationIdxIn (𝓞 K) = 1 ∧
      (span {(11 : ℤ)}).inertiaDegIn (𝓞 K) = 1 := by
  let _ : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  have hc := count_mul_order (K := K) 11 (by norm_num)
  norm_num only [Nat.cast_ofNat, orderOf_eleven] at hc
  refine ⟨by omega, ?_, ?_⟩
  · exact IsCyclotomicExtension.Rat.ramificationIdxIn_eq_of_not_dvd (m := 5) 11 K (by norm_num)
  · simpa [orderOf_eleven] using
      (IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd (m := 5) 11 K (by norm_num))

end TauCeti.NumberField

end
