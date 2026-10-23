/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Cyclotomic.Splitting
import Mathlib.Tactic.NormNum.Prime

/-!
# Small-prime splitting in the fifth cyclotomic field

In a fifth cyclotomic field, the primes `2`, `3`, and `7` are inert, `19` has two primes of
residue degree two, and `11` splits completely. The calculations use Mathlib's cyclotomic
splitting law and the Galois fundamental identity. Mathlib already gives total ramification
at `5`.

## Reference

* L. C. Washington, *Introduction to Cyclotomic Fields*, Chapter 2.
-/

public section
noncomputable section

open Ideal NumberField
open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

variable [IsCyclotomicExtension {5} ℚ K]

private theorem ncard_primesOver_eq_of_orderOf (p : ℕ) [Fact p.Prime] (hp : ¬ p ∣ 5)
    {f g : ℕ} (hf : orderOf (p : ZMod 5) = f) (hfg : ∀ n : ℕ, n * f = 4 → n = g) :
    (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = g := by
  have hc := ncard_primesOver_mul_orderOf_eq_totient (K := K) p hp
  rw [hf, Nat.totient_prime (by norm_num : Nat.Prime 5)] at hc
  exact hfg _ (by simpa using hc)

private theorem orderOf_two : orderOf (2 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by omega)]
  decide

private theorem orderOf_three : orderOf (3 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by omega)]
  decide

private theorem orderOf_seven : orderOf (7 : ZMod 5) = 4 := by
  have h : (7 : ZMod 5) = 2 := by decide
  simpa only [h] using orderOf_two

private theorem orderOf_nineteen : orderOf (19 : ZMod 5) = 2 :=
  orderOf_eq_prime_iff.mpr ⟨by decide, by decide⟩

private theorem orderOf_eleven : orderOf (11 : ZMod 5) = 1 := by
  rw [orderOf_eq_one_iff]
  decide

/-- There is one prime above `2` in a fifth cyclotomic field. -/
@[simp] theorem ncard_primesOver_two_fifthCyclotomic :
    (primesOver (span {(2 : ℤ)}) (𝓞 K)).ncard = 1 := by
  exact ncard_primesOver_eq_of_orderOf (K := K) 2 (by norm_num) orderOf_two (by omega)

/-- The residue degree of `2` in a fifth cyclotomic field is four. -/
@[simp] theorem inertiaDegIn_two_fifthCyclotomic :
    (span {(2 : ℤ)}).inertiaDegIn (𝓞 K) = 4 := by
  simpa [orderOf_two] using
    (IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd (m := 5) 2 K (by norm_num))

/-- There is one prime above `3` in a fifth cyclotomic field. -/
@[simp] theorem ncard_primesOver_three_fifthCyclotomic :
    (primesOver (span {(3 : ℤ)}) (𝓞 K)).ncard = 1 := by
  exact ncard_primesOver_eq_of_orderOf (K := K) 3 (by norm_num) orderOf_three (by omega)

/-- The residue degree of `3` in a fifth cyclotomic field is four. -/
@[simp] theorem inertiaDegIn_three_fifthCyclotomic :
    (span {(3 : ℤ)}).inertiaDegIn (𝓞 K) = 4 := by
  simpa [orderOf_three] using
    (IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd (m := 5) 3 K (by norm_num))

/-- There is one prime above `7` in a fifth cyclotomic field. -/
@[simp] theorem ncard_primesOver_seven_fifthCyclotomic :
    (primesOver (span {(7 : ℤ)}) (𝓞 K)).ncard = 1 := by
  let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  exact ncard_primesOver_eq_of_orderOf (K := K) 7 (by norm_num) orderOf_seven (by omega)

/-- The residue degree of `7` in a fifth cyclotomic field is four. -/
@[simp] theorem inertiaDegIn_seven_fifthCyclotomic :
    (span {(7 : ℤ)}).inertiaDegIn (𝓞 K) = 4 := by
  let _ : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  simpa [orderOf_seven] using
    (IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd (m := 5) 7 K (by norm_num))

/-- There are two primes above `19` in a fifth cyclotomic field. -/
@[simp] theorem ncard_primesOver_nineteen_fifthCyclotomic :
    (primesOver (span {(19 : ℤ)}) (𝓞 K)).ncard = 2 := by
  let _ : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  exact ncard_primesOver_eq_of_orderOf (K := K) 19 (by norm_num) orderOf_nineteen (by omega)

/-- The residue degree of `19` in a fifth cyclotomic field is two. -/
@[simp] theorem inertiaDegIn_nineteen_fifthCyclotomic :
    (span {(19 : ℤ)}).inertiaDegIn (𝓞 K) = 2 := by
  let _ : Fact (Nat.Prime 19) := ⟨by norm_num⟩
  simpa [orderOf_nineteen] using
    (IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd (m := 5) 19 K (by norm_num))

/-- There are four primes above `11` in a fifth cyclotomic field. -/
@[simp] theorem ncard_primesOver_eleven_fifthCyclotomic :
    (primesOver (span {(11 : ℤ)}) (𝓞 K)).ncard = 4 := by
  let _ : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  exact ncard_primesOver_eq_of_orderOf (K := K) 11 (by norm_num) orderOf_eleven (by omega)

/-- The residue degree of `11` in a fifth cyclotomic field is one. -/
@[simp] theorem inertiaDegIn_eleven_fifthCyclotomic :
    (span {(11 : ℤ)}).inertiaDegIn (𝓞 K) = 1 := by
  let _ : Fact (Nat.Prime 11) := ⟨by norm_num⟩
  simpa [orderOf_eleven] using
    (IsCyclotomicExtension.Rat.inertiaDegIn_eq_of_not_dvd (m := 5) 11 K (by norm_num))

end TauCeti.NumberField

end
