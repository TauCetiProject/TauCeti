/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.RamifiedPrimes
public import Mathlib.NumberTheory.Cyclotomic.Basic
import TauCeti.NumberTheory.NumberField.Ideal.IntegersRat
import Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal

/-!
# Ramification at primes dividing a cyclotomic level

For a cyclotomic extension of `ℚ`, a prime dividing the level ramifies, provided that a prime
of norm two divides the level to at least the second power. This excludes primes dividing the
level from Frobenius fibres when the level is not congruent to two modulo four.

## References

* L. Washington, *Introduction to Cyclotomic Fields*, Chapter 2.
* `IsCyclotomicExtension.Rat.ramificationIdx_eq` in
  `Mathlib.NumberTheory.NumberField.Cyclotomic.Ideal` supplies the ramification-index formula.
-/

public section

open scoped NumberField
open IsDedekindDomain (HeightOneSpectrum)

namespace NumberField.Chebotarev

/-- Every prime dividing a cyclotomic level ramifies, provided the level is divisible by four
when the prime has norm two. -/
theorem mem_ramifiedPrimes_of_natCast_mem (F : Type*) [Field F] [NumberField F]
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ F] {𝔭 : HeightOneSpectrum (𝓞 ℚ)}
    (hn : Ideal.absNorm 𝔭.asIdeal = 2 → 4 ∣ n) (hm : (n : 𝓞 ℚ) ∈ 𝔭.asIdeal) :
    𝔭 ∈ ramifiedPrimes ℚ F := by
  let p := Ideal.absNorm 𝔭.asIdeal
  have hp : p.Prime := Rat.HeightOneSpectrum.prime_absNorm_asIdeal 𝔭
  have : Fact p.Prime := ⟨hp⟩
  have hpn : p ∣ n := (Rat.HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd 𝔭).mp hm
  obtain ⟨e, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (NeZero.ne n) p hp.ne_one
  cases e with
  | zero => simp_all
  | succ e =>
    rw [mem_ramifiedPrimes_iff]
    intro hur
    let Q : 𝔭.asIdeal.primesOver (𝓞 F) := Classical.choice inferInstance
    have : Q.val.IsPrime := Q.property.1
    have : Q.val.LiesOver 𝔭.asIdeal := Q.property.2
    have : Q.val.LiesOver (Ideal.span {(p : ℤ)}) :=
      Rat.HeightOneSpectrum.liesOver_span_absNorm 𝔭 Q.val
    have := hur Q.val
    have he := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 ℚ) (p := Q.val)
    rw [Ideal.ramificationIdx_ringOfIntegers_rat_eq_int Q.val,
      IsCyclotomicExtension.Rat.ramificationIdx_eq n F Q.val hnm hpm] at he
    have hp2 : p = 2 := by
      have := Nat.eq_one_of_mul_eq_one_left he
      have := hp.two_le
      omega
    have hfour := hn hp2
    rw [hp2] at he hnm hpm
    have he0 : e = 0 := by
      have := Nat.eq_one_of_mul_eq_one_right he
      simpa using this
    subst e
    simp only [zero_add, pow_one] at hnm
    omega

end NumberField.Chebotarev
