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
  have hp : p.Prime := by
    simpa [p, Rat.HeightOneSpectrum.absNorm_asIdeal] using
      Rat.HeightOneSpectrum.prime_natGenerator 𝔭
  have : Fact p.Prime := ⟨hp⟩
  have hpn : p ∣ n := (Rat.HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd 𝔭).mp hm
  obtain ⟨e, m, hpm, hnm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (NeZero.ne n) p hp.ne_one
  cases e with
  | zero => simp_all
  | succ e =>
    rw [mem_ramifiedPrimes_iff]
    intro hur
    let Q : 𝔭.asIdeal.primesOver (𝓞 F) := Classical.choice inferInstance
    have : Q.1.IsPrime := Q.2.1
    have : Q.1.LiesOver 𝔭.asIdeal := Q.2.2
    have hpQ : (p : 𝓞 F) ∈ Q.1 := by
      have hp𝔭 : (p : 𝓞 ℚ) ∈ 𝔭.asIdeal :=
        (Rat.HeightOneSpectrum.natCast_mem_iff_absNorm_asIdeal_dvd 𝔭).mpr dvd_rfl
      simpa using (Ideal.mem_of_liesOver Q.1 𝔭.asIdeal (p : 𝓞 ℚ)).mp hp𝔭
    have : Q.1.LiesOver (Ideal.span {(p : ℤ)}) := by
      rw [Ideal.liesOver_iff]
      refine Ideal.IsMaximal.eq_of_le (Int.ideal_span_isMaximal_of_prime p)
        Ideal.IsPrime.ne_top' ?_
      simpa [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap] using hpQ
    have := hur Q.1
    have he := Ideal.ramificationIdx_eq_one_of_isUnramifiedAt (R := 𝓞 ℚ) (p := Q.1)
    rw [Ideal.ramificationIdx_ringOfIntegers_rat_eq_int Q.1
      (Ideal.ne_bot_of_liesOver_of_ne_bot 𝔭.ne_bot Q.1),
      IsCyclotomicExtension.Rat.ramificationIdx_eq n F Q.1 hnm hpm] at he
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
