/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.ResidueDegree
public import TauCeti.RingTheory.DedekindDomain.Totient
import Mathlib.LinearAlgebra.FreeModule.IdealQuotient

/-!
# Residue units modulo a rational integer

For a number field `K` of degree `n` and a positive integer `f`, this file counts the units of
`𝓞 K ⧸ f 𝓞 K` prime by prime. Euler's totient for ideals
(`Ideal.card_units_quotient_mul_prod_absNorm`) expresses `#(𝓞 K ⧸ f 𝓞 K)ˣ` through the absolute
norms of the primes of `𝓞 K` dividing `f`. Grouping those primes by the rational prime below them
shows that the count is multiplicative up to the expected powers:

```text
#(𝓞 K ⧸ f 𝓞 K)ˣ · ∏_{p ∣ f} p ^ n = f ^ n · ∏_{p ∣ f} #(𝓞 K ⧸ p 𝓞 K)ˣ.
```

For a single rational prime `p`, the same totient is indexed by the primes of `𝓞 K` above `p`,
which is the form in which the splitting of `p` computes `#(𝓞 K ⧸ p 𝓞 K)ˣ`. In a quadratic field
this gives the residue-unit factor in the class number formula for the order `ℤ + f 𝓞 K`.

## Main results

* `TauCeti.NumberField.card_units_quotient_span_natCast_mul_prod_absNorm`: for a rational prime
  `p`, `#(𝓞 K ⧸ p 𝓞 K)ˣ · ∏_{𝔭 ∣ p} N 𝔭 = p ^ n · ∏_{𝔭 ∣ p} (N 𝔭 - 1)`.
* `TauCeti.NumberField.card_units_quotient_span_natCast_mul_prod_pow`: the reduction of
  `#(𝓞 K ⧸ f 𝓞 K)ˣ` to the primes dividing `f`.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §7, proof of Theorem 7.24.
-/

public section

open IsDedekindDomain Ideal Module
open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K]

/-- **Residue units modulo a rational prime.** If `p` is a rational prime and `n = [K : ℚ]`, then
`#(𝓞 K ⧸ p 𝓞 K)ˣ · ∏_{𝔭 ∣ p} N 𝔭 = p ^ n · ∏_{𝔭 ∣ p} (N 𝔭 - 1)`, the products running over the
primes of `𝓞 K` above `p`. -/
theorem card_units_quotient_span_natCast_mul_prod_absNorm {p : ℕ} [hp : Fact p.Prime]
    [Fintype ((span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K))] :
    Nat.card (𝓞 K ⧸ span {(p : 𝓞 K)})ˣ *
        ∏ 𝔭 : (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K), absNorm 𝔭.1 =
      p ^ finrank ℚ K * ∏ 𝔭 : (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K), (absNorm 𝔭.1 - 1) := by
  have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  have hspan : (span {(p : ℤ)} : Ideal ℤ) ≠ 0 := by simpa using hp0
  have : Finite (𝓞 K ⧸ span {(p : 𝓞 K)}) :=
    Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hp.out.ne_zero)
  have hmem (v : HeightOneSpectrum (𝓞 K)) :
      v ∈ primesDividing K p hp0 ↔ v.asIdeal ∣ span {(p : 𝓞 K)} := by
    rw [mem_primesDividing, v.asIdeal_dvd_span_natCast_iff, Int.natCast_dvd_natCast]
  have hmap : (span {(p : ℤ)} : Ideal ℤ).map (algebraMap ℤ (𝓞 K)) = span {(p : 𝓞 K)} := by
    simp [Ideal.map_span]
  -- The primes dividing `p 𝓞 K` are the primes of `𝓞 K` above `p`.
  have hreindex (g : Ideal (𝓞 K) → ℕ) : ∏ v ∈ primesDividing K p hp0, g v.asIdeal =
      ∏ 𝔭 : (span {(p : ℤ)} : Ideal ℤ).primesOver (𝓞 K), g 𝔭.1 := by
    have hmem' (v : HeightOneSpectrum (𝓞 K)) : v ∈ primesDividing K p hp0 ↔
        v.asIdeal ∣ (span {(p : ℤ)} : Ideal ℤ).map (algebraMap ℤ (𝓞 K)) := by
      rw [hmap, hmem]
    rw [← Finset.prod_coe_sort]
    exact Fintype.prod_equiv ((Equiv.subtypeEquivRight hmem').trans
      (HeightOneSpectrum.equivPrimesOver (𝓞 K) hspan)) _ _ fun _ ↦ rfl
  have h := card_units_quotient_mul_prod_absNorm (span {(p : 𝓞 K)}) hmem
  rwa [absNorm_span_natCast, NumberField.RingOfIntegers.rank, hreindex (absNorm ·),
    hreindex (absNorm · - 1)] at h

/-- **Residue units modulo `f`, prime by prime.** For a positive integer `f` and `n = [K : ℚ]`,
`#(𝓞 K ⧸ f 𝓞 K)ˣ · ∏_{p ∣ f} p ^ n = f ^ n · ∏_{p ∣ f} #(𝓞 K ⧸ p 𝓞 K)ˣ`: the number of residue units
modulo `f` is determined by the numbers of residue units modulo the primes dividing `f`. -/
theorem card_units_quotient_span_natCast_mul_prod_pow {f : ℕ} (hf : f ≠ 0) :
    Nat.card (𝓞 K ⧸ span {(f : 𝓞 K)})ˣ * ∏ p ∈ f.primeFactors, p ^ finrank ℚ K =
      f ^ finrank ℚ K * ∏ p ∈ f.primeFactors, Nat.card (𝓞 K ⧸ span {(p : 𝓞 K)})ˣ := by
  classical
  have hf0 : (f : ℤ) ≠ 0 := by exact_mod_cast hf
  set S := primesDividing K f hf0
  have hS (v : HeightOneSpectrum (𝓞 K)) : v ∈ S ↔ v.asIdeal ∣ span {(f : 𝓞 K)} := by
    rw [mem_primesDividing, v.asIdeal_dvd_span_natCast_iff, Int.natCast_dvd_natCast]
  -- The primes dividing `f 𝓞 K` with rational prime `p` below are the primes dividing `p 𝓞 K`.
  have hfib {p : ℕ} (hp : p ∈ f.primeFactors) (v : HeightOneSpectrum (𝓞 K)) :
      v ∈ S.filter (rationalPrimeBelow · = p) ↔ v.asIdeal ∣ span {(p : 𝓞 K)} := by
    rw [Finset.mem_filter, hS, v.asIdeal_dvd_span_natCast_iff, v.asIdeal_dvd_span_natCast_iff,
      Nat.prime_dvd_prime_iff_eq (prime_rationalPrimeBelow v) (Nat.prime_of_mem_primeFactors hp)]
    exact ⟨And.right, fun h ↦ ⟨h ▸ Nat.dvd_of_mem_primeFactors hp, h⟩⟩
  have hmaps : ∀ v ∈ S, rationalPrimeBelow v ∈ f.primeFactors := fun v hv ↦
    Nat.mem_primeFactors.mpr ⟨prime_rationalPrimeBelow v,
      (v.asIdeal_dvd_span_natCast_iff f).mp ((hS v).mp hv), hf⟩
  have hsplit (g : HeightOneSpectrum (𝓞 K) → ℕ) : ∏ v ∈ S, g v =
      ∏ p ∈ f.primeFactors, ∏ v ∈ S.filter (rationalPrimeBelow · = p), g v :=
    (Finset.prod_fiberwise_of_maps_to hmaps g).symm
  have : Finite (𝓞 K ⧸ span {(f : 𝓞 K)}) := Ideal.finiteQuotientOfFreeOfNeBot _ (by simpa using hf)
  have hF := card_units_quotient_mul_prod_absNorm (span {(f : 𝓞 K)}) hS
  rw [absNorm_span_natCast, NumberField.RingOfIntegers.rank, hsplit, hsplit] at hF
  have hP {p : ℕ} (hp : p ∈ f.primeFactors) := by
    have : Finite (𝓞 K ⧸ span {(p : 𝓞 K)}) := Ideal.finiteQuotientOfFreeOfNeBot _
      (by simpa using (Nat.prime_of_mem_primeFactors hp).ne_zero)
    have h := card_units_quotient_mul_prod_absNorm (span {(p : 𝓞 K)}) (hfib hp)
    rwa [absNorm_span_natCast, NumberField.RingOfIntegers.rank] at h
  have hpos : 0 < ∏ p ∈ f.primeFactors,
      ∏ v ∈ S.filter (rationalPrimeBelow · = p), absNorm v.asIdeal :=
    Finset.prod_pos fun p _ ↦ Finset.prod_pos fun v _ ↦ by
      rw [absNorm_eq_rationalPrimeBelow_pow]
      exact pow_pos (prime_rationalPrimeBelow v).pos _
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc _ = (Nat.card (𝓞 K ⧸ span {(f : 𝓞 K)})ˣ * ∏ p ∈ f.primeFactors,
        ∏ v ∈ S.filter (rationalPrimeBelow · = p), absNorm v.asIdeal) *
          ∏ p ∈ f.primeFactors, p ^ finrank ℚ K := by ring
    _ = f ^ finrank ℚ K * ∏ p ∈ f.primeFactors, (p ^ finrank ℚ K *
        ∏ v ∈ S.filter (rationalPrimeBelow · = p), (absNorm v.asIdeal - 1)) := by
      rw [hF, Finset.prod_mul_distrib]
      ring
    _ = f ^ finrank ℚ K * ∏ p ∈ f.primeFactors, (Nat.card (𝓞 K ⧸ span {(p : 𝓞 K)})ˣ *
        ∏ v ∈ S.filter (rationalPrimeBelow · = p), absNorm v.asIdeal) := by
      rw [Finset.prod_congr rfl fun p hp ↦ (hP hp).symm]
    _ = _ := by
      rw [Finset.prod_mul_distrib]
      ring

end TauCeti.NumberField
