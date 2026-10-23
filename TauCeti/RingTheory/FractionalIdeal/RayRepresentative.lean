/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.DedekindDomain.Factorization
import TauCeti.RingTheory.DedekindDomain.SInteger.Basic
import TauCeti.RingTheory.Ideal.CoprimeCoset

/-!
# Integral representatives with a multiplier congruent to one

For a Dedekind domain `R` with fraction field `K`, a fractional ideal integral at the primes
dividing an ideal `𝔪` has a common denominator congruent to one modulo `𝔪`. If its multiplicities
at those primes vanish, the resulting integral ideal is still coprime to `𝔪`. Thus a fractional
ideal prime to a finite modulus can be replaced by an integral ideal without changing its ray
class. No finite residue fields or finite class group are required.

The construction uses finite generation of fractional ideals, the denominator ideals
`Algebra.denIdeal`, and `IsDedekindDomain.denIdeal_not_le` to obtain a common denominator
coprime to the modulus. `Ideal.isCoprime_iff_exists_mem_and_sub_one_mem` then supplies the
congruent multiplier. The unit modulus is included: in that case any nonzero denominator works.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VI, §1.
* S. Lang, *Algebraic Number Theory*, Chapter VI, §1.
-/

public section

open IsDedekindDomain
open scoped nonZeroDivisors

namespace FractionalIdeal

variable {R K : Type*} [CommRing R] [IsDedekindDomain R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- A fractional ideal integral at the primes dividing `𝔪` admits a nonzero common denominator
congruent to one modulo `𝔪`. Scaling by it produces an integral ideal. -/
theorem exists_coeIdeal_eq_spanSingleton_mul_of_valuation_le_one
    (I : FractionalIdeal R⁰ K) (𝔪 : Ideal R)
    (hI : ∀ (v : HeightOneSpectrum R), v.asIdeal ∣ 𝔪 → ∀ x ∈ I, v.valuation K x ≤ 1) :
    ∃ (a : R) (J : Ideal R), a ≠ 0 ∧ a - 1 ∈ 𝔪 ∧
      (J : FractionalIdeal R⁰ K) = spanSingleton R⁰ (algebraMap R K a) * I := by
  classical
  obtain ⟨s, hs⟩ := I.fg_of_isNoetherianRing le_rfl
  let D : Ideal R := ⨅ x ∈ s, Algebra.denIdeal K x
  -- A global denominator lies in every generator's denominator ideal.
  obtain ⟨d, hd, hdx⟩ := I.isFractional
  have hdD : d ∈ D := by
    simp only [D, Submodule.mem_iInf]
    intro x hx
    rw [Algebra.mem_denIdeal_iff]
    obtain ⟨r, hr⟩ := hdx x (hs ▸ Submodule.subset_span hx)
    exact ⟨r, by simpa [Algebra.smul_def] using hr.symm⟩
  have hD : D ≠ ⊥ := fun h ↦ nonZeroDivisors.ne_zero hd (by simpa [h] using hdD)
  have hcop : IsCoprime D 𝔪 := by
    apply IsCoprime.symm
    refine Ideal.isCoprime_biInf fun x hx ↦
      Ideal.coprime_of_no_prime_ge fun P hmP hden hP ↦ ?_
    have hP0 : P ≠ ⊥ := fun h0 ↦ Algebra.denIdeal_ne_bot K x
      (le_bot_iff.mp (h0 ▸ hden))
    let v : HeightOneSpectrum R := ⟨P, hP, hP0⟩
    have hxI : x ∈ I := by
      rw [← mem_coe, ← hs]
      exact Submodule.subset_span hx
    exact denIdeal_not_le K
      (hI v (Ideal.dvd_iff_le.mpr hmP) x hxI) hden
  have hex : ∃ a : R, a ≠ 0 ∧ a ∈ D ∧ a - 1 ∈ 𝔪 := by
    by_cases hm : 𝔪 = ⊤
    · obtain ⟨a, ha, ha0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hD
      exact ⟨a, ha0, ha, hm ▸ Submodule.mem_top⟩
    · obtain ⟨a, haD, ham⟩ := Ideal.isCoprime_iff_exists_mem_and_sub_one_mem.mp hcop
      refine ⟨a, ?_, haD, ham⟩
      rintro rfl
      exact hm (Ideal.eq_top_of_isUnit_mem 𝔪 (by simpa using ham) isUnit_one.neg)
  obtain ⟨a, ha0, haD, ham⟩ := hex
  have haD' : ∀ x ∈ s, a ∈ Algebra.denIdeal K x := by
    simpa only [D, Submodule.mem_iInf] using haD
  have hmul : spanSingleton R⁰ (algebraMap R K a) * I ≤ 1 := by
    rw [spanSingleton_mul_le_iff]
    -- Check the generators, then extend by linearity to their span.
    have hle : (I : Submodule R K) ≤
        (1 : Submodule R K).comap (Algebra.lmul R K (algebraMap R K a)) := by
      rw [← hs, Submodule.span_le]
      intro x hx
      obtain ⟨r, hr⟩ := (Algebra.mem_denIdeal_iff K).mp (haD' x hx)
      exact Submodule.mem_one.mpr ⟨r, hr.symm⟩
    intro x hx
    exact (mem_one_iff R⁰).mpr (Submodule.mem_one.mp (hle hx))
  obtain ⟨J, hJ⟩ := le_one_iff_exists_coeIdeal.mp hmul
  exact ⟨a, J, ha0, ham, hJ⟩

/-- **The finite moving lemma for fractional ideals.** A nonzero fractional ideal prime to `𝔪`
has an integral representative coprime to `𝔪`, obtained by multiplication by a nonzero element
of `R` congruent to one modulo `𝔪`. -/
theorem exists_coeIdeal_eq_spanSingleton_mul_and_isCoprime
    (I : FractionalIdeal R⁰ K) (hI0 : I ≠ 0) (𝔪 : Ideal R)
    (hI : ∀ v : HeightOneSpectrum R, v.asIdeal ∣ 𝔪 → count K v I = 0) :
    ∃ (a : R) (J : Ideal R), a ≠ 0 ∧ a - 1 ∈ 𝔪 ∧ J ≠ ⊥ ∧ IsCoprime J 𝔪 ∧
      (J : FractionalIdeal R⁰ K) = spanSingleton R⁰ (algebraMap R K a) * I := by
  obtain ⟨a, J, ha0, ham, hJ⟩ := exists_coeIdeal_eq_spanSingleton_mul_of_valuation_le_one I 𝔪
    (fun v hv x hx ↦ I.valuation_le_one_of_mem_of_count_nonneg v (by rw [hI v hv]) hx)
  have haK : algebraMap R K a ≠ 0 := by simpa using (IsFractionRing.injective R K).ne ha0
  have hJ0 : J ≠ ⊥ := coeIdeal_ne_zero.mp (hJ ▸
    mul_ne_zero (spanSingleton_ne_zero_iff.mpr haK) hI0)
  have hcount (v : HeightOneSpectrum R) (hv : v.asIdeal ∣ 𝔪) : count K v J = 0 := by
    have hav : a ∉ v.asIdeal := by
      intro hav
      exact v.isPrime.ne_top ((Ideal.eq_top_iff_one v.asIdeal).mpr
        (by simpa using v.asIdeal.sub_mem hav (Ideal.le_of_dvd hv ham)))
    rw [hJ, count_mul K v (spanSingleton_ne_zero_iff.mpr haK) hI0, hI v hv,
      add_zero, count_spanSingleton_algebraMap_eq_zero_of_notMem K v hav]
  refine ⟨a, J, ha0, ham, hJ0, Ideal.coprime_of_no_prime_ge ?_, hJ⟩
  intro P hJP hmP hP
  have hP0 : P ≠ ⊥ := fun h0 ↦ hJ0 (le_bot_iff.mp (h0 ▸ hJP))
  let v : HeightOneSpectrum R := ⟨P, hP, hP0⟩
  have hzero := hcount v (Ideal.dvd_iff_le.mpr hmP)
  rw [count_coe K v hJ0, Int.natCast_eq_zero] at hzero
  exact (Associates.count_ne_zero_iff_dvd hJ0 v.irreducible).mpr
    (Ideal.dvd_iff_le.mpr hJP) hzero

end FractionalIdeal
