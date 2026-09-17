/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Relative.Artin.Basic
import TauCeti.NumberTheory.NumberField.Quadratic.TotalRamification

/-!
# Genus-field Frobenius at ramified rational primes

A prime of `K = ℚ(√d)` above a rational prime dividing `disc K` is still unramified in the
prime-discriminant compositum over `K`. Its Frobenius therefore has a well-defined Artin class.
This file identifies that class with the narrow ideal class modulo squares,
including the primes excluded by the coprime-discriminant comparison.

Exactly one prime discriminant is divisible by the rational prime below the ideal. All other
coordinates are computed by the usual quadratic residue character. Both the relative Frobenius
sign vector and the genus-character vector have sum zero, which determines the last coordinate.
The ramified prime has residue degree one because the base is quadratic.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §6.A.
* F. Lemmermeyer, *Reciprocity Laws: From Euler to Eisenstein*, §2.2.
-/

public section

open NumberField
open scoped NumberField nonZeroDivisors

namespace TauCeti.Multiquadratic

variable {d : ℤ}

/-- At a rational prime dividing the quadratic discriminant, the genus-field isomorphism
sends every relative Frobenius to the narrow class modulo squares of the prime below it.
Ramification here is over `ℚ`; the extension of the quadratic base by its prime-discriminant
compositum is unramified. -/
theorem autCandidateGenusFieldEquivNarrowElementaryTwoQuotient_frobenius_of_dvd
    (hd : Squarefree d) (hnsq : ¬ IsSquare ((d : ℤ) : ℚ))
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (candidateGenusFieldBase hd)))
    (hv : (TauCeti.rationalPrimeBelow v : ℤ) ∣ fundamentalDiscriminant d)
    (Q : Ideal (𝓞 (candidateGenusField hd))) [Q.LiesOver v.asIdeal]
    (σ : candidateGenusField hd ≃ₐ[candidateGenusFieldBase hd] candidateGenusField hd)
    (hσ : IsArithFrobAt (𝓞 (candidateGenusFieldBase hd)) σ Q) :
    autCandidateGenusFieldEquivNarrowElementaryTwoQuotient hd hnsq σ =
      Multiplicative.ofAdd (TauCeti.elementaryTwoQuotientMk
        (NarrowClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩)) := by
  classical
  have hq := TauCeti.prime_rationalPrimeBelow v
  let _ : Fact (TauCeti.rationalPrimeBelow v).Prime := ⟨hq⟩
  let _ : v.asIdeal.LiesOver (Ideal.span {(TauCeti.rationalPrimeBelow v : ℤ)}) :=
    ⟨(TauCeti.under_eq_span_rationalPrimeBelow v).symm⟩
  -- Total ramification in the quadratic base makes the residue degree one.
  have hram := (mem_ramifiedPrimes_iff_dvd_fundamentalDiscriminant
    (minpoly_candidateGenusFieldBaseGen hd hnsq)
    (adjoin_candidateGenusFieldBaseGen_eq_top hd) hd hq).mpr hv
  have hnorm := NumberField.absNorm_eq_of_mem_ramifiedPrimes
    (finrank_candidateGenusFieldBase hd hnsq) hram v.asIdeal
  let x : candidateGenusFieldRelativeSignSubmodule hd :=
    ⟨candidateGenusFieldRelativeSignPattern hd σ, candidateGenusFieldRelativeSignPattern_mem hd σ⟩
  let y := narrowElementaryTwoQuotientEquivRelativeSign hd hnsq
    (TauCeti.elementaryTwoQuotientMk
      (NarrowClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩))
  have hgood (P : {P // P ∈ genusPrimeDiscriminants hd})
      (hP : ¬ (TauCeti.rationalPrimeBelow v : ℤ) ∣ P.val) : x.val P = y.val P := by
    rw [narrowElementaryTwoQuotientEquivRelativeSign_apply_coe]
    exact candidateGenusFieldRelativeSignPattern_frobenius_eq_genusChar hd hnsq
      v.asIdeal hnorm Q σ hσ P hP
  -- The rational prime divides exactly one prime-discriminant factor.
  obtain ⟨hs, heven, hprod⟩ := genusPrimeDiscriminants_spec hd
  have hex : ∃ P ∈ genusPrimeDiscriminants hd,
      (TauCeti.rationalPrimeBelow v : ℤ) ∣ P := by
    rw [← hprod, Prime.dvd_finsetProd_iff (Nat.prime_iff_prime_int.mp hq)] at hv
    exact hv
  obtain ⟨P₀, hP₀, hdiv₀⟩ := hex
  let P : {P // P ∈ genusPrimeDiscriminants hd} := ⟨P₀, hP₀⟩
  have haway (R : {P // P ∈ genusPrimeDiscriminants hd}) (hne : R ≠ P) :
      x.val R = y.val R := by
    apply hgood R
    intro hdiv
    apply hne
    apply Subtype.ext
    exact injOn_primeDiscriminantPrime hs heven R.property P.property
      (((natCast_dvd_primeDiscriminant_iff (hs R.val R.property) hq).mp hdiv).symm.trans
        ((natCast_dvd_primeDiscriminant_iff (hs P₀ hP₀) hq).mp hdiv₀))
  -- Equality away from that factor, together with parity, recovers its coordinate.
  have hxy : x = y := by
    have hxsum := (mem_candidateGenusFieldRelativeSignSubmodule_iff hd x.val).mp x.property
    have hysum := (mem_candidateGenusFieldRelativeSignSubmodule_iff hd y.val).mp y.property
    have herase : ∑ R ∈ Finset.univ.erase P, x.val R =
        ∑ R ∈ Finset.univ.erase P, y.val R :=
      Finset.sum_congr rfl fun R hR ↦ haway R (Finset.mem_erase.mp hR).1
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ P), herase] at hxsum
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ P)] at hysum
    have hP : x.val P = y.val P := add_left_cancel (hxsum.trans hysum.symm)
    apply Subtype.ext
    funext R
    by_cases hR : R = P
    · simpa only [hR] using hP
    · exact haway R hR
  rw [autCandidateGenusFieldEquivNarrowElementaryTwoQuotient_apply]
  have heq := congrArg (narrowElementaryTwoQuotientEquivRelativeSign hd hnsq).symm hxy
  rw [LinearEquiv.symm_apply_apply] at heq
  exact congrArg Multiplicative.ofAdd heq

/-- At every rational prime, including those dividing the quadratic discriminant, the
relative genus-field Frobenius corresponds to the narrow prime class modulo squares. -/
theorem autCandidateGenusFieldEquivNarrowElementaryTwoQuotient_frobenius_at_prime
    (hd : Squarefree d) (hnsq : ¬ IsSquare ((d : ℤ) : ℚ))
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (candidateGenusFieldBase hd)))
    (Q : Ideal (𝓞 (candidateGenusField hd))) [Q.IsPrime] [Q.LiesOver v.asIdeal]
    (σ : candidateGenusField hd ≃ₐ[candidateGenusFieldBase hd] candidateGenusField hd)
    (hσ : IsArithFrobAt (𝓞 (candidateGenusFieldBase hd)) σ Q) :
    autCandidateGenusFieldEquivNarrowElementaryTwoQuotient hd hnsq σ =
      Multiplicative.ofAdd (TauCeti.elementaryTwoQuotientMk
        (NarrowClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩)) := by
  by_cases hv : (TauCeti.rationalPrimeBelow v : ℤ) ∣ fundamentalDiscriminant d
  · exact autCandidateGenusFieldEquivNarrowElementaryTwoQuotient_frobenius_of_dvd
      hd hnsq v hv Q σ hσ
  · apply autCandidateGenusFieldEquivNarrowElementaryTwoQuotient_frobenius_of_not_dvd
      hd hnsq v _ Q σ hσ
    intro hdiv
    exact hv hdiv

end TauCeti.Multiquadratic
