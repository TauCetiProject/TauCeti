/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Multiquadratic.CandidateGenusField.Relative.Artin.Basic

/-!
# Artin reciprocity for the imaginary quadratic genus field

For negative squarefree `d`, put `K = ℚ(√d)` and let `K_gen` be the prime-discriminant compositum,
which is the genus field of `K` (`isGenusField_candidateGenusField`). Since `K` is totally complex,
its narrow and ordinary class groups agree, and the genus-field isomorphism takes the classical form
`autCandidateGenusFieldEquivElementaryTwoQuotient : Gal(K_gen/K) ≃* Cl(K)/Cl(K)²`.

This file identifies that isomorphism with the inverse Artin map in its ordinary form:

* at a prime `v` of `K` prime to `2 · disc K`, every Frobenius element above `v` is sent to the
  class of `v` in `Cl(K)/Cl(K)²`;
* on fractional ideals prime to `2 · disc K`, the Artin automorphism of `I` is sent to the class of
  `I` in `Cl(K)/Cl(K)²`.

Consequently the Frobenius at `v` is trivial exactly when the ideal class of `v` is a square, and
the Artin automorphism of `I` is trivial exactly when the ideal class of `I` is a square: the
kernel of the Artin map is the principal genus. Surjectivity of the Artin map does not depend on
the signature and is `artinHomAway_candidateGenusField_surjective`.

## Main results

* `TauCeti.Multiquadratic.autCandidateGenusFieldEquivElementaryTwoQuotient_frobenius_of_not_dvd`:
  the imaginary genus-field isomorphism sends a Frobenius element to the ordinary class of the
  prime below it.
* `TauCeti.Multiquadratic.isArithFrobAt_candidateGenusField_eq_one_iff_of_neg`: the Frobenius at
  such a prime is trivial exactly when its ordinary ideal class is a square.
* `TauCeti.Multiquadratic.autCandidateGenusFieldEquivElementaryTwoQuotient_artinHomAway`: the
  imaginary genus-field isomorphism sends the Artin automorphism of an ideal to its ordinary class.
* `TauCeti.Multiquadratic.artinHomAway_candidateGenusField_eq_one_iff_of_neg`: the Artin
  automorphism of an ideal is trivial exactly when its ordinary ideal class is a square.

## References

* D. A. Cox, *Primes of the Form x² + ny²*, §6.A.
* F. Lemmermeyer, *Reciprocity Laws: From Euler to Eisenstein*, §2.2.
-/

public section

open NumberField
open scoped IsMulCommutative NumberField nonZeroDivisors

namespace TauCeti.Multiquadratic

variable {d : ℤ}

/-- **The imaginary genus-field isomorphism sends every Frobenius to the class of the prime below
it.** Let `d < 0` be squarefree, let `v` be a prime of `K = ℚ(√d)` whose rational prime does not
divide `2 · disc K`, and let `Q` be a prime of the genus field above `v`. Every relative arithmetic
Frobenius `σ` at `Q` is sent by `Gal(K_gen/K) ≃* Cl(K)/Cl(K)²` to the ordinary ideal class of `v`
modulo squares. -/
theorem autCandidateGenusFieldEquivElementaryTwoQuotient_frobenius_of_not_dvd
    (hd : Squarefree d) (hneg : d < 0)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (candidateGenusFieldBase hd)))
    (hv : ¬ ((TauCeti.rationalPrimeBelow v : ℤ) ∣ 2 * fundamentalDiscriminant d))
    (Q : Ideal (𝓞 (candidateGenusField hd))) [Q.IsPrime] [Q.LiesOver v.asIdeal]
    (σ : candidateGenusField hd ≃ₐ[candidateGenusFieldBase hd] candidateGenusField hd)
    (hσ : IsArithFrobAt (𝓞 (candidateGenusFieldBase hd)) σ Q) :
    autCandidateGenusFieldEquivElementaryTwoQuotient hd hneg σ =
      Multiplicative.ofAdd
        (TauCeti.elementaryTwoQuotientMk
          (ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩)) := by
  simp only [autCandidateGenusFieldEquivElementaryTwoQuotient_apply]
  rw [autCandidateGenusFieldEquivNarrowElementaryTwoQuotient_frobenius_of_not_dvd hd _ v hv Q σ hσ]
  simp

/-- **A prime is in the principal genus exactly when its Frobenius in the genus field is
trivial.** For negative squarefree `d` and a prime `v` of `K = ℚ(√d)` prime to `2 · disc K`, a
relative arithmetic Frobenius at any prime of the genus field above `v` is the identity exactly
when the ideal class of `v` is a square in `Cl(K)`. -/
theorem isArithFrobAt_candidateGenusField_eq_one_iff_of_neg
    (hd : Squarefree d) (hneg : d < 0)
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 (candidateGenusFieldBase hd)))
    (hv : ¬ ((TauCeti.rationalPrimeBelow v : ℤ) ∣ 2 * fundamentalDiscriminant d))
    (Q : Ideal (𝓞 (candidateGenusField hd))) [Q.IsPrime] [Q.LiesOver v.asIdeal]
    (σ : candidateGenusField hd ≃ₐ[candidateGenusFieldBase hd] candidateGenusField hd)
    (hσ : IsArithFrobAt (𝓞 (candidateGenusFieldBase hd)) σ Q) :
    σ = 1 ↔ IsSquare
      (ClassGroup.mk0 (⟨v.asIdeal, mem_nonZeroDivisors_iff_ne_zero.mpr v.ne_bot⟩ :
        (Ideal (𝓞 (candidateGenusFieldBase hd)))⁰)) := by
  rw [← (autCandidateGenusFieldEquivElementaryTwoQuotient hd hneg).map_eq_one_iff,
    autCandidateGenusFieldEquivElementaryTwoQuotient_frobenius_of_not_dvd hd hneg v hv Q σ hσ,
    ofAdd_eq_one, TauCeti.elementaryTwoQuotientMk_eq_zero_iff]

/-- **The imaginary genus-field isomorphism inverts the ideal-theoretic Artin map.** Let `d < 0` be
squarefree, let `K = ℚ(√d)`, and let `S` be any finite set of primes of `𝓞 K` containing every
prime whose residue characteristic divides `2 · disc K`. On invertible fractional ideals of
multiplicity zero along `S`, the isomorphism `Gal(K_gen/K) ≃* Cl(K)/Cl(K)²` carries the Artin
automorphism of `I` to the ordinary ideal class of `I` modulo squares. -/
theorem autCandidateGenusFieldEquivElementaryTwoQuotient_artinHomAway
    (hd : Squarefree d) (hneg : d < 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 (candidateGenusFieldBase hd))))
    (hS : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 (candidateGenusFieldBase hd)),
      (TauCeti.rationalPrimeBelow v : ℤ) ∣ 2 * fundamentalDiscriminant d → v ∈ S)
    (I : NumberFieldArithmetic.idealsAway (K := candidateGenusFieldBase hd) S) :
    autCandidateGenusFieldEquivElementaryTwoQuotient hd hneg
        (NumberFieldArithmetic.artinHomAway IsMulCommutative.is_comm.comm S
          (fun v _ Q _ _ ↦ isUnramifiedIn_candidateGenusField hd
            (not_isSquare_of_neg (by exact_mod_cast hneg)) v.asIdeal Q
            inferInstance inferInstance) I) =
      Multiplicative.ofAdd
        (TauCeti.elementaryTwoQuotientMk
          (ClassGroup.mk (candidateGenusFieldBase hd)
            (I : (FractionalIdeal (𝓞 (candidateGenusFieldBase hd))⁰
              (candidateGenusFieldBase hd))ˣ))) := by
  simp only [autCandidateGenusFieldEquivElementaryTwoQuotient_apply]
  rw [autCandidateGenusFieldEquivNarrowElementaryTwoQuotient_artinHomAway hd _ S hS I]
  simp

/-- **The imaginary genus-field Artin map is trivial exactly on the principal genus.** For negative
squarefree `d`, let `S` be any finite set of primes of `𝓞 K` containing every prime whose residue
characteristic divides `2 · disc K`. An invertible fractional ideal of `K = ℚ(√d)` prime to `S`
has trivial Artin automorphism in `Gal(K_gen/K)` precisely when its ideal class is a square in
`Cl(K)`. -/
theorem artinHomAway_candidateGenusField_eq_one_iff_of_neg
    (hd : Squarefree d) (hneg : d < 0)
    (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 (candidateGenusFieldBase hd))))
    (hS : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 (candidateGenusFieldBase hd)),
      (TauCeti.rationalPrimeBelow v : ℤ) ∣ 2 * fundamentalDiscriminant d → v ∈ S)
    (I : NumberFieldArithmetic.idealsAway (K := candidateGenusFieldBase hd) S) :
    NumberFieldArithmetic.artinHomAway IsMulCommutative.is_comm.comm S
        (fun v _ Q _ _ ↦ isUnramifiedIn_candidateGenusField hd
          (not_isSquare_of_neg (by exact_mod_cast hneg)) v.asIdeal Q
          inferInstance inferInstance) I = 1 ↔
      IsSquare (ClassGroup.mk (candidateGenusFieldBase hd)
        (I : (FractionalIdeal (𝓞 (candidateGenusFieldBase hd))⁰
          (candidateGenusFieldBase hd))ˣ)) := by
  rw [← (autCandidateGenusFieldEquivElementaryTwoQuotient hd hneg).map_eq_one_iff,
    autCandidateGenusFieldEquivElementaryTwoQuotient_artinHomAway hd hneg S hS I,
    ofAdd_eq_one, TauCeti.elementaryTwoQuotientMk_eq_zero_iff]

end TauCeti.Multiquadratic
