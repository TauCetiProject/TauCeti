/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Discriminant.RamifiedSupport
public import TauCeti.NumberTheory.NumberField.Ideal.ArtinMap

/-!
# The Artin map away from the ramified primes

Let `L/K` be a finite abelian extension of number fields. The relative discriminant identifies a
canonical finite set of excluded primes: outside `NumberField.ramifiedSupport K L`, every prime
of `L` is unramified over `K`. Specializing the ideal-theoretic Artin map to this set gives the
classical Artin map on fractional ideals prime to the relative discriminant.

The carrier remains `NumberFieldArithmetic.idealsAway`. In particular, this file introduces no
second notion of ideals prime to the discriminant; it only supplies the unramifiedness theorem
needed by `NumberFieldArithmetic.artinHomAway` and names the resulting specialization.

## Main results

* `TauCeti.NumberField.isUnramifiedAway_ramifiedSupport`: primes outside the ramified support are
  unramified throughout the extension.
* `TauCeti.NumberFieldArithmetic.artinHomAway_ramifiedSupport`: the Artin map on fractional
  ideals prime to the relative discriminant.
* `TauCeti.NumberFieldArithmetic.artinHomAway_ramifiedSupport_apply_prime`: this map takes a prime
  outside the ramified support to its arithmetic Frobenius.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter III, §2 and Chapter VI, §7.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped NumberField nonZeroDivisors

namespace TauCeti

namespace NumberField

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **Every prime outside the ramified support is unramified.** If a finite place `v` does not
divide the relative discriminant of `L/K`, then every prime of `L` above `v` is unramified over
`K`. This is the unramified-away hypothesis used to specialize the Artin map. -/
theorem isUnramifiedAway_ramifiedSupport :
    ∀ v : HeightOneSpectrum (𝓞 K), v ∉ ramifiedSupport K L →
      ∀ (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal],
        Algebra.IsUnramifiedAt (𝓞 K) Q := by
  intro v hv Q _ _
  by_contra hQ
  apply hv
  rw [mem_ramifiedSupport, TauCeti.dvd_relDiscr_iff_exists_not_isUnramifiedAt v.ne_bot]
  exact ⟨⟨Q, inferInstance, inferInstance⟩, hQ⟩

end NumberField

namespace NumberFieldArithmetic

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- **The Artin map away from the ramified support.** For an abelian Galois extension `L/K`,
this is the multiplicative Artin map on fractional ideals whose multiplicity vanishes at every
prime dividing the relative discriminant. -/
noncomputable def artinHomAway_ramifiedSupport
    (hab : ∀ σ τ : L ≃ₐ[K] L, Commute σ τ) :
    idealsAway (K := K) (NumberField.ramifiedSupport K L) →* (L ≃ₐ[K] L) :=
  artinHomAway (L := L) hab (NumberField.ramifiedSupport K L)
    NumberField.isUnramifiedAway_ramifiedSupport

/-- **The Artin map away from the ramified support takes an unramified prime to Frobenius.** -/
theorem artinHomAway_ramifiedSupport_apply_prime
    (hab : ∀ σ τ : L ≃ₐ[K] L, Commute σ τ)
    (I : idealsAway (K := K) (NumberField.ramifiedSupport K L))
    (v : HeightOneSpectrum (𝓞 K)) (hv : v ∉ NumberField.ramifiedSupport K L)
    (hI : ((I : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      (v.asIdeal : FractionalIdeal (𝓞 K)⁰ K))
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver v.asIdeal] (σ : L ≃ₐ[K] L)
    (hσ : IsArithFrobAt (𝓞 K) σ Q) :
    artinHomAway_ramifiedSupport hab I = σ :=
  artinHomAway_apply_prime hab (NumberField.ramifiedSupport K L)
    NumberField.isUnramifiedAway_ramifiedSupport I v hv hI Q σ hσ

end NumberFieldArithmetic

end TauCeti
