/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Discriminant.RamifiedSupport.Basic
public import TauCeti.NumberTheory.NumberField.Ideal.ArtinMap

/-!
# The Artin map away from the ramified primes

Let `L/K` be a finite abelian extension of number fields. The relative discriminant identifies a
canonical finite set of excluded primes: outside `NumberField.ramifiedSupport K L`, every prime
of `L` is unramified over `K`. Specializing the ideal-theoretic Artin map to this set gives the
classical Artin map on fractional ideals prime to the relative discriminant.

The carrier remains `NumberFieldArithmetic.idealsAway`. In particular, this file introduces no
second notion of ideals prime to the discriminant; it only feeds the ramified support and its
unramifiedness theorem `NumberField.isUnramifiedAway_ramifiedSupport` into
`NumberFieldArithmetic.artinHomAway` and names the resulting specialization.

## Main definitions

* `TauCeti.NumberFieldArithmetic.artinHomAway_ramifiedSupport`: the Artin map on fractional
  ideals prime to the relative discriminant.

## Main results

* `TauCeti.NumberFieldArithmetic.artinHomAway_ramifiedSupport_def`: this map is the generic Artin
  map at the ramified support.
* `TauCeti.NumberFieldArithmetic.artinHomAway_ramifiedSupport_apply_prime`: this map takes a prime
  outside the ramified support to its arithmetic Frobenius.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter III, §2 and Chapter VI, §7.
-/

public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum NumberField
open scoped NumberField nonZeroDivisors

namespace TauCeti

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

/-- **The defining equation of the Artin map away from the ramified support.** It is the generic
`artinHomAway` at the ramified support, so every lemma about the generic map transfers to it
without unfolding the definition. This is not a `simp` lemma: the specialized name, not the
displayed specialization, is the normal form. -/
theorem artinHomAway_ramifiedSupport_def (hab : ∀ σ τ : L ≃ₐ[K] L, Commute σ τ) :
    artinHomAway_ramifiedSupport (L := L) hab =
      artinHomAway hab (NumberField.ramifiedSupport K L)
        NumberField.isUnramifiedAway_ramifiedSupport :=
  -- The parentheses are the module system's: the body of `artinHomAway_ramifiedSupport` is not
  -- `@[expose]`d, so the parenthesised form elaborates here, where the body is visible, whereas a
  -- bare `rfl` would export its proof term and fail.
  (rfl)

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
