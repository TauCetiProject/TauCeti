/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Krull dimension along integral extensions

For an integral extension `R → S` the Krull dimensions of `R` and `S` are compared by the two
Cohen–Seidenberg theorems.

* *Incomparability*: a strict inclusion of primes of `S` contracts to a strict inclusion of primes
  of `R`, so contraction is strictly monotone on prime spectra and `dim S ≤ dim R`.
* *Lying over and going up*: when every prime of `R` is a contraction and chains of primes of `R`
  lift along `R → S`, every chain of primes of `R` is the contraction of a chain in `S` of the same
  length, so `dim R ≤ dim S`.

For an injective integral extension both hold, and the two dimensions agree. This is the step
that reduces the dimension of a finitely generated algebra over a field to that of a polynomial
ring through Noether normalization.

## Main results

* `TauCeti.ringKrullDim_le_of_isIntegral`: `dim S ≤ dim R` for an integral `R`-algebra `S`.
* `TauCeti.ringKrullDim_le_of_hasGoingUp_of_surjective`: `dim R ≤ dim S` when `R → S` has going
  up and `Spec S → Spec R` is surjective.
* `TauCeti.ringKrullDim_eq_of_isIntegral_of_faithfulSMul`: `dim S = dim R` for an injective
  integral extension.
* `Ideal.height_eq_height_under_of_isIntegral_of_hasGoingDown`: an integral extension with
  going down preserves the heights of prime ideals.

## References

* [Stacks Project, Tag 00GU](https://stacks.math.columbia.edu/tag/00GU) (going up)
* M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative Algebra*, Corollary 5.9 and
  Theorem 5.11.
-/

public section

namespace TauCeti

open PrimeSpectrum

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Contraction of primes along an integral extension is strictly monotone
(incomparability). -/
theorem primeSpectrumComap_strictMono_of_isIntegral [Algebra.IsIntegral R S] :
    StrictMono (PrimeSpectrum.comap (algebraMap R S)) := fun P Q h ↦ by
  rw [← PrimeSpectrum.asIdeal_lt_asIdeal, PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal]
  exact Ideal.IsIntegral.under_lt_under ((PrimeSpectrum.asIdeal_lt_asIdeal P Q).2 h)

/-- Along an integral algebra with going down, the height of a prime is the height of the prime
below it: chains of primes descend by going down and contract injectively by incomparability. -/
theorem _root_.Ideal.height_eq_height_under_of_isIntegral_of_hasGoingDown
    [Algebra.IsIntegral R S] [Algebra.HasGoingDown R S]
    (P : Ideal S) [P.IsPrime] : P.height = (P.under R).height := by
  have h := Order.height_eq_of_strictMono (comap (algebraMap R S))
    primeSpectrumComap_strictMono_of_isIntegral (fun a b hb ↦ by
      have : a.asIdeal.LiesOver (comap (algebraMap R S) a).asIdeal := ⟨rfl⟩
      obtain ⟨Q, hQ, hQp, hQo⟩ :=
        Ideal.exists_ideal_lt_liesOver_of_lt (p := b.asIdeal) a.asIdeal hb
      exact ⟨⟨Q, hQp⟩, hQ, PrimeSpectrum.ext hQo.over.symm⟩) ⟨P, ‹_›⟩
  rwa [← height_eq_orderHeight, ← height_eq_orderHeight] at h

/-- The Krull dimension of an integral `R`-algebra is at most that of `R`. -/
theorem ringKrullDim_le_of_isIntegral [Algebra.IsIntegral R S] :
    ringKrullDim S ≤ ringKrullDim R :=
  Order.krullDim_le_of_strictMono _ primeSpectrumComap_strictMono_of_isIntegral

/-- If `R → S` has going up and every prime of `R` is contracted from a prime of `S`, the Krull
dimension of `R` is at most that of `S`. -/
theorem ringKrullDim_le_of_hasGoingUp_of_surjective [Algebra.HasGoingUp R S]
    (hsurj : Function.Surjective (PrimeSpectrum.comap (algebraMap R S))) :
    ringKrullDim R ≤ ringKrullDim S := by
  rw [ringKrullDim, Order.krullDim]
  refine iSup_le fun l ↦ ?_
  obtain ⟨P, hP⟩ := hsurj l.head
  have : P.asIdeal.LiesOver l.head.asIdeal :=
    ⟨by rw [← hP, PrimeSpectrum.comap_asIdeal, Ideal.under_def]⟩
  obtain ⟨L, hL, -, -⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P.asIdeal
  rw [← hL]
  exact Order.LTSeries.length_le_krullDim L

/-- An injective integral extension preserves Krull dimension. -/
theorem ringKrullDim_eq_of_isIntegral_of_faithfulSMul [Algebra.IsIntegral R S] [FaithfulSMul R S] :
    ringKrullDim S = ringKrullDim R :=
  ringKrullDim_le_of_isIntegral.antisymm <|
    ringKrullDim_le_of_hasGoingUp_of_surjective (Algebra.IsIntegral.comap_surjective R S)

end TauCeti
