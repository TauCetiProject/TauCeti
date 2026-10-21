/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.GoingDown
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.Ideal.Height
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

If moreover `R → S` has going down, a maximal ideal of `S` has the height of
its contraction: incomparability bounds the height from above and going down from below. So when
all maximal ideals of `R` have one height, all maximal ideals of `S` have that height too.

## Main results

* `TauCeti.ringKrullDim_le_of_isIntegral`: `dim S ≤ dim R` for an integral `R`-algebra `S`.
* `TauCeti.ringKrullDim_le_of_hasGoingUp_of_surjective`: `dim R ≤ dim S` when `R → S` has going
  up and `Spec S → Spec R` is surjective.
* `TauCeti.ringKrullDim_eq_of_isIntegral_of_faithfulSMul`: `dim S = dim R` for an injective
  integral extension.
* `TauCeti.height_eq_of_isMaximal_of_isIntegral_of_hasGoingDown`: if every maximal ideal of `R`
  has height `d`, so does every maximal ideal of an integral `R`-algebra with going down.

## References

* [Stacks Project, Tag 00GU](https://stacks.math.columbia.edu/tag/00GU) (going up)
* M. F. Atiyah, I. G. Macdonald, *Introduction to Commutative Algebra*, Corollary 5.9 and
  Theorem 5.11.
-/

public section

namespace TauCeti

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- Contraction of primes along an integral extension is strictly monotone
(incomparability). -/
theorem primeSpectrumComap_strictMono_of_isIntegral [Algebra.IsIntegral R S] :
    StrictMono (PrimeSpectrum.comap (algebraMap R S)) := fun P Q h ↦ by
  rw [← PrimeSpectrum.asIdeal_lt_asIdeal, PrimeSpectrum.comap_asIdeal, PrimeSpectrum.comap_asIdeal]
  exact Ideal.IsIntegral.under_lt_under ((PrimeSpectrum.asIdeal_lt_asIdeal P Q).2 h)

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

/-- Let `S` be an integral `R`-algebra with going down. If every maximal ideal of `R` has height
`d`, then every maximal ideal of `S` has height `d`: a maximal ideal `m` of `S` contracts to a
maximal ideal of `R`, whose height bounds that of `m` above by incomparability and below by going
down. -/
theorem height_eq_of_isMaximal_of_isIntegral_of_hasGoingDown [Algebra.IsIntegral R S]
    [Algebra.HasGoingDown R S] {d : ℕ∞} (hR : ∀ p : Ideal R, p.IsMaximal → p.height = d)
    (m : Ideal S) [m.IsMaximal] : m.height = d := by
  have : (m.under R).IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal m
  let P : PrimeSpectrum S := ⟨m, inferInstance⟩
  have h : (m.under R).height = Order.height (PrimeSpectrum.comap (algebraMap R S) P) := by
    rw [← PrimeSpectrum.height_eq_orderHeight, PrimeSpectrum.comap_asIdeal, Ideal.under_def]
  rw [← hR _ this, PrimeSpectrum.height_eq_orderHeight P, h]
  refine le_antisymm
    (Order.height_le_height_apply_of_strictMono _ primeSpectrumComap_strictMono_of_isIntegral P)
    (Order.height_le fun l hl ↦ ?_)
  -- Going down lifts a chain of primes of `R` ending at `m ∩ R` to one of `S` ending at `m`.
  have : m.LiesOver l.last.asIdeal := ⟨by rw [hl]; rfl⟩
  obtain ⟨L, hlen, hlast, -⟩ := Ideal.exists_ltSeries_of_hasGoingDown l m
  rw [← hlen, show P = L.last from hlast.symm]
  exact Order.length_le_height_last

end TauCeti
