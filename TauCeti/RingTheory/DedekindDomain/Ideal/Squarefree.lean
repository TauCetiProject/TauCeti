/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Products of distinct height-one primes

In a Dedekind domain `R`, a height-one prime `𝔭_v` divides another one `𝔭_w` only when `v = w`,
since both are maximal. Consequently, for a finite set `s` of height-one primes, the prime
divisors of the ideal `∏_{w ∈ s} 𝔭_w` among the height-one primes are exactly the members of `s`,
and this product is squarefree.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.asIdeal_dvd_asIdeal_iff`: `𝔭_v ∣ 𝔭_w` exactly when `v = w`.
* `IsDedekindDomain.HeightOneSpectrum.asIdeal_dvd_prod_asIdeal_iff`: `𝔭_v ∣ ∏_{w ∈ s} 𝔭_w`
  exactly when `v ∈ s`.
* `IsDedekindDomain.HeightOneSpectrum.squarefree_prod_asIdeal`: `∏_{w ∈ s} 𝔭_w` is squarefree.
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R : Type*} [CommRing R] [IsDedekindDomain R] {v w : HeightOneSpectrum R}

/-- One height-one prime divides another exactly when they are equal. -/
@[simp]
theorem asIdeal_dvd_asIdeal_iff : v.asIdeal ∣ w.asIdeal ↔ v = w :=
  (prime_dvd_prime_iff_eq v.prime w.prime).trans asIdeal_injective.eq_iff

/-- A height-one prime divides a product of height-one primes over a finite set `s` exactly when
it belongs to `s`. -/
@[simp]
theorem asIdeal_dvd_prod_asIdeal_iff {s : Finset (HeightOneSpectrum R)} :
    v.asIdeal ∣ ∏ w ∈ s, w.asIdeal ↔ v ∈ s := by
  simp [v.prime.dvd_finsetProd_iff]

/-- A product of distinct height-one primes is squarefree. -/
theorem squarefree_prod_asIdeal (s : Finset (HeightOneSpectrum R)) :
    Squarefree (∏ w ∈ s, w.asIdeal) :=
  Finset.squarefree_prod_of_pairwise_isCoprime (fun v _ _ _ hvw ↦
    v.prime.irreducible.isRelPrime_iff_not_dvd.2 (asIdeal_dvd_asIdeal_iff.not.2 hvw))
    fun v _ ↦ v.prime.squarefree

end IsDedekindDomain.HeightOneSpectrum
