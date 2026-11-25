/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import TauCeti.RingTheory.Noetherian.Countable

/-!
# Countably many height-one primes

A countable Noetherian ring has only countably many ideals
(`Submodule.countable_of_isNoetherian`), hence only countably many height-one primes. For
example, the ring of integers of a number field has countably many finite places.

## Main results

* `IsDedekindDomain.HeightOneSpectrum.countable`: a countable Noetherian ring has countably many
  height-one primes.
-/

public section

/-- A countable Noetherian ring has countably many height-one primes. -/
instance IsDedekindDomain.HeightOneSpectrum.countable {R : Type*} [CommRing R]
    [IsNoetherianRing R] [Countable R] : Countable (HeightOneSpectrum R) :=
  Function.Injective.countable (f := HeightOneSpectrum.asIdeal) fun _ _ ↦ HeightOneSpectrum.ext
