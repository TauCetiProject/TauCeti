/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Countably many submodules of a countable Noetherian module

Every submodule of a Noetherian module is spanned by a finite set, and choosing such a set for each
submodule is injective. A Noetherian module with countably many elements therefore has only
countably many submodules. In particular a countable Noetherian ring has countably many ideals,
and a countable Noetherian ring has countably many height-one primes: the ring of integers of a
number field has countably many finite places.

## Main results

* `Submodule.countable_of_isNoetherian`: a countable Noetherian module has countably many
  submodules.
* `IsDedekindDomain.HeightOneSpectrum.countable`: a countable Noetherian ring has countably many
  height-one primes.
-/

public section

/-- A Noetherian module with countably many elements has countably many submodules. -/
instance Submodule.countable_of_isNoetherian {R M : Type*} [Semiring R] [AddCommMonoid M]
    [Module R M] [IsNoetherian R M] [Countable M] : Countable (Submodule R M) := by
  classical
  choose s hs using fun N : Submodule R M ↦ IsNoetherian.noetherian N
  exact Function.Injective.countable (f := s) fun N N' h ↦ by rw [← hs N, ← hs N', h]

/-- A countable Noetherian ring has countably many height-one primes. -/
instance IsDedekindDomain.HeightOneSpectrum.countable {R : Type*} [CommRing R]
    [IsNoetherianRing R] [Countable R] : Countable (HeightOneSpectrum R) :=
  Function.Injective.countable (f := HeightOneSpectrum.asIdeal) fun _ _ ↦ HeightOneSpectrum.ext
