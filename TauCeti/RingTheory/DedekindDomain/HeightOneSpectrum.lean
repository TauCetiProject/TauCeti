/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas

/-!
# Basic instances on the height-one prime spectrum

This file provides two elementary typeclass instances on `IsDedekindDomain.HeightOneSpectrum R`:

* Every height-one prime `v` has nonzero underlying ideal (`NeZero v.asIdeal`), so
  `Ring.HasFiniteQuotients` synthesizes `Finite (R ⧸ v.asIdeal)` automatically for rings such as
  `ℤ` and rings of integers `𝓞 K`.
* Over a countable Noetherian commutative ring `R`, `HeightOneSpectrum R` is countable, since every
  ideal is finitely generated and therefore determined by a finite generating subset.

## Main instances

* `IsDedekindDomain.HeightOneSpectrum.instNeZeroAsIdeal`: `NeZero v.asIdeal` for every height-one
  prime `v`.
* `IsDedekindDomain.HeightOneSpectrum.instCountable`: `Countable (HeightOneSpectrum R)` for a
  countable Noetherian commutative ring `R`.
-/

public section

namespace IsDedekindDomain.HeightOneSpectrum

/-- Every height-one prime ideal is nonzero (`⊥ = 0` in `Ideal R`), so `Ring.HasFiniteQuotients`
synthesizes `Finite (R ⧸ v.asIdeal)` automatically (for instance for `ℤ` and `𝓞 K`). -/
instance instNeZeroAsIdeal {R : Type*} [CommRing R] (v : HeightOneSpectrum R) :
    NeZero v.asIdeal :=
  ⟨v.ne_bot⟩

/-- A countable Noetherian commutative ring has countably many height-one primes, since every ideal
is finitely generated and hence determined by a finite generating subset. -/
instance instCountable (R : Type*) [CommRing R] [IsNoetherianRing R] [Countable R] :
    Countable (HeightOneSpectrum R) :=
  let s (v : HeightOneSpectrum R) : Set R :=
    (Submodule.fg_def.mp (IsNoetherian.noetherian v.asIdeal)).choose
  have hs_fin (v : HeightOneSpectrum R) : (s v).Finite :=
    (Submodule.fg_def.mp (IsNoetherian.noetherian v.asIdeal)).choose_spec.1
  have hs_span (v : HeightOneSpectrum R) : Submodule.span R (s v) = v.asIdeal :=
    (Submodule.fg_def.mp (IsNoetherian.noetherian v.asIdeal)).choose_spec.2
  letI := Classical.decEq R
  Function.Injective.countable (f := fun v : HeightOneSpectrum R ↦ (hs_fin v).toFinset) fun v w h ↦
    HeightOneSpectrum.ext <| by
      have hset : s v = s w := by simpa using congrArg (↑· : Finset R → Set R) h
      rw [← hs_span v, ← hs_span w, hset]

end IsDedekindDomain.HeightOneSpectrum
