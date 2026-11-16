/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Quotient.Defs
public import Mathlib.RingTheory.Spectrum.Maximal.Defs

/-!
# Maximal spectra of quotients and surjective images

Along a surjective homomorphism `f : R →+* S` of commutative rings, contraction of ideals
embeds `MaximalSpectrum S` into `MaximalSpectrum R`. In particular, every surjective image and
every quotient of a semilocal ring is semilocal.

## Main results

* `MaximalSpectrum.finite_of_surjective`: a surjective image of a commutative ring with
  finitely many maximal ideals has finitely many maximal ideals.
* `MaximalSpectrum.instFiniteQuotient`: a quotient of a commutative ring with finitely many
  maximal ideals has finitely many maximal ideals.
-/

public section

namespace MaximalSpectrum

/-- A surjective homomorphism `f : R →+* S` of commutative rings pulls maximal ideals of `S`
back injectively into `MaximalSpectrum R`, so `S` is semilocal whenever `R` is. -/
theorem finite_of_surjective {R S : Type*} [CommRing R] [CommRing S]
    [Finite (MaximalSpectrum R)] {f : R →+* S} (hf : Function.Surjective f) :
    Finite (MaximalSpectrum S) :=
  Finite.of_injective
    (fun m : MaximalSpectrum S ↦ ⟨m.asIdeal.comap f, Ideal.comap_isMaximal_of_surjective f hf⟩)
    fun _ _ h ↦ MaximalSpectrum.ext <|
      Ideal.comap_injective_of_surjective f hf (congrArg MaximalSpectrum.asIdeal h)

/-- Every quotient of a commutative semilocal ring is semilocal. -/
instance instFiniteQuotient {R : Type*} [CommRing R] [Finite (MaximalSpectrum R)] (I : Ideal R) :
    Finite (MaximalSpectrum (R ⧸ I)) :=
  finite_of_surjective Ideal.Quotient.mk_surjective

end MaximalSpectrum
