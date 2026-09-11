/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.ResidueDegree
public import TauCeti.NumberTheory.Chebotarev.PrimeCounting.VonMangoldt

/-!
# Negligible terms in Frobenius prime counting

Passing from a Frobenius prime-power sum to a prime sum of residue degree one discards three
terms: higher prime powers in the chosen Frobenius class, primes of absolute residue degree above
one, and prime powers over a finite exceptional set. Each term is `o(x)` for a different reason.
This file records that their sum is `o(x)`, in the form needed by weighted crossing arguments.
The statement follows `TauCetiRoadmap/Chebotarev/Suggested.lean` and
`TauCetiRoadmap/Chebotarev/README.md` §11.3(4).

## Main result

* `NumberField.Chebotarev.frobeniusDiscard_isLittleO`: the total discarded contribution is
  negligible compared with `x`.
-/

public section

namespace NumberField.Chebotarev

open Filter TauCeti
open scoped Asymptotics NumberField
open IsDedekindDomain (HeightOneSpectrum)

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- The total contribution discarded when a Frobenius prime-power sum is restricted to
residue-degree-one primes outside a finite exceptional set is `o(x)`.

The three summands respectively remove higher prime powers in the Frobenius fibre, primes whose
absolute residue degree is greater than one, and all prime powers based at an exceptional prime.
-/
theorem frobeniusDiscard_isLittleO (C : ConjClasses (L ≃ₐ[K] L))
    (T : Finset (HeightOneSpectrum (𝓞 K))) :
    (fun x : ℝ ↦ frobeniusPsi K L C x - frobeniusTheta K L C x +
        primeTheta K (higherDegreePrimes K) x +
        primePsi K (T : Set (HeightOneSpectrum (𝓞 K))) x) =o[atTop] fun x : ℝ ↦ x :=
  ((frobeniusPsi_sub_frobeniusTheta_isLittleO C).add
    (primeTheta_higherDegreePrimes_isLittleO K)).add
      (primePsi_isLittleO_of_finite T.finite_toSet)

end NumberField.Chebotarev
