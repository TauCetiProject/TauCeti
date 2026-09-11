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

Weighted crossing arguments bound the error incurred when passing from a Frobenius prime-power sum
to a prime sum of residue degree one by three functions. These account for higher prime powers in
the chosen Frobenius class and use unrestricted sums to majorize the contributions from primes of
absolute residue degree above one and from a finite exceptional set. Each majorant is `o(x)` for a
different reason. This file records that their sum is `o(x)`.

## Main result

* `NumberField.Chebotarev.frobeniusDiscard_isLittleO`: the sum of three majorants for the discard
  error is negligible compared with `x`.
-/

public section

namespace NumberField.Chebotarev

open Filter TauCeti
open scoped Asymptotics NumberField
open IsDedekindDomain (HeightOneSpectrum)

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- The sum of three majorants for the error incurred when a Frobenius prime-power sum is restricted
to residue-degree-one primes outside a finite exceptional set is `o(x)`.

The first summand is the higher-prime-power contribution in the Frobenius fibre. The other two are
unrestricted weighted sums over all primes of absolute residue degree greater than one and all
prime powers based at an exceptional prime.
-/
-- Source: `TauCetiRoadmap/Chebotarev/Suggested.lean` and README §11.3(4).
theorem frobeniusDiscard_isLittleO (C : ConjClasses (L ≃ₐ[K] L))
    (T : Finset (HeightOneSpectrum (𝓞 K))) :
    (fun x : ℝ ↦ frobeniusPsi K L C x - frobeniusTheta K L C x +
        primeTheta K (higherDegreePrimes K) x +
        primePsi K (T : Set (HeightOneSpectrum (𝓞 K))) x) =o[atTop] fun x : ℝ ↦ x :=
  ((frobeniusPsi_sub_frobeniusTheta_isLittleO C).add
    (primeTheta_higherDegreePrimes_isLittleO K)).add
      (primePsi_isLittleO_of_finite T.finite_toSet)

end NumberField.Chebotarev
