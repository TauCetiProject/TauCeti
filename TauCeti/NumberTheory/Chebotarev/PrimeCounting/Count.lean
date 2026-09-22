/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.ArithmeticDirichletSeries.Counting
public import TauCeti.NumberTheory.Chebotarev.PrimeCounting.VonMangoldt

/-!
# Frobenius prime counts

For a conjugacy class `C` in a finite Galois extension `L / K`, this file defines the number of
prime ideals in the Frobenius fibre of norm at most `x`. The count is represented by the filtered
canonical prime carrier and is related to the generic prime-counting API for that carrier.

## Main definitions

* `NumberField.Chebotarev.frobeniusPrimeCount`: the cardinality of the filtered Frobenius prime
  carrier below `x`.

## Main results

* `NumberField.Chebotarev.frobeniusPrimeCount_apply`: the filtered-cardinality characterization
  of the count.
* `NumberField.Chebotarev.frobeniusPrimeCount_eq_primeCount`: the real-valued count is the generic
  prime count of the Frobenius fibre.
-/

public section

namespace NumberField.Chebotarev

open TauCeti

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

variable (K L) in
/-- The number of primes in the Frobenius fibre with absolute norm at most `x`. -/
noncomputable def frobeniusPrimeCount (C : ConjClasses (L ≃ₐ[K] L)) (x : ℝ) : ℕ := by
  classical
  exact ((primesLE K x).filter (· ∈ frobeniusPrimeSet K L C)).card

/-- The Frobenius prime count as the cardinality of its filtered prime carrier. -/
theorem frobeniusPrimeCount_apply (C : ConjClasses (L ≃ₐ[K] L))
    [DecidablePred (fun v ↦ v ∈ frobeniusPrimeSet K L C)] (x : ℝ) :
    frobeniusPrimeCount K L C x =
      ((primesLE K x).filter (· ∈ frobeniusPrimeSet K L C)).card := by
  classical
  simp [frobeniusPrimeCount]

/-- The real coercion of the Frobenius prime count is the generic prime count of its fibre. -/
@[simp] theorem frobeniusPrimeCount_eq_primeCount (C : ConjClasses (L ≃ₐ[K] L)) (x : ℝ) :
    (frobeniusPrimeCount K L C x : ℝ) = primeCount K (frobeniusPrimeSet K L C) x := by
  classical
  simpa [frobeniusPrimeCount] using
    (primeCount_eq_card (K := K) (S := frobeniusPrimeSet K L C) x).symm

end NumberField.Chebotarev
