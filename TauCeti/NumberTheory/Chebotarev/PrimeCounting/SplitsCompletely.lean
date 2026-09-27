/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.PrimeCounting.FrobeniusPrimeCount
public import TauCeti.NumberTheory.Chebotarev.SplitsCompletely
public import TauCeti.NumberTheory.NumberField.SplitsCompletely.GaloisClosure

/-!
# Natural density of completely split primes

In a finite Galois extension `L/K`, complete splitting is exactly the identity Artin fibre.
Natural-density Chebotarev therefore gives the proportion `1/[L:K]` of completely split
primes. For an intermediate extension that is not necessarily Galois, complete splitting is
equivalent to complete splitting in its normal closure, so the denominator is the degree of
that closure.

## Main results

* `NumberField.Chebotarev.hasNaturalDensity_frobeniusPrimeSet_one`: the completely split
  primes of a Galois extension have natural density `1/[L:K]`.
* `NumberField.Chebotarev.hasNaturalDensity_setOf_ncard_primesOver_eq_finrank`: the completely
  split primes of an intermediate extension have natural density given by its normal closure.

## References

* J. Neukirch, *Algebraic Number Theory*, Chapter VII, §13.
* For the analogous Dirichlet-density result, see
  `NumberField.Chebotarev.hasDirichletDensity_setOf_ncard_primesOver_eq_finrank` in
  `TauCeti.NumberTheory.Chebotarev.Density.SplitsCompletely`.
-/

public section

open IsDedekindDomain (HeightOneSpectrum)
open NumberField

namespace NumberField.Chebotarev

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L] [IsGalois K L]

variable (K L) in
/-- The primes splitting completely in a finite Galois extension `L/K` have natural density
`1/[L:K]`. The identity Artin fibre is exactly the set of completely split primes. -/
theorem hasNaturalDensity_frobeniusPrimeSet_one :
    NumberField.Set.HasNaturalDensity (frobeniusPrimeSet K L 1)
      (1 / (Module.finrank K L : ℝ)) := by
  simpa only [ConjClasses.one_eq_mk_one, Nat.card_coe_set_eq,
    ConjClasses.ncard_carrier_mk_of_mem_center (Subgroup.one_mem _), Nat.cast_one,
    IsGalois.card_aut_eq_finrank] using
    hasNaturalDensity_frobeniusPrimeSet K L 1

variable {M : Type*} [Field M] [NumberField M] [Algebra K M] [IsGalois K M] in
/-- Primes splitting completely in an intermediate field `E/K` have natural density the
reciprocal of the degree of its normal closure in `M`. -/
theorem hasNaturalDensity_setOf_ncard_primesOver_eq_finrank (E : IntermediateField K M) :
    NumberField.Set.HasNaturalDensity
      {𝔭 : HeightOneSpectrum (𝓞 K) |
        (𝔭.asIdeal.primesOver (𝓞 E)).ncard = Module.finrank K E}
      (1 / (Module.finrank K (IntermediateField.normalClosure K E M) : ℝ)) := by
  have h := hasNaturalDensity_frobeniusPrimeSet_one K
    (IntermediateField.normalClosure K E M)
  rw [frobeniusPrimeSet_one_eq_setOf_ncard_primesOver_eq_finrank] at h
  simpa only [Ideal.ncard_primesOver_normalClosure_eq_finrank_iff] using h

end NumberField.Chebotarev
