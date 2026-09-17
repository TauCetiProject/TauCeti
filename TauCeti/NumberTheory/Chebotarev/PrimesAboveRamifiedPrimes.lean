/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Chebotarev.RamifiedPrimes
public import TauCeti.RingTheory.DedekindDomain.PrimesAbove

/-!
# The primes of a number field above those ramifying in another

For an extension `L / K` of number fields and a further number field `E` over `K`, this file
collects the height-one primes of `𝓞 E` whose contraction to `𝓞 K` ramifies in `L`. There are
finitely many, so they form a `Finset`.

`E` is unrelated to `L`: the condition constrains the prime of `K` below, and says nothing about
how the prime behaves in `L / E`.

## Main definitions

* `NumberField.Chebotarev.primesAboveRamifiedPrimes`: the finite set of height-one primes of
  `𝓞 E` lying above `ramifiedPrimes K L`.

## Main results

* `NumberField.Chebotarev.mem_primesAboveRamifiedPrimes_iff`: the defining condition for
  membership.

## Comparison with ramification in `L / E`

Nothing here assumes `E` embeds in `L`, so in general there is no ramification in `L / E` to
compare against: membership is a condition on the prime of `K` below `𝔓`, and nothing else.

When a compatible tower `K → E → L` does exist, the two conditions are still not the same one.
Ramification indices multiply along a tower, `e(Q/𝔭) = e(Q/𝔓) · e(𝔓/𝔭)`, so a prime of `E`
ramifying in `L / E` always lies in this set. The inclusion can be strict, and that is why the
condition is imposed below rather than on `L / E`.

For example, take `K = ℚ` and `L = ℚ(∛2, ζ₃)`, so that `Gal(L/K) ≅ S₃`; let `E = ℚ(∛2)`, the field
fixed by a transposition, and let `p = 2`. The inertia group at a prime `Q` of `L` above `2` is the
cyclic group of order three, so `e(Q/2) = 3` while `e(Q/𝔓) = 1`: all of the ramification,
`e(𝔓/2) = 3`, happens below `E`. So `𝔓` is unramified in `L / E` and yet lies above a prime
ramifying in `L / K` — a witness that the inclusion is strict here.

## References

Adapted from `ramifiedBelow_finite` in `CebotarevDensity/FixedFieldDensity.lean` of
[CBirkbeck/chebotarev-density](https://github.com/CBirkbeck/chebotarev-density) (Apache-2.0,
Birkbeck--Brasca) on branch `development` at commit
`8575c9df1ae0a61120ab5c964c7911414254bec7`, where the set appears for `E` the fixed field of a
cyclic subgroup of `Gal(L/K)`.
-/

public section

open scoped NumberField

open IsDedekindDomain (HeightOneSpectrum)

namespace NumberField.Chebotarev

variable (K L E : Type*) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [Field E] [NumberField E] [Algebra K E]

/-- **The primes of `E` above those of `K` ramifying in `L`.** The height-one primes of `𝓞 E`
whose contraction to `𝓞 K` lies in `ramifiedPrimes K L`.

The condition is on the prime of `K` below. It is not ramification in `L / E`, which need not
even be defined here; the module docstring compares the two when a tower exists. -/
noncomputable def primesAboveRamifiedPrimes : Finset (HeightOneSpectrum (𝓞 E)) :=
  (HeightOneSpectrum.primesAbove_finite (𝓞 K) (𝓞 E)
    (ramifiedPrimes K L).finite_toSet).toFinset

variable {K L E}

/-- The defining condition for membership in `primesAboveRamifiedPrimes`: the prime of `𝓞 K`
below `𝔓` ramifies in `L`. -/
@[simp]
theorem mem_primesAboveRamifiedPrimes_iff (𝔓 : HeightOneSpectrum (𝓞 E)) :
    𝔓 ∈ primesAboveRamifiedPrimes K L E ↔ 𝔓.under (𝓞 K) ∈ ramifiedPrimes K L :=
  (Set.Finite.mem_toFinset _).trans (HeightOneSpectrum.mem_primesAbove_iff _ _ _ _)

end NumberField.Chebotarev
