/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.CharZero.Infinite
public import Mathlib.NumberTheory.NumberField.Basic
public import Mathlib.RingTheory.Ideal.Int
public import TauCeti.NumberTheory.RamificationInertia.Galois
public import TauCeti.NumberTheory.RamificationInertia.Splitting

/-!
# Complete splitting in number fields

For a finite Galois number field `K / ℚ`, a rational prime `p` splits completely — meaning
there are exactly `[K : ℚ]` primes of `𝓞 K` above `p` — if and only if `p` is unramified with
residue degree one, i.e. both the ramification index `e` and the inertia degree `f` (which are
common to all primes above `p`, the extension being Galois) equal `1`.

One direction needs no Galois hypothesis at all: a full complement of primes already forces
`e = f = 1` at each of them, directly from the fundamental identity, and hence identifies each
residue field with the prime field.

The relative criteria apply to a finite Galois extension `L / K` and a base ring over which
`Gal(L/K)` acts as a Galois group on `𝓞 L`. They include the rings of integers `𝓞 K` and,
when `K = ℚ`, the rational integers. This is the count form of the fundamental identity
`(#primes) · e · f = [L : K]`: the number of primes is maximal exactly when `e = f = 1`.
Equivalently, the decomposition group of a prime above the base ideal is trivial. These
criteria connect complete splitting with the residue conditions used in prime-splitting laws.

## Main results

* `NumberField.ncard_primesOver_eq_finrank_iff_of_isGalois`: the relative criterion over an
  arbitrary Dedekind base.
* `NumberField.ncard_primesOver_eq_finrank_iff`: the rational-prime specialization.
* `Ideal.isUnramifiedAt_of_ncard_primesOver_eq_finrank`: complete splitting implies
  unramifiedness in any extension of number fields.
* `Ideal.bijective_algebraMap_quotient_of_ncard_primesOver_eq_finrank`:
  complete splitting makes each residue field the prime field.
* `Ideal.absNorm_eq_of_ncard_primesOver_eq_finrank`: a prime above a completely split
  rational prime has that prime as its absolute norm.
* `NumberField.ncard_primesOver_eq_finrank_iff_stabilizer_eq_bot`: the relative
  orbit–stabilizer form of the splitting criterion.

## Provenance

Two of Mathlib's fundamental identities are used, according to whether a Galois hypothesis is
available. The splitting criterion itself rests on the Galois identity
(`Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn`). The consequences drawn without
a Galois hypothesis — that complete splitting forces `e = f = 1`, and hence that the residue field
at `Q` is the prime field — rest instead on the general identity for finite flat extensions of
domains (`Ideal.sum_ramification_inertia_eq_finrank`), applied through
the general theorem in `TauCeti.RamificationInertia.Splitting`.
The decomposition-group criterion uses the description of the primes above an ideal as one
orbit (`Algebra.IsInvariant.orbit_eq_primesOver`) and orbit–stabilizer
(`MulAction.index_stabilizer`), through `TauCeti.NumberTheory.RamificationInertia.Galois`.
-/

public section

open NumberField Ideal Module MulAction
open scoped Pointwise

namespace NumberField

variable (K L : Type*) [Field K] [Field L] [NumberField K] [NumberField L] [Algebra K L]
  [IsGalois K L]

/-- In a Galois extension of number fields, the number of primes over a prime ideal of a
Dedekind base equals the relative degree iff the common ramification index and inertia degree
are both `1`. -/
theorem ncard_primesOver_eq_finrank_iff_of_isGalois {A : Type*} [CommRing A]
    [IsDedekindDomain A] [Algebra A (𝓞 L)] [Module.Finite A (𝓞 L)]
    [IsTorsionFree A (𝓞 L)] [IsGaloisGroup Gal(L/K) A (𝓞 L)] (P : Ideal A) [P.IsPrime] :
    (primesOver P (𝓞 L)).ncard = finrank K L ↔
      P.ramificationIdxIn (𝓞 L) = 1 ∧ P.inertiaDegIn (𝓞 L) = 1 := by
  rw [← IsGaloisGroup.card_eq_finrank Gal(L/K) K L]
  exact Ideal.ncard_primesOver_eq_natCard_iff_of_isGaloisGroup Gal(L/K) P

/-- In a Galois number field, a rational prime `p` splits completely (there are `[K : ℚ]` primes
of `𝓞 K` above `p`) iff its ramification index and inertia degree are both `1`. -/
theorem ncard_primesOver_eq_finrank_iff (K : Type*) [Field K] [NumberField K] [IsGalois ℚ K]
    (p : ℕ) [Fact p.Prime] : (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = finrank ℚ K ↔
      (span {(p : ℤ)}).ramificationIdxIn (𝓞 K) = 1 ∧ (span {(p : ℤ)}).inertiaDegIn (𝓞 K) = 1 :=
  ncard_primesOver_eq_finrank_iff_of_isGalois ℚ K (span {(p : ℤ)})

/-- In a Galois extension of number fields, a base ideal `P` has `[L : K]` primes above it
iff the decomposition group of a prime `Q` above it is trivial. The base ring may be `𝓞 K`
or, when `K = ℚ`, the rational integers. -/
theorem ncard_primesOver_eq_finrank_iff_stabilizer_eq_bot {A : Type*} [CommRing A]
    [Algebra A (𝓞 L)] [IsGaloisGroup Gal(L/K) A (𝓞 L)] (P : Ideal A)
    (Q : Ideal (𝓞 L)) [Q.IsPrime] [Q.LiesOver P] :
    (primesOver P (𝓞 L)).ncard = finrank K L ↔ stabilizer Gal(L/K) Q = ⊥ := by
  rw [← IsGaloisGroup.card_eq_finrank Gal(L/K) K L,
    ncard_primesOver_eq_natCard_iff_stabilizer_eq_bot _ _ Q]

end NumberField

namespace Ideal

open TauCeti.RamificationInertia in
/-- **A full complement of primes forces unramifiedness.** If `𝓞 L` has `[L : K]` primes above a
prime ideal `𝔭` of `𝓞 K`, then every prime `Q` of `𝓞 L` above `𝔭` is unramified over `𝓞 K`.
No Galois hypothesis is needed. -/
theorem isUnramifiedAt_of_ncard_primesOver_eq_finrank {K L : Type*} [Field K] [NumberField K]
    [Field L] [NumberField L] [Algebra K L] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime]
    (hsplit : (primesOver 𝔭 (𝓞 L)).ncard = finrank K L) (Q : Ideal (𝓞 L)) [Q.IsPrime]
    [Q.LiesOver 𝔭] : Algebra.IsUnramifiedAt (𝓞 K) Q := by
  -- The fundamental identity `∑ e f = [L : K]` leaves no room for `e > 1` once the primes above
  -- `𝔭` already number the rank; that count is taken over the rings, so the degree of the field
  -- extension has to be transported down to `𝓞 L` over `𝓞 K` first.
  rw [← Ideal.ramificationIdx_eq_one_iff]
  exact (ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ncard_primesOver_eq_finrank 𝔭 Q
    (by rwa [IsFractionRing.finrank_eq (𝓞 K) K (𝓞 L) L] at hsplit)).1

/-- **Complete splitting makes the residue field at `Q` the prime field.** If `p` splits
completely then `algebraMap (ℤ ⧸ (p)) (𝓞 K ⧸ Q)` is bijective. No Galois hypothesis is needed. -/
theorem bijective_algebraMap_quotient_of_ncard_primesOver_eq_finrank {K : Type*} [Field K]
    [NumberField K]
    {p : ℕ} [Fact p.Prime] (Q : Ideal (𝓞 K)) [Q.IsPrime]
    [Q.LiesOver (span {(p : ℤ)})]
    (hsplit : (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = finrank ℚ K) :
    Function.Bijective (algebraMap (ℤ ⧸ span {(p : ℤ)}) (𝓞 K ⧸ Q)) :=
  TauCeti.RamificationInertia.bijective_algebraMap_quotient_of_ncard_primesOver_eq_finrank
    (span {(p : ℤ)}) Q (by rwa [NumberField.RingOfIntegers.rank])

open TauCeti.RamificationInertia in
/-- **The absolute norm of a prime above a completely split rational prime is that prime.** If
`p` splits completely in `K` then the inertia degree at each prime `𝔭` above `p` is `1`, so the
residue field at `𝔭` is `ℤ/p` and `N(𝔭) = p`. No Galois hypothesis is needed. -/
theorem absNorm_eq_of_ncard_primesOver_eq_finrank {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] (𝔭 : Ideal (𝓞 K)) [𝔭.IsPrime] [𝔭.LiesOver (span {(p : ℤ)})]
    (hsplit : (primesOver (span {(p : ℤ)}) (𝓞 K)).ncard = finrank ℚ K) :
    absNorm 𝔭 = p := by
  have hinertia : 𝔭.inertiaDeg ℤ = 1 :=
    (ramificationIdx_eq_one_and_inertiaDeg_eq_one_of_ncard_primesOver_eq_finrank
      (span {(p : ℤ)}) 𝔭 (by rwa [NumberField.RingOfIntegers.rank])).2
  rw [← Ideal.pow_inertiaDeg p 𝔭, hinertia, pow_one]

end Ideal
