/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Different
public import Mathlib.NumberTheory.NumberField.ExistsRamified

/-!
# The ramified rational primes of a number field

The genus theory of a quadratic field is governed by the number `t` of rational primes that ramify
in it: the genus field has degree `2 ^ t` over `ℚ` and the `2`-rank of the narrow class group is
`t - 1`. This file names that set of primes and records its basic properties.

Mathlib phrases ramification of a rational prime `p` in a number field `K` as
`Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)})`, and characterises it by divisibility of the
discriminant (`NumberField.not_dvd_discr_iff_isUnramifiedIn`). We package the negation as a set of
natural primes, which is the form in which `t` is counted.

## Main definitions

* `NumberField.ramifiedPrimes`: the set of natural primes ramifying in `K`.

## Main results

* `NumberField.mem_ramifiedPrimes_iff_dvd_discr`: a prime ramifies iff it divides the
  discriminant.
* `NumberField.coprime_natAbs_discr_iff_isUnramifiedIn`: a prime is unramified iff it is coprime
  to the discriminant.
* `AlgEquiv.ramifiedPrimes_eq`: isomorphic number fields have the same ramified primes.
* `NumberField.ramifiedPrimes_rat`: no prime ramifies in `ℚ`.
* `NumberField.finite_ramifiedPrimes`: only finitely many primes ramify.
* `NumberField.ramifiedPrimes_nonempty_iff`: some prime ramifies iff `K` is not `ℚ`
  (Minkowski, via `NumberField.exists_not_isUnramifiedIn`).
-/

public section

open scoped NumberField

namespace NumberField

variable (K : Type*) [Field K]

/-- **The ramified rational primes of a number field.** The set of natural primes `p` such that
`p` — as the ideal `span {p}` of `ℤ` — ramifies in the ring of integers of `K`. For a quadratic
field `K`, its cardinality is the `t` of genus theory. -/
def ramifiedPrimes : Set ℕ :=
  {p | p.Prime ∧ ¬ Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)})}

variable {K}

/-- The defining condition for membership in `ramifiedPrimes`. -/
@[simp]
theorem mem_ramifiedPrimes_iff {p : ℕ} :
    p ∈ ramifiedPrimes K ↔
      p.Prime ∧ ¬ Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)}) :=
  Iff.rfl

/-- A ramified prime is prime. -/
theorem prime_of_mem_ramifiedPrimes {p : ℕ} (hp : p ∈ ramifiedPrimes K) : p.Prime :=
  hp.1

variable [NumberField K]

/-- **Ramification is divisibility of the discriminant.** A natural prime `p` ramifies in `K` iff
`p` divides `NumberField.discr K`. This is `NumberField.not_dvd_discr_iff_isUnramifiedIn` in the
`ramifiedPrimes` packaging. -/
theorem mem_ramifiedPrimes_iff_dvd_discr {p : ℕ} (hp : p.Prime) :
    p ∈ ramifiedPrimes K ↔ (p : ℤ) ∣ NumberField.discr K := by
  rw [mem_ramifiedPrimes_iff, and_iff_right hp,
    ← NumberField.not_dvd_discr_iff_isUnramifiedIn K (𝓞 K) (Nat.prime_iff_prime_int.mp hp),
    not_not]

/-- **Isomorphic number fields have the same ramified primes**, since they have the same
discriminant (`NumberField.discr_eq_discr_of_algEquiv`). -/
theorem _root_.AlgEquiv.ramifiedPrimes_eq {L : Type*} [Field L] [NumberField L]
    (f : K ≃ₐ[ℚ] L) :
    ramifiedPrimes K = ramifiedPrimes L := by
  ext p
  by_cases hp : p.Prime
  · rw [mem_ramifiedPrimes_iff_dvd_discr hp, mem_ramifiedPrimes_iff_dvd_discr hp,
      NumberField.discr_eq_discr_of_algEquiv K f]
  · simp [hp]

/-- **No prime ramifies in `ℚ`**, whose discriminant is `1`. -/
@[simp]
theorem ramifiedPrimes_rat : ramifiedPrimes ℚ = ∅ :=
  Set.eq_empty_of_forall_notMem fun p hp => by
    have hp' := prime_of_mem_ramifiedPrimes hp
    simpa [discr_rat, Int.natCast_dvd, hp'.ne_one] using
      (mem_ramifiedPrimes_iff_dvd_discr hp').mp hp

-- Source. The hypothesis this discharges is
-- `hcop : ((NumberField.discr L).natAbs).Coprime m` in the Birkbeck--Brasca Chebotarev
-- development, CBirkbeck/chebotarev-density (Apache-2.0), branch `development` at
-- `8575c9df1ae0a61120ab5c964c7911414254bec7`. There `CebotarevDensity/Abelian.lean` carries it
-- undischarged throughout, obtaining `p ∤ discr E` from
-- `NumberField.not_dvd_discr_iff_forall_liesOver` inline. The statement below is that hypothesis;
-- deriving it from `Algebra.IsUnramifiedIn` is not done in the source, which propagates it.

/-- **A prime is unramified iff it is coprime to the discriminant.** A natural prime `p` is
unramified in `K` iff `|discr K|` and `p` are coprime. This is
`NumberField.not_dvd_discr_iff_isUnramifiedIn` in the form `((discr _).natAbs).Coprime m` that the
Chebotarev crossing lemmas take as a hypothesis, so that hypothesis can be discharged from
unramifiedness. -/
theorem coprime_natAbs_discr_iff_isUnramifiedIn {p : ℕ} (hp : p.Prime) :
    (discr K).natAbs.Coprime p ↔ Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)}) := by
  rw [Nat.coprime_comm, hp.coprime_iff_not_dvd, ← Int.natCast_dvd,
    not_dvd_discr_iff_isUnramifiedIn K (𝓞 K) (Nat.prime_iff_prime_int.mp hp)]

/-- **Only finitely many primes ramify**, since they all divide the nonzero integer
`NumberField.discr K`. -/
theorem finite_ramifiedPrimes : (ramifiedPrimes K).Finite :=
  (discr K).natAbs.primeFactors.finite_toSet.subset fun _ hp =>
    have hp' := prime_of_mem_ramifiedPrimes hp
    Nat.mem_primeFactors.mpr ⟨hp',
      Int.natCast_dvd.mp ((mem_ramifiedPrimes_iff_dvd_discr hp').mp hp),
      Int.natAbs_ne_zero.mpr (discr_ne_zero K)⟩

/-- **Some prime ramifies in a number field iff it is not `ℚ`**, i.e. iff its degree over `ℚ` is
not `1`. The nontrivial direction is Minkowski's bound in the form
`NumberField.exists_not_isUnramifiedIn`. -/
theorem ramifiedPrimes_nonempty_iff : (ramifiedPrimes K).Nonempty ↔ Module.finrank ℚ K ≠ 1 := by
  refine ⟨fun hne h => ?_, fun h => ?_⟩
  · rw [← (AlgEquiv.ofBijective (Algebra.ofId ℚ K)
      (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp h)).ramifiedPrimes_eq,
      ramifiedPrimes_rat] at hne
    exact Set.not_nonempty_empty hne
  · simpa only [Set.nonempty_def, mem_ramifiedPrimes_iff] using
      exists_not_isUnramifiedIn (𝒪 := 𝓞 K) h

end NumberField
