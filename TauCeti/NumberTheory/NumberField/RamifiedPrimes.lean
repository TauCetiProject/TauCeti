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
* `NumberField.coprime_natAbs_discr_of_isUnramifiedIn`: an unramified prime is coprime to the
  discriminant.
* `NumberField.ramifiedPrimes_eq_of_algEquiv`: isomorphic number fields have the same ramified
  primes.
* `NumberField.ramifiedPrimes_rat`: no prime ramifies in `ℚ`.
* `NumberField.finite_ramifiedPrimes`: only finitely many primes ramify.
* `NumberField.ramifiedPrimes_nonempty`: some prime ramifies, unless `K = ℚ`
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
theorem ramifiedPrimes_eq_of_algEquiv {L : Type*} [Field L] [NumberField L] (f : K ≃ₐ[ℚ] L) :
    ramifiedPrimes K = ramifiedPrimes L := by
  ext p
  by_cases hp : p.Prime
  · rw [mem_ramifiedPrimes_iff_dvd_discr hp, mem_ramifiedPrimes_iff_dvd_discr hp,
      NumberField.discr_eq_discr_of_algEquiv K f]
  · simp [hp]

/-- **No prime ramifies in `ℚ`**, whose discriminant is `1`. -/
@[simp]
theorem ramifiedPrimes_rat : ramifiedPrimes ℚ = ∅ := by
  ext p
  simp only [Set.mem_empty_iff_false, iff_false]
  intro hp
  have h := (mem_ramifiedPrimes_iff_dvd_discr hp.1).mp hp
  rw [NumberField.discr_rat] at h
  exact hp.1.not_dvd_one (Int.natCast_dvd_natCast.mp (by exact_mod_cast h))

-- Source. The hypothesis this discharges is
-- `hcop : ((NumberField.discr L).natAbs).Coprime m` in the Birkbeck--Brasca Chebotarev
-- development, CBirkbeck/chebotarev-density (Apache-2.0), branch `development` at
-- `8575c9df1ae0a61120ab5c964c7911414254bec7`. There `CebotarevDensity/Abelian.lean` carries it
-- undischarged throughout, obtaining `p ∤ discr E` from
-- `NumberField.not_dvd_discr_iff_forall_liesOver` inline. The statement below is that hypothesis;
-- deriving it from `Algebra.IsUnramifiedIn` is not done in the source, which propagates it.

/-- **An unramified prime is coprime to the discriminant.** If the rational prime `p` is
unramified in `K` then it does not divide `NumberField.discr K`, so `|discr K|` and `p` are
coprime.

This is `mem_ramifiedPrimes_iff_dvd_discr` in the form the cyclotomic-crossing lemmas consume.
They take `((NumberField.discr _).natAbs).Coprime m` as an undischarged hypothesis, and
`IsCyclotomicExtension.finrank_eq_totient` records in its implementation notes that a caller is
expected to arrange it "by choosing `m` to be a prime unramified in `K`". This is that sentence
as a lemma, so the hypothesis can be discharged rather than propagated. -/
theorem coprime_natAbs_discr_of_isUnramifiedIn {p : ℕ} (hp : p.Prime)
    (hur : Algebra.IsUnramifiedIn (𝓞 K) (Ideal.span {(p : ℤ)})) :
    (NumberField.discr K).natAbs.Coprime p := by
  refine (hp.coprime_iff_not_dvd.mpr fun hdvd => ?_).symm
  exact (mem_ramifiedPrimes_iff.mp
    ((mem_ramifiedPrimes_iff_dvd_discr hp).mpr (Int.natCast_dvd.mpr hdvd))).2 hur

/-- **Only finitely many primes ramify**, since they all divide the nonzero integer
`NumberField.discr K`. -/
theorem finite_ramifiedPrimes : (ramifiedPrimes K).Finite := by
  have hne : (NumberField.discr K).natAbs ≠ 0 :=
    Int.natAbs_ne_zero.mpr (NumberField.discr_ne_zero K)
  refine Set.Finite.subset (NumberField.discr K).natAbs.divisors.finite_toSet fun p hp => ?_
  exact Finset.mem_coe.mpr (Nat.mem_divisors.mpr
    ⟨Int.natCast_dvd.mp ((mem_ramifiedPrimes_iff_dvd_discr hp.1).mp hp), hne⟩)

/-- **Some prime ramifies in a number field other than `ℚ`.** This is Minkowski's bound in the form
`NumberField.exists_not_isUnramifiedIn`. -/
theorem ramifiedPrimes_nonempty (h : Module.finrank ℚ K ≠ 1) : (ramifiedPrimes K).Nonempty := by
  simpa only [Set.nonempty_def, mem_ramifiedPrimes_iff] using
    NumberField.exists_not_isUnramifiedIn (𝒪 := 𝓞 K) h

end NumberField
