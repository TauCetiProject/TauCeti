/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.Derivation.Localization
public import TauCeti.RingTheory.Ideal.Order.Basic

/-!
# Order bound for derivation ideals

Over arbitrary commutative rings `k` and `R`, the Leibniz rule and the unconditional localization
inclusion `Ideal.map_derivationIdeal_le` show that every `k`-derivation lowers ideal order at a
prime by at most one: `I.orderAt p ≤ (I.derivationIdeal k).orderAt p + 1`, with no finiteness,
regularity, or characteristic hypothesis.

## Main results

* `Ideal.orderAt_le_orderAt_derivationIdeal_add_one`: over commutative rings `k` and `R`,
  `I.orderAt p ≤ (I.derivationIdeal k).orderAt p + 1` at every prime `p`.
-/

public section

namespace Ideal

/-- At any prime of a commutative `k`-algebra `R` over a commutative ring `k`, the derivation
ideal lowers ideal order by at most one. -/
theorem orderAt_le_orderAt_derivationIdeal_add_one (k : Type*) [CommRing k] {R : Type*}
    [CommRing R] [Algebra k R] (I : Ideal R) (p : PrimeSpectrum R) :
    I.orderAt p ≤ (I.derivationIdeal k).orderAt p + 1 := by
  refine ENat.forall_natCast_le_iff_le.mp fun m hm ↦ ?_
  cases m with
  | zero => simp
  | succ n =>
    rw [natCast_le_orderAt_iff] at hm
    have hle : (I.derivationIdeal k).map (algebraMap R (Localization.AtPrime p.asIdeal)) ≤
        IsLocalRing.maximalIdeal (Localization.AtPrime p.asIdeal) ^ n :=
      (map_derivationIdeal_le k p.asIdeal.primeCompl I).trans
        (derivationIdeal_le_pow_of_le_pow_succ k hm)
    have hn : (n : ℕ∞) ≤ (I.derivationIdeal k).orderAt p :=
      (natCast_le_orderAt_iff _ p n).mpr hle
    push_cast
    gcongr

end Ideal
