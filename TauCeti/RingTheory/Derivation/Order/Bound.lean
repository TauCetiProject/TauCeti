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
* `Ideal.orderAt_derivationIdeal_eq_sub_one`: deduces
  `(I.derivationIdeal k).orderAt p = I.orderAt p - 1` from the order-increase step
  `n + 1 ≤ (I.derivationIdeal k).orderAt p → n + 2 ≤ I.orderAt p`.
* `Ideal.orderAt_derivationIdeal_iterate_eq_sub`: lifts the one-step order drop to iterates.
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

/-- If every positive lower bound `n + 1` on `(I.derivationIdeal k).orderAt p` improves to `n + 2`
on `I.orderAt p`, then `(I.derivationIdeal k).orderAt p = I.orderAt p - 1`. -/
theorem orderAt_derivationIdeal_eq_sub_one (k : Type*) [CommRing k] {R : Type*}
    [CommRing R] [Algebra k R] (I : Ideal R) (p : PrimeSpectrum R)
    (h : ∀ n : ℕ, ((n + 1 : ℕ) : ℕ∞) ≤ (I.derivationIdeal k).orderAt p →
      ((n + 2 : ℕ) : ℕ∞) ≤ I.orderAt p) :
    (I.derivationIdeal k).orderAt p = I.orderAt p - 1 := by
  refine le_antisymm ?_
    (tsub_le_iff_right.mpr (orderAt_le_orderAt_derivationIdeal_add_one k I p))
  refine ENat.forall_natCast_le_iff_le.mp fun m hm ↦ ?_
  cases m with
  | zero => simp
  | succ n => exact ENat.le_sub_of_add_le_right ENat.one_ne_top (h n (by exact_mod_cast hm))

/-- If `derivationIdeal k` lowers the order at `p` of every ideal by `1`, then its `n`-th iterate
lowers the order of `I` at `p` by `n`. -/
theorem orderAt_derivationIdeal_iterate_eq_sub (k : Type*) [CommRing k] {R : Type*}
    [CommRing R] [Algebra k R] (I : Ideal R) (p : PrimeSpectrum R) (n : ℕ)
    (h : ∀ J : Ideal R, (J.derivationIdeal k).orderAt p = J.orderAt p - 1) :
    ((derivationIdeal k)^[n] I).orderAt p = I.orderAt p - n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Function.iterate_succ_apply', h, ih, tsub_tsub, Nat.cast_succ]

end Ideal
