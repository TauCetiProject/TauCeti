/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.MaximalProP
public import TauCeti.Topology.Algebra.Group.Profinite.Order
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic

/-!
# Pro-`p` groups and supernatural order

A profinite group is pro-`p` exactly when its supernatural order is supported at `p`. This
connects the finite-quotient definition of `IsProP` with the primewise invariant
`profiniteOrder`: every quotient by an open normal subgroup has prime-power order precisely
when every other prime has exponent zero in the supremum of the quotient orders.

The equivalent bound by the infinite supernatural prime power is the form used in
divisibility arguments.

## Main results

* `isProP_iff_profiniteOrder_apply_eq_zero`: pro-`p` groups are characterized by the
  vanishing of every exponent away from `p`.
* `isProP_iff_profiniteOrder_le_primePower`: the equivalent supernatural divisibility
  criterion.
* `proPKernel_eq_top_of_profiniteOrder_apply_eq_zero`: if `p` does not divide the supernatural
  order of a profinite group, then the group has no nontrivial pro-`p` quotient.
* `maximalProPQuotient.subsingleton_of_profiniteOrder_apply_eq_zero`: the corresponding maximal
  pro-`p` quotient is trivial.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.3.
-/

public section

namespace TauCeti

universe u

variable {p : ℕ} [Fact p.Prime] {G : Type u} [Group G] [TopologicalSpace G]
  [SeparatelyContinuousMul G] [CompactSpace G]

/-- A profinite group is pro-`p` exactly when every prime other than `p` has exponent zero
in its supernatural order. -/
theorem isProP_iff_profiniteOrder_apply_eq_zero :
    IsProP p G ↔ ∀ q : Nat.Primes, (q : ℕ) ≠ p → profiniteOrder G q = 0 := by
  rw [isProP_iff]
  constructor
  · intro hG q hqp
    rw [profiniteOrder_apply]
    apply iSup_eq_bot.mpr
    intro U
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hG U)
    rw [hn]
    let _ : Fact q.val.Prime := ⟨q.prop⟩
    have hval : padicValNat q.val (p ^ n) = 0 :=
      padicValNat_prime_prime_pow n hqp
    rw [hval]
    rfl
  · intro hG U
    apply IsPGroup.iff_card.mpr
    let c := Nat.card (G ⧸ U.toSubgroup)
    refine ⟨c.primeFactorsList.length, Nat.eq_prime_pow_of_unique_prime_dvd
      (Nat.card_pos.ne' : c ≠ 0) ?_⟩
    intro q hq hdvd
    by_contra hqp
    let q' : Nat.Primes := ⟨q, hq⟩
    let _ : Fact q.Prime := ⟨hq⟩
    have hzero : profiniteOrder G q' = 0 := hG q' hqp
    have hle : (padicValNat q c : ℕ∞) ≤ profiniteOrder G q' := by
      rw [profiniteOrder_apply]
      exact le_iSup
        (fun V : OpenNormalSubgroup G ↦
          (padicValNat q (Nat.card (G ⧸ V.toSubgroup)) : ℕ∞)) U
    rw [hzero] at hle
    have hval : padicValNat q c = 0 := by
      apply ENat.natCast_inj.mp
      exact le_antisymm hle bot_le
    exact (dvd_iff_padicValNat_ne_zero (p := q) (Nat.card_pos.ne' : c ≠ 0)).mp hdvd hval

/-- A profinite group is pro-`p` exactly when its supernatural order divides the infinite
`p`-power. -/
theorem isProP_iff_profiniteOrder_le_primePower :
    IsProP p G ↔
      profiniteOrder G ≤ Supernatural.primePower (⟨p, Fact.out⟩ : Nat.Primes) ⊤ := by
  rw [isProP_iff_profiniteOrder_apply_eq_zero]
  constructor
  · intro h
    refine Supernatural.le_iff.mpr fun q ↦ ?_
    by_cases hqp : q = (⟨p, Fact.out⟩ : Nat.Primes)
    · calc
        profiniteOrder G q ≤ ⊤ := le_top
        _ = Supernatural.primePower (⟨p, Fact.out⟩ : Nat.Primes) ⊤ q := by
          subst q
          exact (Supernatural.primePower_apply_self _ ⊤).symm
    · rw [Supernatural.primePower_apply_of_ne hqp]
      exact (h q fun hq ↦ hqp (Subtype.ext hq)).le
  · intro h q hqp
    have hq := Supernatural.le_iff.mp h q
    rw [Supernatural.primePower_apply_of_ne (p := (⟨p, Fact.out⟩ : Nat.Primes)) (q := q)
      fun hq' ↦ hqp (congrArg Subtype.val hq')] at hq
    exact bot_unique hq

section MaximalProPQuotient

/-- **A prime absent from the supernatural order gives no nontrivial pro-`p` quotient.** If the
`p`-exponent of the supernatural order of a profinite group `G` is zero, then its pro-`p` kernel
is all of `G`. -/
theorem proPKernel_eq_top_of_profiniteOrder_apply_eq_zero
    (h : profiniteOrder G (⟨p, Fact.out⟩ : Nat.Primes) = 0) : proPKernel p G = ⊤ := by
  rw [proPKernel_eq_top_iff]
  intro U hU
  rw [← QuotientGroup.subsingleton_iff]
  apply (Nat.card_eq_one_iff_unique.mp ?_).1
  apply hU.card_eq_or_dvd.resolve_right
  intro hp
  have hle : (padicValNat p (Nat.card (G ⧸ U.toSubgroup)) : ℕ∞) ≤
      profiniteOrder G ⟨p, Fact.out⟩ :=
    (Supernatural.ofNat_apply _ ⟨p, Fact.out⟩).symm.trans_le
      (Supernatural.le_iff.mp (ofNat_card_quotient_le_profiniteOrder G U) _)
  rw [h, nonpos_iff_eq_zero, Nat.cast_eq_zero] at hle
  exact (dvd_iff_padicValNat_ne_zero Nat.card_pos.ne').mp hp hle

/-- **The maximal pro-`p` quotient is trivial when `p` is absent from the supernatural order.** -/
theorem maximalProPQuotient.subsingleton_of_profiniteOrder_apply_eq_zero
    (h : profiniteOrder G (⟨p, Fact.out⟩ : Nat.Primes) = 0) :
    Subsingleton (maximalProPQuotient p G) :=
  maximalProPQuotient.subsingleton_iff.mpr
    (proPKernel_eq_top_of_profiniteOrder_apply_eq_zero h)

end MaximalProPQuotient

end TauCeti
