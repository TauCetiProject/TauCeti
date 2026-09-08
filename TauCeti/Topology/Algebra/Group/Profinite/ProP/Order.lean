/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic
public import TauCeti.Topology.Algebra.Group.Profinite.Order
public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Basic

/-!
# Pro-`p` groups and supernatural order

A profinite group is pro-`p` exactly when its supernatural order is supported at `p`. This
connects the finite-quotient definition of `IsProP` with the primewise invariant
`profiniteOrder`: every finite quotient has prime-power order precisely when every other
prime has exponent zero in the supremum of the quotient orders.

The equivalent bound by the infinite supernatural prime power is the form used in
divisibility arguments.

## Main results

* `isProP_iff_profiniteOrder_apply_eq_zero`: pro-`p` groups are characterized by the
  vanishing of every exponent away from `p`.
* `isProP_iff_profiniteOrder_le_primePower`: the equivalent supernatural divisibility
  criterion.

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
  let pp : Nat.Primes := ⟨p, Fact.out⟩
  have hpp : IsProP pp.val G ↔
      profiniteOrder G ≤ Supernatural.primePower pp ⊤ := by
    let _ : Fact pp.val.Prime := ⟨pp.prop⟩
    rw [isProP_iff_profiniteOrder_apply_eq_zero]
    constructor
    · intro h
      apply Supernatural.le_iff.mpr
      intro q
      by_cases hqp : q = pp
      · calc
          profiniteOrder G q ≤ ⊤ := le_top
          _ = Supernatural.primePower pp ⊤ q := by
            subst q
            exact (TauCeti.Supernatural.primePower_apply_self pp ⊤).symm
      · rw [TauCeti.Supernatural.primePower_apply_of_ne hqp]
        exact (h q (fun hqp' ↦ hqp (Subtype.ext hqp'))).le
    · intro h q hqp
      have hq := Supernatural.le_iff.mp h q
      rw [TauCeti.Supernatural.primePower_apply_of_ne
        (p := pp) (q := q)
        (fun h ↦ hqp (congrArg Subtype.val h))] at hq
      exact bot_unique hq
  exact hpp

end TauCeti
