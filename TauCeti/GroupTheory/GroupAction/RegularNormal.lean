/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupAction.Primitive
public import TauCeti.GroupTheory.Sylow.Basic

/-!
# Excluding regular normal subgroups of quasi-primitive groups

Several simplicity criteria for a group acting faithfully and quasi-primitively ask that no normal
subgroup act regularly, in the form `stabilizer N x ≠ ⊥` for every transitive normal subgroup `N`
(for instance `TauCeti.isSimpleGroup_of_isSimpleGroup_stabilizer_of_forall_stabilizer_ne_bot`).
This file supplies that hypothesis from the degree alone.

A regular normal subgroup `N` of a quasi-primitive group has no characteristic subgroups other
than `⊥` and `⊤` (`TauCeti.MulAction.eq_top_of_characteristic_of_stabilizer_eq_bot`), and its
order is the degree. A unique Sylow subgroup is characteristic, so Sylow's counting theorem
excludes regular normal subgroups for degrees such as `100`: a group of order `100` has a unique
Sylow `5`-subgroup, of order `25`.

## Main results

* `TauCeti.stabilizer_ne_bot_of_forall_dvd_natCard_modEq_one`: no normal subgroup acts
  regularly when two distinct primes divide the degree and, for one of them, `q`, the only divisor
  of the degree congruent to `1` modulo `q` is `1`.

## References

* J. D. Dixon and B. Mortimer, *Permutation Groups*, Chapter 4, for the normal subgroups of a
  primitive group.
-/

public section

namespace TauCeti

open _root_.MulAction TauCeti.MulAction

variable {G X : Type*} [Group G] [MulAction G X] [IsQuasiPreprimitive G X]

/-- In a quasi-primitive action, no normal subgroup acts regularly when two distinct primes `q`
and `r` divide the degree and `1` is the only divisor of the degree congruent to `1` modulo
`q`. -/
theorem stabilizer_ne_bot_of_forall_dvd_natCard_modEq_one {q r : ℕ}
    (hq : q.Prime) (hr : r.Prime) (hqr : q ≠ r)
    (hqdvd : q ∣ Nat.card X) (hrdvd : r ∣ Nat.card X)
    (hmod : ∀ d, d ∣ Nat.card X → d ≡ 1 [MOD q] → d = 1)
    (N : Subgroup G) [N.Normal] [IsPretransitive N X] (x : X) : stabilizer N x ≠ ⊥ := by
  intro hx
  have hcard : Nat.card N = Nat.card X := by
    rw [← Subgroup.index_bot, ← hx, index_stabilizer_of_transitive]
  have : Fact q.Prime := ⟨hq⟩
  have : Subsingleton (Sylow q N) :=
    subsingleton_sylow_of_forall_dvd_natCard_modEq_one (hcard ▸ hmod)
  have : Finite N := Nat.finite_of_card_ne_zero fun h0 ↦
    hq.ne_zero (Nat.succ_injective (hmod (q + 1) (hcard ▸ h0 ▸ dvd_zero _) (by simp [Nat.ModEq])))
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow q N))
  have hP : (P : Subgroup N) = ⊤ :=
    eq_top_of_characteristic_of_stabilizer_eq_bot hx (P.ne_bot_of_dvd_card (hcard ▸ hqdvd))
  -- So `N` is a `q`-group, although `r` divides its order.
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp P.isPGroup
  rw [hP, Subgroup.card_top, hcard] at hk
  exact hqr ((Nat.prime_dvd_prime_iff_eq hr hq).mp (hr.dvd_of_dvd_pow (hk ▸ hrdvd))).symm

end TauCeti
