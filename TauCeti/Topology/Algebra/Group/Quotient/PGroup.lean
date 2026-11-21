/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PGroup
public import TauCeti.Topology.Algebra.Group.Quotient.Basic
import TauCeti.GroupTheory.PGroup

/-!
# Finite `p`-group quotients of topological groups

A nontrivial finite `p`-group quotient of a topological group by an open normal subgroup `V` has
an open normal subgroup `W > V` such that `W ⧸ V` has order `p` and `G ⧸ W` is a `p`-group. This is
the inductive step for reducing statements about finite `p`-group quotients to the prime-order
case.

## Main result

* `TauCeti.exists_isOpen_normal_lt_card_quotient_eq_prime`: the existence of such a `W`.
-/

public section

open Subgroup (quotientSubgroupOfEquivMap quotientQuotientContinuousMulEquiv)

namespace TauCeti

/-- A nontrivial finite `p`-group quotient `G ⧸ V` by an open normal subgroup has an open normal
overgroup `W > V` with `W ⧸ V` of order `p` and `G ⧸ W` a `p`-group: `W` is the preimage of a
central subgroup of order `p`. -/
theorem exists_isOpen_normal_lt_card_quotient_eq_prime {p : ℕ} (hp : p.Prime) {G : Type*}
    [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G] {V : Subgroup G} [V.Normal]
    (hV : IsOpen (V : Set G)) [Finite (G ⧸ V)] [Nontrivial (G ⧸ V)]
    (hpV : IsPGroup p (G ⧸ V)) :
    ∃ (W : Subgroup G) (_ : W.Normal), V < W ∧ IsOpen (W : Set G) ∧
      Nat.card (W ⧸ V.subgroupOf W) = p ∧ IsPGroup p (G ⧸ W) := by
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hzc, hz⟩ := hpV.exists_mem_center_orderOf_eq_prime
  let Z : Subgroup (G ⧸ V) := Subgroup.zpowers z
  have hZcenter : Z ≤ Subgroup.center (G ⧸ V) := Subgroup.zpowers_le.2 hzc
  let _ : Z.Normal := Subgroup.normal_of_le_center hZcenter
  set W : Subgroup G := Z.comap (QuotientGroup.mk' V) with hWdef
  let _ : W.Normal := inferInstance
  have hVW : V ≤ W :=
    (QuotientGroup.ker_mk' V).ge.trans (MonoidHom.ker_le_comap _ Z)
  have hWmap : W.map (QuotientGroup.mk' V) = Z := by
    rw [hWdef]
    exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective V) Z
  have hz1 : z ≠ 1 := fun h ↦ hp.one_lt.ne (by rw [← hz, h, orderOf_one])
  have hVW' : V < W := by
    have hbot : (⊥ : Subgroup (G ⧸ V)) < Z :=
      bot_lt_iff_ne_bot.2 fun h ↦ hz1 (by simpa using (Subgroup.zpowers_eq_bot.1 h))
    simpa [hWdef, MonoidHom.comap_bot, QuotientGroup.ker_mk'] using
      (Subgroup.comap_lt_comap_of_surjective (QuotientGroup.mk'_surjective V)).2 hbot
  refine ⟨W, inferInstance, hVW', Subgroup.isOpen_mono hVW hV, ?_, ?_⟩
  · calc
      Nat.card (W ⧸ V.subgroupOf W) = Nat.card (W.map (QuotientGroup.mk' V)) :=
        Nat.card_congr (quotientSubgroupOfEquivMap V W hV).toEquiv
      _ = Nat.card Z := by rw [hWmap]
      _ = p := by rw [Nat.card_zpowers, hz]
  · refine (hpV.to_quotient (W.map (QuotientGroup.mk' V))).of_equiv ?_
    exact (quotientQuotientContinuousMulEquiv V W hVW).toMulEquiv

end TauCeti
