/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Sylow.Basic
public import TauCeti.GroupTheory.Subgroup.Simple

/-!
# Sylow-local certificates for simplicity

To cover the prime-order elements of a finite group up to conjugacy, it suffices to cover the
order-`p` elements of one Sylow `p`-subgroup for each prime divisor `p` of the group order.
Conjugacy here is always conjugacy in the ambient group: distinct classes inside a Sylow
subgroup may fuse in that group.

This file proves the local-to-global coverage equivalence and combines it with normal
generation to certify simplicity. The local subgroups can be supplied as ordinary subgroups
whose orders have been independently checked to be the full prime parts of the group order.
Thus neither an enumeration of the ambient group nor a complete conjugacy classification is
needed. Normal-generation proofs can, for example, come from checked straight-line programs.

The underlying group-theoretic inputs are Mathlib's Sylow containment and conjugacy theorems,
and `IsMulTorsion.isSimpleGroup_of_isConj_of_normalClosure_eq_top`.
-/

public section

variable {G : Type*} [Group G] {p : ℕ}

namespace Sylow

/-- A set covers all order-`p` elements up to ambient conjugacy if and only if it covers the
order-`p` elements of a single Sylow `p`-subgroup. The representatives need not lie in that
Sylow subgroup. -/
theorem forall_orderOf_eq_exists_isConj_iff [Fact p.Prime] [Finite (Sylow p G)]
    (P : Sylow p G) (s : Set G) :
    (∀ g : G, orderOf g = p → ∃ x ∈ s, IsConj x g) ↔
      ∀ g : P, orderOf g = p → ∃ x ∈ s, IsConj x (g : G) := by
  refine ⟨fun h g hg ↦ h g ((Subgroup.orderOf_coe g).trans hg), fun h g hg ↦ ?_⟩
  obtain ⟨y, hy⟩ := P.exists_isConj_of_orderOf_dvd_pow (g := g) (n := 1) (by simp [hg])
  have hyorder : orderOf y = p := by
    obtain ⟨c, hc⟩ := hy
    exact (Subgroup.orderOf_coe y).symm.trans ((hc.orderOf_eq (c : G)).trans hg)
  obtain ⟨x, hx, hxy⟩ := h y hyorder
  exact ⟨x, hx, hxy.trans hy⟩

end Sylow

namespace Subgroup

/-- A subgroup of the full `p`-part order can be used in place of a bundled Sylow subgroup when
checking coverage of order-`p` elements up to ambient conjugacy. -/
theorem forall_orderOf_eq_exists_isConj_iff_of_card_eq [Finite G] [Fact p.Prime]
    (P : Subgroup G) (hP : Nat.card P = p ^ (Nat.card G).factorization p) (s : Set G) :
    (∀ g : G, orderOf g = p → ∃ x ∈ s, IsConj x g) ↔
      ∀ g : P, orderOf g = p → ∃ x ∈ s, IsConj x (g : G) := by
  rw [← Sylow.coe_ofCard P hP]
  exact (Sylow.ofCard P hP).forall_orderOf_eq_exists_isConj_iff s

end Subgroup

namespace TauCeti

/-- **Simplicity from Sylow-local conjugacy coverage and normal generation.** For each prime
divisor `p` of the order of a nontrivial finite group, choose a subgroup `P p` with order equal
to the full `p`-part. If its order-`p` elements are covered up to ambient conjugacy by a set `s`
of elements, each of which generates the whole group as a normal subgroup, the group is simple.

The subgroup orders, local coverage, and normal generation are separate proof obligations.
In particular, a subgroup with merely a prime-power order need not suffice. -/
theorem isSimpleGroup_of_card_eq_of_normalClosure_eq_top_of_isConj [Finite G] [Nontrivial G]
    (P : ℕ → Subgroup G) {s : Set G}
    (hcard : ∀ p, p.Prime → p ∣ Nat.card G →
      Nat.card (P p) = p ^ (Nat.card G).factorization p)
    (hgen : ∀ x ∈ s, Subgroup.normalClosure {x} = ⊤)
    (hcover : ∀ p, p.Prime → p ∣ Nat.card G →
      ∀ g : P p, orderOf g = p → ∃ x ∈ s, IsConj x (g : G)) : IsSimpleGroup G := by
  refine isMulTorsion_of_finite.isSimpleGroup_of_isConj_of_normalClosure_eq_top hgen
    fun g hg ↦ ?_
  have : Fact (orderOf g).Prime := ⟨hg⟩
  have hdvd := orderOf_dvd_natCard g
  exact ((P (orderOf g)).forall_orderOf_eq_exists_isConj_iff_of_card_eq
    (hcard _ hg hdvd) s).mpr (hcover _ hg hdvd) g rfl

end TauCeti
