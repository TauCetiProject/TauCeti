/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.GroupAction.Primitive
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

A faithful quasiprimitive action can replace all but one prime of such a certificate. Every
nontrivial normal subgroup is then transitive, so its order is divisible by the degree. If a
prime `p` divides the degree but `p ^ 2` does not divide the group order, the Sylow
`p`-subgroups have order `p` and are conjugate, so the normal subgroup contains every element of
order `p`. One element of order `p` that normally generates the group then certifies simplicity.
This applies, for instance, to the Mathieu groups `M₁₁` and `M₂₃` acting on `11` and `23` points.

## Main results

* `TauCeti.isSimpleGroup_of_card_eq_of_normalClosure_eq_top_of_isConj`: simplicity from
  Sylow-local coverage of the elements of prime order and their normal generation.
* `TauCeti.isSimpleGroup_of_isQuasiPreprimitive_of_normalClosure_eq_top`: simplicity of a group
  with a faithful quasiprimitive action from one normally generating element of prime order `p`,
  where `p` divides the degree and `p ^ 2` does not divide the group order.
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

open MulAction in
/-- **Simplicity from a quasiprimitive action and one normal generator.** Let a finite group act
faithfully and quasiprimitively, for instance primitively, on `X`. Let `p` be a prime dividing the
degree `Nat.card X` with `p ^ 2` not dividing the group order. If some element of order `p`
generates the group as a normal subgroup, the group is simple. -/
theorem isSimpleGroup_of_isQuasiPreprimitive_of_normalClosure_eq_top [Finite G] {X : Type*}
    [MulAction G X] [FaithfulSMul G X] [IsQuasiPreprimitive G X] (hp : p.Prime)
    (hpX : p ∣ Nat.card X) (hsq : ¬ p ^ 2 ∣ Nat.card G) {r : G} (hr : orderOf r = p)
    (hgen : Subgroup.normalClosure {r} = ⊤) : IsSimpleGroup G := by
  have : Fact p.Prime := ⟨hp⟩
  have : Nontrivial G := ⟨⟨r, 1, fun h ↦ hp.one_lt.ne' (by rw [← hr, h, orderOf_one])⟩⟩
  refine ⟨fun N hN ↦ or_iff_not_imp_left.mpr fun hbot ↦ ?_⟩
  -- A nontrivial normal subgroup moves some point, since the action is faithful.
  have hfix : fixedPoints N X ≠ Set.univ := fun h ↦ hbot <|
    (Subgroup.eq_bot_iff_forall N).mpr fun n hn ↦ eq_of_smul_eq_smul (α := X) fun x ↦ by
      simpa using (h ▸ Set.mem_univ x : x ∈ fixedPoints N X) ⟨n, hn⟩
  have := IsQuasiPreprimitive.isPretransitive_of_normal hfix
  obtain ⟨x, -⟩ := Set.nonempty_compl.mpr hfix
  -- Being transitive, it has order divisible by the degree, hence an element of order `p`.
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := N) p <|
    hpX.trans (index_stabilizer_of_transitive N x ▸ (stabilizer N x).index_dvd_card)
  obtain ⟨y, hy⟩ := exists_mul_mul_inv_mem_zpowers_of_not_sq_dvd hsq hr
    (h := (g : G)) (by rw [Subgroup.orderOf_coe, hg])
  -- Its conjugate `y * g * y⁻¹` lies in `N` and generates the same subgroup as `r`.
  have hmem : y * g * y⁻¹ ∈ N := hN.conj_mem _ g.2 y
  have hzpow : Subgroup.zpowers (y * g * y⁻¹) = Subgroup.zpowers r :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hy) <| by
      rw [Nat.card_zpowers, Nat.card_zpowers, hr, ← (SemiconjBy.conj_mk y _).orderOf_eq,
        Subgroup.orderOf_coe, hg]
  have hrN : r ∈ N := Subgroup.zpowers_le.mpr hmem (hzpow ▸ Subgroup.mem_zpowers r)
  exact top_le_iff.mp (hgen ▸ Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr hrN))

end TauCeti
