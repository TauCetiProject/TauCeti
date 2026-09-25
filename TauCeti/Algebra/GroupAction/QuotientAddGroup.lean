/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Subgroup.ZPowers.Basic
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.GroupTheory.QuotientGroup.Defs

/-!
# Distributive actions on the quotient by a stable additive subgroup

Let a monoid `G` act distributively on an additive group `M`, and let `N` be a `G`-stable
additive subgroup: `g • x ∈ N` for every `g : G` and `x ∈ N`. Then `G` acts distributively on
`N` by restriction. When `M` is commutative, the action also descends to the quotient `M ⧸ N`,
with `g • ↑x = ↑(g • x)`. Mathlib provides these actions for submodules
(`Submodule.Quotient.distribMulAction`) but not for a bare `G`-stable additive subgroup, where
the stability is a hypothesis rather than an instance, so the actions are definitions rather than
instances.

The file also records that stability passes to `N ⊔ zmultiples x` when the class of `x` is fixed
by `G` modulo `N`, which is what lets a `G`-stable subgroup be enlarged one element at a time.

## Main declarations

* `AddSubgroup.restrictDistribMulAction`: the action of `G` on a `G`-stable `N` by restriction.
* `AddSubgroup.restrictDistribMulAction_coe_smul`: its defining equation `↑(g • x) = g • ↑x`.
* `AddSubgroup.quotientDistribMulAction`: the action of `G` on `M ⧸ N` for a `G`-stable `N`.
* `AddSubgroup.quotientDistribMulAction_smul_mk`: its defining equation `g • ↑x = ↑(g • x)`.
* `AddSubgroup.subquotientDistribMulAction`: the induced action on `K ⧸ N.addSubgroupOf K`
  for two stable subgroups `N` and `K`, the quotient action for the restricted action on `K`.
* `TauCeti.smul_mem_sup_zmultiples`: if `N` is `G`-stable and `g • x - x ∈ N` for every `g`,
  then `N ⊔ zmultiples x` is `G`-stable.
* `TauCeti.subquotient_smul_eq_self_of_eq_sup_zmultiples`: adjoining a generator fixed modulo
  `N` gives a quotient on which the induced action is trivial.
-/

public section

namespace TauCeti

variable {G : Type*} [Monoid G] {M : Type*}

section AddGroup

variable [AddGroup M] [DistribMulAction G M]

/-- The action of `G` on a `G`-stable additive subgroup `N` of `M`, by restriction. It is a
definition rather than an instance because it depends on the stability hypothesis. See note
[reducible non-instances]. -/
abbrev _root_.AddSubgroup.restrictDistribMulAction (N : AddSubgroup M)
    (hN : ∀ g : G, ∀ x ∈ N, g • x ∈ N) : DistribMulAction G N :=
  letI : SMul G N := ⟨fun g x ↦ ⟨g • (x : M), hN g x x.property⟩⟩
  N.subtype_injective.distribMulAction N.subtype fun _ _ ↦ rfl

/-- The defining equation of `AddSubgroup.restrictDistribMulAction`: the inclusion of `N` in `M`
is equivariant. -/
@[simp]
theorem _root_.AddSubgroup.restrictDistribMulAction_coe_smul (N : AddSubgroup M)
    (hN : ∀ g : G, ∀ x ∈ N, g • x ∈ N) (g : G) (x : N) :
    letI := N.restrictDistribMulAction hN
    ((g • x : N) : M) = g • (x : M) :=
  rfl

/-- The inclusion of one `G`-stable additive subgroup in another is equivariant for the
restricted actions. -/
theorem _root_.AddSubgroup.restrictDistribMulAction_inclusion_smul {N K : AddSubgroup M}
    (hN : ∀ g : G, ∀ x ∈ N, g • x ∈ N) (hK : ∀ g : G, ∀ x ∈ K, g • x ∈ K) (h : N ≤ K)
    (g : G) (x : N) :
    letI := N.restrictDistribMulAction hN
    letI := K.restrictDistribMulAction hK
    AddSubgroup.inclusion h (g • x) = g • AddSubgroup.inclusion h x :=
  Subtype.ext (by
    simp only [AddSubgroup.coe_inclusion, AddSubgroup.restrictDistribMulAction_coe_smul])

end AddGroup

variable [AddCommGroup M] [DistribMulAction G M]

/-- The action of `G` on the quotient of `M` by a `G`-stable additive subgroup `N`, with
`g • ↑x = ↑(g • x)`. It is a definition rather than an instance because it depends on the
stability hypothesis. See note [reducible non-instances]. -/
abbrev _root_.AddSubgroup.quotientDistribMulAction (N : AddSubgroup M)
    (hN : ∀ g : G, ∀ x ∈ N, g • x ∈ N) : DistribMulAction G (M ⧸ N) :=
  letI : SMul G (M ⧸ N) :=
    ⟨fun g ↦ QuotientAddGroup.map N N (DistribSMul.toAddMonoidHom M g) fun x hx ↦ hN g x hx⟩
  (QuotientAddGroup.mk'_surjective N).distribMulAction (QuotientAddGroup.mk' N) fun _ _ ↦ rfl

/-- The defining equation of `AddSubgroup.quotientDistribMulAction` on the class of an
element. -/
@[simp]
theorem _root_.AddSubgroup.quotientDistribMulAction_smul_mk (N : AddSubgroup M)
    (hN : ∀ g : G, ∀ x ∈ N, g • x ∈ N) (g : G) (x : M) :
    letI := N.quotientDistribMulAction hN
    g • (x : M ⧸ N) = ((g • x : M) : M ⧸ N) :=
  rfl

/-- The induced action on `K ⧸ N.addSubgroupOf K` for two `G`-stable additive subgroups: the
quotient action `AddSubgroup.quotientDistribMulAction` for the restricted action
`AddSubgroup.restrictDistribMulAction` on `K`. The equation
`AddSubgroup.quotientDistribMulAction_smul_mk`, applied to that restricted action, computes its
value on quotient classes. See note [reducible non-instances]. -/
abbrev _root_.AddSubgroup.subquotientDistribMulAction (N K : AddSubgroup M)
    (hN : ∀ g : G, ∀ x ∈ N, g • x ∈ N) (hK : ∀ g : G, ∀ x ∈ K, g • x ∈ K) :
    DistribMulAction G (K ⧸ N.addSubgroupOf K) :=
  letI := K.restrictDistribMulAction hK
  (N.addSubgroupOf K).quotientDistribMulAction fun g x hx ↦
    AddSubgroup.mem_addSubgroupOf.mpr (hN g x (AddSubgroup.mem_addSubgroupOf.mp hx))

/-- If `N` is `G`-stable and `g • x - x ∈ N` for every `g`, then `N ⊔ zmultiples x` is
`G`-stable. The element is explicit so that the partial application to `hN` and `hx` has the
shape of a stability hypothesis. -/
theorem smul_mem_sup_zmultiples {N : AddSubgroup M} (hN : ∀ g : G, ∀ y ∈ N, g • y ∈ N) {x : M}
    (hx : ∀ g : G, g • x - x ∈ N) (g : G) (y : M) (hy : y ∈ N ⊔ AddSubgroup.zmultiples x) :
    g • y ∈ N ⊔ AddSubgroup.zmultiples x := by
  obtain ⟨n, hn, m, hm, rfl⟩ := AddSubgroup.mem_sup.mp hy
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
  have : g • (n + k • x) = (g • n + k • (g • x - x)) + k • x := by
    rw [smul_add, smul_comm, zsmul_sub, add_assoc, sub_add_cancel]
  rw [this]
  exact AddSubgroup.add_mem _
    (AddSubgroup.mem_sup_left
      (AddSubgroup.add_mem _ (hN g n hn) (AddSubgroup.zsmul_mem _ (hx g) k)))
    (AddSubgroup.mem_sup_right (AddSubgroup.zsmul_mem _ (AddSubgroup.mem_zmultiples x) k))

/-- If `K` is obtained from `N` by adjoining an element fixed modulo `N`, then the induced
action on `K ⧸ N.addSubgroupOf K` is trivial. The stability of `K` is automatic, by
`TauCeti.smul_mem_sup_zmultiples`, so the induced action is stated for that proof of it; any other
proof gives the same action by proof irrelevance. No finiteness or torsion assumption is
needed. -/
theorem subquotient_smul_eq_self_of_eq_sup_zmultiples {N K : AddSubgroup M}
    (hN : ∀ g : G, ∀ y ∈ N, g • y ∈ N)
    {x : M} (hgen : K = N ⊔ AddSubgroup.zmultiples x) (hx : ∀ g : G, g • x - x ∈ N)
    (g : G) (y : K ⧸ N.addSubgroupOf K) :
    letI := N.subquotientDistribMulAction K hN (hgen ▸ smul_mem_sup_zmultiples hN hx)
    g • y = y := by
  have hK : ∀ g : G, ∀ y ∈ K, g • y ∈ K := hgen ▸ smul_mem_sup_zmultiples hN hx
  let := K.restrictDistribMulAction hK
  let := N.subquotientDistribMulAction K hN hK
  obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective y
  rw [AddSubgroup.quotientDistribMulAction_smul_mk, QuotientAddGroup.eq_iff_sub_mem,
    AddSubgroup.mem_addSubgroupOf, AddSubgroup.coe_sub,
    AddSubgroup.restrictDistribMulAction_coe_smul]
  have hy : (y : M) ∈ N ⊔ AddSubgroup.zmultiples x := hgen ▸ y.property
  obtain ⟨n, hn, m, hm, hnm⟩ := AddSubgroup.mem_sup.mp hy
  obtain ⟨k, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hm
  rw [← hnm, smul_add, smul_comm g k, add_sub_add_comm, ← zsmul_sub]
  exact N.add_mem (N.sub_mem (hN g n hn) hn) (N.zsmul_mem (hx g) k)

end TauCeti
