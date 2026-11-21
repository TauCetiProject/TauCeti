/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.GroupAction.OrbitRelQuotient
import TauCeti.GroupTheory.Index.Basic

/-!
# Orbits of a quotient group on normal-subgroup orbits

Let a group `G` act on a type `X`, and let `N` be a normal subgroup of `G`. The quotient group
`G ⧸ N` acts on the space of `N`-orbits `orbitRel.Quotient N X` by translating representatives
(`MulAction.orbitRel.Quotient.instMulActionQuotientGroup`). This file relates the orbits and
stabilizers of that quotient action to those of the original `G`-action on `X`.

Two `N`-orbits lie in the same `(G ⧸ N)`-orbit exactly when their representatives lie in the same
`G`-orbit, so the orbit space of `G ⧸ N` on `orbitRel.Quotient N X` identifies canonically with
the `G`-orbit space `orbitRel.Quotient G X`. The stabilizer in `G ⧸ N` of the `N`-orbit of `x` is
the image of `stabilizer G x` in `G ⧸ N`, whose preimage in `G` is `N ⊔ stabilizer G x`. Taking
indices via the relative-index identity across `N ⊔ stabilizer G x` yields the orbit-size
factorization

`Nat.card (orbit (G ⧸ N) ⟦x⟧) * Nat.card (orbit N x) = Nat.card (orbit G x)`

with no finiteness hypothesis on `G` or `X`.

## Main definitions

* `MulAction.orbitRel.Quotient.quotientEquiv`: canonical bijection between the `(G ⧸ N)`-orbits on
  `orbitRel.Quotient N X` and the `G`-orbits on `X`.

## Main results

* `MulAction.stabilizer_quotientGroup_mk`: the stabilizer in `G ⧸ N` of the `N`-orbit of `x` is
  the image of `stabilizer G x` under `QuotientGroup.mk' N`.
* `MulAction.comap_stabilizer_quotientGroup_mk`: the preimage in `G` of that stabilizer is
  `N ⊔ stabilizer G x`.
* `MulAction.card_orbit_quotientGroup_mul_card_orbit_normal`: the `(G ⧸ N)`-orbit size of the
  `N`-orbit of `x` times the `N`-orbit size of `x` equals the `G`-orbit size of `x`.
-/

public section

namespace MulAction

variable {G X : Type*} [Group G] [MulAction G X]

namespace orbitRel.Quotient

/-- **Orbits of a quotient group on normal-subgroup orbits.** For a normal subgroup `N` of `G`
acting on `X`, the `(G ⧸ N)`-orbits on the `N`-orbit space identify with the `G`-orbits on `X`. -/
@[to_additive
  /-- **Orbits of a quotient group on normal-subgroup orbits.** For a normal additive subgroup `N`
  of `G` acting on `X`, the `(G ⧸ N)`-orbits on the `N`-orbit space identify with the `G`-orbits on
  `X`. -/]
def quotientEquiv (N : Subgroup G) [N.Normal] :
    orbitRel.Quotient (G ⧸ N) (orbitRel.Quotient N X) ≃ orbitRel.Quotient G X where
  toFun := _root_.Quotient.lift
    (_root_.Quotient.lift (fun x ↦ (_root_.Quotient.mk'' x : orbitRel.Quotient G X))
      fun _ _ ⟨n, hn⟩ ↦ _root_.Quotient.sound' ⟨(n : G), hn⟩)
    fun ω₁ ω₂ h ↦ by
      induction ω₁ using _root_.Quotient.inductionOn' with | h x =>
      induction ω₂ using _root_.Quotient.inductionOn' with | h y =>
      obtain ⟨g, hg⟩ := mem_orbit_iff.mp (orbitRel_apply.mp h)
      induction g using QuotientGroup.induction_on with | H g =>
      rw [mk_smul_mk] at hg
      obtain ⟨n, hn⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (_root_.Quotient.exact' hg))
      exact _root_.Quotient.sound' (orbitRel_apply.mpr
        (mem_orbit_iff.mpr ⟨(n : G)⁻¹ * g, by
          rw [mul_smul, inv_smul_eq_iff, ← Subgroup.smul_def, hn]⟩))
  invFun := _root_.Quotient.lift
    (fun x ↦ _root_.Quotient.mk'' (_root_.Quotient.mk'' x : orbitRel.Quotient N X))
    fun _ _ h ↦ by
      obtain ⟨g, hg⟩ := mem_orbit_iff.mp (orbitRel_apply.mp h)
      exact _root_.Quotient.sound' (orbitRel_apply.mpr (mem_orbit_iff.mpr
        ⟨(g : G ⧸ N), by rw [mk_smul_mk, hg]⟩))
  left_inv q := by
    induction q using _root_.Quotient.inductionOn' with | h ω =>
    induction ω using _root_.Quotient.inductionOn' with | h x =>
    rfl
  right_inv q := by
    induction q using _root_.Quotient.inductionOn' with | h x =>
    rfl

/-- `quotientEquiv` sends the `(G ⧸ N)`-orbit of the `N`-orbit of `x` to the `G`-orbit of `x`. -/
@[to_additive (attr := simp)
  /-- `quotientEquiv` sends the `(G ⧸ N)`-orbit of the `N`-orbit of `x` to the `G`-orbit of
  `x`. -/]
theorem quotientEquiv_mk (N : Subgroup G) [N.Normal] (x : X) :
    quotientEquiv N (_root_.Quotient.mk'' (_root_.Quotient.mk'' x : orbitRel.Quotient N X)) =
      _root_.Quotient.mk'' x :=
  (rfl)

/-- The inverse of `quotientEquiv` sends the `G`-orbit of `x` to the `(G ⧸ N)`-orbit of the
`N`-orbit of `x`. -/
@[to_additive (attr := simp)
  /-- The inverse of `quotientEquiv` sends the `G`-orbit of `x` to the `(G ⧸ N)`-orbit of the
  `N`-orbit of `x`. -/]
theorem quotientEquiv_symm_mk (N : Subgroup G) [N.Normal] (x : X) :
    (quotientEquiv N).symm (_root_.Quotient.mk'' x) =
      _root_.Quotient.mk'' (_root_.Quotient.mk'' x : orbitRel.Quotient N X) :=
  (rfl)

end orbitRel.Quotient

/-- **Stabilizer of an `N`-orbit in `G ⧸ N`.** An element of `G ⧸ N` stabilizes the `N`-orbit of
`x` exactly when it is the image of an element of `stabilizer G x`. -/
@[to_additive
  /-- **Stabilizer of an `N`-orbit in `G ⧸ N`.** An element of `G ⧸ N` stabilizes the `N`-orbit of
  `x` exactly when it is the image of an element of `stabilizer G x`. -/]
theorem stabilizer_quotientGroup_mk (N : Subgroup G) [N.Normal] (x : X) :
    stabilizer (G ⧸ N) (Quotient.mk'' x : orbitRel.Quotient N X) =
      (stabilizer G x).map (QuotientGroup.mk' N) := by
  ext q
  induction q using QuotientGroup.induction_on with | H g =>
  simp only [mem_stabilizer_iff, orbitRel.Quotient.mk_smul_mk, Subgroup.mem_map,
    QuotientGroup.mk'_apply]
  constructor
  · intro h
    obtain ⟨n, hn⟩ := mem_orbit_iff.mp (orbitRel_apply.mp (Quotient.exact' h))
    refine ⟨(n : G)⁻¹ * g, ?_, ?_⟩
    · rw [mul_smul, inv_smul_eq_iff, ← Subgroup.smul_def, hn]
    · rw [QuotientGroup.eq, mul_inv_rev, inv_inv]
      exact ‹N.Normal›.conj_mem' n n.property g
  · rintro ⟨s, hs, hsg⟩
    have hns : s⁻¹ * g ∈ N := QuotientGroup.eq.mp hsg
    have hgn : g * s⁻¹ ∈ N := by
      have h := ‹N.Normal›.conj_mem (s⁻¹ * g) hns s
      rwa [← mul_assoc, mul_inv_cancel, one_mul] at h
    exact Quotient.sound' (orbitRel_apply.mpr (mem_orbit_iff.mpr
      ⟨⟨g * s⁻¹, hgn⟩, by rw [Subgroup.smul_def, mul_smul]; congr 1; rw [inv_smul_eq_iff, hs]⟩))

/-- **Preimage of the stabilizer of an `N`-orbit.** The elements of `G` whose coset stabilizes the
`N`-orbit of `x` form the join `N ⊔ stabilizer G x`. -/
@[to_additive
  /-- **Preimage of the stabilizer of an `N`-orbit.** The elements of `G` whose coset stabilizes the
  `N`-orbit of `x` form the join `N ⊔ stabilizer G x`. -/]
theorem comap_stabilizer_quotientGroup_mk (N : Subgroup G) [N.Normal] (x : X) :
    (stabilizer (G ⧸ N) (Quotient.mk'' x : orbitRel.Quotient N X)).comap (QuotientGroup.mk' N) =
      N ⊔ stabilizer G x := by
  rw [stabilizer_quotientGroup_mk, Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_comm]

/-- **Orbit-size factorization across a normal subgroup.** For a normal subgroup `N` of `G`, the
size of the `(G ⧸ N)`-orbit of the `N`-orbit of `x`, times the size of the `N`-orbit of `x`, equals
the size of the `G`-orbit of `x`. No finiteness hypothesis is needed. -/
@[to_additive
  /-- **Orbit-size factorization across a normal subgroup.** For a normal additive subgroup `N` of
  `G`, the size of the `(G ⧸ N)`-orbit of the `N`-orbit of `x`, times the size of the `N`-orbit of
  `x`, equals the size of the `G`-orbit of `x`. No finiteness hypothesis is needed. -/]
theorem card_orbit_quotientGroup_mul_card_orbit_normal (N : Subgroup G) [N.Normal] (x : X) :
    Nat.card (orbit (G ⧸ N) (Quotient.mk'' x : orbitRel.Quotient N X)) * Nat.card (orbit N x) =
      Nat.card (orbit G x) := by
  calc
    Nat.card (orbit (G ⧸ N) (Quotient.mk'' x : orbitRel.Quotient N X)) * Nat.card (orbit N x)
      = (stabilizer (G ⧸ N) (Quotient.mk'' x : orbitRel.Quotient N X)).index *
          (stabilizer N x).index := by
        rw [Nat.card_congr (orbitEquivQuotientStabilizer _ _),
          Nat.card_congr (orbitEquivQuotientStabilizer _ _),
          Subgroup.index_eq_card, Subgroup.index_eq_card]
    _ = (N ⊔ stabilizer G x).index * (stabilizer G x).relIndex N := by
        rw [← Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective N),
          comap_stabilizer_quotientGroup_mk, ← stabilizer_subgroupOf, Subgroup.relIndex]
    _ = (stabilizer G x).relIndex (stabilizer G x ⊔ N) * (stabilizer G x ⊔ N).index := by
        rw [Subgroup.relIndex_sup_of_le_normalizer Subgroup.le_normalizer_of_normal,
          sup_comm, mul_comm]
    _ = (stabilizer G x).index := Subgroup.relIndex_mul_index le_sup_left
    _ = Nat.card (orbit G x) := by
        rw [Nat.card_congr (orbitEquivQuotientStabilizer G x), Subgroup.index_eq_card]

end MulAction
