/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PGroup
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Basic
import Mathlib.GroupTheory.Perm.Cycle.Type
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClosedSubgroup
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Cyclic.FirstCohomology
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Inflation

/-!
# Vanishing of `H¹` of the pro-p class module for p-group quotients

Let `G` be a profinite group with `scd_p G ≤ 2` and let `V` be an open normal subgroup such
that `G ⧸ V` is a finite `p`-group. Then `H¹(G ⧸ V, V^ab(p)) = 0`.

The proof is the induction in NSW (3.6.4). For a nontrivial quotient, choose a central subgroup
of order `p` and let `W` be its inverse image in `G`. Restriction to `W ⧸ V` vanishes by the
prime-order case, while the induction hypothesis applies to `G ⧸ W`. Exactness of
inflation-restriction then gives the result.

## Main result

* `TauCeti.subsingleton_h1_abelianizationProP_of_isPGroup`: `H¹(G ⧸ V, V^ab(p)) = 0`
  when `G ⧸ V` is a finite `p`-group.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  the proof of (3.6.4), (ii) ⇒ (iii).
-/

public section

namespace TauCeti

open ContCohomology

universe u

private theorem subsingleton_h1_abelianizationProP_of_isPGroup_aux (p m : ℕ)
    (hp : p.Prime) :
    ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [CompactSpace G] [TotallyDisconnectedSpace G] (V : Subgroup G) [V.Normal],
      V.index = m → strictCohomologicalDimensionAt.{u} p G ≤ 2 →
        IsOpen (V : Set G) → IsPGroup p (G ⧸ V) →
          Subsingleton (H1 (G ⧸ V) (Additive (abelianizationProP p G V))) := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro G _ _ _ _ _ V _ hm hG hV hpV
      have : Finite (G ⧸ V) := V.quotient_finite_of_isOpen hV
      rcases subsingleton_or_nontrivial (G ⧸ V) with htrivial | hnontrivial
      · let _ := htrivial
        infer_instance
      · let _ := hnontrivial
        let _ : Fact p.Prime := ⟨hp⟩
        have hcenter : Nontrivial (Subgroup.center (G ⧸ V)) := hpV.center_nontrivial
        obtain ⟨z, hz⟩ : ∃ z : Subgroup.center (G ⧸ V), orderOf z = p := by
          refine exists_prime_orderOf_dvd_card' p ?_
          rcases (hpV.to_subgroup (Subgroup.center (G ⧸ V))).card_eq_or_dvd with h | h
          · exact absurd h Finite.one_lt_card.ne'
          · exact h
        let Z : Subgroup (G ⧸ V) := Subgroup.zpowers (z : G ⧸ V)
        have hZcenter : Z ≤ Subgroup.center (G ⧸ V) := Subgroup.zpowers_le.2 z.2
        let _ : Z.Normal := Subgroup.normal_of_le_center hZcenter
        let W : Subgroup G := Z.comap (QuotientGroup.mk' V)
        let _ : W.Normal := inferInstance
        have hVW : V ≤ W := by
          intro g hg
          rw [show W = Z.comap (QuotientGroup.mk' V) from rfl, Subgroup.mem_comap]
          change (g : G ⧸ V) ∈ Z
          rw [(QuotientGroup.eq_one_iff g).2 hg]
          exact Z.one_mem
        have hW : IsOpen (W : Set G) := Subgroup.isOpen_mono hVW hV
        have : V.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
        have hz1 : (z : G ⧸ V) ≠ 1 := by
          intro h
          have horder := Subgroup.orderOf_coe z
          rw [h, orderOf_one, hz] at horder
          exact hp.one_lt.ne horder
        have hVWne : V ≠ W := by
          intro heq
          have hzmem : (z : G ⧸ V) ∈ W.map (QuotientGroup.mk' V) := by
            refine ⟨(z : G ⧸ V).out, ?_, QuotientGroup.out_eq' (z : G ⧸ V)⟩
            change ((z : G ⧸ V).out : G ⧸ V) ∈ Z
            rw [QuotientGroup.out_eq']
            exact Subgroup.mem_zpowers (z : G ⧸ V)
          rw [← heq] at hzmem
          rcases hzmem with ⟨g, hg, hgz⟩
          exact hz1 (hgz ▸ ((QuotientGroup.eq_one_iff g).2 hg))
        have hindex : W.index < m := by
          rw [← hm]
          exact Subgroup.index_strictAnti (lt_of_le_of_ne hVW hVWne)
        have hpGW : IsPGroup p (G ⧸ W) := by
          refine (hpV.to_quotient (W.map (QuotientGroup.mk' V))).of_equiv ?_
          exact (quotientQuotientContinuousMulEquiv V W hVW hV).toMulEquiv
        have hsource : Subsingleton
            (H1 (G ⧸ W) (Additive (abelianizationProP p G W))) :=
          ih W.index hindex G W rfl hG hW hpGW
        have : CompactSpace W :=
          isCompact_iff_compactSpace.mp (W.isClosed_of_isOpen hW).isCompact
        have hWdim : strictCohomologicalDimensionAt.{u} p W ≤ 2 :=
          (strictCohomologicalDimensionAt_le_of_isClosed (W.isClosed_of_isOpen hW)).trans hG
        have hcard : Nat.card (W ⧸ V.subgroupOf W) = p := by
          calc
            Nat.card (W ⧸ V.subgroupOf W) =
                Nat.card (W.map (QuotientGroup.mk' V)) :=
              Nat.card_congr (quotientSubgroupOfEquivMap V W hV).toEquiv
            _ = Nat.card Z := by
              rw [show W = Z.comap (QuotientGroup.mk' V) from rfl,
                Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective V)]
            _ = p := by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hz]
        have hrestricted : Subsingleton
            (H1 (W ⧸ V.subgroupOf W)
              (Additive (abelianizationProP p W (V.subgroupOf W)))) :=
          subsingleton_h1_abelianizationProP_of_card_eq_prime hp hWdim
            (W.subgroupOf_isOpen V hV) hcard
        let _ : Subsingleton
            (H1 (W.map (QuotientGroup.mk' V))
              (Additive (abelianizationProP p G V))) :=
          (abelianizationProPSubgroupOfH1Equiv p hVW hV).toEquiv.subsingleton_congr.mp
            hrestricted
        refine ⟨fun x y ↦ ?_⟩
        have hres : explicitRes1 (G ⧸ V) (Additive (abelianizationProP p G V))
            (W.map (QuotientGroup.mk' V)) (x - y) = 0 := Subsingleton.elim _ _
        have hker : x - y ∈ (explicitRes1 (G ⧸ V)
            (Additive (abelianizationProP p G V)) (W.map (QuotientGroup.mk' V))).ker := hres
        rw [← abelianizationProPInfl1_exact p hVW hV hp hG] at hker
        rcases hker with ⟨a, ha⟩
        have : a = 0 := Subsingleton.elim _ _
        rw [this, map_zero] at ha
        exact sub_eq_zero.mp ha.symm

/-- **The class module of a finite `p`-group quotient has trivial `H¹`.** For a profinite group
`G` with `scd_p G ≤ 2` and an open normal subgroup `V` whose quotient is a `p`-group,
`H¹(G ⧸ V, V^ab(p)) = 0`. This is the degree-one part of NSW (3.6.4), (ii) ⇒ (iii). -/
theorem subsingleton_h1_abelianizationProP_of_isPGroup {p : ℕ} {G : Type u} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    {V : Subgroup G} [V.Normal] (hp : p.Prime)
    (hG : strictCohomologicalDimensionAt.{u} p G ≤ 2) (hV : IsOpen (V : Set G))
    (hpV : IsPGroup p (G ⧸ V)) :
    Subsingleton (H1 (G ⧸ V) (Additive (abelianizationProP p G V))) :=
  subsingleton_h1_abelianizationProP_of_isPGroup_aux p V.index hp G V rfl hG hV hpV

end TauCeti
