/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PGroup
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.Basic
public import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Basic
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClosedSubgroup
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Cyclic.FirstCohomology
import TauCeti.RepresentationTheory.Homological.ContCohomology.CohomologicalDimension.ClassModule.Inflation
import TauCeti.Topology.Algebra.Group.Quotient.PGroup

/-!
# Vanishing of `H¹` of the pro-p class module for p-group quotients

Let `G` be a profinite group with `scd_p G ≤ 2` and let `V` be an open normal subgroup such
that `G ⧸ V` is a finite `p`-group. Then `H¹(G ⧸ V, V^ab(p)) = 0`.

This is the degree-one half of the class-module axioms for `V^ab(p)` in the `p`-group case of
NSW (3.6.4), (ii) ⇒ (iii), extending the prime-order case by the reduction of NSW (3.6.3)
through a central subgroup of order `p`. It is the input for the corresponding
statement about the class `u_{G/V}(p)` in `H²` for `p`-group quotients, and then for the Sylow
reduction to arbitrary finite quotients `G ⧸ V`.

## Main result

* `TauCeti.subsingleton_h1_abelianizationProP_of_isPGroup`: `H¹(G ⧸ V, V^ab(p)) = 0`
  when `G ⧸ V` is a finite `p`-group.

## References

* J. Neukirch, A. Schmidt and K. Wingberg, *Cohomology of Number Fields*, 2nd ed.,
  (3.6.3) and the proof of (3.6.4), (ii) ⇒ (iii).
-/

public section

namespace TauCeti

open ContCohomology

universe u

section Step

variable {p : ℕ} {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [CompactSpace G] [TotallyDisconnectedSpace G] {V W : Subgroup G} [V.Normal] [W.Normal]

/-- For open normal subgroups `V ≤ W` of `G` with `scd_p G ≤ 2`, if `H¹(G ⧸ W, W^ab(p))` and
`H¹(W ⧸ V, V^ab(p))` vanish, then so does `H¹(G ⧸ V, V^ab(p))`. -/
theorem subsingleton_h1_abelianizationProP_of_le (hp : p.Prime)
    (h : strictCohomologicalDimensionAt.{u} p G ≤ 2) (hVW : V ≤ W) (hV : IsOpen (V : Set G))
    [Subsingleton (H1 (G ⧸ W) (Additive (abelianizationProP p G W)))]
    [Subsingleton
      (H1 (W ⧸ V.subgroupOf W) (Additive (abelianizationProP p W (V.subgroupOf W))))] :
    Subsingleton (H1 (G ⧸ V) (Additive (abelianizationProP p G V))) := by
  -- The map `i` from `H¹(G ⧸ W, W^ab(p))` is onto the kernel of restriction to the image of `W`
  -- in `G ⧸ V`, and that restriction lands in `H¹(W ⧸ V, V^ab(p))`.
  have : Finite (G ⧸ V) := V.quotient_finite_of_isOpen hV
  have : V.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
  have : Subsingleton (H1 (W.map (QuotientGroup.mk' V)) (Additive (abelianizationProP p G V))) :=
    (abelianizationProPSubgroupOfH1Equiv p hVW hV).surjective.subsingleton
  have hsurj : Function.Surjective (abelianizationProPInfl1 p hVW hV) := by
    rw [← AddMonoidHom.range_eq_top, abelianizationProPInfl1_exact p hVW hV hp h,
      AddMonoidHom.ker_eq_top_iff]
    ext
    exact Subsingleton.elim _ _
  exact hsurj.subsingleton

end Step

private theorem subsingleton_h1_abelianizationProP_of_isPGroup_aux (p m : ℕ)
    (hp : p.Prime) :
    ∀ (G : Type u) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [CompactSpace G] [TotallyDisconnectedSpace G] (V : Subgroup G) [V.Normal],
      V.index = m → strictCohomologicalDimensionAt.{u} p G ≤ 2 →
        IsOpen (V : Set G) → IsPGroup p (G ⧸ V) →
          Subsingleton (H1 (G ⧸ V) (Additive (abelianizationProP p G V))) := by
  induction m using Nat.strong_induction_on with
  | ind m ih =>
      intro G _ _ _ _ _ V _ hm hG hV hpV
      have : Finite (G ⧸ V) := V.quotient_finite_of_isOpen hV
      rcases subsingleton_or_nontrivial (G ⧸ V) with htrivial | hnontrivial
      · let _ := htrivial
        infer_instance
      · let _ := hnontrivial
        obtain ⟨W, _, hVW, hW, hcard, hpGW⟩ :=
          exists_isOpen_normal_lt_card_quotient_eq_prime hp hV hpV
        have : V.FiniteIndex := Subgroup.finiteIndex_of_finite_quotient
        have hindex : W.index < m := by
          rw [← hm]
          exact Subgroup.index_strictAnti hVW
        have hsource : Subsingleton
            (H1 (G ⧸ W) (Additive (abelianizationProP p G W))) :=
          ih W.index hindex G W rfl hG hW hpGW
        have : CompactSpace W :=
          isCompact_iff_compactSpace.mp (W.isClosed_of_isOpen hW).isCompact
        have hWdim : strictCohomologicalDimensionAt.{u} p W ≤ 2 :=
          (strictCohomologicalDimensionAt_le_of_isClosed (W.isClosed_of_isOpen hW)).trans hG
        have hrestricted : Subsingleton
            (H1 (W ⧸ V.subgroupOf W)
              (Additive (abelianizationProP p W (V.subgroupOf W)))) :=
          subsingleton_h1_abelianizationProP_of_card_eq_prime hp hWdim
            (W.subgroupOf_isOpen V hV) hcard
        let _ := hsource
        let _ := hrestricted
        exact subsingleton_h1_abelianizationProP_of_le hp hG hVW.le hV

/-- **The class module of a finite `p`-group quotient has trivial `H¹`.** For a profinite group
`G` with `scd_p G ≤ 2` and an open normal subgroup `V` whose quotient is a `p`-group,
`H¹(G ⧸ V, V^ab(p)) = 0`. This is the degree-one part of NSW (3.6.4), (ii) ⇒ (iii), in the
`p`-group case reduced to prime order as in NSW (3.6.3). -/
theorem subsingleton_h1_abelianizationProP_of_isPGroup {p : ℕ} {G : Type u} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G] [TotallyDisconnectedSpace G]
    {V : Subgroup G} [V.Normal] (hp : p.Prime)
    (hG : strictCohomologicalDimensionAt.{u} p G ≤ 2) (hV : IsOpen (V : Set G))
    (hpV : IsPGroup p (G ⧸ V)) :
    Subsingleton (H1 (G ⧸ V) (Additive (abelianizationProP p G V))) :=
  subsingleton_h1_abelianizationProP_of_isPGroup_aux p V.index hp G V rfl hG hV hpV

end TauCeti
