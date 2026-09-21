/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Algebra.Group.Profinite.ProP.Burnside

/-!
# Surjectivity detected by the Frattini quotient

A homomorphism into a profinite pro-`p` group has dense range exactly when its composites
with all index-`p` quotient maps are surjective. Equivalently, its composite with the
Frattini quotient map has dense range. For continuous homomorphisms from compact groups,
the images are closed, so these criteria detect surjectivity itself.

These are the homomorphism forms of Burnside's basis theorem: they check surjectivity of a
map given on generators by checking its values modulo the Frattini subgroup. The source
need not be pro-`p`, and the density criteria need no topology on the source.

## References

* L. Ribes and P. Zalesskii, *Profinite Groups*, Section 2.8.
-/

public section

namespace TauCeti

namespace IsProP

variable {p : ℕ} [hp : Fact p.Prime]
variable {G : Type*} [Group G]
variable {H : Type*} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]
  [CompactSpace H] [TotallyDisconnectedSpace H]

/-- A homomorphism into a profinite pro-`p` group has dense range exactly when it surjects
onto every quotient of index `p`. No topology or continuity on the source is needed. -/
theorem denseRange_iff_surjective_quotient_index_eq (hH : IsProP p H) (f : G →* H) :
    DenseRange f ↔ ∀ U : OpenNormalSubgroup H, U.toSubgroup.index = p →
      Function.Surjective ((QuotientGroup.mk' U.toSubgroup).comp f) := by
  constructor
  · intro hd U _
    exact denseRange_discrete.mp <|
      (QuotientGroup.mk'_surjective U.toSubgroup).denseRange.comp hd
        QuotientGroup.continuous_mk
  · intro hs
    have htop : f.range.topologicalClosure = ⊤ := by
      apply hH.eq_top_of_forall_not_le_openNormalSubgroup_index_eq
        (Subgroup.isClosed_topologicalClosure _)
      intro U hU hle
      have hUtop : U.toSubgroup = ⊤ := by
        apply top_unique
        intro x _
        obtain ⟨g, hg⟩ := hs U hU ((QuotientGroup.mk' U.toSubgroup) x)
        have hfg : f g ∈ U.toSubgroup :=
          hle (Subgroup.le_topologicalClosure _ ⟨g, rfl⟩)
        apply (QuotientGroup.eq_one_iff x).mp
        exact hg.symm.trans ((QuotientGroup.eq_one_iff (f g)).mpr hfg)
      exact hp.out.ne_one (hU.symm.trans (Subgroup.index_eq_one.mpr hUtop))
    rw [denseRange_iff_closure_range, ← MonoidHom.coe_range,
      ← Subgroup.topologicalClosure_coe, htop, Subgroup.coe_top]

/-- A homomorphism into a profinite pro-`p` group has dense range exactly when its composite
with the Frattini quotient map has dense range. -/
theorem denseRange_iff_denseRange_frattiniQuotient (hH : IsProP p H) (f : G →* H) :
    DenseRange f ↔ DenseRange ((QuotientGroup.mk' (proPFrattini p H)).comp f) := by
  have h := topologicallyGenerates_iff_frattiniQuotient hH (Set.range f)
  rw [← MonoidHom.coe_range, ← Subgroup.coe_map, MonoidHom.map_range,
    Subgroup.closure_eq, Subgroup.closure_eq] at h
  simpa only [← SetLike.coe_set_eq, Subgroup.topologicalClosure_coe,
    Subgroup.coe_top, MonoidHom.coe_range, ← denseRange_iff_closure_range] using h

variable [TopologicalSpace G] [CompactSpace G]

/-- **Burnside's surjectivity criterion.** A continuous homomorphism from a compact group
to a profinite pro-`p` group is surjective exactly when its composites with all index-`p`
quotient maps are surjective. -/
theorem surjective_iff_surjective_quotient_index_eq (hH : IsProP p H) (f : G →* H)
    (hf : Continuous f) :
    Function.Surjective f ↔ ∀ U : OpenNormalSubgroup H, U.toSubgroup.index = p →
      Function.Surjective ((QuotientGroup.mk' U.toSubgroup).comp f) := by
  rw [← hH.denseRange_iff_surjective_quotient_index_eq f, denseRange_iff_closure_range,
    hf.isClosedMap.isClosed_range.closure_eq, Set.range_eq_univ]

/-- A continuous homomorphism from a compact group to a profinite pro-`p` group is
surjective exactly when its composite with the Frattini quotient map is surjective. -/
theorem surjective_iff_surjective_frattiniQuotient (hH : IsProP p H) (f : G →* H)
    (hf : Continuous f) :
    Function.Surjective f ↔
      Function.Surjective ((QuotientGroup.mk' (proPFrattini p H)).comp f) := by
  have h := hH.denseRange_iff_denseRange_frattiniQuotient f
  have hfq : Continuous ((QuotientGroup.mk' (proPFrattini p H)).comp f) :=
    QuotientGroup.continuous_mk.comp hf
  simpa only [denseRange_iff_closure_range, hf.isClosedMap.isClosed_range.closure_eq,
    hfq.isClosedMap.isClosed_range.closure_eq,
    Set.range_eq_univ] using h

end IsProP

end TauCeti
