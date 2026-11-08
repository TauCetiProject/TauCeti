/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ConstMulAction
public import TauCeti.Topology.Compactness.LocallyCompact

/-!
# Compact orbit spaces and compact sets meeting every orbit

A compact subset meeting every orbit makes the standard orbit quotient compact. This applies,
for example, to smooth or complex quotients with a compact fundamental domain, but needs neither
freeness nor proper discontinuity. The compact set need not meet an orbit uniquely, so closed
fundamental polygons with identified boundary points are allowed.

Conversely, for an action by homeomorphisms on a weakly locally compact space, compactness of the
orbit space implies that some compact set meets every orbit. This uses the open orbit projection
and `IsOpenMap.exists_isCompact_subset_image`; no separation assumption is needed.

Both results have additive versions on `AddAction.orbitRel.Quotient`.

## References

* John M. Lee, *Introduction to Smooth Manifolds*, Chapter 21, for orbit spaces of group actions.
-/

public section

open Set

variable {G X : Type*} [Group G] [MulAction G X] [TopologicalSpace X]

namespace IsCompact

/-- A compact set meeting every orbit makes the orbit quotient compact. No continuity of the
action is required: the orbit projection is continuous for the quotient topology. -/
@[to_additive
  /-- A compact set meeting every additive orbit makes the orbit quotient compact. No continuity
  of the action is required: the orbit projection is continuous for the quotient topology. -/]
theorem compactSpace_mulAction_orbitRel_quotient {K : Set X} (hK : IsCompact K)
    (hcover : ∀ x : X, ∃ g : G, g • x ∈ K) : CompactSpace (MulAction.orbitRel.Quotient G X) := by
  have himage : Quotient.mk (MulAction.orbitRel G X) '' K = univ := by
    apply eq_univ_of_forall
    intro z
    induction z using Quotient.inductionOn with | h x =>
      obtain ⟨g, hg⟩ := hcover x
      exact ⟨g • x, hg, Quotient.sound (MulAction.orbitRel_apply.mpr ⟨g, rfl⟩)⟩
  exact ⟨himage ▸ hK.image continuous_quot_mk⟩

end IsCompact

namespace TauCeti

/-- For an action by homeomorphisms on a weakly locally compact space, the orbit quotient is
compact exactly when a compact set meets every orbit. The set is not required to meet each orbit
uniquely. -/
@[to_additive
  /-- For an additive action by homeomorphisms on a weakly locally compact space, the orbit quotient
  is compact exactly when a compact set meets every orbit. The set is not required to meet each
  orbit uniquely. -/]
theorem compactSpace_mulAction_orbitRel_quotient_iff [ContinuousConstSMul G X]
    [WeaklyLocallyCompactSpace X] :
    CompactSpace (MulAction.orbitRel.Quotient G X) ↔
      ∃ K : Set X, IsCompact K ∧ ∀ x : X, ∃ g : G, g • x ∈ K := by
  constructor
  · intro h
    let := h
    obtain ⟨K, hK, hcover⟩ :=
      MulAction.isOpenQuotientMap_quotientMk.isOpenMap.exists_isCompact_subset_image
        (isCompact_univ : IsCompact (univ : Set (MulAction.orbitRel.Quotient G X)))
        Quotient.mk_surjective.range_eq.ge
    refine ⟨K, hK, fun x ↦ ?_⟩
    obtain ⟨y, hy, hyx⟩ := hcover (mem_univ (Quotient.mk (MulAction.orbitRel G X) x))
    obtain ⟨g, hg⟩ := MulAction.orbitRel_apply.mp (Quotient.exact hyx)
    exact ⟨g, by simpa only [hg] using hy⟩
  · rintro ⟨K, hK, hcover⟩
    exact hK.compactSpace_mulAction_orbitRel_quotient hcover

end TauCeti
