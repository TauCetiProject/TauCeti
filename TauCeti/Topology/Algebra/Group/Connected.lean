/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Connectedness of topological groups

This file derives connectedness of a group from preconnectedness of a subgroup and its coset
quotient.

## Main result

* `Subgroup.connectedSpace_of_quotient`: a group with continuous left translations is
  connected when a subgroup and the corresponding coset quotient are preconnected.
-/

public section

open Set

namespace TauCeti

variable {G : Type*} [Group G] [TopologicalSpace G] [ContinuousConstSMul G G]

/-- A group with continuous left translations is connected when a subgroup and its coset quotient
are preconnected. -/
theorem _root_.Subgroup.connectedSpace_of_quotient (H : Subgroup G) [PreconnectedSpace H]
    [PreconnectedSpace (G ⧸ H)] : ConnectedSpace G := by
  rw [connectedSpace_iff_univ]
  -- Each fiber of the quotient projection is a left translate of `H`.
  have hfiber : ∀ q : G ⧸ H, IsConnected (QuotientGroup.mk ⁻¹' {q}) := by
    intro q
    refine QuotientGroup.induction_on q ?_
    intro g
    have hrange : IsConnected (Set.range fun h : H => g * (h : G)) :=
      ⟨Set.range_nonempty _,
        isPreconnected_range ((continuous_const_smul g).comp continuous_subtype_val)⟩
    convert hrange using 1
    ext x
    simp only [mem_preimage, mem_singleton_iff, mem_range]
    constructor
    · intro hx
      have hxH : g⁻¹ * x ∈ H := by
        simpa only [mul_inv_rev, inv_inv] using H.inv_mem (QuotientGroup.eq.mp hx)
      exact ⟨⟨g⁻¹ * x, hxH⟩, by simp⟩
    · rintro ⟨h, rfl⟩
      apply QuotientGroup.eq.mpr
      convert H.inv_mem h.property using 1
      simp
  -- Pull connectedness of the whole quotient back through the quotient projection.
  have hquot : IsConnected (Set.univ : Set (G ⧸ H)) :=
    ⟨Set.univ_nonempty, isPreconnected_univ⟩
  have huniv := (QuotientGroup.isQuotientMap_mk H).isCoinducing.isConnected_preimage_of_isClosed
    hfiber isClosed_univ hquot
  simpa using huniv

end TauCeti
