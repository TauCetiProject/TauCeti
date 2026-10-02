/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.Group.Quotient

import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Connectedness of topological groups

This file derives connectedness of a group from preconnectedness of a subgroup and its coset
quotient, and develops the identity component `Subgroup.connectedComponentOfOne G` of a
topological group `G`: it is a closed normal subgroup, it lies in every open subgroup, continuous
homomorphisms preserve it, and the quotient of `G` by it is totally disconnected.  Thus a group
whose quotient by its identity component is compact is an extension of a profinite group by a
connected one.

## Main results

* `Subgroup.connectedSpace_of_quotient`: a group with continuous left translations is
  connected when a subgroup and the corresponding coset quotient are preconnected.
* `Subgroup.connectedComponentOfOne_le_of_isOpen`: an open subgroup contains the identity
  component.
* `Subgroup.map_connectedComponentOfOne_le`: a continuous homomorphism maps the identity
  component into the identity component.
* `QuotientGroup.totallyDisconnectedSpace_connectedComponentOfOne`: the quotient of a
  topological group by its identity component is totally disconnected.

## References

* E. Hewitt and K. A. Ross, *Abstract Harmonic Analysis I*, Theorem 7.3.
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

section IdentityComponent

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The underlying set of the identity component is the connected component of `1`. -/
@[simp]
theorem _root_.Subgroup.coe_connectedComponentOfOne :
    (Subgroup.connectedComponentOfOne G : Set G) = connectedComponent 1 :=
  (rfl)

/-- An element lies in the identity component exactly when it lies in the connected component
of `1`. -/
@[simp]
theorem _root_.Subgroup.mem_connectedComponentOfOne_iff {g : G} :
    g ∈ Subgroup.connectedComponentOfOne G ↔ g ∈ connectedComponent 1 :=
  Iff.rfl

/-- The identity component of a topological group is closed. -/
instance _root_.Subgroup.isClosed_connectedComponentOfOne :
    IsClosed (Subgroup.connectedComponentOfOne G : Set G) :=
  isClosed_connectedComponent

/-- The identity component of a topological group is normal: conjugation is a homeomorphism
fixing `1`, so it preserves the connected component of `1`. -/
instance _root_.Subgroup.normal_connectedComponentOfOne :
    (Subgroup.connectedComponentOfOne G).Normal where
  conj_mem n hn g := by
    have h := (IsTopologicalGroup.continuous_conj g).mapsTo_connectedComponent 1 hn
    rwa [mul_one, mul_inv_cancel] at h

/-- **An open subgroup contains the identity component**: it is also closed, so the connected
component of `1` cannot leave it. -/
theorem _root_.Subgroup.connectedComponentOfOne_le_of_isOpen {H : Subgroup G}
    (hH : IsOpen (H : Set G)) : Subgroup.connectedComponentOfOne G ≤ H :=
  fun _ hg ↦ IsClopen.connectedComponent_subset ⟨H.isClosed_of_isOpen hH, hH⟩ H.one_mem hg

/-- A continuous homomorphism maps the identity component into the identity component. -/
theorem _root_.Subgroup.map_connectedComponentOfOne_le {G' : Type*} [Group G']
    [TopologicalSpace G'] [IsTopologicalGroup G'] {f : G →* G'} (hf : Continuous f) :
    (Subgroup.connectedComponentOfOne G).map f ≤ Subgroup.connectedComponentOfOne G' := by
  rintro _ ⟨g, hg, rfl⟩
  have h := hf.mapsTo_connectedComponent 1 hg
  rwa [map_one] at h

open scoped Pointwise in
/-- **The quotient of a topological group by its identity component is totally disconnected.**
The fibres of the quotient map are the translates of the identity component, which are connected,
so the preimage of the connected component of `1` in the quotient is connected and hence lies in
the identity component. -/
instance _root_.QuotientGroup.totallyDisconnectedSpace_connectedComponentOfOne :
    TotallyDisconnectedSpace (G ⧸ Subgroup.connectedComponentOfOne G) := by
  set N := Subgroup.connectedComponentOfOne G
  rw [totallyDisconnectedSpace_iff_connectedComponent_one]
  -- The fibre of the quotient map over the class of `g` is the connected component of `g`.
  have hfib (q : G ⧸ N) : IsConnected ((QuotientGroup.mk : G → G ⧸ N) ⁻¹' {q}) := by
    induction q using QuotientGroup.induction_on with | H g => ?_
    have hg : g • connectedComponent (1 : G) = connectedComponent g := by
      rw [smul_connectedComponent, mul_one]
    convert (isConnected_connectedComponent (x := g)) using 1
    ext x
    rw [Set.mem_preimage, Set.mem_singleton_iff, eq_comm, QuotientGroup.eq, ← hg,
      Set.mem_smul_set_iff_inv_smul_mem, smul_eq_mul, Subgroup.mem_connectedComponentOfOne_iff]
  have hpre := (QuotientGroup.isQuotientMap_mk N).isCoinducing.preimage_connectedComponent hfib 1
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_connectedComponent, fun y hy ↦ ?_⟩
  induction y using QuotientGroup.induction_on with | H g => ?_
  rw [← QuotientGroup.mk_one, ← Set.mem_preimage, hpre] at hy
  exact (QuotientGroup.eq_one_iff g).mpr hy

end IdentityComponent

end TauCeti
