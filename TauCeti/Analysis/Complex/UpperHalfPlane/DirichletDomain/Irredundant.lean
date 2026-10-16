/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.DirichletDomain.FiniteFaces
import Mathlib.Order.Minimal
import Mathlib.Topology.Order.IntermediateValue

/-!
# Irredundant finite Dirichlet descriptions

A finite closed-half-plane description of a Dirichlet domain can be reduced to an irredundant
subfamily. Each retained constraint defines a genuine side: its equality face contains an open
interval on the supporting geodesic. These faces still cover the entire boundary, so neither
empty faces nor singleton faces are needed in a finite boundary description.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, §9.4.
* Svetlana Katok, *Fuchsian Groups*, §3.2.
-/

public section

open Set UpperHalfPlane
open scoped MatrixGroups

namespace TauCeti.UpperHalfPlane

variable {G : Type*} [SMul G ℍ] [DecidableEq G]

private theorem exists_open_interval_subset_dirichletFace_of_essential
    {p : ℍ} {s : Finset G} (hmove : ∀ g ∈ s, p ≠ g • p)
    (hD : dirichletDomain G p =
      ⋂ g ∈ s, closure (leftHalfPlane (perpBisector p (g • p))))
    {g : G} (hg : g ∈ s) {x : ℍ}
    (hx : x ∈ ⋂ h ∈ s.erase g, closure (leftHalfPlane (perpBisector p (h • p))))
    (hxg : x ∉ closure (leftHalfPlane (perpBisector p (g • p)))) :
    ∃ a b : ℝ, a < b ∧
      geodesicLine (perpBisector p (g • p)) '' Ioo a b ⊆ dirichletFace p g := by
  classical
  -- Cross the essential bisector along a radial segment from the strictly feasible centre.
  let k := geodesicBetween p x
  let f : ℝ → ℝ := fun t ↦ dist (geodesicLine k t) p - dist (geodesicLine k t) (g • p)
  have hf : Continuous f :=
    ((isometry_geodesicLine k).continuous.dist continuous_const).sub
      ((isometry_geodesicLine k).continuous.dist continuous_const)
  have hf0 : f 0 < 0 := by
    dsimp [f, k]
    rw [geodesicLine_geodesicBetween_zero, dist_self, zero_sub]
    exact neg_neg_of_pos (dist_pos.mpr (hmove g hg))
  have hfx : 0 < f (dist p x) := by
    dsimp [f, k]
    rw [geodesicLine_geodesicBetween_dist, sub_pos]
    exact lt_of_not_ge fun h ↦ hxg
      ((mem_closure_leftHalfPlane_perpBisector_iff (hmove g hg) x).mpr h)
  obtain ⟨u, hu, hfu⟩ := intermediate_value_Ioo dist_nonneg hf.continuousOn ⟨hf0, hfx⟩
  have hueq : dist (geodesicLine k u) p = dist (geodesicLine k u) (g • p) :=
    sub_eq_zero.mp hfu
  have hpstrict (h : G) (hh : h ∈ s) : p ∈ leftHalfPlane (perpBisector p (h • p)) := by
    rw [mem_leftHalfPlane_perpBisector_iff (hmove h hh), dist_self]
    exact dist_pos.mpr (hmove h hh)
  have hstrict (h : G) (hh : h ∈ s.erase g) :
      geodesicLine k u ∈ leftHalfPlane (perpBisector p (h • p)) := by
    have hh' := (Finset.mem_erase.mp hh).2
    apply geodesicLine_mem_leftHalfPlane_of_mem_closure hu.1 hu.2
    · simpa only [k, geodesicLine_geodesicBetween_zero] using subset_closure (hpstrict h hh')
    · simpa only [k, geodesicLine_geodesicBetween_dist] using mem_iInter₂.mp hx h hh
    · intro heq
      have hp : p ∈ range (geodesicLine (perpBisector p (h • p))) :=
        heq ▸ mem_range_geodesicLine_geodesicBetween_left p x
      exact Set.disjoint_left.mp
        (disjoint_leftHalfPlane_range_geodesicLine _) (hpstrict h hh') hp
  -- At the crossing all remaining constraints are strict, hence stay valid on an open
  -- interval of the essential bisector.
  obtain ⟨v, hv⟩ := (mem_range_geodesicLine_perpBisector_iff (hmove g hg) _).mpr hueq
  let U : Set ℍ := ⋂ h ∈ s.erase g, leftHalfPlane (perpBisector p (h • p))
  have hU : IsOpen U := isOpen_biInter_finset fun h _ ↦ isOpen_leftHalfPlane _
  have hvU : geodesicLine (perpBisector p (g • p)) v ∈ U := by
    rw [hv]
    exact mem_iInter₂.mpr hstrict
  obtain ⟨a, b, hab, hsub⟩ :=
    (hU.preimage (isometry_geodesicLine _).continuous).exists_Ioo_subset ⟨v, hvU⟩
  refine ⟨a, b, hab, ?_⟩
  rintro z ⟨t, ht, rfl⟩
  have htU := mem_iInter₂.mp (hsub ht)
  have hteq := (mem_range_geodesicLine_perpBisector_iff (hmove g hg) _).mp
    (mem_range_self t)
  refine mem_dirichletFace.mpr ⟨?_, hteq⟩
  rw [hD]
  refine mem_iInter₂.mpr fun h hh ↦ ?_
  by_cases hhg : h = g
  · subst h
    exact (mem_closure_leftHalfPlane_perpBisector_iff (hmove g hg) _).mpr hteq.le
  · exact subset_closure (htU h (Finset.mem_erase.mpr ⟨hhg, hh⟩))

/-- A finite description of a Dirichlet domain admits an irredundant subfamily. Removing any
retained half-plane strictly enlarges the intersection, and each retained equality face contains
an open interval on its supporting geodesic. These genuine sides cover the entire boundary. -/
theorem exists_finset_irredundant_dirichletFace_cover
    {p : ℍ} {s : Finset G} (hmove : ∀ g ∈ s, p ≠ g • p)
    (hD : dirichletDomain G p =
      ⋂ g ∈ s, closure (leftHalfPlane (perpBisector p (g • p)))) :
    ∃ t : Finset G, t ⊆ s ∧
      dirichletDomain G p =
        ⋂ g ∈ t, closure (leftHalfPlane (perpBisector p (g • p))) ∧
      (∀ g ∈ t, dirichletDomain G p ⊂
        ⋂ h ∈ t.erase g, closure (leftHalfPlane (perpBisector p (h • p)))) ∧
      frontier (dirichletDomain G p) = ⋃ g ∈ t, dirichletFace p g ∧
      ∀ g ∈ t, ∃ a b : ℝ, a < b ∧
        geodesicLine (perpBisector p (g • p)) '' Ioo a b ⊆ dirichletFace p g := by
  classical
  obtain ⟨t, hts, ht, hmin⟩ := exists_minimal_le_of_wellFoundedLT
    (fun t : Finset G ↦ dirichletDomain G p =
      ⋂ g ∈ t, closure (leftHalfPlane (perpBisector p (g • p)))) s hD
  have htmove : ∀ g ∈ t, p ≠ g • p := fun g hg ↦ hmove g (hts hg)
  have hproper (g : G) (hg : g ∈ t) : dirichletDomain G p ⊂
      ⋂ h ∈ t.erase g, closure (leftHalfPlane (perpBisector p (h • p))) := by
    have hsub : dirichletDomain G p ⊆
        ⋂ h ∈ t.erase g, closure (leftHalfPlane (perpBisector p (h • p))) := by
      rw [ht]
      exact iInter₂_mono' fun h hh ↦ ⟨h, Finset.mem_of_mem_erase hh, Subset.rfl⟩
    refine hsub.ssubset_of_ne ?_
    intro heq
    have := hmin heq (Finset.erase_subset g t)
    exact Finset.notMem_erase g t (this hg)
  refine ⟨t, hts, ht, hproper,
    frontier_dirichletDomain_eq_biUnion_dirichletFace_of_eq_iInter htmove ht, ?_⟩
  intro g hg
  obtain ⟨x, hx, hxD⟩ := exists_of_ssubset (hproper g hg)
  apply exists_open_interval_subset_dirichletFace_of_essential htmove ht hg hx
  intro hxg
  apply hxD
  rw [ht]
  exact mem_iInter₂.mpr fun h hh ↦ by
    by_cases hhg : h = g
    · simpa only [hhg] using hxg
    · exact mem_iInter₂.mp hx h (Finset.mem_erase.mpr ⟨hhg, hh⟩)

end TauCeti.UpperHalfPlane
