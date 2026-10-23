/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Complex.UpperHalfPlane.DirichletDomain.Basic
public import TauCeti.MeasureTheory.Group.DirichletDomain.Compact

/-!
# Finite bisector descriptions of bounded Dirichlet domains

A bounded Dirichlet domain for a properly discontinuous action on the upper half-plane is a
finite intersection of closed geodesic half-planes. The equality holds on the entire upper
half-plane, not merely inside a prescribed bounded set. Constraints indexed by elements fixing
the centre are omitted. In particular, an isometric action with compact orbit quotient has
such a finite description.

This is the finite-constraint step in constructing compact Dirichlet polygons. It does not
assert finite-sidedness for an unbounded finite-area domain, or enumerate the sides and vertices
of the finite intersection.

## References

* Alan Beardon, *The Geometry of Discrete Groups*, §9.4.
* Svetlana Katok, *Fuchsian Groups*, §3.2.

We use `TauCeti.exists_finset_dirichletDomain_inter_eq` for local finiteness and the geodesic
convexity of distance-dominance regions to obtain global equality.
-/

public section

open Metric Set UpperHalfPlane
open scoped MatrixGroups

namespace TauCeti.UpperHalfPlane

variable {G : Type*}

section

variable [SMul G ℍ] [ProperlyDiscontinuousSMul G ℍ]

/-- A bounded hyperbolic Dirichlet domain is globally cut out by finitely many perpendicular
bisectors. The finite family contains only indices moving the centre. -/
theorem exists_finset_dirichletDomain_eq_iInter_closure_leftHalfPlane {p : ℍ}
    (hb : Bornology.IsBounded (dirichletDomain G p)) :
    ∃ s : Finset G, (∀ g ∈ s, p ≠ g • p) ∧
      dirichletDomain G p =
        ⋂ g ∈ s, closure (leftHalfPlane (perpBisector p (g • p))) := by
  classical
  obtain ⟨r, hr⟩ := hb.subset_closedBall p
  have hr0 : 0 ≤ r := by
    simpa using hr (self_mem_dirichletDomain (G := G) p)
  obtain ⟨s, hs⟩ := exists_finset_dirichletDomain_inter_eq (G := G) p
    (K := closedBall p (r + 1)) isBounded_closedBall
  let C : Set ℍ := ⋂ g ∈ s, {z | dist z p ≤ dist z (g • p)}
  have hlocal {x : ℍ} (hx : x ∈ C) (hxB : x ∈ closedBall p (r + 1)) :
      x ∈ dirichletDomain G p := by
    have hxD : x ∈ dirichletDomain G p ∩ closedBall p (r + 1) := by
      rw [hs]
      exact ⟨hx, hxB⟩
    exact hxD.1
  -- A radial segment from the centre would cross the larger sphere while staying in `C`.
  have hC : C ⊆ dirichletDomain G p := by
    intro z hz
    have hzB : z ∈ closedBall p (r + 1) := by
      by_contra hzB
      have hzdist : r + 1 < dist p z := by
        simpa only [mem_closedBall, dist_comm, not_le] using hzB
      let u := geodesicLine (geodesicBetween p z) (r + 1)
      have huS : u ∈ geodesicSegment p z :=
        (mem_geodesicSegment_iff p z u).mpr
          ⟨r + 1, ⟨by linarith, by simpa [dist_comm] using hzdist.le⟩, rfl⟩
      have huC : u ∈ C := by
        refine mem_iInter₂.mpr fun g hg ↦ ?_
        exact geodesicSegment_subset_setOf_dist_le_dist
          (by simp [dist_nonneg]) (mem_iInter₂.mp hz g hg) huS
      have huDist : dist u p = r + 1 := by
        rw [← geodesicLine_geodesicBetween_zero p z, dist_geodesicLine]
        simp [abs_of_nonneg (by linarith : 0 ≤ r + 1)]
      have huB : u ∈ closedBall p (r + 1) := by
        simp only [mem_closedBall, huDist, le_refl]
      have := hr (hlocal huC huB)
      rw [mem_closedBall, huDist] at this
      linarith
    exact hlocal hz hzB
  -- Replace distance constraints by bisectors, discarding the tautological fixed-centre ones.
  refine ⟨s.filter (fun g ↦ p ≠ g • p), fun g hg ↦ (Finset.mem_filter.mp hg).2, ?_⟩
  ext z
  simp only [mem_dirichletDomain, mem_iInter, Finset.mem_filter]
  constructor
  · intro hz g hg
    exact (mem_closure_leftHalfPlane_perpBisector_iff hg.2 z).mpr (hz g)
  · intro hz
    apply mem_dirichletDomain.mp (hC ?_)
    refine mem_iInter₂.mpr fun g hg ↦ ?_
    by_cases hgp : p = g • p
    · simp [← hgp]
    · exact (mem_closure_leftHalfPlane_perpBisector_iff hgp z).mp (hz g ⟨hg, hgp⟩)

end

variable (G)

/-- For a properly discontinuous isometric action with compact orbit space, every hyperbolic
Dirichlet domain has a finite closed-half-plane description. -/
theorem exists_finset_dirichletDomain_eq_iInter_closure_leftHalfPlane_of_compactSpace
    [Group G] [MulAction G ℍ] [IsIsometricSMul G ℍ] [ProperlyDiscontinuousSMul G ℍ]
    [CompactSpace (MulAction.orbitRel.Quotient G ℍ)] (p : ℍ) :
    ∃ s : Finset G, (∀ g ∈ s, p ≠ g • p) ∧
      dirichletDomain G p =
        ⋂ g ∈ s, closure (leftHalfPlane (perpBisector p (g • p))) :=
  exists_finset_dirichletDomain_eq_iInter_closure_leftHalfPlane
    (isCompact_dirichletDomain_of_compactSpace p).isBounded

end TauCeti.UpperHalfPlane
