/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PL.Preimage
public import Mathlib.Topology.OpenPartialHomeomorph.Composition

/-!
# Polyhedral overlaps of compact chart patches

If the transition between two charts is PL, the overlap of compact convex polyhedral patches
has an exact finite polyhedral decomposition in the first chart. The source and target models
may be different, and no manifold structure on the underlying Hausdorff space is required.

This is the local intersection calculation needed to fit polyhedral chart triangulations
together. In particular, the transition is used only on its actual source.

Reference: Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Corollary 2.3
and Chapter 2, pp. 13--14 (convex cells).
-/

public section

open Set

namespace OpenPartialHomeomorph

variable {ι F M : Type*} [TopologicalSpace M] [T2Space M]
  [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]

/-- The overlap of two compact convex polyhedral chart patches has an exact finite
polyhedral decomposition in the first chart, provided the transition is PL. The chart models
may differ, and the underlying space needs only be Hausdorff. -/
theorem exists_polyhedral_overlap (e : OpenPartialHomeomorph M (ι → ℝ))
    (d : OpenPartialHomeomorph M F)
    (hf : TauCeti.IsPLOn (d ∘ e.symm) (e.symm.trans d).source)
    {P : Set (ι → ℝ)} {Q : Set F}
    (hP : IsCompact P) (hPpoly : TauCeti.IsConvexPolyhedron P) (hPt : P ⊆ e.target)
    (hQ : IsCompact Q) (hQpoly : TauCeti.IsConvexPolyhedron Q) (hQt : Q ⊆ d.target) :
    ∃ C : Finset (Set (ι → ℝ)),
      (∀ R ∈ C, IsCompact R ∧ TauCeti.IsConvexPolyhedron R) ∧
      (⋃ R ∈ C, R) = e '' ((e.symm '' P) ∩ (d.symm '' Q)) := by
  have heP : IsCompact (e.symm '' P) :=
    hP.image_of_continuousOn (e.continuousOn_symm.mono hPt)
  have hdQ : IsCompact (d.symm '' Q) :=
    hQ.image_of_continuousOn (d.continuousOn_symm.mono hQt)
  have hsource : (e.symm '' P) ∩ (d.symm '' Q) ⊆ e.source := by
    rintro _ ⟨⟨y, hy, rfl⟩, -⟩
    exact e.map_target (hPt hy)
  have hcoords : P ∩ (e.symm.trans d).source ∩ (d ∘ e.symm) ⁻¹' Q =
      e '' ((e.symm '' P) ∩ (d.symm '' Q)) := by
    apply Subset.antisymm
    · rintro y ⟨⟨hyP, hyS⟩, hyQ⟩
      have hyD : e.symm y ∈ d.source := hyS.2
      exact ⟨e.symm y, ⟨⟨y, hyP, rfl⟩,
        ⟨d (e.symm y), hyQ, d.left_inv hyD⟩⟩, e.right_inv (hPt hyP)⟩
    · rintro _ ⟨x, ⟨⟨y, hyP, rfl⟩, ⟨z, hzQ, hzx⟩⟩, rfl⟩
      rw [e.right_inv (hPt hyP)]
      have hyD : e.symm y ∈ d.source := hzx ▸ d.map_target (hQt hzQ)
      refine ⟨⟨hyP, hPt hyP, hyD⟩, ?_⟩
      simpa only [mem_preimage, Function.comp_apply, ← hzx, d.right_inv (hQt hzQ)] using hzQ
  have hK : IsCompact (P ∩ (e.symm.trans d).source ∩ (d ∘ e.symm) ⁻¹' Q) := by
    rw [hcoords]
    exact (heP.inter_right hdQ.isClosed).image_of_continuousOn
      (e.continuousOn.mono hsource)
  obtain ⟨C, hC, hEq⟩ := hf.exists_polyhedral_inter_preimage
    (e.symm.trans d).open_source hPpoly hQpoly hK
  exact ⟨C, hC, hEq.trans hcoords⟩

end OpenPartialHomeomorph
