/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PL.Map
public import TauCeti.Analysis.Convex.Polyhedron.Pi.Neighborhood

/-!
# Compact polyhedral inverse images under PL maps

For a PL map on an open set, a compact intersection of a convex polyhedron with the
inverse image of another convex polyhedron is a finite union of compact convex polyhedra.
The intersection is taken inside the open domain of the map. This matters for chart
transitions, whose values away from their domains have no geometric meaning.

This result allows compact polyhedral chart patches to be cut along their overlaps before
their triangulations are fitted together.

The finite-subcover argument follows `TauCeti/Topology/PL/Compact.lean`, with the cells
additionally cut by the source polyhedron and affine inverse images of the target polyhedron.

Reference: Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Corollary 2.3
(decomposition of PL maps), and Chapter 2, pp. 13--14 (convex cells).
-/

public section

open Set Filter Topology

namespace TauCeti

variable {ι F : Type*} [AddCommGroup F] [Module ℝ F] [TopologicalSpace F]
  {f : (ι → ℝ) → F} {s u : Set (ι → ℝ)} {t : Set F}

/-- A compact polyhedral inverse image, inside the open domain of a PL map, is exactly a
finite union of compact convex polyhedra. No finiteness assumption on the source coordinate
type, or dimension or separation assumption on the target, is needed. -/
theorem IsPLOn.exists_polyhedral_inter_preimage (hf : IsPLOn f u) (hu : IsOpen u)
    (hs : IsConvexPolyhedron s) (ht : IsConvexPolyhedron t)
    (hK : IsCompact (s ∩ u ∩ f ⁻¹' t)) :
    ∃ C : Finset (Set (ι → ℝ)),
      (∀ P ∈ C, IsCompact P ∧ IsConvexPolyhedron P) ∧
      (⋃ P ∈ C, P) = s ∩ u ∩ f ⁻¹' t := by
  classical
  let K := s ∩ u ∩ f ⁻¹' t
  have hlocal (x : K) : ∃ V ∈ 𝓝 x.1,
      IsConvexPolyhedron V ∧ V ⊆ u ∧ IsPiecewiseAffineOn f V := by
    obtain ⟨W, hW, hpiece⟩ := isPLOn_iff.mp hf x.1 x.2.1.2
    rw [nhdsWithin_eq_nhds.mpr (hu.mem_nhds x.2.1.2)] at hW
    obtain ⟨V, hV, hpoly, hVW⟩ := exists_isConvexPolyhedron_mem_nhds_pi
      (inter_mem hW (hu.mem_nhds x.2.1.2))
    exact ⟨V, hV, hpoly, fun y hy => (hVW hy).2,
      hpiece.mono (fun y hy => (hVW hy).1)⟩
  choose V hV hpoly hVu hpiece using hlocal
  obtain ⟨a, ha⟩ := hK.elim_nhdsWithin_subcover'
    (fun x hx => V ⟨x, hx⟩) (fun x hx => nhdsWithin_le_nhds (hV ⟨x, hx⟩))
  choose n D A hD hcover heq using
    fun x : a => isPiecewiseAffineOn_iff.mp (hpiece x.1)
  let cell (p : Σ x : a, Fin (n x)) :=
    s ∩ V p.1.1 ∩ D p.1 p.2 ∩ (A p.1 p.2) ⁻¹' t
  have hcell_poly (p) : IsConvexPolyhedron (cell p) :=
    ((hs.inter (hpoly p.1.1)).inter (hD p.1 p.2)).inter (ht.preimage (A p.1 p.2))
  have hcell_sub (p) : cell p ⊆ K := by
    rintro y ⟨⟨⟨hys, hyV⟩, hyD⟩, hyA⟩
    refine ⟨⟨hys, hVu p.1.1 hyV⟩, ?_⟩
    simpa only [mem_preimage, heq p.1 p.2 ⟨hyV, hyD⟩] using hyA
  refine ⟨Finset.univ.image cell, ?_, ?_⟩
  · intro P hP
    obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hP
    exact ⟨hK.of_isClosed_subset (hcell_poly p).isClosed (hcell_sub p), hcell_poly p⟩
  · apply Subset.antisymm
    · intro y hy
      obtain ⟨P, hP, hyP⟩ := mem_iUnion₂.mp hy
      obtain ⟨p, -, rfl⟩ := Finset.mem_image.mp hP
      exact hcell_sub p hyP
    · intro y hy
      obtain ⟨x, hx, hyV⟩ := mem_iUnion₂.mp (ha hy)
      obtain ⟨j, hyD⟩ := mem_iUnion.mp (hcover ⟨x, hx⟩ hyV)
      have hyA : A ⟨x, hx⟩ j y ∈ t := (heq ⟨x, hx⟩ j ⟨hyV, hyD⟩) ▸ hy.2
      exact mem_iUnion₂.mpr ⟨cell ⟨⟨x, hx⟩, j⟩, Finset.mem_image.mpr
        ⟨⟨⟨x, hx⟩, j⟩, Finset.mem_univ _, rfl⟩, ⟨⟨⟨hy.1.1, hyV⟩, hyD⟩, hyA⟩⟩

end TauCeti
