/-
Copyright (c) 2026 Mei contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Geometry.Convex.PolyhedralComplex.Sweep
public import TauCeti.Geometry.ScatteringDiagram.SingularSupport
import TauCeti.Analysis.Convex.Polyhedron.Facet

/-!
# Avoiding the singular support of a complex's walls

Relative boundaries of walls and intersections of walls with different
supporting directions are carried by the codimension-at-least-two skeleton
of the complex. A point generic for the skeleton sweep arrangement therefore
gives lines that avoid the singular support in each prescribed direction.

Adapted from `Mei/Geometry/Convex/PolyhedralComplex/Strata.lean` and
`Mei/Geometry/Convex/PolyhedralComplex/Discriminant.lean` in
[yuma-mizuno-lean/Mei](https://github.com/yuma-mizuno-lean/Mei), commit
`bf3986029ff4d3eb4025d4067489511b0724374e` (Apache 2.0).
-/

public section

namespace TauCeti.FinitePolyhedralComplex

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  {i : N →+ V} {h : Toric.IsIntegralLattice i}

/-- The singular support of the walls is contained in the codimension-at-least-two
skeleton. Boundary points lie on facets, and distinct supporting directions
force a nonempty wall intersection to have smaller dimension. -/
theorem singularSupport_walls_subset_support_codimensionGE_two (C : FinitePolyhedralComplex h) :
    singularSupport (Subtype.val : C.walls → Set V) ⊆ (C.codimensionGE 2).support := by
  have := h.finiteDimensional
  intro x hx
  rcases mem_singularSupport.mp hx with ⟨P, hxP⟩ | ⟨P, Q, hne, hxP, hxQ⟩
  · obtain ⟨hP, hdP⟩ := mem_cellsOfCodimension.mp P.property
    obtain ⟨F, hF, hxF, hdF⟩ :=
      (C.isConvexPolyhedron hP).mem_intrinsicFrontier_iff_exists_facet.mp hxP
    refine mem_support.mpr ⟨F, mem_cells_codimensionGE.mpr ⟨C.face_closed _ hP F
      ⟨⟨x, hxF⟩, hF⟩, ?_⟩, hxF⟩
    rw [← direction_affineSpan, ← direction_affineSpan] at hdF
    omega
  · obtain ⟨hP, hdP⟩ := mem_cellsOfCodimension.mp P.property
    obtain ⟨hQ, hdQ⟩ := mem_cellsOfCodimension.mp Q.property
    have hPQ := C.inter_mem_cells hP hQ ⟨x, hxP, hxQ⟩
    refine mem_support.mpr ⟨_, mem_cells_codimensionGE.mpr ⟨hPQ, ?_⟩, hxP, hxQ⟩
    by_contra! hd
    have heP := C.eq_of_subset_of_finrank_direction_le hPQ hP Set.inter_subset_left (by omega)
    have heQ := C.eq_of_subset_of_finrank_direction_le hPQ hQ Set.inter_subset_right (by omega)
    exact hne (congrArg (fun W => (affineSpan ℝ W).direction) (heP.symm.trans heQ))

/-- From a generic base point, every full line in a specified direction avoids
the singular support of the walls. -/
theorem add_smul_notMem_singularSupport_walls {C : FinitePolyhedralComplex h}
    {vectors : Finset V} {x v : V} (hx : (C.skeletonSweepExceptions vectors).IsGeneric x)
    (hv : v ∈ vectors) (t : ℝ) : x + t • v ∉ singularSupport (Subtype.val : C.walls → Set V) :=
  fun hxsing => add_smul_notMem_support_codimensionGE_two hx hv t
    (C.singularSupport_walls_subset_support_codimensionGE_two hxsing)

end TauCeti.FinitePolyhedralComplex
