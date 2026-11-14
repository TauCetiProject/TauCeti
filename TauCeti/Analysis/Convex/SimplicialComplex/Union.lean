/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Convex.SimplicialComplex.Basic
public import Mathlib.Analysis.Normed.Module.FiniteDimension
public import TauCeti.Analysis.Convex.SimplicialComplex.Subdivision
import TauCeti.Analysis.Convex.Polyhedron.Simplex
import TauCeti.Analysis.Convex.SimplicialComplex.Arrangement
import TauCeti.Analysis.Convex.SimplicialComplex.Carrier
import TauCeti.Analysis.Convex.SimplicialComplex.Glue
import TauCeti.Analysis.Convex.SimplicialComplex.Relative

/-!
# Triangulating the union of two polyhedra

Let `K` and `L` be finite geometric simplicial complexes in a finite-dimensional real normed space.
Their underlying spaces may meet in an arbitrary way, so the faces of `K` and `L` together are in
general not a simplicial complex. They become one after subdivision: there are finite subdivisions
`K'` of `K` and `L'` of `L` whose faces together form a finite simplicial complex `M`, with
`|M| = |K| ∪ |L|` (`Geometry.SimplicialComplex.exists_space_eq_union`). In particular `K'` and
`L'` are subcomplexes of `M`, and the intersection `|K| ∩ |L|` is triangulated by the faces they
have in common. This is the union counterpart of the triangulation of `|K| ∩ |L|` in
`TauCeti.Analysis.Convex.SimplicialComplex.CommonSubdivision`.

The theorem is what makes rectilinear complexes in a coordinate chart fit together. In Munkres'
construction of a smooth triangulation of a manifold, two embedded complexes are made rectilinear
near their overlap in a chart, and their images there must then be triangulated by one complex
containing subdivisions of both. It equally underlies the triangulation of a PL manifold chart
by chart.

The proof first subdivides `K` along the simplices of `L` so that every simplex of the
subdivision `K₁` whose open simplex meets a simplex `u` of `L` lies in `u`
(`Geometry.SimplicialComplex.exists_isSubdivision_convexHull_subset_of_inter_nonempty`), and
then subdivides `L` along the simplices of `K₁` in the same way, obtaining `L₁`. The simplices of
`K₁` lying in `|L|` then triangulate `|K| ∩ |L|`, and so do the simplices of `L₁` lying in `|K|`,
the second triangulation subdividing the first. Extending the second one to a subdivision `K₂`
of `K₁` (`Geometry.SimplicialComplex.IsSubdivision.exists_finite_extension`) makes `K₂` and `L₁`
agree on `|K| ∩ |L|`, and they glue along this common subcomplex
(`Geometry.SimplicialComplex.inter_convexHull_subset_convexHull_of_space_inter_subset`).

## Main results

* `Geometry.SimplicialComplex.exists_space_eq_union`: two finite complexes have finite
  subdivisions whose faces together form a finite complex triangulating the union of their
  underlying spaces.

## References

* C. P. Rourke, B. J. Sanderson, *Introduction to Piecewise-Linear Topology*, Springer (1972),
  Chapter 2 (unions and intersections of polyhedra).
* J. Munkres, *Elementary Differential Topology*, Annals of Math. Studies 54 (1966), Chapter II,
  Section 10 (fitting together embedded complexes).
-/

public section

open Set

namespace Geometry.SimplicialComplex

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {K L : SimplicialComplex ℝ E}

/-- **Triangulating the union of two polyhedra.** Two finite geometric simplicial complexes `K`
and `L` in a finite-dimensional real normed space have finite subdivisions `K'` and `L'` whose
faces together form a finite simplicial complex `M`. Its underlying space is `|K| ∪ |L|`, it
contains `K'` and `L'` as subcomplexes, and their common faces triangulate `|K| ∩ |L|`. -/
theorem exists_space_eq_union (hK : K.faces.Finite) (hL : L.faces.Finite) :
    ∃ K' L' M : SimplicialComplex ℝ E, K'.IsSubdivision K ∧ L'.IsSubdivision L ∧
      M.faces = K'.faces ∪ L'.faces ∧ M.space = K.space ∪ L.space ∧
      (K' ⊓ L').space = K.space ∩ L.space ∧ M.faces.Finite := by
  have := hL.to_subtype
  -- Cut `K` along the simplices of `L`, and then `L` along the simplices of the result.
  obtain ⟨K₁, hK₁, hK₁f, hK₁L⟩ := exists_isSubdivision_convexHull_subset_of_inter_nonempty hK
    (C := fun u : L.faces => convexHull ℝ (u.1 : Set E))
    fun u => (L.indep u.2).isConvexPolyhedron_convexHull
  have := hK₁f.to_subtype
  obtain ⟨L₁, hL₁, hL₁f, hL₁K⟩ := exists_isSubdivision_convexHull_subset_of_inter_nonempty hL
    (C := fun s : K₁.faces => convexHull ℝ (s.1 : Set E))
    fun s => (K₁.indep s.2).isConvexPolyhedron_convexHull
  -- Both cuts triangulate `|K| ∩ |L|`, the second one subdividing the first.
  set A := K₁.restrictConvexHull L.space
  set B := L₁.restrictConvexHull K₁.space
  have hA : A.space = K.space ∩ L.space := by
    rw [space_restrictConvexHull_space fun s hs u hu => hK₁L s hs ⟨u, hu⟩, hK₁.space_eq]
  have hB : B.space = K.space ∩ L.space := by
    rw [space_restrictConvexHull_space fun t ht s hs => hL₁K t ht ⟨s, hs⟩, hL₁.space_eq,
      hK₁.space_eq, inter_comm]
  have hBA : B.IsSubdivision A := by
    refine ⟨hB.trans hA.symm, fun t ht => ?_⟩
    obtain ⟨x, hxt⟩ := (convexHull_nonempty_iff.2 (B.nonempty_of_mem_faces ht)).intrinsicInterior
      (convex_convexHull ℝ _)
    obtain ⟨s, hs, hxs⟩ := mem_space_iff.1
      ((hB.trans hA.symm).subset (convexHull_subset_space ht (intrinsicInterior_subset hxt)))
    exact ⟨s, hs, hL₁K t (restrictConvexHull_le ht) ⟨s, restrictConvexHull_le hs⟩ ⟨x, hxt, hxs⟩⟩
  -- Extend the finer triangulation of `|K| ∩ |L|` to a subdivision `K₂` of `K₁`.
  obtain ⟨K₂, hK₂, hK₂B, hK₂f⟩ := hBA.exists_finite_extension restrictConvexHull_le hK₁f
    (hL₁f.subset restrictConvexHull_le)
  have hBK₂ : B ≤ K₂ := hK₂B ▸ restrict_le
  have hKL₂ : (K₂ ⊓ L₁).space = K.space ∩ L.space := by
    refine Subset.antisymm ?_ (hB ▸ space_mono (le_inf hBK₂ restrictConvexHull_le))
    rw [← hK₁.space_eq, ← hK₂.space_eq, ← hL₁.space_eq]
    exact subset_inter (space_mono inf_le_left) (space_mono inf_le_right)
  -- `K₂` and `L₁` meet in their common subcomplex, so their faces form a complex.
  let T : Bool → SimplicialComplex ℝ E := fun b => cond b K₂ L₁
  have hTT : ∀ i j, (T i).space ∩ (T j).space ⊆ (T i ⊓ T j).space := by
    have h : K₂.space ∩ L₁.space ⊆ (K₂ ⊓ L₁).space := by
      rw [hKL₂, hK₂.space_eq, hK₁.space_eq, hL₁.space_eq]
    rintro (_ | _) (_ | _)
    exacts [by simp [T], by simpa [T, inter_comm, inf_comm] using h, h, by simp [T]]
  let M := glue T fun i j _ _ => inter_convexHull_subset_convexHull_of_space_inter_subset (hTT i j)
  have hM : M.faces = K₂.faces ∪ L₁.faces := by
    ext s
    simp [M, T, or_comm]
  refine ⟨K₂, L₁, M, hK₂.trans hK₁, hL₁, hM, ?_, hKL₂, hM ▸ hK₂f.union hL₁f⟩
  rw [← hK₁.space_eq, ← hK₂.space_eq, ← hL₁.space_eq]
  ext x
  simp [M, T, or_comm]

end Geometry.SimplicialComplex
