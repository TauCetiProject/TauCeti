/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Region.Height

/-!
# Boundary heights of lozenge regions

A boundary height of a region `R` (`TauCeti.IsBoundaryHeight`) is a function `h : ℤ × ℤ → ℤ`
whose increment along every boundary edge `(u, k)` of `R` is the neutral increment `c₀(u, k)`; only
its values on the boundary vertices matter. A boundary edge lies in no tiling of `R`, so the height
function on `R` of a tiling of `R` is a boundary height
(`TauCeti.IsHeightFunctionOn.isTiling_tilingOfHeightOn_iff`). When the boundary graph of `R` is
connected, two boundary heights agreeing at one boundary vertex agree on every boundary vertex.
Hence the height functions on `R` of any two tilings of `R`, normalised at a common boundary
vertex, agree on the boundary: the boundary height depends only on the region.

## Main statements

* `TauCeti.IsBoundaryHeight.eqOn_boundaryVertices`: on a region with preconnected boundary graph,
  two boundary heights agreeing at a boundary vertex agree on all boundary vertices.

## References

* A. Aggarwal, *Universality for lozenge tiling local statistics*, Ann. of Math. 198 (2023),
  Section 1.2.
* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021),
  Lecture 1.
-/

public section

namespace TauCeti

variable {R : Set TriFace} {h h' : ℤ × ℤ → ℤ}

namespace IsBoundaryHeight

/-- Two functions agreeing on the boundary vertices of `R` are boundary heights together. -/
theorem congr (hh : IsBoundaryHeight R h) (hhh' : Set.EqOn h h' (boundaryVertices R)) :
    IsBoundaryHeight R h' := isBoundaryHeight_def.2 fun e he => by
  rw [← hhh' (target_mem_boundaryVertices he), ← hhh' (v_mem_boundaryVertices he)]
  exact hh.sub_eq he

/-- Adding a constant to a boundary height gives a boundary height. -/
theorem add_const (hh : IsBoundaryHeight R h) (a : ℤ) : IsBoundaryHeight R (h + fun _ => a) :=
  isBoundaryHeight_def.2 fun e he => by
    simpa using hh.sub_eq he

/-- Two boundary heights have equal values of `h − h'` at the ends of a boundary edge. -/
theorem sub_eq_sub_of_adj (hh : IsBoundaryHeight R h) (hh' : IsBoundaryHeight R h')
    {u u' : boundaryVertices R} (hu : (boundaryGraph R).Adj u u') :
    h u - h' u = h u' - h' u' := by
  obtain ⟨e, he, hend⟩ := boundaryGraph_adj.1 hu
  have h₁ := hh.sub_eq he
  have h₂ := hh'.sub_eq he
  rw [TriEdge.endpoints_def, Sym2.eq_iff] at hend
  rcases hend with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩
  · rw [← h₃, ← h₄]
    omega
  · rw [← h₃, ← h₄]
    omega

/-- **Uniqueness of boundary heights.** If the boundary graph of `R` is preconnected, two boundary
heights of `R` agreeing at a boundary vertex `u₀` agree on all boundary vertices. By
`IsHeightFunctionOn.isTiling_tilingOfHeightOn_iff` this applies to the height functions on `R` of
any two tilings of `R`, so the boundary height depends only on the region. -/
theorem eqOn_boundaryVertices (hR : (boundaryGraph R).Preconnected) (hh : IsBoundaryHeight R h)
    (hh' : IsBoundaryHeight R h') {u₀ : ℤ × ℤ} (hu₀ : u₀ ∈ boundaryVertices R)
    (h₀ : h u₀ = h' u₀) : Set.EqOn h h' (boundaryVertices R) := fun u hu => by
  obtain ⟨p⟩ := hR ⟨u₀, hu₀⟩ ⟨u, hu⟩
  suffices ∀ {a b : boundaryVertices R} (_ : (boundaryGraph R).Walk a b),
      h a - h' a = h b - h' b by
    have := this p
    simp only at this
    omega
  intro a b q
  induction q with
  | nil => rfl
  | cons hab _ ih => exact (hh.sub_eq_sub_of_adj hh' hab).trans ih

end IsBoundaryHeight

end TauCeti
