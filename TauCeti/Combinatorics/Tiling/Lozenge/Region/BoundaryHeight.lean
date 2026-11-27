/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.Tiling.Lozenge.Region.Height

/-!
# Boundary heights of lozenge regions

A boundary height of a region `R` is a function `h : ℤ × ℤ → ℤ` whose increment along every
boundary edge `(u, k)` of `R` is the neutral increment `c₀(u, k)`; only its values on the boundary
vertices matter. A boundary edge lies in no tiling of `R`, so the height function on `R` of a
tiling of `R` is a boundary height. When the boundary graph of `R` is connected, two boundary
heights agreeing at one boundary vertex agree on every boundary vertex. Hence for a simply
connected region with connected boundary graph, the height functions of any two tilings,
normalised at a common boundary vertex, agree on the boundary: the boundary height depends only on
the region.

## Main definitions

* `TauCeti.IsBoundaryHeight R h`: the increment of `h` along every boundary edge of `R` is the
  neutral one.

## Main statements

* `TauCeti.IsBoundaryHeight.eqOn_boundaryVertices`: on a region with preconnected boundary graph,
  two boundary heights agreeing at a boundary vertex agree on all boundary vertices.
* `TauCeti.IsHeightFunctionOn.isBoundaryHeight_iff`: a height function on `R` is a boundary height
  exactly when its free tiling is a tiling of `R`.
* `TauCeti.IsSimplyConnectedRegion.exists_isBoundaryHeight`: a tileable simply connected region
  has a boundary height.
* `TauCeti.IsHeightFunctionOn.eqOn_boundaryVertices_of_isTiling`: on a region with preconnected
  boundary graph, height functions of two tilings agreeing at a boundary vertex agree on all
  boundary vertices; on a simply connected region every tiling has a height function.

## References

* A. Aggarwal, *Universality for lozenge tiling local statistics*, Ann. of Math. 198 (2023),
  Section 1.2.
* V. Gorin, *Lectures on random lozenge tilings*, Cambridge Stud. Adv. Math. 193 (2021),
  Lecture 1.
-/

public section

namespace TauCeti

variable {R : Set TriFace} {M M' : Set TriEdge} {h h' H H' : ℤ × ℤ → ℤ}

/-- A boundary height of `R`: the increment of `h` along every boundary edge of `R` is the neutral
increment. Only the values of `h` on the boundary vertices of `R` matter. -/
def IsBoundaryHeight (R : Set TriFace) (h : ℤ × ℤ → ℤ) : Prop :=
  ∀ e ∈ boundaryEdges R, h e.target - h e.v = neutralIncrement e

theorem isBoundaryHeight_def : IsBoundaryHeight R h ↔
    ∀ e ∈ boundaryEdges R, h e.target - h e.v = neutralIncrement e := Iff.rfl

namespace IsBoundaryHeight

/-- Two functions agreeing on the boundary vertices of `R` are boundary heights together. -/
theorem congr (hh : IsBoundaryHeight R h) (hhh' : Set.EqOn h h' (boundaryVertices R)) :
    IsBoundaryHeight R h' := isBoundaryHeight_def.2 fun e he => by
  rw [← hhh' (target_mem_boundaryVertices he), ← hhh' (v_mem_boundaryVertices he)]
  exact isBoundaryHeight_def.1 hh e he

/-- Adding a constant to a boundary height gives a boundary height. -/
theorem add_const (hh : IsBoundaryHeight R h) (a : ℤ) : IsBoundaryHeight R (h + fun _ => a) :=
  isBoundaryHeight_def.2 fun e he => by
    simpa using isBoundaryHeight_def.1 hh e he

/-- Two boundary heights have equal values of `h − h'` at the ends of a boundary edge. -/
theorem sub_eq_sub_of_adj (hh : IsBoundaryHeight R h) (hh' : IsBoundaryHeight R h')
    {u u' : boundaryVertices R} (hu : (boundaryGraph R).Adj u u') :
    h u - h' u = h u' - h' u' := by
  obtain ⟨e, he, hend⟩ := boundaryGraph_adj.1 hu
  have h₁ := isBoundaryHeight_def.1 hh e he
  have h₂ := isBoundaryHeight_def.1 hh' e he
  rw [TriEdge.endpoints_def, Sym2.eq_iff] at hend
  rcases hend with ⟨h₃, h₄⟩ | ⟨h₃, h₄⟩
  · rw [← h₃, ← h₄]
    omega
  · rw [← h₃, ← h₄]
    omega

/-- **Uniqueness of boundary heights.** If the boundary graph of `R` is preconnected, two boundary
heights of `R` agreeing at a boundary vertex `u₀` agree on all boundary vertices. -/
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

/-- **Height functions of tilings are boundary heights.** A height function on `R` is a boundary
height of `R` exactly when its free tiling is a tiling of `R`. -/
theorem IsHeightFunctionOn.isBoundaryHeight_iff (hH : IsHeightFunctionOn R H) :
    IsBoundaryHeight R H ↔ IsTiling R (tilingOfHeightOn R H) :=
  hH.isTiling_tilingOfHeightOn_iff.symm

namespace IsSimplyConnectedRegion

variable (hR : IsSimplyConnectedRegion R)
include hR

/-- A tiling `M` of a simply connected region has a height function on `R` with free tiling `M`,
taking any prescribed value at any point, and it is a boundary height of `R`. -/
theorem exists_isHeightFunctionOn_isBoundaryHeight (hM : IsTiling R M) (v₀ : ℤ × ℤ) (m : ℤ) :
    ∃ H, IsHeightFunctionOn R H ∧ tilingOfHeightOn R H = M ∧ H v₀ = m ∧
      IsBoundaryHeight R H := by
  obtain ⟨H, hH, hHM, hHm⟩ := hR.exists_isHeightFunctionOn hM.isFreeTiling v₀ m
  exact ⟨H, hH, hHM, hHm, hH.isBoundaryHeight_iff.2 (hHM ▸ hM)⟩

/-- **Tileable simply connected regions have boundary heights.** -/
theorem exists_isBoundaryHeight (hM : IsTiling R M) : ∃ h, IsBoundaryHeight R h := by
  obtain ⟨H, -, -, -, hH⟩ := hR.exists_isHeightFunctionOn_isBoundaryHeight hM 0 0
  exact ⟨H, hH⟩

end IsSimplyConnectedRegion

/-- **The boundary height depends only on the region.** On a region `R` whose boundary graph is
preconnected, height functions on `R` of two tilings of `R` that agree at a boundary vertex agree
on all boundary vertices. On a simply connected region every tiling has a height function
(`IsSimplyConnectedRegion.exists_isHeightFunctionOn_isBoundaryHeight`). -/
theorem IsHeightFunctionOn.eqOn_boundaryVertices_of_isTiling (hc : (boundaryGraph R).Preconnected)
    (hH : IsHeightFunctionOn R H) (hM : IsTiling R (tilingOfHeightOn R H))
    (hH' : IsHeightFunctionOn R H') (hM' : IsTiling R (tilingOfHeightOn R H'))
    {u₀ : ℤ × ℤ} (hu₀ : u₀ ∈ boundaryVertices R) (h₀ : H u₀ = H' u₀) :
    Set.EqOn H H' (boundaryVertices R) :=
  IsBoundaryHeight.eqOn_boundaryVertices hc (hH.isBoundaryHeight_iff.2 hM)
    (hH'.isBoundaryHeight_iff.2 hM') hu₀ h₀


end TauCeti
