/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Convex.Polyhedron.Basic
public import Mathlib.Analysis.Normed.Affine.AddTorsorBases
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-!
# Simplices are convex polyhedra

The convex hull of an affinely independent family in a finite-dimensional real normed space
is a convex polyhedron. This includes simplices of positive codimension: coordinates outside
the chosen face vanish, rather than merely being nonnegative. Consequently the simplices of
a geometric simplicial complex can serve as the polyhedral cells of a piecewise-affine map.

The construction uses Mathlib's extension of an affinely independent set to an affine basis
and its barycentric-coordinate description of the convex hull. The half-space description
of a simplex follows Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapter 1.
-/

public section

open Set
open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

namespace AffineBasis

/-- Every face of the simplex spanned by an affine basis is a convex polyhedron, including
the empty face and faces of positive codimension. -/
theorem isConvexPolyhedron_convexHull_image {ι : Type*} (b : AffineBasis ι ℝ E) (s : Set ι) :
    IsConvexPolyhedron (convexHull ℝ (b '' s)) := by
  classical
  have : Finite ι := b.finite
  let : Fintype ι := Fintype.ofFinite ι
  let c : ι → (E →ᴬ[ℝ] ℝ) := fun i =>
    ⟨b.coord i, continuous_barycentric_coord b i⟩
  have hset : convexHull ℝ (b '' s) =
      {x | (∀ i, 0 ≤ b.coord i x) ∧ ∀ i ∉ s, b.coord i x ≤ 0} := by
    ext x
    constructor
    · intro hx
      refine ⟨?_, fun i hi => ?_⟩
      · have hfull := convexHull_mono (image_subset_range b s) hx
        rwa [b.convexHull_eq_nonneg_coord] at hfull
      · apply convexHull_min (t := (b.coord i) ⁻¹' Iic 0) ?_
          ((convex_Iic (0 : ℝ)).affine_preimage (b.coord i)) hx
        rintro _ ⟨j, hj, rfl⟩
        simp [b.coord_apply, (ne_of_mem_of_not_mem hj hi).symm]
    · rintro ⟨hpos, hneg⟩
      let t := s.toFinite.toFinset
      have hz : ∀ i ∉ t, b.coord i x = 0 := by
        intro i hi
        exact le_antisymm (hneg i (by simpa [t] using hi)) (hpos i)
      have hsum : ∑ i ∈ t, b.coord i x = 1 := by
        rw [← b.sum_coord_apply_eq_one x]
        exact Finset.sum_subset (Finset.subset_univ t) (fun i _ hi => hz i hi)
      have hrepr : ∑ i ∈ t, b.coord i x • b i = x := by
        calc
          ∑ i ∈ t, b.coord i x • b i = ∑ i, b.coord i x • b i :=
            Finset.sum_subset (Finset.subset_univ t) (fun i _ hi => by rw [hz i hi, zero_smul])
          _ = x := b.linear_combination_coord_eq_self x
      rw [← hrepr]
      exact (convex_convexHull ℝ (b '' s)).sum_mem (fun i _ => hpos i) hsum
        (fun i hi => subset_convexHull ℝ _ ⟨i, by simpa [t] using hi, rfl⟩)
  rw [hset]
  have hineq := isConvexPolyhedron_setOf_forall
    (fun i : ι ⊕ {i // i ∉ s} => Sum.elim (fun j => -c j) (fun j => c j.1) i)
  convert hineq using 1
  ext x
  simp [Sum.forall, c]

end AffineBasis

namespace AffineIndependent

/-- An affinely independent set in a finite-dimensional real normed space spans a convex
polyhedron. No assumption that its affine span is the whole ambient space is needed. -/
theorem isConvexPolyhedron_convexHull {s : Set E}
    (hs : AffineIndependent ℝ ((↑) : s → E)) : IsConvexPolyhedron (convexHull ℝ s) := by
  obtain ⟨t, hst, ht, hspan⟩ := exists_subset_affineIndependent_affineSpan_eq_top hs
  let b : AffineBasis t ℝ E := ⟨Subtype.val, ht, by simpa using hspan⟩
  have himage : b '' {i : t | (i : E) ∈ s} = s := by
    ext x
    exact ⟨fun ⟨_, hi, hix⟩ => hix ▸ hi, fun hx => ⟨⟨x, hst hx⟩, hx, rfl⟩⟩
  rw [← himage]
  exact b.isConvexPolyhedron_convexHull_image _

end AffineIndependent
