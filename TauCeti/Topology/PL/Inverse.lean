/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.PL.Map
public import TauCeti.Analysis.Convex.Polyhedron.Simplex
public import TauCeti.Analysis.Normed.Affine.Interpolation

/-!
# Inverses of simplicial piecewise-affine maps

A map affine on each simplex of a finite cover has a piecewise-affine inverse on its image,
provided each simplex's vertex images are affinely independent. The inverse need only be
supplied as a function with the left inverse law; continuity and PL regularity follow from
the simplex formulas. This is the inverse regularity criterion used when identifying
polyhedra by subdivisions.

The finite-cover conclusion gives `TauCeti.IsPLOn` by
`TauCeti.IsPiecewiseAffineOn.isPLOn` and restricts to chart domains by `TauCeti.IsPLOn.mono`.
This is the local map predicate used by `TauCeti.PLPregroupoid` and `TauCeti.PLGroupoid`
in `TauCeti.Geometry.Manifold.PLGroupoid`.

The image simplices give the polyhedral cover, and affine interpolation on their vertices
gives the inverse formulas. The ambient target is finite dimensional; the source may be
any topological real vector space. The simplices and their images may have positive
codimension or be empty. No intersection condition between the simplices is needed.

Reference: Rourke--Sanderson, *Introduction to Piecewise-Linear Topology*, Chapters 1--2.
-/

public section

open Set

namespace TauCeti

variable {E F : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  {f : E → F} {g : F → E}

/-- An inverse of a simplexwise affine map is piecewise affine on the image of a finite
simplex cover. Nondegeneracy is required only for the image vertices of each individual simplex;
neither full-dimensional simplices nor a normed or finite-dimensional source are required. -/
theorem isPiecewiseAffineOn_inverse_of_finite_simplex_cover {ι : Type*} [Finite ι]
    (s : ι → Set E) (A : ι → (E →ᴬ[ℝ] F))
    (heq : ∀ i, EqOn f (A i) (convexHull ℝ (s i)))
    (hind : ∀ i, AffineIndependent ℝ ((↑) : ((A i) '' s i) → F))
    (hgf : ∀ x ∈ ⋃ i, convexHull ℝ (s i), g (f x) = x) :
    IsPiecewiseAffineOn g (f '' ⋃ i, convexHull ℝ (s i)) := by
  classical
  have hleft (i : ι) (x : E) (hx : x ∈ s i) : g (A i x) = x := by
    rw [← heq i (subset_convexHull ℝ _ hx)]
    exact hgf x (mem_iUnion.mpr ⟨i, subset_convexHull ℝ _ hx⟩)
  choose B hB using fun i => (A i).exists_leftInverseOn_convexHull (hind i) (hleft i)
  let C (i : ι) : Set F := convexHull ℝ ((A i) '' s i)
  have himage (i : ι) : C i = f '' convexHull ℝ (s i) := by
    calc
      C i = (A i) '' convexHull ℝ (s i) := by
        simpa only [ContinuousAffineMap.coe_toAffineMap] using
          ((A i).toAffineMap.image_convexHull (s i)).symm
      _ = f '' convexHull ℝ (s i) := image_congr (fun x hx => (heq i hx).symm)
  refine isPiecewiseAffineOn_of_finite (C := C) (A := B)
    (fun i => (hind i).isConvexPolyhedron_convexHull) ?_ ?_
  · rintro _ ⟨x, hx, rfl⟩
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    exact mem_iUnion.mpr ⟨i, by rw [himage]; exact ⟨x, hxi, rfl⟩⟩
  · intro i y hy
    rw [himage i] at hy
    obtain ⟨x, hx, rfl⟩ := hy.2
    rw [hgf x (mem_iUnion.mpr ⟨i, hx⟩), heq i hx]
    exact (hB i x hx).symm

end TauCeti
