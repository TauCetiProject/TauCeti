/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Convex.Cone.Face.Simplicial
public import TauCeti.Geometry.Toric.Algebraic.Ray.Generation

/-!
# The faces of a regular cone are indexed by subsets of its rays

A regular cone is the cone hull of the images of its primitive ray generators, and those images
are part of a real basis of the ambient space. The faces of such a cone are therefore exactly the
cones spanned by subfamilies of the primitive ray generators, and the assignment is an order
isomorphism between Mathlib's face lattice of the cone and the powerset of its ray type.

Under this isomorphism a face corresponds to the set of its own rays, so a face of a regular cone
is determined by, and can be prescribed by, the rays of the ambient cone that it contains. This is
the combinatorial input of the orbit description of an affine toric chart: the rays of a regular
cone index the coordinates of the mixed chart, a face is cut out by demanding that the
coordinates of its rays vanish, and the face lattice must match the lattice of such coordinate
conditions.

Regularity is used only through simpliciality, and simpliciality cannot be dropped: the cone over
a square in `ℝ³`, spanned by `(1, 0, 1)`, `(0, 1, 1)`, `(-1, 0, 1)` and `(0, -1, 1)`, is salient
with four rays, but the cone spanned by two opposite rays is not a face, so its ten faces do not
exhaust the sixteen subsets of its rays.

## Main declarations

* `TauCeti.Toric.IsRegularCone.faceOrderIso`: the face lattice of a regular cone is the lattice
  of subsets of its rays.
* `TauCeti.Toric.IsRegularCone.faceOrderIso_apply`: the subset attached to a face is the set of
  rays of that face.
* `TauCeti.Toric.IsRegularCone.toPointedCone_faceOrderIso_symm`: the face attached to a subset of
  rays is the cone spanned by the corresponding primitive ray generators.

## References

* W. Fulton, *Introduction to Toric Varieties*, §§1.2 and 2.1.
* D. Cox, J. Little and H. Schenck, *Toric Varieties*, §1.2 and Proposition 1.2.10.
-/

public section

namespace TauCeti.Toric

variable {N V : Type*} [AddCommGroup N] [AddCommGroup V] [Module ℝ V]
  {i : N →+ V} {σ : PointedCone ℝ V}

namespace IsRegularCone

variable (hi : IsIntegralLattice i) (hσ : IsRegularCone i σ)

/-- The face lattice of a regular cone is the lattice of subsets of its rays: a face is recorded
by the set of rays it contains, and a set of rays spans the corresponding face. -/
noncomputable def faceOrderIso : σ.Face ≃o Set (ToricRay σ) :=
  PointedCone.faceOrderIsoSet (hσ.linearIndependent_primitiveGenerator hi)
    (hσ.toIsToricCone.hull_range_primitiveGenerator hi).symm

@[simp]
theorem mem_faceOrderIso_iff (F : σ.Face) (ρ : ToricRay σ) :
    ρ ∈ faceOrderIso hi hσ F ↔ i (primitiveGenerator hi hσ.toIsToricCone ρ) ∈ F := by
  rw [faceOrderIso, PointedCone.faceOrderIsoSet_apply]
  exact Iff.rfl

@[simp]
theorem toPointedCone_faceOrderIso_symm (A : Set (ToricRay σ)) :
    ((faceOrderIso hi hσ).symm A).toPointedCone =
      PointedCone.hull ℝ (i '' (primitiveGenerator hi hσ.toIsToricCone '' A)) := by
  rw [faceOrderIso, PointedCone.toPointedCone_faceOrderIsoSet_symm, Set.image_image]

/-- The subset of rays attached to a face of a regular cone is the set of rays of that face. -/
theorem faceOrderIso_apply (F : σ.Face) :
    faceOrderIso hi hσ F = Set.range (ToricRay.faceEmbedding F.isFaceOf) := by
  rw [ToricRay.range_faceEmbedding]
  ext ρ
  rw [mem_faceOrderIso_iff, Set.mem_ofPred_eq]
  refine ⟨fun h ↦ ?_, fun h ↦ h (primitiveGenerator_mem hi hσ.toIsToricCone ρ)⟩
  rw [ρ.eq_hull_singleton (hσ.salient.anti ρ.1.isFaceOf.le)
    (primitiveGenerator_mem hi hσ.toIsToricCone ρ)
    (by simpa using hi.injective.ne (primitiveGenerator_ne_zero hi hσ.toIsToricCone ρ))]
  exact Submodule.span_le.2 (Set.singleton_subset_iff.2 h)

end IsRegularCone

end TauCeti.Toric
