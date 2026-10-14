/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.ContMDiff.Subtype
public import TauCeti.Geometry.Manifold.Riemannian.PathELength
public import TauCeti.Geometry.Manifold.Riemannian.Restriction

/-!
# The Riemannian distance on inner product spaces and their convex open subsets

The standard Riemannian metric of an inner product space `F` restricts to any open subset `U ⊆ F`
through the open-submanifold instances of `TauCeti.Geometry.Manifold.Riemannian.Restriction`. This
file computes the resulting Riemannian distance when `U` is convex: straight segments stay in `U`,
so every two points of `U` are joined by a curve of length exactly the ambient norm distance,
while no curve can be shorter than that chord. Hence

* the Riemannian extended distance of a convex open subset equals the ambient norm distance;
* with its ambient metric, a convex open subset satisfies `IsRiemannianManifold`, which makes the
  ordinary-metric layer (`dist`, closed balls, `ProperSpace`, `CompleteSpace`) available on it.

This computation lets examples such as the open unit ball use the ordinary metric presentation.
No finite-dimensionality assumption is needed: convexity is the only substantive hypothesis. The
general facts about path length used along the way live in their canonical modules:
`TauCeti.Manifold.pathELength_lineMap`
(`Riemannian.PathELength`), and `TauCeti.Manifold.pathELength_subtypeVal_comp`
(`Riemannian.Restriction`). That module also proves
`TopologicalSpace.Opens.riemannianEDist_le_riemannianEDist_subtype`: restriction to any open
submanifold cannot decrease distance.

## Main results

* `TopologicalSpace.Opens.riemannianEDist_eq_enorm_sub_of_convex`: on a convex open subset, the
  restricted Riemannian extended distance is the ambient norm distance.
* `TopologicalSpace.Opens.isRiemannianManifold_of_convex`: the ambient metric makes a convex open
  subset a Riemannian manifold.
* `TopologicalSpace.Opens.exists_pathELength_eq_edist_of_convex`: any two points of a
  convex open subset are joined by a `C¹` path whose Riemannian length is their distance.

## References

* The ambient distance computation adapts the proof of the `IsRiemannianManifold 𝓘(ℝ, F) F`
  instance in [Mathlib, `Mathlib/Geometry/Manifold/Riemannian/Basic.lean`](https://github.com/leanprover-community/mathlib4/blob/master/Mathlib/Geometry/Manifold/Riemannian/Basic.lean)
  by S. Gouëzel.
* M. P. do Carmo, *Riemannian Geometry*, Birkhäuser, 1992, Ch. 1, §2 (arc length; the length of a
  segment).
-/

public section

open Manifold Set TopologicalSpace
open scoped Bundle ENNReal Manifold TauCeti

namespace TopologicalSpace.Opens

/-! ### Convex open subsets of an inner product space -/

section InnerProductSpace

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable (U : Opens F)

/-- The length of a straight segment in a convex open subset is the ambient norm distance between
its endpoints. -/
theorem pathELength_convexSegment (hU : Convex ℝ (U : Set F)) (x y : U) :
    pathELength (M := U) 𝓘(ℝ, F) ((U : Set F).convexSegment hU x y) 0 1 =
      ‖((x : F) - (y : F))‖ₑ := by
  rw [TauCeti.Manifold.pathELength_subtypeVal_comp (contMDiffOn_convexSegment U hU x y)]
  apply (Manifold.pathELength_congr ((U : Set F).convexSegment_val_eqOn hU x y)).trans
  rw [← ContinuousAffineMap.coe_lineMap_eq]
  exact TauCeti.Manifold.pathELength_lineMap _ _

/-- **The Riemannian distance of a convex open subset is the ambient norm distance.** For an
open subset `U` of a real inner product space `F`, endowed with the restriction of the standard
Riemannian metric, the Riemannian extended distance between two points of `U` equals their norm
distance read in `F`: the straight segment stays in `U` and realizes the distance. Together with
`TopologicalSpace.Opens.isRiemannianManifold_of_convex`, this identifies the ambient metric
with the distance induced by the restricted Riemannian metric. -/
@[simp]
theorem riemannianEDist_eq_enorm_sub_of_convex (hU : Convex ℝ (U : Set F)) (x y : U) :
    riemannianEDist 𝓘(ℝ, F) x y = ‖((x : F) - (y : F))‖ₑ :=
  ((riemannianEDist_le_pathELength
      (contMDiffOn_convexSegment U hU x y)
      (Set.convexSegment_zero (U : Set F) hU x y)
      (Set.convexSegment_one (U : Set F) hU x y)
      zero_le_one).trans_eq
    (pathELength_convexSegment U hU x y)).antisymm
    (by
      have h := U.riemannianEDist_le_riemannianEDist_subtype (I := 𝓘(ℝ, F)) x y
      rwa [← IsRiemannianManifold.out (I := 𝓘(ℝ, F)) (x : F) (y : F),
        edist_eq_enorm_sub] at h)

/-- A convex open subset of an inner product space, endowed with its ambient metric, satisfies
the `IsRiemannianManifold` predicate: its ambient extended distance is the infimum of the lengths
of `C¹` curves, because that infimum is exactly the norm distance. -/
theorem isRiemannianManifold_of_convex (hU : Convex ℝ (U : Set F)) :
    IsRiemannianManifold 𝓘(ℝ, F) U :=
  ⟨fun x y ↦ by
    rw [Subtype.edist_eq, edist_eq_enorm_sub,
      riemannianEDist_eq_enorm_sub_of_convex U hU x y]⟩

/-! ### Distance-realizing segments in convex open subsets -/

/-- A straight segment in a convex open subset realizes the ambient distance between its
endpoints. -/
theorem pathELength_convexSegment_eq_edist (hU : Convex ℝ (U : Set F)) (x y : U) :
    pathELength (M := U) 𝓘(ℝ, F) ((U : Set F).convexSegment hU x y) 0 1 = edist x y := by
  rw [pathELength_convexSegment U hU x y, Subtype.edist_eq, edist_eq_enorm_sub]

/-- Any two points of a convex open subset of a real inner-product space are joined by a `C¹`
path whose Riemannian length is their ambient distance. -/
theorem exists_pathELength_eq_edist_of_convex (hU : Convex ℝ (U : Set F)) (x y : U) :
    ∃ γ : ℝ → U, CMDiff[Icc 0 1] 1 γ ∧ γ 0 = x ∧ γ 1 = y ∧
      pathELength 𝓘(ℝ, F) γ 0 1 = edist x y := by
  exact ⟨(U : Set F).convexSegment hU x y, contMDiffOn_convexSegment U hU x y,
    Set.convexSegment_zero (U : Set F) hU x y, Set.convexSegment_one (U : Set F) hU x y,
    pathELength_convexSegment_eq_edist U hU x y⟩

end InnerProductSpace

end TopologicalSpace.Opens
