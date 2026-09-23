/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Collar.Basic
public import TauCeti.Geometry.Manifold.Boundary.Collar.Global
public import TauCeti.Geometry.Manifold.Boundary.Collar.Local

/-!
# The standard collar of a Euclidean half-space boundary

The boundary parametrization of the standard Euclidean half-space has a global collar.  The
collar is obtained by restricting the product identification from
`EuclideanHalfSpace.collarDiffeomorph` to the open normal segment `[0, 1)`.

This is the first global producer for `IsCollar` in the smooth-manifold boundary API.  It is the
model case used by the general collar theorem: local collar charts have this form, while the
global theorem must still patch them on an arbitrary manifold with boundary.

The interval `[0, 1)` is open in the one-dimensional half-space model, via
`EuclideanHalfSpace.homeomorphNormalIio`; this is why the resulting map is an open embedding
rather than merely an embedding.
-/

public section

open Function Set Topology

open scoped Manifold ContDiff

namespace TauCeti.EuclideanHalfSpace

private def depth (t : Ico (0 : ℝ) 1) : EuclideanHalfSpace 1 :=
  normalRay t.1

private theorem depth_eq_homeomorph_symm (t : Ico (0 : ℝ) 1) :
    depth t = ((homeomorphNormalIio 1).symm t : EuclideanHalfSpace 1) := by
  apply Subtype.ext
  simp only [depth]
  have h := congrArg Subtype.val ((homeomorphNormalIio 1).apply_symm_apply t)
  have hcoord : t.1 = (((homeomorphNormalIio 1).symm t).1.1).ofLp 0 := by
    simpa only [coe_homeomorphNormalIio] using h.symm
  rw [← normalRay_normalCoord ((homeomorphNormalIio 1).symm t).1, hcoord]

private theorem isOpenEmbedding_depth :
    IsOpenEmbedding (depth : Ico (0 : ℝ) 1 → EuclideanHalfSpace 1) := by
  have hdepth : depth = (fun t : Ico (0 : ℝ) 1 =>
      ((homeomorphNormalIio 1).symm t : EuclideanHalfSpace 1)) := by
    funext t
    exact depth_eq_homeomorph_symm t
  rw [hdepth]
  exact (isOpen_normalIio 1).isOpenEmbedding_subtypeVal.comp
    (homeomorphNormalIio 1).symm.isOpenEmbedding

/-- The standard collar map of the boundary of `EuclideanHalfSpace (n + 1)`. -/
noncomputable def boundaryCollar (n : ℕ) :
    EuclideanSpace ℝ (Fin n) × Ico (0 : ℝ) 1 → EuclideanHalfSpace (n + 1) :=
  (collarDiffeomorph (k := ⊤) n) ∘ Prod.map id depth

/-- The standard half-space boundary parametrization admits a global collar. -/
theorem isCollar_boundaryParam (n : ℕ) :
    IsCollar (fun x : EuclideanSpace ℝ (Fin n) =>
      EuclideanHalfSpace.boundaryParam n x)
      (boundaryCollar n) := by
  refine ⟨?_, ?_⟩
  · exact (collarDiffeomorph (k := ⊤) n).toHomeomorph.isOpenEmbedding.comp
      (IsOpenEmbedding.id.prodMap isOpenEmbedding_depth)
  · intro x
    simp [boundaryCollar, depth]

@[simp]
theorem boundaryCollar_apply_zero (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    boundaryCollar n (x, 0) = EuclideanHalfSpace.boundaryParam n x :=
  (isCollar_boundaryParam n).apply_zero x

theorem isCollared_boundaryParam (n : ℕ) :
    IsCollared (fun x : EuclideanSpace ℝ (Fin n) =>
      EuclideanHalfSpace.boundaryParam n x) :=
  (isCollar_boundaryParam n).isCollared

end TauCeti.EuclideanHalfSpace

end
