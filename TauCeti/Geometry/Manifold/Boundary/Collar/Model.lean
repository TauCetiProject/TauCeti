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

This standard model is the input for the general collar theorem: local collar charts have this
form, while the global theorem patches them on an arbitrary manifold with boundary.  The collar
neighbourhood construction follows M. Hirsch, *Differential Topology*, Springer GTM 33 (1976),
Theorem 6.1, and J. Lee, *Introduction to Smooth Manifolds*, Springer GTM 218, 2nd ed. (2013),
Theorem 9.25.

The interval `[0, 1)` is open in the one-dimensional half-space model, via
`EuclideanHalfSpace.homeomorphNormalIio`; this is why the resulting map is an open embedding
rather than merely an embedding.
-/

public section

open Function Set Topology

open scoped Manifold ContDiff

namespace TauCeti.EuclideanHalfSpace

private noncomputable def depth (t : Ico (0 : ℝ) 1) : EuclideanHalfSpace 1 :=
  (homeomorphNormalIio 1).symm t

private theorem isOpenEmbedding_depth :
    IsOpenEmbedding (depth : Ico (0 : ℝ) 1 → EuclideanHalfSpace 1) := by
  change IsOpenEmbedding (fun t : Ico (0 : ℝ) 1 =>
    ((homeomorphNormalIio 1).symm t : EuclideanHalfSpace 1))
  exact (isOpen_normalIio 1).isOpenEmbedding_subtypeVal.comp
    (homeomorphNormalIio 1).symm.isOpenEmbedding

private theorem depth_eq_normalRay (t : Ico (0 : ℝ) 1) :
    depth t = normalRay t.1 := by
  rw [← normalRay_normalCoord (depth t)]
  congr 1
  change (((homeomorphNormalIio 1).symm t).1.1 0) = (t : ℝ)
  have h := congrArg (fun q : Ico (0 : ℝ) 1 => (q : ℝ))
    ((homeomorphNormalIio 1).apply_symm_apply t)
  simpa only [coe_homeomorphNormalIio] using h

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
    rw [boundaryCollar, Function.comp_apply, Prod.map_apply]
    simp only [id_eq]
    rw [depth_eq_normalRay, normalRay_zero]
    exact collarDiffeomorph_apply_zero_eq_boundaryParam n x

/-- The zero-depth slice of `boundaryCollar` is the boundary parametrization. -/
@[simp]
theorem boundaryCollar_apply_zero (n : ℕ) (x : EuclideanSpace ℝ (Fin n)) :
    boundaryCollar n (x, 0) = EuclideanHalfSpace.boundaryParam n x :=
  (isCollar_boundaryParam n).apply_zero x

/-- The normal coordinate of `boundaryCollar` is the interval depth. -/
@[simp]
theorem boundaryCollar_apply_zero_coord (n : ℕ)
    (p : EuclideanSpace ℝ (Fin n) × Ico (0 : ℝ) 1) :
    (boundaryCollar n p).1 0 = p.2.1 := by
  rw [boundaryCollar, Function.comp_apply, collarDiffeomorph_apply_zero]
  rw [Prod.map_apply]
  rw [depth_eq_normalRay]
  rw [normalRay_coe_apply, max_eq_left p.2.2.1]

/-- The tangential coordinates of `boundaryCollar` are unchanged. -/
@[simp]
theorem boundaryCollar_apply_succ (n : ℕ)
    (p : EuclideanSpace ℝ (Fin n) × Ico (0 : ℝ) 1) (i : Fin n) :
    (boundaryCollar n p).1 i.succ = p.1 i := by
  simp [boundaryCollar]

/-- The standard half-space boundary parametrization is collared by `boundaryCollar`. -/
theorem isCollared_boundaryParam (n : ℕ) :
    IsCollared (fun x : EuclideanSpace ℝ (Fin n) =>
      EuclideanHalfSpace.boundaryParam n x) :=
  (isCollar_boundaryParam n).isCollared

end TauCeti.EuclideanHalfSpace

end
