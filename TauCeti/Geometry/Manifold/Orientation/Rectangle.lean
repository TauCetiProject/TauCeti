/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.Rectangle
public import TauCeti.Geometry.Manifold.Orientation.Interval
public import TauCeti.Geometry.Manifold.Orientation.Prod

/-!
# Orientation of the rectangle manifold

The product interval orientation is carried by the inclusion derivative to the ordered coordinate
orientation, including at boundary and corner points. In the increasing charts it is the standard
product basis orientation directly.
-/

public section

noncomputable section

open Set Fact.Manifold
open scoped Manifold

namespace TauCeti

variable {a b c d : ℝ} [Fact (a < b)] [Fact (c < d)]

/-- Inclusion carries the canonical rectangle orientation to the standard coordinate-plane
orientation at every point, including all four corners. -/
theorem Manifold.Orientation.map_orientationAt_interval_prod (x : Icc a b × Icc c d) :
    _root_.Orientation.map (Fin 2) (subtypeValRectangleTangentEquiv x).toLinearEquiv
      (((interval a b).prod (interval c d)).orientationAt x) =
        (((Module.Basis.singleton (Fin 1) ℝ).prod
          (Module.Basis.singleton (Fin 1) ℝ)).reindex finSumFinEquiv).orientation := by
  have he : (subtypeValRectangleTangentEquiv x).toLinearEquiv =
      (subtypeValIccTangentEquiv x.1).toLinearEquiv.prodCongr
        (subtypeValIccTangentEquiv x.2).toLinearEquiv := by
    apply LinearEquiv.ext
    intro v
    -- Normalize the linear-equivalence coercions to the public continuous-map evaluation API.
    change subtypeValRectangleTangentEquiv x v =
      (subtypeValIccTangentEquiv x.1 v.1, subtypeValIccTangentEquiv x.2 v.2)
    simpa only [subtypeValIccTangentEquiv_apply, PiLp.proj_apply] using
      subtypeValRectangleTangentEquiv_apply x v
  rw [he]
  have hx := map_orientationAt_interval x.1
  have hy := map_orientationAt_interval x.2
  rw [orientationAt_interval] at hx hy
  rw [orientationAt_prod, orientationAt_interval, orientationAt_interval]
  -- State product transport on the fixed models with their model finrank proofs;
  -- the tangent-space finrank proofs otherwise retain the dependent base points.
  change _root_.Orientation.map (Fin (1 + 1))
    ((subtypeValIccTangentEquiv x.1).toLinearEquiv.prodCongr
      (subtypeValIccTangentEquiv x.2).toLinearEquiv)
    (_root_.Orientation.prod
      (if (x.1 : ℝ) < b then (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation
        else -(EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation)
      (if (x.2 : ℝ) < d then (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation
        else -(EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.orientation) (by simp) (by simp)) = _
  rw [_root_.Orientation.map_prod, hx, hy, _root_.Orientation.prod_basis_orientation]

/-- Wherever both preferred charts are increasing, the actual tangent orientation of the
rectangle is the ordered standard coordinate orientation. -/
theorem orientationAt_interval_prod_of_lt (x : Icc a b × Icc c d)
    (hx : (x.1 : ℝ) < b) (hy : (x.2 : ℝ) < d) :
    Manifold.Orientation.orientationAt
        ((Manifold.Orientation.interval a b).prod (Manifold.Orientation.interval c d)) x =
      (((EuclideanSpace.basisFun (Fin 1) ℝ).toBasis.prod
        (EuclideanSpace.basisFun (Fin 1) ℝ).toBasis).reindex finSumFinEquiv).orientation := by
  rw [Manifold.Orientation.orientationAt_prod,
    Manifold.Orientation.orientationAt_interval, Manifold.Orientation.orientationAt_interval]
  simp only [hx, hy, ↓reduceIte]
  exact _root_.Orientation.prod_basis_orientation _ _ _ _

end TauCeti
