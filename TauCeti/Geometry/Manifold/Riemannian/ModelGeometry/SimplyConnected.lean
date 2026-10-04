/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicTopology.FundamentalGroup.Product
public import TauCeti.AlgebraicTopology.Sphere.SimplyConnected
public import TauCeti.Geometry.Manifold.Riemannian.ModelGeometry.Basic

/-!
# Simple connectedness of Thurston's model geometries

All eight model spaces are simply connected. The spherical factors use simple connectedness of
spheres of dimension at least two; the Euclidean, hyperbolic, Nil, Sol, and `SL₂ℝ~` models are
contractible. The two product geometries use the product theorem for simple connectedness.

Thus a free, properly discontinuous quotient of any model has that model as its universal
cover, not merely as a covering space. Together with local path connectedness from the basic
model geometry module, this enables covering-space lifting and uniqueness results.

## References

* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983), 401–487,
  Sections 1 and 4.
* W. P. Thurston, *Three-Dimensional Geometry and Topology*, Vol. 1, Princeton University
  Press (1997), Sections 3.4 and 3.8.
-/

public section

namespace TauCeti.ModelGeometry

/-- Every Thurston model space is simply connected, including both product geometries. -/
instance (G : ModelGeometry) : SimplyConnectedSpace G.Space := by
  cases G with
  | spherical => exact simplyConnectedSpace_sphere_euclideanSpace (n := 3) (by decide)
  | sphereProd =>
    have : SimplyConnectedSpace (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
      simplyConnectedSpace_sphere_euclideanSpace (n := 2) (by decide)
    infer_instance
  | euclidean | hyperbolic | hyperbolicProd | sl2Tilde | nil | sol => infer_instance

end TauCeti.ModelGeometry
