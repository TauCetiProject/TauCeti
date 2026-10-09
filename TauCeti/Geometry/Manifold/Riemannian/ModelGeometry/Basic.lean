/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Hyperbolic.UpperHalfSpace.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Euclidean
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Prod
public import TauCeti.Geometry.Manifold.Riemannian.Isometry.Sphere.Basic
public import TauCeti.Geometry.Manifold.Riemannian.Nil
public import TauCeti.Geometry.Manifold.Riemannian.SL2Tilde
public import TauCeti.Geometry.Manifold.Riemannian.Sol.Basic

/-!
# The eight Thurston model geometries

`TauCeti.ModelGeometry` is the closed list of spherical, Euclidean, hyperbolic,
`S² × ℝ`, `ℍ² × ℝ`, `SL₂ℝ~`, Nil, and Sol geometries. Its `Space` and `model` accessors select
concrete manifolds with the standard analytic Riemannian metrics. The three-dimensional model
vector spaces, analytic manifold structures, and transitive actions of the full Riemannian
isometry groups are available uniformly for an arbitrary member of the list.

The metrics and their homogeneity proofs come from the individual model files. In particular,
the product geometries carry the product metrics, and Nil, Sol, and `SL₂ℝ~` keep their distinct
metrics on distinct type synonyms of `ℝ³`. The acting group is `TauCeti.Isom G.model G.Space`,
which contains every smooth self-diffeomorphism preserving the metric, rather than just the
transitive subgroups exhibited by those proofs.

This finite index type allows geometric-structure statements to quantify over the eight models
without allowing arbitrary homogeneous spaces. A manifold modeled on `G` can use
`ChartedSpace G.Space M` and the existing isometry-action structure groupoid; completeness of
such a structure is an additional condition on its induced metric.

## References

* P. Scott, *The geometries of 3-manifolds*, Bull. London Math. Soc. 15 (1983), 401–487,
  Sections 4 and 5.
* W. P. Thurston, *Three-Dimensional Geometry and Topology*, Vol. 1, Princeton University
  Press (1997), Section 3.8.
-/

public section

open Bundle Module
open scoped Manifold ContDiff EuclideanSpace TauCeti

namespace TauCeti

/-- The eight Thurston geometries, indexing their standard homogeneous Riemannian models. -/
inductive ModelGeometry
  /-- The round three-sphere. -/
  | spherical
  /-- Euclidean three-space. -/
  | euclidean
  /-- Hyperbolic three-space. -/
  | hyperbolic
  /-- The product of the round two-sphere and the real line. -/
  | sphereProd
  /-- The product of the hyperbolic plane and the real line. -/
  | hyperbolicProd
  /-- The universal cover of `SL₂ℝ`, with its standard geometry. -/
  | sl2Tilde
  /-- The real Heisenberg group with its standard left-invariant metric. -/
  | nil
  /-- The solvable Lie group Sol with its standard left-invariant metric. -/
  | sol
  deriving DecidableEq

namespace ModelGeometry

instance : Fintype ModelGeometry where
  elems := {.spherical, .euclidean, .hyperbolic, .sphereProd, .hyperbolicProd,
    .sl2Tilde, .nil, .sol}
  complete G := by cases G <;> simp

noncomputable section

/-- The concrete manifold underlying a model geometry.

The spherical factors are unit spheres, and the hyperbolic factors use the upper half-space
model. The `SL₂ℝ~`, Nil, and Sol cases use their metric-bearing type synonyms. -/
abbrev Space : ModelGeometry → Type
  | .spherical => Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1
  | .euclidean => EuclideanSpace ℝ (Fin 3)
  | .hyperbolic => UpperHalfSpace (EuclideanSpace ℝ (Fin 2))
  | .sphereProd => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ
  | .hyperbolicProd => UpperHalfSpace ℝ × ℝ
  | .sl2Tilde => SL2Tilde
  | .nil => Nil
  | .sol => Sol

/-- The vector space for the charts of a model geometry. It has real dimension three in every
case, including the product geometries. -/
abbrev ModelSpace : ModelGeometry → Type
  | .spherical => EuclideanSpace ℝ (Fin 3)
  | .euclidean => EuclideanSpace ℝ (Fin 3)
  | .hyperbolic => WithLp 2 (EuclideanSpace ℝ (Fin 2) × ℝ)
  | .sphereProd => EuclideanSpace ℝ (Fin 2) × ℝ
  | .hyperbolicProd => WithLp 2 (ℝ × ℝ) × ℝ
  | .sl2Tilde => ℝ × ℝ × ℝ
  | .nil => ℝ × ℝ × ℝ
  | .sol => ℝ × ℝ × ℝ

instance (G : ModelGeometry) : NormedAddCommGroup G.ModelSpace := by
  cases G <;> infer_instance

instance (G : ModelGeometry) : NormedSpace ℝ G.ModelSpace := by
  cases G <;> infer_instance

instance (G : ModelGeometry) : FiniteDimensional ℝ G.ModelSpace := by
  cases G <;> infer_instance

/-- The topological chart model. The product cases use Mathlib's `ModelProd` tag to retain
its canonical product atlas. -/
abbrev ChartSpace : ModelGeometry → Type
  | .sphereProd => ModelProd (EuclideanSpace ℝ (Fin 2)) ℝ
  | .hyperbolicProd => ModelProd (WithLp 2 (ℝ × ℝ)) ℝ
  | G => G.ModelSpace

instance (G : ModelGeometry) : TopologicalSpace G.ChartSpace := by
  cases G <;> infer_instance

/-- The boundaryless model with corners used by the standard charts. Products use the product
model, so their tangent metrics are the existing product Riemannian metrics. -/
abbrev model (G : ModelGeometry) : ModelWithCorners ℝ G.ModelSpace G.ChartSpace :=
  match G with
  | .spherical => 𝓡 3
  | .euclidean => 𝓡 3
  | .hyperbolic => 𝓘(ℝ, WithLp 2 (EuclideanSpace ℝ (Fin 2) × ℝ))
  | .sphereProd => (𝓡 2).prod 𝓘(ℝ, ℝ)
  | .hyperbolicProd => 𝓘(ℝ, WithLp 2 (ℝ × ℝ)).prod 𝓘(ℝ, ℝ)
  | .sl2Tilde => 𝓘(ℝ, ℝ × ℝ × ℝ)
  | .nil => 𝓘(ℝ, ℝ × ℝ × ℝ)
  | .sol => 𝓘(ℝ, ℝ × ℝ × ℝ)

instance (G : ModelGeometry) : TopologicalSpace G.Space := by
  cases G <;> infer_instance

/-- Every model has points, so homogeneity is a nonempty transitive action. -/
instance (G : ModelGeometry) : Nonempty G.Space := by
  cases G with
  | spherical => exact NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
  | sphereProd =>
    have : Nonempty (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) :=
      NormedSpace.sphere_nonempty_rclike ℝ zero_le_one
    infer_instance
  | hyperbolic =>
    exact ⟨UpperHalfSpace.mk (WithLp.toLp 2 (0, 1)) (by simp)⟩
  | hyperbolicProd =>
    exact ⟨(UpperHalfSpace.mk (WithLp.toLp 2 (0, 1)) (by simp), 0)⟩
  | euclidean => infer_instance
  | sl2Tilde => exact ⟨SL2Tilde.mk 0 0 0⟩
  | nil => exact ⟨Nil.mk 0 0 0⟩
  | sol => exact ⟨Sol.mk 0 0 0⟩

instance (G : ModelGeometry) : ChartedSpace G.ChartSpace G.Space := by
  cases G <;> infer_instance

/-- Every model is Hausdorff. -/
instance (G : ModelGeometry) : T2Space G.Space := by
  cases G <;> infer_instance

/-- Every model is locally compact, being locally homeomorphic to a finite-dimensional space. -/
instance (G : ModelGeometry) : LocallyCompactSpace G.Space := by
  have : LocallyCompactSpace G.ChartSpace := by
    cases G with
    | sphereProd => exact inferInstanceAs (LocallyCompactSpace (EuclideanSpace ℝ (Fin 2) × ℝ))
    | hyperbolicProd => exact inferInstanceAs (LocallyCompactSpace (WithLp 2 (ℝ × ℝ) × ℝ))
    | _ => infer_instance
  exact ChartedSpace.locallyCompactSpace G.ChartSpace G.Space

/-- Each model is locally path connected in its standard manifold topology. -/
instance (G : ModelGeometry) : LocallyPathConnectedSpace G.Space := by
  have : LocallyPathConnectedSpace G.ChartSpace := by
    cases G with
    | sphereProd =>
      exact inferInstanceAs (LocallyPathConnectedSpace (EuclideanSpace ℝ (Fin 2) × ℝ))
    | hyperbolicProd =>
      exact inferInstanceAs (LocallyPathConnectedSpace (WithLp 2 (ℝ × ℝ) × ℝ))
    | _ => infer_instance
  exact ChartedSpace.locallyPathConnectedSpace G.ChartSpace G.Space

/-- All eight models are analytic manifolds in their standard charts. -/
instance (G : ModelGeometry) : IsManifold G.model ω G.Space := by
  cases G <;> infer_instance

instance (G : ModelGeometry) : G.model.Boundaryless := by
  cases G <;> infer_instance

/-- The standard metric on each model, including the round and product metrics. -/
instance (G : ModelGeometry) :
    RiemannianBundle (fun x : G.Space => TangentSpace G.model x) := by
  cases G <;> infer_instance

/-- The standard metrics of all eight models are analytic. -/
instance (G : ModelGeometry) : IsContMDiffRiemannianBundle G.model ω G.ModelSpace
    (fun x : G.Space => TangentSpace G.model x) := by
  cases G <;> infer_instance

instance (G : ModelGeometry) : IsContinuousRiemannianBundle G.ModelSpace
    (fun x : G.Space => TangentSpace G.model x) :=
  IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle (IB := G.model) (n := ω)

/-- Each model is homogeneous under its full Riemannian isometry group. -/
instance (G : ModelGeometry) :
    MulAction.IsPretransitive (Isom G.model G.Space) G.Space := by
  cases G <;> infer_instance

/-- Every model geometry has dimension three. -/
@[simp]
theorem finrank_modelSpace (G : ModelGeometry) : finrank ℝ G.ModelSpace = 3 := by
  cases G with
  | hyperbolic =>
    exact (WithLp.linearEquiv 2 ℝ (EuclideanSpace ℝ (Fin 2) × ℝ)).finrank_eq.trans
      (by simp [Module.finrank_prod])
  | hyperbolicProd =>
    simp [Module.finrank_prod, (WithLp.linearEquiv 2 ℝ (ℝ × ℝ)).finrank_eq]
  | spherical | euclidean | sphereProd | sl2Tilde | nil | sol =>
    simp [Module.finrank_prod]

/-- There are exactly eight model geometries. -/
@[simp]
theorem card : Fintype.card ModelGeometry = 8 := by decide

end

end ModelGeometry

end TauCeti
