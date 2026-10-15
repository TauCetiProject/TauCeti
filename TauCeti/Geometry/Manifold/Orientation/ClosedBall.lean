/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Orientation.MFDerivEquiv
public import TauCeti.Geometry.Manifold.Instances.ClosedBall.Inclusion

/-!
# Orientations of closed unit balls

The inclusion tangent equivalence transports any orientation of a positive-dimensional real
inner-product space to its closed unit ball, including at every boundary point.
-/

public section
noncomputable section

open scoped Manifold

namespace TauCeti.Manifold.Orientation

variable {n : ℕ} [NeZero n] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = n)]

/-- The closed unit ball's orientation induced by its inclusion derivative. -/
def closedBall (o : _root_.Orientation ℝ V (Fin n)) :
    Orientation (𝓡∂ n) (Metric.closedBall (0 : V) 1) (Fin n) :=
  ofMFDerivEquiv (contMDiff_subtypeVal_closedBall (n := n) (k := 1))
    (subtypeValClosedBallTangentEquiv (n := n))
    subtypeValClosedBallTangentEquiv_toContinuousLinearMap
    (EuclideanSpace.basisFun (Fin n) ℝ).toBasis.orientation (by simp) o

/-- At every point of the ball, its inclusion tangent equivalence preserves the chosen
ambient orientation. This also holds at the sphere boundary and in dimension one. -/
@[simp]
theorem map_orientationAt_closedBall (o : _root_.Orientation ℝ V (Fin n))
    (x : Metric.closedBall (0 : V) 1) :
    _root_.Orientation.map (Fin n)
      (subtypeValClosedBallTangentEquiv (n := n) x).toLinearEquiv
      ((closedBall o).orientationAt x) = o :=
  map_orientationAt_ofMFDerivEquiv _ _ _ _ _ _ x

end TauCeti.Manifold.Orientation

namespace TauCeti

variable {n : ℕ} [NeZero n] {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [Fact (Module.finrank ℝ V = n)]

/-- Every positive-dimensional closed unit ball is orientable, including dimension one. -/
theorem orientable_closedBall : Orientable (𝓡∂ n) (Metric.closedBall (0 : V) 1) := by
  have hV : Module.finrank ℝ V = n := Fact.out
  have : FiniteDimensional ℝ V := Module.finite_of_finrank_pos (by
    rw [hV]
    exact Nat.pos_of_neZero n)
  let o := ((Module.finBasis ℝ V).reindex (finCongr hV)).orientation
  constructor
  rw [finrank_euclideanSpace_fin]
  exact ⟨Manifold.Orientation.closedBall o⟩

end TauCeti
