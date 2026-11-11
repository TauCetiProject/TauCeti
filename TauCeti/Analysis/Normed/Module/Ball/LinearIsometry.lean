/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Topology.MetricSpace.Isometry

/-!
# Linear isometries of the closed unit ball

A (semi)linear isometry preserves norms, so it maps the closed unit ball into the closed unit
ball. This file records the restriction to the closed unit balls, independently of any manifold
structure: it is an isometry, hence a topological embedding when the source is normed. These are
the point-set facts behind the smooth embedding of closed balls induced by a linear isometry, the
flat disc that a great circle bounds.

## Main definitions

* `LinearIsometry.unitClosedBallMap`: the restriction of a (semi)linear isometry to the closed
  unit balls.

## Main results

* `LinearIsometry.isometry_unitClosedBallMap`, `LinearIsometry.isEmbedding_unitClosedBallMap`:
  the restriction is an isometry, hence (for a normed source) a topological embedding.
-/

public section

open Metric

namespace LinearIsometry

section Seminormed

variable {R R₂ E F : Type*} [Semiring R] [Semiring R₂] {σ₁₂ : R →+* R₂}
  [SeminormedAddCommGroup E] [SeminormedAddCommGroup F] [Module R E] [Module R₂ F]

/-- The restriction of a (semi)linear isometry to the closed unit balls. -/
def unitClosedBallMap (f : E →ₛₗᵢ[σ₁₂] F) (x : closedBall (0 : E) 1) : closedBall (0 : F) 1 :=
  ⟨f x, f.map_zero ▸ f.isometry.mapsTo_closedBall 0 1 x.2⟩

@[simp]
theorem coe_unitClosedBallMap_apply (f : E →ₛₗᵢ[σ₁₂] F) (x : closedBall (0 : E) 1) :
    (f.unitClosedBallMap x : F) = f x :=
  (rfl)

/-- The restriction of a linear isometry to the closed unit balls is an isometry. -/
theorem isometry_unitClosedBallMap (f : E →ₛₗᵢ[σ₁₂] F) : Isometry f.unitClosedBallMap :=
  Isometry.of_dist_eq fun x y => by simp [Subtype.dist_eq]

/-- The restriction of a linear isometry to the closed unit balls is continuous. -/
theorem continuous_unitClosedBallMap (f : E →ₛₗᵢ[σ₁₂] F) : Continuous f.unitClosedBallMap :=
  f.isometry_unitClosedBallMap.continuous

end Seminormed

section Normed

variable {R R₂ E F : Type*} [Semiring R] [Semiring R₂] {σ₁₂ : R →+* R₂}
  [NormedAddCommGroup E] [SeminormedAddCommGroup F] [Module R E] [Module R₂ F]

/-- The restriction of a linear isometry to the closed unit balls is a topological embedding. -/
theorem isEmbedding_unitClosedBallMap (f : E →ₛₗᵢ[σ₁₂] F) :
    Topology.IsEmbedding f.unitClosedBallMap :=
  f.isometry_unitClosedBallMap.isEmbedding

end Normed

end LinearIsometry
