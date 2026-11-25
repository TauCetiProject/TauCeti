/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.Curvature.Ricci
public import TauCeti.Geometry.Manifold.VectorBundle.NondegenerateMetric.Musical

/-!
# Ricci curvature with one raised index

A native nondegenerate metric identifies covectors and vectors. Composing its inverse flat map
with a connection's native Ricci tensor gives the Ricci endomorphism. Lowering the index
recovers the original Ricci tensor. The connection need not be compatible with the metric.
-/

public noncomputable section

open Bundle
open TauCeti.Manifold
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]

namespace CovariantDerivative

variable (cov : CovariantDerivative I E (TangentSpace I : M → Type _))
  [ContMDiffCovariantDerivative cov ∞]

/-- Ricci curvature with one index raised by a supplied nondegenerate metric. The connection
need not be metric compatible; its native Ricci tensor is used without changing the connection. -/
def ricciEndomorphism
    (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x :=
  (g x).inverse ∘L (cov.ricciTensor x).toContinuousBilinearMap

/-- Raising a Ricci index composes its continuous bilinear form with the inverse flat map. -/
theorem ricciEndomorphism_def
    (g : ContMDiffNondegenerateMetric (I := I) (M := M)) (x : M) :
    cov.ricciEndomorphism g x =
      (g x).inverse ∘L (cov.ricciTensor x).toContinuousBilinearMap := (rfl)

/-- Lowering the raised index recovers the native Ricci tensor. -/
@[simp]
theorem inner_ricciEndomorphism
    (g : ContMDiffNondegenerateMetric (I := I) (M := M))
    (x : M) (v w : TangentSpace I x) :
    g x (cov.ricciEndomorphism g x v) w = cov.ricciTensor x v w := by
  rw [ricciEndomorphism_def, ContinuousLinearMap.comp_apply]
  have hinv := g.isInvertible x
  rw [hinv.self_apply_inverse]
  rfl

end CovariantDerivative
