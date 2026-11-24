/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Isometry
public import TauCeti.Topology.VectorBundle.Riemannian.MetricChange.Basic

/-!
# Changing the metric of orthonormal frames

Let `E → B` be a continuous Riemannian vector bundle with finite-dimensional fibres, and let `g`
be a second continuous Riemannian metric on `E`. The fibres of `E` carrying `g` as their inner
product are the copy `TauCeti.WithFiberMetric g` of `E`. In each fibre the inverse square root
`B ^ (-1/2)` of the positive self-adjoint operator `B` with `g u v = ⟪B u, v⟫` is a linear isometric
equivalence `E b ≃ₗᵢ[ℝ] WithFiberMetric g b`
(`Bundle.ContinuousRiemannianMetric.metricChangeIsometry`), continuous in both directions on total
spaces.

Composing frames with these isometries carries orthonormal frames of the given metric to
orthonormal frames of `g`, equivariantly for the orthogonal group: this is the homeomorphism of
orthonormal frame bundles `TauCeti.OrthonormalFrameBundle.metricChangeHomeomorph`.

## Main definitions

* `TauCeti.OrthonormalFrameBundle.metricChangeHomeomorph`: the homeomorphism from the orthonormal
  frames of the given metric to those of `g` induced by the metric change isometries.

## References

* J. Milnor and J. Stasheff, *Characteristic Classes*, Princeton University Press, 1974, §2
  (Euclidean vector bundles and their orthonormal frames).
-/

public section

noncomputable section

open Bundle

universe w

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] [∀ b, FiniteDimensional ℝ (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E] (g : ContinuousRiemannianMetric F E)

namespace TauCeti.OrthonormalFrameBundle

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- The **metric change of orthonormal frames**: composing with the metric change isometries of
`g` carries the orthonormal frames of the given metric homeomorphically onto the orthonormal frames
of `g`, covering the identity of the base and commuting with the right action of the orthogonal
group (`TauCeti.OrthonormalFrameBundle.map_smul`). -/
def metricChangeHomeomorph :
    OrthonormalFrameBundle ℝ F E V ≃ₜ OrthonormalFrameBundle ℝ F (WithFiberMetric g) V :=
  mapHomeomorph g.metricChangeIsometry g.continuous_metricChangeIsometry
    g.continuous_metricChangeIsometry_symm

@[simp]
theorem metricChangeHomeomorph_apply (p : OrthonormalFrameBundle ℝ F E V) :
    metricChangeHomeomorph g p = map g.metricChangeIsometry p :=
  mapHomeomorph_apply _ _ _ p

@[simp]
theorem metricChangeHomeomorph_symm_apply
    (p : OrthonormalFrameBundle ℝ F (WithFiberMetric g) V) :
    (metricChangeHomeomorph g).symm p = map (fun b ↦ (g.metricChangeIsometry b).symm) p :=
  mapHomeomorph_symm_apply _ _ _ p

end TauCeti.OrthonormalFrameBundle
