/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Lift
public import TauCeti.Topology.VectorBundle.OrthonormalFrame.MetricChange

/-!
# Changing the metric of lifts of orthonormal frame bundles

Let `E → B` be a continuous Riemannian vector bundle with finite-dimensional fibres, and let `g`
be a second continuous Riemannian metric on `E`, so that `TauCeti.WithFiberMetric g` is the copy of
`E` whose fibres carry `g`. Composing the frame map of a lift of the orthonormal frame bundle along
`ρ : G →* GL(ℝⁿ)` with the metric change of orthonormal frames
(`TauCeti.OrthonormalFrameBundle.metricChangeHomeomorph`) transports the lift to a lift for `g`
with the same principal bundle (`TauCeti.OrthonormalFrameLift.metricChange`). For `ρ` the vector
action of `Spin(n)` this carries Spin structures for the given metric to Spin structures for `g`.

Metric change is a bijection on lifts and on their equivalence classes
(`TauCeti.OrthonormalFrameLift.metricChange_injective`,
`TauCeti.OrthonormalFrameLift.metricChange_surjective`,
`TauCeti.OrthonormalFrameLift.nonempty_equiv_metricChange_iff`): the classification of lifts does
not depend on the metric.

## Main definitions

* `TauCeti.OrthonormalFrameLift.metricChange`: the lift for `g` induced by a lift for the given
  metric.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Chapter II,
  §1 (independence of Spin structures from the metric).
-/

public section

open Bundle

universe w

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] [∀ b, FiniteDimensional ℝ (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] [IsContinuousRiemannianBundle F E] (g : ContinuousRiemannianMetric F E)

namespace TauCeti.OrthonormalFrameLift

variable {n : ℕ} {G : Type*} [Group G] [TopologicalSpace G]
  {ρ : G →* (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ)}

/-- The **metric change of a lift** of the orthonormal frame bundle along `ρ`: the same principal
bundle, with its frame map composed with the metric change of orthonormal frames to the second
metric `g`. For `ρ` the vector action of `Spin(n)` this carries a Spin structure for the given
metric to a Spin structure for `g`. -/
noncomputable abbrev metricChange (s : OrthonormalFrameLift F E n G ρ) :
    OrthonormalFrameLift F (WithFiberMetric g) n G ρ :=
  s.map g.metricChangeIsometry g.continuous_metricChangeIsometry

/-- The frame of a point of the metric change of a lift is the metric change of its frame. -/
theorem toFrame_metricChange (s : OrthonormalFrameLift F E n G ρ) (p : TotalSpace G s.P) :
    (s.metricChange g).toFrame p = OrthonormalFrameBundle.metricChangeHomeomorph g (s.toFrame p) :=
  (s.toFrame_map p).trans (OrthonormalFrameBundle.metricChangeHomeomorph_apply g _).symm

/-- Metric change is injective on lifts. -/
theorem metricChange_injective :
    Function.Injective fun s : OrthonormalFrameLift F E n G ρ ↦ s.metricChange g :=
  map_injective

/-- Every lift for the metric `g` is the metric change of a lift for the given metric. -/
theorem metricChange_surjective :
    Function.Surjective fun s : OrthonormalFrameLift F E n G ρ ↦ s.metricChange g :=
  map_surjective g.continuous_metricChangeIsometry_symm

/-- **Metric change preserves and reflects equivalence of lifts**, so it is a bijection on
equivalence classes of lifts. -/
theorem nonempty_equiv_metricChange_iff (s t : OrthonormalFrameLift F E n G ρ) :
    Nonempty ((s.metricChange g).Equiv (t.metricChange g)) ↔ Nonempty (s.Equiv t) :=
  nonempty_equiv_map_iff s t

end TauCeti.OrthonormalFrameLift
