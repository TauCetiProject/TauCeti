/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.VectorBundle.OrthonormalFrame.Lift
public import TauCeti.Topology.VectorBundle.Riemannian.MetricChange.Basic
public import TauCeti.Topology.VectorBundle.Riemannian.WithFiberMetric

/-!
# Changing the metric of orthonormal frames and of their lifts

Let `E → B` be a continuous Riemannian vector bundle with finite-dimensional fibres, and let `g`
be a second continuous Riemannian metric on `E`. The fibres of `E` carrying `g` as their inner
product are the copy `TauCeti.WithFiberMetric g` of `E`. In each fibre the inverse square root
`B ^ (-1/2)` of the positive self-adjoint operator `B` with `g u v = ⟪B u, v⟫` is an isometry from
the given inner product to `g`
(`Bundle.ContinuousRiemannianMetric.inner_metricChangeTransport_metricChangeTransport`), so it is
a linear isometric equivalence `E b ≃ₗᵢ[ℝ] WithFiberMetric g b`
(`Bundle.ContinuousRiemannianMetric.metricChangeIsometry`). These isometries are continuous in
both directions on total spaces.

Composing frames with them carries orthonormal frames of the given metric to orthonormal frames of
`g`, equivariantly for the orthogonal group: this is the homeomorphism of orthonormal frame
bundles `TauCeti.OrthonormalFrameBundle.metricChangeHomeomorph`. Composing the frame map of a lift
of the orthonormal frame bundle along `ρ : G →* GL(ℝⁿ)` with it transports the lift to a lift for
`g` with the same principal bundle (`TauCeti.OrthonormalFrameLift.metricChange`). For `ρ` the
vector action of `Spin(n)` this carries Spin structures for the given metric to Spin structures
for `g`. Metric change is a bijection on lifts and on their equivalence classes
(`TauCeti.OrthonormalFrameLift.metricChange_injective`,
`TauCeti.OrthonormalFrameLift.nonempty_equiv_metricChange_iff`): the classification of lifts does
not depend on the metric.

## Main definitions

* `Bundle.ContinuousRiemannianMetric.metricChangeIsometry`: the fibrewise isometry `B ^ (-1/2)`
  from the given metric to `g`.
* `TauCeti.OrthonormalFrameBundle.metricChangeHomeomorph`: the induced homeomorphism from the
  orthonormal frames of the given metric to those of `g`.
* `TauCeti.OrthonormalFrameLift.metricChange`: the lift for `g` induced by a lift for the given
  metric.

## References

* H. B. Lawson, M.-L. Michelsohn, *Spin Geometry*, Princeton University Press, 1989, Chapter II,
  §1 (independence of Spin structures from the metric).
* J. Milnor and J. Stasheff, *Characteristic Classes*, Princeton University Press, 1974, §2
  (Euclidean vector bundles and their orthonormal frames).
-/

public section

noncomputable section

open Bundle InnerProductSpace TauCeti
open scoped InnerProductSpace

/-- The Riesz operator of a real bilinear form, written as Mathlib's `InnerProductSpace.Dual`
writes it. -/
local postfix:1024 "♯" => continuousLinearMapOfBilin (𝕜 := ℝ)

universe w

variable {B : Type*} [TopologicalSpace B] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {E : B → Type w} [TopologicalSpace (TotalSpace F E)] [∀ b, NormedAddCommGroup (E b)]
  [∀ b, InnerProductSpace ℝ (E b)] [∀ b, FiniteDimensional ℝ (E b)] [FiberBundle F E]
  [VectorBundle ℝ F E] (g : ContinuousRiemannianMetric F E)

namespace Bundle.ContinuousRiemannianMetric

/-- The **metric change isometry** of a second continuous Riemannian metric `g`: on the fibre over
`b`, the inverse square root of the Riesz operator of `g` for the given inner product, a linear
isometric equivalence from the given inner product to the copy `WithFiberMetric g b` of the fibre
carrying `g`. -/
def metricChangeIsometry (b : B) : E b ≃ₗᵢ[ℝ] WithFiberMetric g b :=
  (((g.inner b).metricChangeEquiv
      (g.isStrictlyPositive_continuousLinearMapOfBilin_inner b)).toLinearEquiv.trans
    (WithFiberMetric.toWithFiberMetric g b).toLinearEquiv).isometryOfInner fun u v ↦ by
    simp

/-- The metric change isometry applies the metric change transport of `g`. -/
theorem metricChangeIsometry_apply (b : B) (v : E b) :
    g.metricChangeIsometry b v =
      WithFiberMetric.toWithFiberMetric g b ((g.inner b).metricChangeTransport v) := by
  simp [metricChangeIsometry]

/-- As a linear equivalence, the metric change isometry is the metric change equivalence of `g`
followed by the identification of `E b` with its copy carrying `g`. -/
theorem toLinearEquiv_metricChangeIsometry (b : B) :
    (g.metricChangeIsometry b).toLinearEquiv =
      ((g.inner b).metricChangeEquiv
          (g.isStrictlyPositive_continuousLinearMapOfBilin_inner b)).toLinearEquiv.trans
        (WithFiberMetric.toWithFiberMetric g b).toLinearEquiv :=
  (rfl)

/-- The inverse of the metric change isometry applies the square root of the Riesz operator of
`g`. -/
theorem metricChangeIsometry_symm_apply (b : B) (v : WithFiberMetric g b) :
    (g.metricChangeIsometry b).symm v =
      CFC.sqrt (g.inner b)♯ ((WithFiberMetric.toWithFiberMetric g b).symm v) := by
  rw [LinearIsometryEquiv.symm_apply_eq, metricChangeIsometry_apply,
    ContinuousLinearMap.metricChangeTransport_apply_sqrt_apply
      (g.isStrictlyPositive_continuousLinearMapOfBilin_inner b),
    ContinuousLinearEquiv.apply_symm_apply]

variable [IsContinuousRiemannianBundle F E]

/-- The metric change isometries form a continuous map of total spaces. -/
theorem continuous_metricChangeIsometry :
    Continuous fun v : TotalSpace F E ↦
      (⟨v.proj, g.metricChangeIsometry v.proj v.snd⟩ : TotalSpace F (WithFiberMetric g)) :=
  ((WithFiberMetric.continuous_totalSpaceMk_toWithFiberMetric_iff g (p := TotalSpace.proj)
    (s := fun v ↦ (g.inner v.proj).metricChangeTransport v.snd)).2
    g.continuous_metricChangeTransport).congr fun v ↦ by rw [metricChangeIsometry_apply]

/-- The inverses of the metric change isometries form a continuous map of total spaces. -/
theorem continuous_metricChangeIsometry_symm :
    Continuous fun v : TotalSpace F (WithFiberMetric g) ↦
      (⟨v.proj, (g.metricChangeIsometry v.proj).symm v.snd⟩ : TotalSpace F E) := by
  -- Both total spaces carry the topology of `TotalSpace F E`, so the identity is continuous.
  have hid : Continuous fun v : TotalSpace F (WithFiberMetric g) ↦
      (⟨v.proj, v.snd⟩ : TotalSpace F E) :=
    (WithFiberMetric.continuous_totalSpaceMk_toWithFiberMetric_iff g (p := TotalSpace.proj)
      (s := fun v ↦ (v.snd : E v.proj))).1
      (continuous_id.congr fun v ↦ (congrArg (TotalSpace.mk' F (E := WithFiberMetric g) v.proj)
        (WithFiberMetric.toWithFiberMetric_apply g v.proj v.snd)).symm)
  refine (g.metricChangeHomeomorph.continuous_symm.comp hid).congr fun v ↦ ?_
  rw [Function.comp_apply, metricChangeHomeomorph_symm_apply, metricChangeIsometry_symm_apply,
    WithFiberMetric.toWithFiberMetric_symm_apply]

end Bundle.ContinuousRiemannianMetric

variable [IsContinuousRiemannianBundle F E]

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

/-- Metric change is injective on lifts: a lift for the given metric is recovered from its metric
change by transporting back along the inverse isometries. -/
theorem metricChange_injective :
    Function.Injective fun s : OrthonormalFrameLift F E n G ρ ↦ s.metricChange g :=
  map_injective g.continuous_metricChangeIsometry_symm

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
