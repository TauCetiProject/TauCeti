/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Schrodinger.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Relative.Basic
import TauCeti.Geometry.Manifold.Riemannian.Gradient.Isometry
import TauCeti.Geometry.Manifold.Riemannian.WithMetric.Isometry

/-!
# Scalar Schrödinger forms with a reference volume

The native scalar form can be integrated against a fixed metric's volume by multiplying
by the relative volume density and transporting the gradient along `ofWithMetric`.
-/

public noncomputable section

open Bundle Manifold MeasureTheory
open scoped ContDiff Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

namespace Bundle.ContMDiffRiemannianMetric

open TauCeti TauCeti.Manifold

variable [LindelofSpace M]

/-- Express the scalar Schrödinger form using a fixed reference volume and the relative
volume density. The gradient on the underlying manifold is computed with the metric `g`. -/
theorem scalarSchrodingerForm_eq_integral_relativeVolumeDensity
    (r g : ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M → Type _))
    (P : M → ℝ) {φ : M → ℝ} (hφ : MDifferentiable I 𝓘(ℝ) φ) :
    letI : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
    scalarSchrodingerForm g P φ =
      ∫ x : WithMetric r, r.relativeVolumeDensity g x.ofWithMetric *
        (‖mgradient I φ x.ofWithMetric‖ ^ 2 + P x.ofWithMetric * φ x.ofWithMetric ^ 2)
        ∂riemannianVolume I (WithMetric r) := by
  let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩
  rw [scalarSchrodingerForm_def]
  have hiso : IsLocalRiemannianIsometry I I
      (WithMetric.ofWithMetric : WithMetric g → M) := by
    simpa only [WithMetric.coe_riemannianIsometry] using
      (WithMetric.riemannianIsometry g).isLocalRiemannianIsometry
  simp_rw [hiso.norm_mgradient_comp (hφ _)]
  simpa only [smul_eq_mul] using
    r.integral_riemannianVolume_eq_integral_relativeVolumeDensity_smul g
      (fun x ↦ ‖mgradient I φ x‖ ^ 2 + P x * φ x ^ 2)

end Bundle.ContMDiffRiemannianMetric
