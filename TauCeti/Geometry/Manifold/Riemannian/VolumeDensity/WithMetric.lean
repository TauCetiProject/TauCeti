/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Isometry
public import TauCeti.Geometry.Manifold.Riemannian.WithMetric

/-!
# The Riemannian volume of a metric-indexed copy

The copy `TauCeti.WithMetric g` of a manifold `M` carries the metric `g` as its
`RiemannianBundle` instance, and the tautological map `ofWithMetric : WithMetric g → M` is an
isometry onto `M` with `g` installed as its instance. Consequently it carries the Riemannian volume
of the copy to the Riemannian volume of `(M, g)`, and an integral over the copy of a function read
through `ofWithMetric` is the corresponding integral over `(M, g)`.

This lets results proved for the instance metric of a manifold, such as integration-by-parts
formulas, be applied to integrals over metric-indexed copies, which is how two metrics on one
manifold are compared without installing two metric instances on the same carrier.

## Main results

* `TauCeti.WithMetric.measurePreserving_ofWithMetric`: `ofWithMetric` carries the volume of
  `WithMetric g` to the volume of `(M, g)`.
* `TauCeti.WithMetric.integral_comp_ofWithMetric`: `∫ φ ∘ ofWithMetric dV_{WithMetric g} =
  ∫ φ dV_{(M, g)}`.
-/

public section

open Bundle MeasureTheory
open scoped Manifold ContDiff

noncomputable section

namespace TauCeti.WithMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))

/-- The tautological map from the copy of `M` carrying `g` to `M` carries the Riemannian volume
of the copy to the Riemannian volume of `M` with `g` installed as its metric. -/
theorem measurePreserving_ofWithMetric :
    MeasurePreserving (ofWithMetric : WithMetric g → M) (riemannianVolume I (WithMetric g))
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric;
        riemannianVolume I M) := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  have h := (homeomorph g).measurePreserving_riemannianVolume (I' := I)
    (by rw [coe_homeomorph]; exact contMDiff_ofWithMetric.mdifferentiable one_ne_zero)
    fun x v w ↦ by rw [coe_homeomorph, inner_def x v w]; rfl
  rwa [coe_homeomorph] at h

/-- Integration over the copy of `M` carrying `g` of a function read through `ofWithMetric` is
integration over `M` with `g` installed as its metric. -/
theorem integral_comp_ofWithMetric {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : M → F) :
    ∫ x, φ x.ofWithMetric ∂riemannianVolume I (WithMetric g) =
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩;
        letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
          instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric;
        ∫ x, φ x ∂riemannianVolume I M) :=
  (measurePreserving_ofWithMetric g).integral_comp
    (coe_homeomorph g ▸ (homeomorph g).measurableEmbedding) φ

end TauCeti.WithMetric
