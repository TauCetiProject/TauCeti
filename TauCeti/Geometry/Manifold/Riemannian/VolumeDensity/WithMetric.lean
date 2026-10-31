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
isometry onto `M` with `g` installed as its fibre metric. By the isometry invariance of the
Riemannian volume, this map carries the volume of the copy to the volume of `(M, g)`, so integrals
against the volume of `WithMetric g` are integrals against the volume of `g` on `M` itself.

This lets results proved for the installed metric of a manifold, such as the divergence theorem
and Green's identities, be applied to the volumes of the copies, which are used to compare two
metrics on `M` without installing both on the same carrier.

## Main results

* `TauCeti.WithMetric.measurePreserving_ofWithMetric`: `ofWithMetric` carries the volume of
  `WithMetric g` to the volume of `M` with `g` installed.
* `TauCeti.WithMetric.integral_comp_ofWithMetric`: `∫ φ ∘ ofWithMetric` against the volume of
  `WithMetric g` is `∫ φ` against the volume of `g` on `M`.
-/

public section

open Bundle MeasureTheory
open scoped ContDiff InnerProductSpace Manifold

noncomputable section

namespace TauCeti.WithMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  (g : ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x))

/-- **The volume of a metric-indexed copy.** The tautological map `ofWithMetric` carries the
Riemannian volume of `WithMetric g` to the Riemannian volume of `M` with `g` installed as its
fibre metric. -/
theorem measurePreserving_ofWithMetric :
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
      instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
    MeasurePreserving (ofWithMetric : WithMetric g → M) (riemannianVolume I (WithMetric g))
      (riemannianVolume I M) := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  have h := (homeomorph g).measurePreserving_riemannianVolume (I := I) (I' := I) ?_ ?_
  · rwa [coe_homeomorph] at h
  · rw [coe_homeomorph]
    exact contMDiff_ofWithMetric.mdifferentiable one_ne_zero
  · intro x v w
    rw [coe_homeomorph]
    exact (inner_def x v w).symm

/-- Integration against the volume of the metric-indexed copy `WithMetric g` is integration
against the volume of `g` on `M`: `∫ φ ∘ ofWithMetric dV_{WithMetric g} = ∫ φ dV_g`. -/
theorem integral_comp_ofWithMetric {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (φ : M → F) :
    ∫ x, φ x.ofWithMetric ∂riemannianVolume I (WithMetric g) =
      (letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
      letI : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
        instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
      ∫ x, φ x ∂riemannianVolume I M) := by
  let _ : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  let _ : IsContinuousRiemannianBundle E (fun x : M ↦ TangentSpace I x) :=
    instIsContinuousRiemannianBundle g.toContinuousRiemannianMetric
  have hemb : MeasurableEmbedding (ofWithMetric : WithMetric g → M) := by
    simpa only [coe_homeomorph] using (homeomorph g).measurableEmbedding
  exact (measurePreserving_ofWithMetric g).integral_comp hemb φ

end TauCeti.WithMetric
