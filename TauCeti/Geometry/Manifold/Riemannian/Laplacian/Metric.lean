/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Laplacian
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Basic

/-!
# Transporting the Laplacian between equal metric carriers

Installing a bundled C¹ metric gives the same native Laplace–Beltrami operator as an already
installed equal metric. The identity transports the dependent norm and regularity instances
together; rewriting only the carrier inside the operator would leave those instances behind.
It applies in particular when a smooth metric is regarded as a C¹ metric.

## Main results

* `Bundle.ContMDiffRiemannianMetric.laplaceBeltrami_eq_of_metric_eq`: equality of the operators
  under equality of the installed metric carriers.
-/

public noncomputable section
open scoped ContDiff Manifold

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]

/-- Installing a bundled C¹ metric preserves the native Laplacian when its carrier equals the
already installed Riemannian metric. -/
theorem laplaceBeltrami_eq_of_metric_eq
    (g : ContMDiffRiemannianMetric I 1 E (TangentSpace I : M → Type _))
    [inst : RiemannianBundle (TangentSpace I : M → Type _)]
    [IsContMDiffRiemannianBundle I 1 E (TangentSpace I : M → Type _)]
    (hg : RiemannianBundle.g = g.toRiemannianMetric) (f : M → ℝ) (x : M) :
    (let : RiemannianBundle (TangentSpace I : M → Type _) := ⟨g.toRiemannianMetric⟩;
      TauCeti.Manifold.laplaceBeltrami I f x) = TauCeti.Manifold.laplaceBeltrami I f x := by
  -- The bundle has only its metric as data; substitution leaves equal regularity proofs.
  obtain ⟨_⟩ := inst
  subst hg
  rfl

end Bundle.ContMDiffRiemannianMetric
