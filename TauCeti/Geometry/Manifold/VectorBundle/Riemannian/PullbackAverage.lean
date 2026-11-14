/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Mean
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Pullback

/-!
# Averaging a bundle metric with its pullback by a fibre automorphism

Let `A` be a `C^n` field of continuous linear automorphisms of the fibres of a real vector bundle.
The mean of a `C^n` metric `g` and its pullback by `A`,

`g'(u, v) = ½ (g(u, v) + g(A u, A v))`,

is again a `C^n` metric. When `A² = -1` in every fibre, as for a complex structure, `A` is an
isometry of `g'`, so averaging produces `A`-invariant metrics. A metric is its own average exactly
when `A` is already an isometry of it.

This is the construction behind Hermitian metrics on complex bundles, with `A` multiplication by
`i`, and behind metrics compatible with an almost complex structure, with `A` the structure
itself.

## Main declarations

* `Bundle.ContMDiffRiemannianMetric.pullbackAverage`: the average `½ (g + A^* g)`.
* `Bundle.ContMDiffRiemannianMetric.pullbackAverage_inner_apply_apply`: if `A² = -1`, then `A` is
  an isometry of the average.
* `Bundle.ContMDiffRiemannianMetric.pullbackAverage_eq_self_iff`: the average of `g` is `g`
  exactly when `A` is an isometry of `g`.
-/

public noncomputable section

open Bundle
open scoped Manifold ContDiff

namespace Bundle.ContMDiffRiemannianMetric

variable {X H B F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [TopologicalSpace H] {IB : ModelWithCorners ℝ X H}
  [TopologicalSpace B] [ChartedSpace H B]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  {V : B → Type*}
  [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [∀ x, TopologicalSpace (V x)]
  [∀ x, IsTopologicalAddGroup (V x)] [∀ x, ContinuousSMul ℝ (V x)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V] [VectorBundle ℝ F V]
  {n : ℕ∞ω} (A : ∀ x, V x ≃L[ℝ] V x)
  (hA : ContMDiff IB (IB.prod 𝓘(ℝ, F →L[ℝ] F)) n
    (fun x ↦ (⟨x, (A x).toContinuousLinearMap⟩ :
      TotalSpace (F →L[ℝ] F) (fun y ↦ V y →L[ℝ] V y))))

/-- **The pullback average of a metric.** The mean `½ (g(u, v) + g(A u, A v))` of a metric `g` and
its pullback by a `C^n` field `A` of fibre automorphisms. -/
def pullbackAverage (g : ContMDiffRiemannianMetric IB n F V) :
    ContMDiffRiemannianMetric IB n F V :=
  TauCeti.meanRiemannianMetric (fun b : Bool ↦ if b then g.pullbackBundleEquiv A hA else g)

/-- The pullback average is the half-sum of the metric and its pullback. -/
@[simp]
theorem pullbackAverage_inner (g : ContMDiffRiemannianMetric IB n F V) (x : B) (u v : V x) :
    (g.pullbackAverage A hA).inner x u v = 2⁻¹ * (g.inner x u v + g.inner x (A x u) (A x v)) := by
  simp [pullbackAverage, TauCeti.meanRiemannianMetric_inner, add_comm]

/-- If `A² = -1` in every fibre, then `A` is an isometry of the pullback average. -/
theorem pullbackAverage_inner_apply_apply (hA₂ : ∀ x (v : V x), A x (A x v) = -v)
    (g : ContMDiffRiemannianMetric IB n F V) (x : B) (u v : V x) :
    (g.pullbackAverage A hA).inner x (A x u) (A x v) = (g.pullbackAverage A hA).inner x u v := by
  rw [pullbackAverage_inner, pullbackAverage_inner, hA₂, hA₂, map_neg,
    ContinuousLinearMap.map_neg₂, neg_neg]
  ring

/-- A metric is its own pullback average exactly when `A` is an isometry of it. -/
theorem pullbackAverage_eq_self_iff (g : ContMDiffRiemannianMetric IB n F V) :
    g.pullbackAverage A hA = g ↔ ∀ x (u v : V x), g.inner x (A x u) (A x v) = g.inner x u v := by
  constructor
  · intro h x u v
    have := congrArg (fun g : ContMDiffRiemannianMetric IB n F V ↦ g.inner x u v) h
    simp only [pullbackAverage_inner] at this
    linarith
  · intro h
    ext x u v
    rw [pullbackAverage_inner, h]
    ring

/-- If `A² = -1` in every fibre, then pullback averaging is idempotent. -/
theorem pullbackAverage_pullbackAverage (hA₂ : ∀ x (v : V x), A x (A x v) = -v)
    (g : ContMDiffRiemannianMetric IB n F V) :
    (g.pullbackAverage A hA).pullbackAverage A hA = g.pullbackAverage A hA :=
  (pullbackAverage_eq_self_iff A hA _).2 (pullbackAverage_inner_apply_apply A hA hA₂ g)

end Bundle.ContMDiffRiemannianMetric
