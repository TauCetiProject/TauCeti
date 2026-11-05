/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.ConnectedSum
public import TauCeti.Geometry.Manifold.Riemannian.PositiveScalarCurvature.Basic

/-!
# Metrics of positive scalar curvature on a connected sum

Let `g₁` and `g₂` be smooth metrics on `M` and `N` which agree on the neck `a < ‖v‖ < b` of the
connected sum `TauCeti.ConnectedSum e₁ e₂`, and let `Bundle.ContMDiffRiemannianMetric.connectedSum`
be the metric on `M # N` glued from them. Its scalar curvature at each point is that of `g₁` or of
`g₂` (`Bundle.ContMDiffRiemannianMetric.range_scalarCurvature_connectedSum_subset`), so it has
positive scalar curvature when `g₁` and `g₂` do.

## Main results

* `Bundle.ContMDiffRiemannianMetric.HasPositiveScalarCurvature.connectedSum`: the glued metric of
  two metrics of positive scalar curvature has positive scalar curvature.

## References

* M. Gromov, H. B. Lawson, *The classification of simply connected manifolds of positive
  scalar curvature*, Ann. of Math. 111 (1980), 423–434, Theorem A.
* R. Schoen, S.-T. Yau, *On the structure of manifolds with positive scalar curvature*,
  Manuscripta Math. 28 (1979), 159–183, for the connected sum of manifolds of positive scalar
  curvature.
-/

public section

open Set Topology EuclideanGeometry
open TauCeti
open scoped ContDiff Manifold

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  {N : Type*} [TopologicalSpace N] [T2Space N] [ChartedSpace H N] [IsManifold I ∞ N]
  {e₁ : E → M} {e₂ : E → N} {a b : ℝ}
  {g₁ : ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)}
  {g₂ : ContMDiffRiemannianMetric I ∞ E (fun y : N ↦ TangentSpace I y)}
  (h₁ : IsOpenEmbedding e₁) (h₂ : IsOpenEmbedding e₂)
  (d₁ : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ e₁) (d₂ : IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ e₂)
  (hg : ∀ v : E, a < ‖v‖ → ‖v‖ < b → ∀ ξ ζ : E,
    g₁.inner (e₁ v) (mfderiv 𝓘(ℝ, E) I e₁ v ξ) (mfderiv 𝓘(ℝ, E) I e₁ v ζ) =
      g₂.inner (e₂ (inversion 0 1 v))
        (mfderiv 𝓘(ℝ, E) I e₂ (inversion 0 1 v) (fderiv ℝ (inversion (0 : E) 1) v ξ))
        (mfderiv 𝓘(ℝ, E) I e₂ (inversion 0 1 v) (fderiv ℝ (inversion (0 : E) 1) v ζ)))

/-- **Positive scalar curvature on a connected sum.** If `g₁` and `g₂` have positive scalar
curvature and agree on the neck, the metric on `M # N` glued from them has positive scalar
curvature. -/
theorem HasPositiveScalarCurvature.connectedSum (hg₁ : g₁.HasPositiveScalarCurvature)
    (hg₂ : g₂.HasPositiveScalarCurvature) (ha : 0 ≤ a) (hab : a < b) :
    letI := ConnectedSum.chartedSpace (H := H) h₁ h₂
    haveI := ConnectedSum.isManifold (n := ⊤) h₁ h₂ d₁ d₂
    haveI := ConnectedSum.t2Space h₁ h₂
    (g₁.connectedSum g₂ h₁ h₂ d₁ d₂ hg ha hab).HasPositiveScalarCurvature := by
  let := ConnectedSum.chartedSpace (H := H) h₁ h₂
  have := ConnectedSum.isManifold (n := ⊤) h₁ h₂ d₁ d₂
  have := ConnectedSum.t2Space h₁ h₂
  rw [hasPositiveScalarCurvature_iff]
  intro p
  obtain ⟨x, hx⟩ | ⟨y, hy⟩ :=
    range_scalarCurvature_connectedSum_subset h₁ h₂ d₁ d₂ hg ha hab (mem_range_self p)
  · exact hx ▸ (hasPositiveScalarCurvature_iff g₁).1 hg₁ x
  · exact hy ▸ (hasPositiveScalarCurvature_iff g₂).1 hg₂ y

end Bundle.ContMDiffRiemannianMetric
