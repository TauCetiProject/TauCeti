/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.Riemannian.Pullback

/-!
# The induced Riemannian metric on a manifold boundary

A `C^k` Riemannian metric on a `C^(k + 1)` manifold with boundary pulls back along the boundary
inclusion to a `C^k` Riemannian metric on the intrinsic boundary manifold, for every
`k : ℕ∞ω`.

## Main results

* `Bundle.ContMDiffRiemannianMetric.restrictBoundaryTangentSpace`: the induced metric on the
  boundary.
* `Bundle.ContMDiffRiemannianMetric.restrictBoundaryTangentSpace_inner`: the induced metric
  evaluates tangent vectors by applying the ambient metric to their derivatives under the boundary
  inclusion.

## References

* J. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (induced metrics on submanifolds and boundaries).
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace Bundle.ContMDiffRiemannianMetric

variable {n : ℕ} {k : ℕ∞ω} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) 1 M]
  [IsManifold (𝓡∂ (n + 1)) (k + 1) M]

local instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (k + 1)
    ((𝓡∂ (n + 1)).boundary M) :=
  TauCeti.isManifold_boundary (n := n) (k := k + 1) M (by simp)

local instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1
    ((𝓡∂ (n + 1)).boundary M) :=
  TauCeti.isManifold_boundary (n := n) (k := 1) M one_ne_zero

private lemma contMDiff_subtypeVal_boundary :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) (k + 1)
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) := by
  exact (TauCeti.isSmoothEmbedding_subtypeVal_boundary (n := n) (k := k + 1) M
    (by simp)).contMDiff

include k in
private lemma injective_mfderiv_subtypeVal_boundary :
    ∀ x, Function.Injective
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x) := by
  intro x
  exact (TauCeti.isImmersion_subtypeVal_boundary (n := n) (k := k + 1) M
    (by simp)).mfderiv_injective (by simp) x

/-- The `C^k` Riemannian metric induced on the boundary by an ambient `C^k` metric. -/
noncomputable def restrictBoundaryTangentSpace
    (g : ContMDiffRiemannianMetric (𝓡∂ (n + 1)) k
        (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)) :
    ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k
      (EuclideanSpace ℝ (Fin n))
      (fun x : (𝓡∂ (n + 1)).boundary M ↦
        TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
    g.pullback Subtype.val (contMDiff_subtypeVal_boundary (n := n) (k := k) (M := M))
      (injective_mfderiv_subtypeVal_boundary (n := n) (k := k) (M := M))

/-- The induced boundary metric evaluates the ambient metric on boundary tangent derivatives. -/
@[simp]
theorem restrictBoundaryTangentSpace_inner
    (g : ContMDiffRiemannianMetric (𝓡∂ (n + 1)) k
        (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)) :
    ∀ (x : (𝓡∂ (n + 1)).boundary M)
      (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
      (g.restrictBoundaryTangentSpace).inner x v w =
        g.inner (x : M)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
            (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x v)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
            (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x w) := by
  intro x v w
  exact g.pullback_inner Subtype.val
    (contMDiff_subtypeVal_boundary (n := n) (k := k) (M := M))
    (injective_mfderiv_subtypeVal_boundary (n := n) (k := k) (M := M)) x v w

end Bundle.ContMDiffRiemannianMetric
