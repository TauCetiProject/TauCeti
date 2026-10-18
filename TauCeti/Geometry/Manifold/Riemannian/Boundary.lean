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

A smooth Riemannian metric on a manifold with boundary restricts to the intrinsic boundary
manifold by pulling it back along the boundary inclusion.  The construction uses the existing
boundary charts and the generic pullback metric, so the inclusion's injective differential supplies
positive definiteness automatically.
-/

public section

noncomputable section

open Bundle
open scoped ContDiff Manifold

namespace Bundle.ContMDiffRiemannianMetric

variable {n k : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) 1 M]
  [IsManifold (𝓡∂ (n + 1)) (k + 1) M]

local instance boundaryRegular :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (k + 1)
      ((𝓡∂ (n + 1)).boundary M) :=
  TauCeti.isManifold_boundary (n := n) (k := k + 1) M (by simp)
local instance boundaryOne :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1
      ((𝓡∂ (n + 1)).boundary M) :=
  TauCeti.isManifold_boundary (n := n) (k := 1) M one_ne_zero

/-- The `C^k` Riemannian metric induced on the boundary by an ambient `C^k` metric. -/
noncomputable def restrictBoundaryTangentSpace
    (g : ContMDiffRiemannianMetric (𝓡∂ (n + 1)) k
      (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)) :
    ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k
      (EuclideanSpace ℝ (Fin n))
      (fun x : (𝓡∂ (n + 1)).boundary M ↦
        TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) := by
  let f : (𝓡∂ (n + 1)).boundary M → M := Subtype.val
  have hf : ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) (k + 1) f :=
    (TauCeti.isSmoothEmbedding_subtypeVal_boundary (n := n) (k := k + 1) M
      (by simp)).contMDiff
  have hfinj : ∀ x, Function.Injective
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) f x) := by
    intro x
    exact (TauCeti.isImmersion_subtypeVal_boundary (n := n) (k := k + 1) M
        (by simp)).mfderiv_injective
      (by simp) x
  exact g.pullback f hf hfinj

/-- The induced boundary metric evaluates the ambient metric on boundary tangent derivatives. -/
@[simp]
theorem restrictBoundaryTangentSpace_inner
    (g : ContMDiffRiemannianMetric (𝓡∂ (n + 1)) k
      (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x))
    (x : (𝓡∂ (n + 1)).boundary M)
    (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    (g.restrictBoundaryTangentSpace).inner x v w =
      g.inner (x : M)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x v)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x w) := by
  let f : (𝓡∂ (n + 1)).boundary M → M := Subtype.val
  simpa only [restrictBoundaryTangentSpace, f] using
    g.pullback_inner f (by
      exact (TauCeti.isSmoothEmbedding_subtypeVal_boundary (n := n) (k := k + 1) M
        (by simp)).contMDiff)
      (fun y ↦ (TauCeti.isImmersion_subtypeVal_boundary (n := n) (k := k + 1) M
        (by simp)).mfderiv_injective
        (by simp) y) x v w

end Bundle.ContMDiffRiemannianMetric
