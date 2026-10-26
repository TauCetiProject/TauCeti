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
  [IsManifold (𝓡∂ (n + 1)) (k + 1) M]

private abbrev ambientOne (n : ℕ) (k : ℕ∞ω) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) (k + 1) M] : IsManifold (𝓡∂ (n + 1)) 1 M :=
  IsManifold.of_le (n := k + 1) (ENat.one_le_iff_ne_zero_withTop.2 (by simp))

private abbrev boundaryManifold (n : ℕ) (k : ℕ∞ω) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) 1 M]
    [IsManifold (𝓡∂ (n + 1)) (k + 1) M] :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (k + 1)
      ((𝓡∂ (n + 1)).boundary M) :=
  TauCeti.isManifold_boundary (n := n) (k := k + 1) M (by simp)

private abbrev boundaryOne (n : ℕ) (k : ℕ∞ω) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (𝓡∂ (n + 1)) 1 M]
    [IsManifold (𝓡∂ (n + 1)) (k + 1) M] :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M) := by
  let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (k + 1)
      ((𝓡∂ (n + 1)).boundary M) := boundaryManifold n k M
  exact IsManifold.of_le (n := k + 1) (ENat.one_le_iff_ne_zero_withTop.2 (by simp))

private lemma contMDiff_subtypeVal_boundary :
    let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      ambientOne n k M
    let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (k + 1)
        ((𝓡∂ (n + 1)).boundary M) :=
      boundaryManifold n k M
    let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1
        ((𝓡∂ (n + 1)).boundary M) :=
      boundaryOne n k M
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) (k + 1)
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) := by
  let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
    ambientOne n k M
  let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (k + 1)
      ((𝓡∂ (n + 1)).boundary M) :=
    boundaryManifold n k M
  let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1
      ((𝓡∂ (n + 1)).boundary M) :=
    boundaryOne n k M
  exact (TauCeti.isSmoothEmbedding_subtypeVal_boundary (n := n) (k := k + 1) M
    (by simp)).contMDiff

private lemma injective_mfderiv_subtypeVal_boundary :
    let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      ambientOne n k M
    let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (k + 1)
        ((𝓡∂ (n + 1)).boundary M) :=
      boundaryManifold n k M
    let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1
        ((𝓡∂ (n + 1)).boundary M) :=
      boundaryOne n k M
    ∀ x, Function.Injective
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x) := by
  let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
    ambientOne n k M
  let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (k + 1)
      ((𝓡∂ (n + 1)).boundary M) :=
    boundaryManifold n k M
  let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1
      ((𝓡∂ (n + 1)).boundary M) :=
    boundaryOne n k M
  dsimp only
  intro x
  exact (TauCeti.isImmersion_subtypeVal_boundary (n := n) (k := k + 1) M
    (by simp)).mfderiv_injective (by simp) x

/-- The `C^k` Riemannian metric induced on the boundary by an ambient `C^k` metric. -/
noncomputable def restrictBoundaryTangentSpace
    (g : let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      IsManifold.of_le (n := k + 1) (ENat.one_le_iff_ne_zero_withTop.2 (by simp))
      ContMDiffRiemannianMetric (𝓡∂ (n + 1)) k
        (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)) :
    let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      IsManifold.of_le (n := k + 1) (ENat.one_le_iff_ne_zero_withTop.2 (by simp))
    let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (k + 1)
        ((𝓡∂ (n + 1)).boundary M) :=
      TauCeti.isManifold_boundary (n := n) (k := k + 1) M (by simp)
    let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1
        ((𝓡∂ (n + 1)).boundary M) :=
      IsManifold.of_le (n := k + 1) (ENat.one_le_iff_ne_zero_withTop.2 (by simp))
    ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k
      (EuclideanSpace ℝ (Fin n))
      (fun x : (𝓡∂ (n + 1)).boundary M ↦
        TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
    let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      ambientOne n k M
    let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (k + 1)
        ((𝓡∂ (n + 1)).boundary M) :=
      boundaryManifold n k M
    let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1
        ((𝓡∂ (n + 1)).boundary M) :=
      boundaryOne n k M
    g.pullback Subtype.val (contMDiff_subtypeVal_boundary (n := n) (k := k) (M := M))
      (injective_mfderiv_subtypeVal_boundary (n := n) (k := k) (M := M))

/-- The induced boundary metric evaluates the ambient metric on boundary tangent derivatives. -/
@[simp]
theorem restrictBoundaryTangentSpace_inner
    (g : let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      IsManifold.of_le (n := k + 1) (ENat.one_le_iff_ne_zero_withTop.2 (by simp))
      ContMDiffRiemannianMetric (𝓡∂ (n + 1)) k
        (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)) :
    let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      IsManifold.of_le (n := k + 1) (ENat.one_le_iff_ne_zero_withTop.2 (by simp))
    let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (k + 1)
        ((𝓡∂ (n + 1)).boundary M) :=
      TauCeti.isManifold_boundary (n := n) (k := k + 1) M (by simp)
    let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1
        ((𝓡∂ (n + 1)).boundary M) :=
      IsManifold.of_le (n := k + 1) (ENat.one_le_iff_ne_zero_withTop.2 (by simp))
    ∀ (x : (𝓡∂ (n + 1)).boundary M)
      (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x),
      (g.restrictBoundaryTangentSpace).inner x v w =
        g.inner (x : M)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
            (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x v)
          (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
            (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x w) := by
  let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
    ambientOne n k M
  let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (k + 1)
      ((𝓡∂ (n + 1)).boundary M) :=
    boundaryManifold n k M
  let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1
      ((𝓡∂ (n + 1)).boundary M) :=
    boundaryOne n k M
  dsimp only
  intro x v w
  rw [restrictBoundaryTangentSpace]
  exact g.pullback_inner Subtype.val
    (contMDiff_subtypeVal_boundary (n := n) (k := k) (M := M))
    (injective_mfderiv_subtypeVal_boundary (n := n) (k := k) (M := M)) x v w

end Bundle.ContMDiffRiemannianMetric
