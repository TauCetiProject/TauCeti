/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Charts
public import TauCeti.Geometry.Manifold.Boundary.TangentSpace
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
import TauCeti.Geometry.Manifold.IsManifold.Basic

/-!
# The induced Riemannian metric on a manifold boundary

Let `M` be a manifold with boundary modeled on `EuclideanHalfSpace (n + 1)` (`𝓡∂ (n + 1)`), `n ≥ 0`.
Pulling an ambient Riemannian metric back along `Subtype.val : (𝓡∂ (n + 1)).boundary M → M` equips
the intrinsic boundary manifold with its induced Riemannian metric and regularity instances: a `C^k`
Riemannian metric on a `C^(k + 1)` manifold with boundary pulls back to a `C^k` Riemannian metric on
the intrinsic boundary manifold, for every `k : ℕ∞ω`.

## Main definitions

* `Bundle.RiemannianMetric.restrictBoundaryTangentSpace` and
  `Bundle.ContMDiffRiemannianMetric.restrictBoundaryTangentSpace`: induced boundary metric (bare
  and `C^k`).
* `TauCeti.halfSpaceBoundaryMetric`: induced `RiemannianBundle` instance on the boundary, with
  `C^k` (`TauCeti.halfSpaceBoundaryMetric_isContMDiff`) and continuous
  (`TauCeti.halfSpaceBoundaryMetric_continuous`) regularity instances.

## Main results

* `Bundle.ContMDiffRiemannianMetric.restrictBoundaryTangentSpace_inner`: the induced metric
  evaluates tangent vectors by applying the ambient metric to their derivatives under the boundary
  inclusion.
* `TauCeti.inner_tangentSpace_boundary`, `TauCeti.norm_tangentSpace_boundary`: boundary inner
  product and norm evaluated via `mfderiv Subtype.val`.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Proposition
  15.33.
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (induced metrics on submanifolds and boundaries).
-/

public section

noncomputable section

open Bundle Filter Set
open scoped ContDiff Manifold RealInnerProductSpace Topology

namespace Bundle.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]

/-- Pull a bundled `RiemannianMetric` on `M` back along the boundary inclusion to a bundled
`RiemannianMetric` on the intrinsic boundary manifold. -/
noncomputable def restrictBoundaryTangentSpace
    (g : RiemannianMetric (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)) :
    RiemannianMetric (fun x : (𝓡∂ (n + 1)).boundary M ↦
      TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
  g.pullback Subtype.val TauCeti.injective_mfderiv_subtypeVal_boundary

/-- The restricted boundary metric evaluates the ambient metric on boundary tangent derivatives. -/
@[simp]
theorem restrictBoundaryTangentSpace_inner
    (g : RiemannianMetric (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x))
    (x : (𝓡∂ (n + 1)).boundary M) (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    g.restrictBoundaryTangentSpace.inner x v w = g.inner (x : M)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x v)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x w) :=
  g.pullback_inner Subtype.val _ x v w

end Bundle.RiemannianMetric

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
    [IsManifold (𝓡∂ (n + 1)) (k + 1) M] :
    IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (k + 1)
      ((𝓡∂ (n + 1)).boundary M) :=
  TauCeti.isManifold_boundary (n := n) (k := k + 1) M

private abbrev boundaryOne (n : ℕ) (k : ℕ∞ω) (M : Type*) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
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
  exact (TauCeti.isSmoothEmbedding_subtypeVal_boundary (n := n) (k := k + 1) M).contMDiff

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
      TauCeti.isManifold_boundary (n := n) (k := k + 1) M
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
      TauCeti.injective_mfderiv_subtypeVal_boundary

/-- Restricting a `C^k` metric to the boundary commutes with forgetting regularity via
`toRiemannianMetric`. -/
@[simp]
theorem toRiemannianMetric_restrictBoundaryTangentSpace
    (g : let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      IsManifold.of_le (n := k + 1) (ENat.one_le_iff_ne_zero_withTop.2 (by simp))
      ContMDiffRiemannianMetric (𝓡∂ (n + 1)) k
        (EuclideanSpace ℝ (Fin (n + 1)))
        (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)) :
    let _ : IsManifold (𝓡∂ (n + 1)) 1 M :=
      IsManifold.of_le (n := k + 1) (ENat.one_le_iff_ne_zero_withTop.2 (by simp))
    let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (k + 1)
        ((𝓡∂ (n + 1)).boundary M) :=
      TauCeti.isManifold_boundary (n := n) (k := k + 1) M
    let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1
        ((𝓡∂ (n + 1)).boundary M) :=
      IsManifold.of_le (n := k + 1) (ENat.one_le_iff_ne_zero_withTop.2 (by simp))
    g.restrictBoundaryTangentSpace.toRiemannianMetric =
      g.toRiemannianMetric.restrictBoundaryTangentSpace := by
  let _ : IsManifold (𝓡∂ (n + 1)) 1 M := ambientOne n k M
  let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (k + 1)
      ((𝓡∂ (n + 1)).boundary M) := boundaryManifold n k M
  let _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1
      ((𝓡∂ (n + 1)).boundary M) := boundaryOne n k M
  dsimp only [restrictBoundaryTangentSpace, RiemannianMetric.restrictBoundaryTangentSpace]
  exact g.toRiemannianMetric_pullback Subtype.val
    (contMDiff_subtypeVal_boundary (n := n) (k := k) (M := M))
    TauCeti.injective_mfderiv_subtypeVal_boundary

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
      TauCeti.isManifold_boundary (n := n) (k := k + 1) M
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
    TauCeti.injective_mfderiv_subtypeVal_boundary x v w

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti

/-! ### The induced Riemannian metric on the boundary -/

section BoundaryMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- The induced `RiemannianBundle` on the boundary of a manifold modeled on `𝓡∂ (n + 1)`,
obtained by pulling back the ambient metric along the boundary inclusion `Subtype.val`. -/
noncomputable instance halfSpaceBoundaryMetric :
    RiemannianBundle (fun x : (𝓡∂ (n + 1)).boundary M ↦
      TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
  ⟨(RiemannianBundle.g (E := fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)).restrictBoundaryTangentSpace⟩

/-- The induced boundary inner product evaluates the ambient inner product on the images of
boundary tangent vectors under `mfderiv Subtype.val`. -/
@[simp]
theorem inner_tangentSpace_boundary (x : (𝓡∂ (n + 1)).boundary M)
    (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    inner ℝ v w = inner ℝ
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x v)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x w) :=
  RiemannianMetric.restrictBoundaryTangentSpace_inner _ x v w

/-- The induced boundary norm is the ambient norm of the image under `mfderiv Subtype.val`. -/
@[simp]
theorem norm_tangentSpace_boundary (x : (𝓡∂ (n + 1)).boundary M)
    (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    ‖v‖ = ‖mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x v‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_tangentSpace_boundary]

variable [IsManifold (𝓡∂ (n + 1)) 1 M]

/-- If `M` is `C^(k + 1)` and its ambient Riemannian metric is `C^k`, then the induced boundary
metric is `C^k`. -/
instance halfSpaceBoundaryMetric_isContMDiff {k : ℕ∞ω} [IsManifold (𝓡∂ (n + 1)) (k + 1) M]
    [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) k (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M)] :
    IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k (EuclideanSpace ℝ (Fin n))
      (fun x : (𝓡∂ (n + 1)).boundary M ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
  let g := ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := 𝓡∂ (n + 1)) (n := k)
    (F := EuclideanSpace ℝ (Fin (n + 1))) (V := fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)
  ⟨g.restrictBoundaryTangentSpace.inner, g.restrictBoundaryTangentSpace.contMDiff, fun x v w ↦ by
    rw [inner_tangentSpace_boundary,
      ContMDiffRiemannianMetric.restrictBoundaryTangentSpace_inner (n := n) (k := k) (M := M) g,
      ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner,
      RiemannianMetric.inner_riemannianBundle]⟩

/-- If the ambient Riemannian metric is continuous on a `C¹` manifold with boundary, then the
induced boundary metric is continuous. -/
instance halfSpaceBoundaryMetric_continuous
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M)] :
    IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin n))
      (fun x : (𝓡∂ (n + 1)).boundary M ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) := by
  have _ : IsManifold (𝓡∂ (n + 1)) (0 + 1) M := by simpa using ‹IsManifold (𝓡∂ (n + 1)) 1 M›
  have _ := IsContinuousRiemannianBundle.toIsContMDiffZero (IB := 𝓡∂ (n + 1))
    (F := EuclideanSpace ℝ (Fin (n + 1))) (V := fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)
  exact IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := 0)

end BoundaryMetric

end TauCeti
