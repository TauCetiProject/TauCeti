/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Boundary.Derivative
public import TauCeti.Geometry.Manifold.Boundary.Orientation
public import TauCeti.Geometry.Manifold.Riemannian.Pullback.Basic
public import TauCeti.Geometry.Manifold.Riemannian.VolumeDensity.Volume
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Geometry.Manifold.Algebra.Structures
import TauCeti.Geometry.Manifold.Boundary.TangentSpace
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.Riemannian.Immersion.Projection
import TauCeti.Geometry.Manifold.VectorBundle.Scalar

/-!
# The induced Riemannian geometry of a manifold boundary

Let `M` be a manifold with boundary modeled on `EuclideanHalfSpace (n + 1)` (`𝓡∂ (n + 1)`), `n ≥ 0`.
Pulling an ambient Riemannian metric back along `Subtype.val : (𝓡∂ (n + 1)).boundary M → M` equips
the intrinsic boundary manifold with its induced metric, volume measure, and outward unit normal.

## Main definitions

* `Bundle.RiemannianMetric.restrictBoundaryTangentSpace` and
  `Bundle.ContMDiffRiemannianMetric.restrictBoundaryTangentSpace`: induced boundary metric (bare
  and `C^k`).
* `TauCeti.halfSpaceBoundaryMetric`: induced `RiemannianBundle` instance on the boundary, with
  `C^k` (`TauCeti.halfSpaceBoundaryMetric_isContMDiff`) and continuous
  (`TauCeti.halfSpaceBoundaryMetric_continuous`) regularity instances.
* `TauCeti.halfSpaceBoundaryVolume`: Riemannian volume measure of the induced boundary metric.
* `TauCeti.halfSpaceOutwardUnitNormal`: unique outward-pointing unit normal vector field along `∂M`.

## Main results

* `TauCeti.inner_tangentSpace_boundary`, `TauCeti.norm_tangentSpace_boundary`: boundary inner
  product and norm evaluated via `mfderiv Subtype.val`.
* `TauCeti.halfSpaceBoundaryVolume_zero_eq_count`,
  `TauCeti.halfSpaceBoundaryVolume_zero_singleton`: for `n = 0`, counting measure on `∂M`.
* `TauCeti.norm_halfSpaceOutwardUnitNormal`, `TauCeti.isOutwardPointing_halfSpaceOutwardUnitNormal`,
  `TauCeti.inner_halfSpaceOutwardUnitNormal_mfderiv_subtypeVal`: defining properties of `N`.
* `TauCeti.eq_halfSpaceOutwardUnitNormal_of_norm_eq_one`: uniqueness of the outward unit normal.
* `TauCeti.contMDiff_halfSpaceOutwardUnitNormal`, `TauCeti.continuous_halfSpaceOutwardUnitNormal`,
  `TauCeti.exists_halfSpaceOutwardUnitNormal`: `C^k` and continuous regularity along the boundary.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Proposition
  15.33 and Chapter 16 (induced boundary metrics, outward unit normal, and boundary volume).
* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (induced metrics and the Riemannian density on submanifolds and boundaries).
-/

public section

noncomputable section

open Bundle Filter MeasureTheory Set
open scoped ContDiff Manifold RealInnerProductSpace Topology

namespace Bundle.RiemannianMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 1 M]

/-- Pull a bundled `RiemannianMetric` on `M` back along the boundary inclusion to a bundled
`RiemannianMetric` on the intrinsic boundary manifold. -/
noncomputable def restrictBoundaryTangentSpace
    (g : RiemannianMetric (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)) :
    RiemannianMetric (fun x : (𝓡∂ (n + 1)).boundary M ↦
      TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
  g.pullback Subtype.val fun x ↦
    let _ := TauCeti.isManifold_boundary (n := n) (k := 1) M
    (TauCeti.isImmersion_subtypeVal_boundary (n := n) (k := 1) M).mfderiv_injective one_ne_zero x

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
  exact (TauCeti.isImmersion_subtypeVal_boundary (n := n) (k := k + 1) M).mfderiv_injective
    (by simp) x

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
    (injective_mfderiv_subtypeVal_boundary (n := n) (k := k) (M := M)) x v w

end Bundle.ContMDiffRiemannianMetric

namespace TauCeti

/-! ### The induced Riemannian metric and volume measure on the boundary -/

section BoundaryMetric

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 1 M]
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
      ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle_inner]; rfl⟩

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

variable [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
    (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- The **Riemannian boundary volume measure** on `(𝓡∂ (n + 1)).boundary M`, i.e.
`TauCeti.riemannianVolume` of `TauCeti.halfSpaceBoundaryMetric` (`LindelofSpace` descends). -/
noncomputable def halfSpaceBoundaryVolume : Measure ((𝓡∂ (n + 1)).boundary M) :=
  let _ := isManifold_boundary (n := n) (k := 1) M
  riemannianVolume 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((𝓡∂ (n + 1)).boundary M)

/-- Unfold `TauCeti.halfSpaceBoundaryVolume` as `TauCeti.riemannianVolume` on the boundary. -/
theorem halfSpaceBoundaryVolume_eq_riemannianVolume
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M)] :
    halfSpaceBoundaryVolume (n := n) (M := M) =
      riemannianVolume 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((𝓡∂ (n + 1)).boundary M) := by rfl

/-- The Riemannian boundary volume measure is locally finite. -/
instance isLocallyFiniteMeasure_halfSpaceBoundaryVolume :
    IsLocallyFiniteMeasure (halfSpaceBoundaryVolume (n := n) (M := M)) := by
  let _ := isManifold_boundary (n := n) (k := 1) M
  rw [halfSpaceBoundaryVolume_eq_riemannianVolume]; infer_instance

end BoundaryMetric

/-! ### Zero-dimensional boundary volume (`n = 0`) -/

section ZeroDimBoundary

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanHalfSpace 1) M]
  [IsManifold (𝓡∂ 1) 1 M] [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ 1) x)]
  [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 1)) (fun x : M ↦ TangentSpace (𝓡∂ 1) x)]

/-- For `n = 0`, the induced boundary measure is counting measure on the boundary. -/
theorem halfSpaceBoundaryVolume_zero_eq_count :
    halfSpaceBoundaryVolume (n := 0) (M := M) = Measure.count := by
  let _ := isManifold_boundary (n := 0) (k := 1) M
  exact riemannianVolume_eq_count_of_subsingleton

/-- Each boundary point of a one-dimensional Riemannian manifold with boundary has measure `1`. -/
@[simp]
theorem halfSpaceBoundaryVolume_zero_singleton (x : (𝓡∂ 1).boundary M) :
    halfSpaceBoundaryVolume (n := 0) (M := M) {x} = 1 := by
  have _ : T1Space ((𝓡∂ 1).boundary M) := ChartedSpace.t1Space (EuclideanSpace ℝ (Fin 0)) _
  rw [halfSpaceBoundaryVolume_zero_eq_count, Measure.count_singleton' (measurableSet_singleton x)]

end ZeroDimBoundary

/-! ### The outward-pointing unit normal along the boundary -/

section OutwardUnitNormal

private abbrev bdryI (n : ℕ) := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
private abbrev Espace (m : ℕ) := EuclideanSpace ℝ (Fin m)
private abbrev ambTriv (n : ℕ) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 1 M] (α : M) :=
  trivializationAt (Espace (n + 1)) (TangentSpace (𝓡∂ (n + 1))) α

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 1 M]
  [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- Orthogonal projection onto the normal complement of `T_x(∂M)` preserves outwardness. -/
theorem IsOutwardPointing.starProjection_orthogonal_range_mfderiv_subtypeVal
    {x : (𝓡∂ (n + 1)).boundary M} {v : TangentSpace (𝓡∂ (n + 1)) (x : M)}
    (hv : IsOutwardPointing (x : M) v) :
    IsOutwardPointing (x : M) ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x).rangeᗮ.starProjection v) := by
  set dι := mfderiv (bdryI n) (𝓡∂ (n + 1)) (Subtype.val : _ → M) x
  obtain ⟨w, hw⟩ := dι.range.starProjection_apply_mem v
  have hsub : dι.rangeᗮ.starProjection v = v + dι (-w) := by
    rw [Submodule.starProjection_orthogonal_val, ← hw, map_neg, sub_eq_add_neg]; rfl
  rwa [hsub, isOutwardPointing_add_mfderiv_subtypeVal_boundary]

/-- Unnormalized local outward normal near a boundary chart center `α`. -/
private noncomputable def localOutwardNormalAux (α y : (𝓡∂ (n + 1)).boundary M) :
    TangentSpace (𝓡∂ (n + 1)) (y : M) :=
  (mfderiv (bdryI n) (𝓡∂ (n + 1)) (Subtype.val : _ → M) y).rangeᗮ.starProjection
    ((ambTriv n (α : M)).symmL ℝ (y : M) (-EuclideanSpace.single 0 1))

private theorem isOutwardPointing_localOutwardNormalAux {α y : (𝓡∂ (n + 1)).boundary M}
    (hy : (y : M) ∈ (ambTriv n (α : M)).baseSet) :
    IsOutwardPointing (y : M) (localOutwardNormalAux α y) :=
  IsOutwardPointing.starProjection_orthogonal_range_mfderiv_subtypeVal
    (isOutwardPointing_trivializationAt_symmL_neg_single_zero hy)

private theorem inner_localOutwardNormalAux_mfderiv_subtypeVal (α y : (𝓡∂ (n + 1)).boundary M)
    (w : TangentSpace (bdryI n) y) :
    inner ℝ (localOutwardNormalAux α y)
      (mfderiv (bdryI n) (𝓡∂ (n + 1)) (Subtype.val : _ → M) y w) = 0 := by
  rw [localOutwardNormalAux, Submodule.starProjection_orthogonal_val]
  exact (mfderiv (bdryI n) (𝓡∂ (n + 1)) (Subtype.val : _ → M) y).range.starProjection_inner_eq_zero
    _ _ (LinearMap.mem_range_self _ w)

/-- The **outward-pointing unit normal** along the boundary of a Riemannian manifold modeled on
`𝓡∂ (n + 1)`: at each `x ∈ ∂M`, the unique ambient tangent vector of norm `1` that points outward
(`TauCeti.IsOutwardPointing`) and is orthogonal to `mfderiv Subtype.val x`. -/
noncomputable def halfSpaceOutwardUnitNormal (x : (𝓡∂ (n + 1)).boundary M) :
    TangentSpace (𝓡∂ (n + 1)) (x : M) :=
  ‖localOutwardNormalAux x x‖⁻¹ • localOutwardNormalAux x x

/-- The outward unit normal has norm `1` at every boundary point. -/
@[simp]
theorem norm_halfSpaceOutwardUnitNormal (x : (𝓡∂ (n + 1)).boundary M) :
    ‖halfSpaceOutwardUnitNormal x‖ = 1 := by
  have hne := (isOutwardPointing_localOutwardNormalAux
    (FiberBundle.mem_baseSet_trivializationAt' (x : M))).ne_zero
  rw [halfSpaceOutwardUnitNormal, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hne)]

/-- The outward unit normal points outward at every boundary point. -/
theorem isOutwardPointing_halfSpaceOutwardUnitNormal (x : (𝓡∂ (n + 1)).boundary M) :
    IsOutwardPointing (x : M) (halfSpaceOutwardUnitNormal x) :=
  have hout := isOutwardPointing_localOutwardNormalAux (FiberBundle.mem_baseSet_trivializationAt' _)
  hout.smul_pos (inv_pos.2 (norm_pos_iff.2 hout.ne_zero))

/-- The outward unit normal is orthogonal to every boundary tangent vector. -/
@[simp]
theorem inner_halfSpaceOutwardUnitNormal_mfderiv_subtypeVal (x : (𝓡∂ (n + 1)).boundary M)
    (w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    inner ℝ (halfSpaceOutwardUnitNormal x) (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x w) = 0 := by
  rw [halfSpaceOutwardUnitNormal, real_inner_smul_left,
    inner_localOutwardNormalAux_mfderiv_subtypeVal, mul_zero]

/-- Symmetric form of `TauCeti.inner_halfSpaceOutwardUnitNormal_mfderiv_subtypeVal`. -/
@[simp]
theorem inner_mfderiv_subtypeVal_halfSpaceOutwardUnitNormal (x : (𝓡∂ (n + 1)).boundary M)
    (w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    inner ℝ (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x w) (halfSpaceOutwardUnitNormal x) = 0 := by
  rw [real_inner_comm, inner_halfSpaceOutwardUnitNormal_mfderiv_subtypeVal]

/-- **Uniqueness of the outward unit normal.** Any ambient tangent vector at `x ∈ ∂M` of norm `1`
pointing outward and orthogonal to `mfderiv Subtype.val x` equals `halfSpaceOutwardUnitNormal x`. -/
theorem eq_halfSpaceOutwardUnitNormal_of_norm_eq_one {x : (𝓡∂ (n + 1)).boundary M}
    {v : TangentSpace (𝓡∂ (n + 1)) (x : M)} (hnorm : ‖v‖ = 1) (hout : IsOutwardPointing (x : M) v)
    (horth : ∀ w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x,
      inner ℝ v (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x w) = 0) :
    v = halfSpaceOutwardUnitNormal x := by
  let _ := isManifold_boundary (n := n) (k := 1) M
  set dι := mfderiv (bdryI n) (𝓡∂ (n + 1)) (Subtype.val : _ → M) x
  set N := halfSpaceOutwardUnitNormal x
  have hvW : v ∈ dι.rangeᗮ := (Submodule.mem_orthogonal' _ _).2 fun _ ⟨w, hw⟩ ↦ hw ▸ horth w
  have hNW : N ∈ dι.rangeᗮ := (Submodule.mem_orthogonal' _ _).2 fun _ ⟨w, hw⟩ ↦
    hw ▸ inner_halfSpaceOutwardUnitNormal_mfderiv_subtypeVal x w
  have hdimOrth : Module.finrank ℝ dι.rangeᗮ = 1 := by
    have hsum := dι.range.finrank_add_finrank_orthogonal
    rw [LinearMap.finrank_range_of_inj
        ((isImmersion_subtypeVal_boundary (n := n) (k := 1) M).mfderiv_injective one_ne_zero x),
      TauCeti.finrank_tangentSpace, TauCeti.finrank_tangentSpace] at hsum
    simp only [finrank_euclideanSpace_fin] at hsum; omega
  have hNne : (⟨N, hNW⟩ : dι.rangeᗮ) ≠ 0 := fun h0 ↦ by
    have h := congrArg (fun u : dι.rangeᗮ ↦ ‖u.val‖) h0; simp [N] at h
  have htop := Submodule.eq_top_of_finrank_eq ((finrank_span_singleton hNne).trans hdimOrth.symm)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
    (htop.symm ▸ Submodule.mem_top (x := (⟨v, hvW⟩ : dι.rangeᗮ)))
  have hvc : v = c • N := (congrArg Subtype.val hc).symm
  have habs : |c| = 1 := by
    simpa [N, hvc, norm_smul, norm_halfSpaceOutwardUnitNormal, Real.norm_eq_abs] using hnorm
  rcases (abs_eq (by positivity : (0 : ℝ) ≤ 1)).1 habs with rfl | rfl
  · simp [hvc]
  · exact absurd (by rw [hvc, neg_one_smul, add_neg_cancel])
      ((isOutwardPointing_halfSpaceOutwardUnitNormal x).add hout).ne_zero

private theorem contMDiffAt_localOutwardNormalAux {k : ℕ∞ω} [IsManifold (𝓡∂ (n + 1)) (k + 1) M]
    [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) k (Espace (n + 1))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)] (α : (𝓡∂ (n + 1)).boundary M) :
    ContMDiffAt (bdryI n) ((𝓡∂ (n + 1)).prod 𝓘(ℝ, Espace (n + 1))) k
      (fun y : (𝓡∂ (n + 1)).boundary M ↦ TotalSpace.mk' (Espace (n + 1))
        (E := fun z : M ↦ TangentSpace (𝓡∂ (n + 1)) z) (y : M) (localOutwardNormalAux α y)) α := by
  have _ := isManifold_boundary (n := n) (k := k + 1) M
  have _ : IsManifold (bdryI n) 1 ((𝓡∂ (n + 1)).boundary M) :=
    IsManifold.of_le (n := k + 1) (ENat.one_le_iff_ne_zero_withTop.2 (by simp))
  have hι := (isSmoothEmbedding_subtypeVal_boundary (n := n) (k := k + 1) M).contMDiff
  have hinj := (isImmersion_subtypeVal_boundary (n := n) (k := k + 1) M).mfderiv_injective
    (by simp) α
  let e := ambTriv n (α : M); let v₀ : Espace (n + 1) := -EuclideanSpace.single 0 1
  have hW : ContMDiffAt (𝓡∂ (n + 1)) ((𝓡∂ (n + 1)).prod 𝓘(ℝ, Espace (n + 1))) k
      (fun z : M ↦ TotalSpace.mk' (Espace (n + 1))
        (E := fun z : M ↦ TangentSpace (𝓡∂ (n + 1)) z) z (e.symmL ℝ z v₀)) (α : M) := by
    rw [contMDiffAt_section_iff]
    refine (contMDiffAt_const (c := v₀)).congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _)] with z hz
    exact (congrArg (fun v ↦ (e ⟨z, v⟩).2) (e.symmL_apply hz v₀)).trans
      (congrArg Prod.snd (e.apply_mk_symm hz v₀))
  exact (hι α).starProjection_orthogonal_range_mfderiv_apply le_rfl hinj
    (hW.comp α ((hι α).of_le le_self_add))

/-- **Regularity of the outward unit normal.** On a `C^(k + 1)` manifold with boundary carrying a
`C^k` Riemannian metric, the outward unit normal is a `C^k` map into the ambient tangent bundle. -/
theorem contMDiff_halfSpaceOutwardUnitNormal {k : ℕ∞ω} [IsManifold (𝓡∂ (n + 1)) (k + 1) M]
    [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) k (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)] :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)).tangent k
      (fun x : (𝓡∂ (n + 1)).boundary M ↦
        (⟨(x : M), halfSpaceOutwardUnitNormal x⟩ : TangentBundle (𝓡∂ (n + 1)) M)) := by
  intro α
  have hU := contMDiffAt_localOutwardNormalAux (k := k) α
  have hα_ne := (isOutwardPointing_localOutwardNormalAux
    (FiberBundle.mem_baseSet_trivializationAt' (α : M))).ne_zero
  have hnorm : ContMDiffAt (bdryI n) 𝓘(ℝ) k (fun y ↦ ‖localOutwardNormalAux α y‖) α := by
    simpa only [Function.comp_def, ← norm_eq_sqrt_real_inner] using
      (Real.contDiffAt_sqrt (inner_self_ne_zero.mpr hα_ne)).contMDiffAt.comp α
        (ContMDiffAt.inner_bundle hU hU)
  refine ((hnorm.inv₀ (norm_ne_zero_iff.mpr hα_ne)).smul_totalSpace hU).congr_of_eventuallyEq ?_
  filter_upwards [continuous_subtypeVal.continuousAt.preimage_mem_nhds
    ((ambTriv n (α : M)).open_baseSet.mem_nhds (FiberBundle.mem_baseSet_trivializationAt' _))] with
    y hy
  refine congrArg (fun v : TangentSpace (𝓡∂ (n + 1)) (y : M) ↦
    (⟨(y : M), v⟩ : TangentBundle (𝓡∂ (n + 1)) M)) (Eq.symm ?_)
  have hy_out := isOutwardPointing_localOutwardNormalAux hy
  refine eq_halfSpaceOutwardUnitNormal_of_norm_eq_one
    (by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hy_out.ne_zero)])
    (hy_out.smul_pos (inv_pos.2 (norm_pos_iff.2 hy_out.ne_zero))) fun w ↦ by
      rw [real_inner_smul_left, inner_localOutwardNormalAux_mfderiv_subtypeVal, mul_zero]

/-- On a `C¹` manifold with continuous metric, the outward unit normal is continuous. -/
theorem continuous_halfSpaceOutwardUnitNormal
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)] :
    Continuous (fun x : (𝓡∂ (n + 1)).boundary M ↦
      (⟨(x : M), halfSpaceOutwardUnitNormal x⟩ : TangentBundle (𝓡∂ (n + 1)) M)) := by
  have _ : IsManifold (𝓡∂ (n + 1)) (0 + 1) M := by simpa using ‹IsManifold (𝓡∂ (n + 1)) 1 M›
  have _ := IsContinuousRiemannianBundle.toIsContMDiffZero (IB := 𝓡∂ (n + 1))
    (F := EuclideanSpace ℝ (Fin (n + 1))) (V := fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)
  exact (contMDiff_halfSpaceOutwardUnitNormal (n := n) (M := M) (k := 0)).continuous

/-- **Existence of a smooth outward unit normal** along the boundary of a smooth Riemannian
manifold with boundary: norm `1`, outward-pointing, and orthogonal to `T(∂M)`. -/
theorem exists_halfSpaceOutwardUnitNormal [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) ∞ (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)] :
    ∃ N : (x : (𝓡∂ (n + 1)).boundary M) → TangentSpace (𝓡∂ (n + 1)) (x : M),
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)).tangent ∞
        (fun x : (𝓡∂ (n + 1)).boundary M ↦ (⟨(x : M), N x⟩ : TangentBundle (𝓡∂ (n + 1)) M)) ∧
      ∀ x, ‖N x‖ = 1 ∧ IsOutwardPointing (x : M) (N x) ∧
        ∀ w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x,
          inner ℝ (N x)
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) Subtype.val x w) = 0 := by
  have _ : IsManifold (𝓡∂ (n + 1)) (∞ + 1) M := by simpa using ‹IsManifold (𝓡∂ (n + 1)) ∞ M›
  exact ⟨halfSpaceOutwardUnitNormal, contMDiff_halfSpaceOutwardUnitNormal (k := ∞), fun x ↦
    ⟨norm_halfSpaceOutwardUnitNormal x, isOutwardPointing_halfSpaceOutwardUnitNormal x,
      inner_halfSpaceOutwardUnitNormal_mfderiv_subtypeVal x⟩⟩

end OutwardUnitNormal

end TauCeti
