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
import Mathlib.MeasureTheory.Measure.Dirac.Basic
import TauCeti.Geometry.Manifold.IsManifold.Basic
import TauCeti.Geometry.Manifold.Riemannian.Immersion.Projection
import TauCeti.Geometry.Manifold.VectorBundle.Scalar
import TauCeti.MeasureTheory.Measure.Haar.OfBasis

/-!
# The induced Riemannian geometry of a manifold boundary

Let `M` be a manifold with boundary modeled on `EuclideanHalfSpace (n + 1)` (`𝓡∂ (n + 1)`), for
any `n ≥ 0`. Pulling an ambient Riemannian metric back along the boundary inclusion
`Subtype.val : (𝓡∂ (n + 1)).boundary M → M` equips the intrinsic boundary manifold with its
induced Riemannian metric, induced Riemannian volume measure, and unique outward-pointing unit
normal field.

## Main definitions

* `Bundle.RiemannianMetric.restrictBoundaryTangentSpace` and
  `Bundle.ContMDiffRiemannianMetric.restrictBoundaryTangentSpace`: the induced Riemannian metric
  on the boundary, for bundled bare and `C^k` metrics.
* `TauCeti.halfSpaceBoundaryMetric`: the induced `RiemannianBundle` instance on the boundary from
  an ambient `RiemannianBundle`, with its `C^k` (`TauCeti.halfSpaceBoundaryMetric_isContMDiff`)
  and continuous (`TauCeti.halfSpaceBoundaryMetric_continuous`) regularity instances.
* `TauCeti.halfSpaceBoundaryVolume`: the Riemannian volume measure of the induced boundary metric.
* `TauCeti.halfSpaceOutwardUnitNormal`: the unique outward-pointing unit normal vector field along
  the boundary.

## Main results

* `TauCeti.inner_tangentSpace_boundary` and `TauCeti.norm_tangentSpace_boundary`: the boundary
  inner product and norm evaluate the ambient metric on images under `mfderiv Subtype.val`.
* `TauCeti.halfSpaceBoundaryVolume_zero_eq_count` and
  `TauCeti.halfSpaceBoundaryVolume_zero_singleton`: for a one-dimensional manifold with boundary
  (`n = 0`), the induced boundary measure is counting measure, giving each boundary point mass `1`.
* `TauCeti.norm_halfSpaceOutwardUnitNormal`, `TauCeti.isOutwardPointing_halfSpaceOutwardUnitNormal`,
  `TauCeti.inner_halfSpaceOutwardUnitNormal_mfderiv_subtypeVal`: the three defining properties of
  the outward unit normal.
* `TauCeti.eq_halfSpaceOutwardUnitNormal_of_norm_eq_one`: any boundary vector of norm `1` that
  points outward and is orthogonal to the boundary tangent space equals
  `TauCeti.halfSpaceOutwardUnitNormal`.
* `TauCeti.contMDiff_halfSpaceOutwardUnitNormal`, `TauCeti.continuous_halfSpaceOutwardUnitNormal`,
  and `TauCeti.exists_halfSpaceOutwardUnitNormal`: `C^k` and continuous regularity of the outward
  unit normal along the boundary.

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
      TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) where
  inner x :=
    let dι := mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x
    (ContinuousLinearMap.precomp ℝ dι).comp ((g.inner (x : M)).comp dι)
  symm x _ _ := by
    simpa only [ContinuousLinearMap.precomp_apply, ContinuousLinearMap.comp_apply] using
      g.symm (x : M) _ _
  pos x _ hv := by
    let _ := TauCeti.isManifold_boundary (n := n) (k := 1) M one_ne_zero
    have hinj := (TauCeti.isImmersion_subtypeVal_boundary (n := n) (k := 1) M
      one_ne_zero).mfderiv_injective one_ne_zero x
    exact g.pos (x : M) _ ((map_ne_zero_iff _ hinj).2 hv)
  continuousAt x :=
    let dι := mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
      (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x
    (g.continuousAt (x : M)).comp_of_eq dι.continuous.continuousAt (map_zero dι)
  isVonNBounded x := by
    let _ := TauCeti.isManifold_boundary (n := n) (k := 1) M one_ne_zero
    let _ : NormedAddCommGroup (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
      inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin n)))
    let _ : NormedSpace ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
      inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin n)))
    let _ : NormedAddCommGroup (TangentSpace (𝓡∂ (n + 1)) (x : M)) :=
      inferInstanceAs (NormedAddCommGroup (EuclideanSpace ℝ (Fin (n + 1))))
    let _ : NormedSpace ℝ (TangentSpace (𝓡∂ (n + 1)) (x : M)) :=
      inferInstanceAs (NormedSpace ℝ (EuclideanSpace ℝ (Fin (n + 1))))
    have hinj := (TauCeti.isImmersion_subtypeVal_boundary (n := n) (k := 1) M
      one_ne_zero).mfderiv_injective one_ne_zero x
    let A : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x →L[ℝ]
        TangentSpace (𝓡∂ (n + 1)) (x : M) :=
      mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) Subtype.val x
    obtain ⟨_, -, hK⟩ := A.toLinearMap.exists_antilipschitzWith (LinearMap.ker_eq_bot.2 hinj)
    exact NormedSpace.isVonNBounded_of_isBounded ℝ
      ((hK.isBounded_preimage
        ((NormedSpace.isVonNBounded_iff ℝ).mp (g.isVonNBounded (x : M)))).subset fun _ hv ↦ hv)

/-- The restricted boundary metric evaluates the ambient metric on boundary tangent derivatives. -/
@[simp]
theorem restrictBoundaryTangentSpace_inner
    (g : RiemannianMetric (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x))
    (x : (𝓡∂ (n + 1)).boundary M)
    (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    g.restrictBoundaryTangentSpace.inner x v w =
      g.inner (x : M)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x v)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x w) :=
  (rfl)

end Bundle.RiemannianMetric

namespace Bundle.ContMDiffRiemannianMetric

variable {n : ℕ} {k : ℕ∞ω} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
  [IsManifold (𝓡∂ (n + 1)) 1 M] [IsManifold (𝓡∂ (n + 1)) (k + 1) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M)]

/-- The `C^k` Riemannian metric induced on the boundary by an ambient `C^k` metric. -/
noncomputable def restrictBoundaryTangentSpace
    (g : ContMDiffRiemannianMetric (𝓡∂ (n + 1)) k
      (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)) :
    ContMDiffRiemannianMetric 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k
      (EuclideanSpace ℝ (Fin n))
      (fun x : (𝓡∂ (n + 1)).boundary M ↦
        TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
  g.pullback Subtype.val
    (TauCeti.isSmoothEmbedding_subtypeVal_boundary (n := n) (k := k + 1) M (by simp)).contMDiff
    fun x ↦ (TauCeti.isImmersion_subtypeVal_boundary (n := n) (k := 1) M
      one_ne_zero).mfderiv_injective one_ne_zero x

/-- The induced boundary metric evaluates the ambient metric on boundary tangent derivatives. -/
@[simp]
theorem restrictBoundaryTangentSpace_inner
    (g : ContMDiffRiemannianMetric (𝓡∂ (n + 1)) k
      (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x))
    (x : (𝓡∂ (n + 1)).boundary M)
    (v w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    g.restrictBoundaryTangentSpace.inner x v w =
      g.inner (x : M)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x v)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x w) :=
  g.pullback_inner Subtype.val _ _ x v w

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
    inner ℝ v w =
      inner ℝ
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x v)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x w) :=
  (rfl)

/-- The induced boundary norm is the ambient norm of the image under `mfderiv Subtype.val`. -/
@[simp]
theorem norm_tangentSpace_boundary (x : (𝓡∂ (n + 1)).boundary M)
    (v : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    ‖v‖ =
      ‖mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x v‖ := by
  rw [norm_eq_sqrt_real_inner, norm_eq_sqrt_real_inner, inner_tangentSpace_boundary]

/-- If `M` is `C^(k + 1)` and its ambient Riemannian metric is `C^k`, then the induced boundary
metric is `C^k`. -/
instance halfSpaceBoundaryMetric_isContMDiff {k : ℕ∞ω}
    [IsManifold (𝓡∂ (n + 1)) (k + 1) M]
    [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) k (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M)] :
    IsContMDiffRiemannianBundle 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) k (EuclideanSpace ℝ (Fin n))
      (fun x : (𝓡∂ (n + 1)).boundary M ↦ TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
  let g := ContMDiffRiemannianMetric.ofIsContMDiffRiemannianBundle (IB := 𝓡∂ (n + 1)) (n := k)
    (F := EuclideanSpace ℝ (Fin (n + 1))) (V := fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)
  let gb := g.restrictBoundaryTangentSpace
  ⟨gb.inner, gb.contMDiff, fun x v w ↦ by
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
  have _ : IsManifold (𝓡∂ (n + 1)) (0 + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡∂ (n + 1)) 1 M)
  have _ : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 0 (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  exact IsContMDiffRiemannianBundle.toIsContinuousRiemannianBundle
    (IB := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := 0)

/-- The **Riemannian boundary volume measure** on `(𝓡∂ (n + 1)).boundary M`: the Riemannian volume
`TauCeti.riemannianVolume` of the induced boundary metric `TauCeti.halfSpaceBoundaryMetric`. Since
the boundary is closed in `M`, `LindelofSpace` descends from `M` to the boundary automatically. -/
noncomputable def halfSpaceBoundaryVolume [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)] :
    Measure ((𝓡∂ (n + 1)).boundary M) :=
  let _ := isManifold_boundary (n := n) (k := 1) M one_ne_zero
  let _ : LindelofSpace ((𝓡∂ (n + 1)).boundary M) :=
    ((𝓡∂ (n + 1)).isClosed_boundary one_ne_zero).isClosedEmbedding_subtypeVal.LindelofSpace
  riemannianVolume 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((𝓡∂ (n + 1)).boundary M)

/-- Unfold `TauCeti.halfSpaceBoundaryVolume` as `TauCeti.riemannianVolume` on the boundary when its
manifold and Lindelöf instances are in scope. -/
theorem halfSpaceBoundaryVolume_eq_riemannianVolume
    [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M)]
    [LindelofSpace ((𝓡∂ (n + 1)).boundary M)] :
    halfSpaceBoundaryVolume (n := n) (M := M) =
      riemannianVolume 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ((𝓡∂ (n + 1)).boundary M) :=
  (rfl)

/-- The Riemannian boundary volume measure is locally finite: every boundary point has a
neighbourhood in the boundary of finite boundary measure. -/
instance isLocallyFiniteMeasure_halfSpaceBoundaryVolume
    [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)] :
    IsLocallyFiniteMeasure (halfSpaceBoundaryVolume (n := n) (M := M)) := by
  let _ := isManifold_boundary (n := n) (k := 1) M one_ne_zero
  let _ : LindelofSpace ((𝓡∂ (n + 1)).boundary M) :=
    ((𝓡∂ (n + 1)).isClosed_boundary one_ne_zero).isClosedEmbedding_subtypeVal.LindelofSpace
  rw [halfSpaceBoundaryVolume_eq_riemannianVolume]
  infer_instance

end BoundaryMetric

/-! ### Zero-dimensional boundary volume (`n = 0`) -/

section ZeroDimBoundary

/-- On a zero-dimensional Riemannian manifold, the Riemannian volume measure is counting measure,
giving mass `1` to every point. -/
private theorem riemannianVolume_eq_count_of_subsingleton
    {E B : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Subsingleton E]
    [TopologicalSpace B] [ChartedSpace E B] [IsManifold 𝓘(ℝ, E) 1 B]
    [MeasurableSpace B] [BorelSpace B] [LindelofSpace B]
    [RiemannianBundle (fun x : B ↦ TangentSpace 𝓘(ℝ, E) x)]
    [IsContinuousRiemannianBundle E (fun x : B ↦ TangentSpace 𝓘(ℝ, E) x)] :
    riemannianVolume 𝓘(ℝ, E) B = Measure.count := by
  let _ : MeasurableSpace E := borel E
  have _ : BorelSpace E := ⟨rfl⟩
  have hsource (x : B) : (chartAt E x).source = {x} := Set.ext fun y ↦
    ⟨fun hy ↦ (chartAt E x).injOn hy (mem_chart_source E x) (Subsingleton.elim _ _),
      fun hy ↦ hy.symm ▸ mem_chart_source E x⟩
  have _ : DiscreteTopology B := discreteTopology_iff_isOpen_singleton.2 fun x ↦
    hsource x ▸ (chartAt E x).open_source
  have _ : Countable B := by
    obtain ⟨t, ht, hcover⟩ := LindelofSpace.elim_nhds_subcover (fun x : B ↦ ({x} : Set B))
      fun x ↦ (isOpen_discrete {x}).mem_nhds rfl
    exact countable_univ_iff.1 (hcover ▸ ht.biUnion fun x _ ↦ countable_singleton x)
  refine Measure.ext_of_singleton fun x ↦ ?_
  have _ : IsEmpty (Fin (Module.finrank ℝ E)) :=
    Module.finrank_zero_of_subsingleton (R := ℝ) (M := E) ▸ inferInstanceAs (IsEmpty (Fin 0))
  have hx_meas : MeasurableSet ({x} : Set B) := (isOpen_discrete {x}).measurableSet
  rw [Measure.count_singleton' hx_meas, riemannianVolume_apply_of_subset (hsource x).symm.subset,
    chartRiemannianVolume_apply x hx_meas, Module.Basis.addHaar_eq_dirac, extChartAt_source,
    hsource x, inter_self, image_singleton, Subsingleton.elim (extChartAt 𝓘(ℝ, E) x x) 0,
    setLIntegral_dirac]
  simp [chartVolumeDensity_def, Matrix.det_isEmpty]

/-- For a one-dimensional manifold with boundary (`n = 0`), the induced boundary measure is
counting measure on the zero-dimensional boundary. -/
theorem halfSpaceBoundaryVolume_zero_eq_count {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) 1 M]
    [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ 1) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 1))
      (fun x : M ↦ TangentSpace (𝓡∂ 1) x)] :
    halfSpaceBoundaryVolume (n := 0) (M := M) = Measure.count := by
  let _ := isManifold_boundary (n := 0) (k := 1) M one_ne_zero
  let _ : LindelofSpace ((𝓡∂ 1).boundary M) :=
    ((𝓡∂ 1).isClosed_boundary one_ne_zero).isClosedEmbedding_subtypeVal.LindelofSpace
  exact riemannianVolume_eq_count_of_subsingleton

/-- Each boundary point of a one-dimensional Riemannian manifold with boundary has boundary
measure `1`. -/
@[simp]
theorem halfSpaceBoundaryVolume_zero_singleton {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace 1) M] [IsManifold (𝓡∂ 1) 1 M]
    [MeasurableSpace M] [BorelSpace M] [LindelofSpace M]
    [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ 1) x)]
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin 1))
      (fun x : M ↦ TangentSpace (𝓡∂ 1) x)]
    (x : (𝓡∂ 1).boundary M) :
    halfSpaceBoundaryVolume (n := 0) (M := M) {x} = 1 := by
  have _ : T1Space ((𝓡∂ 1).boundary M) := ChartedSpace.t1Space (EuclideanSpace ℝ (Fin 0)) _
  rw [halfSpaceBoundaryVolume_zero_eq_count, Measure.count_singleton' (measurableSet_singleton x)]

end ZeroDimBoundary

/-! ### The outward-pointing unit normal along the boundary -/

section OutwardUnitNormal

variable {n : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanHalfSpace (n + 1)) M] [IsManifold (𝓡∂ (n + 1)) 1 M]

/-- Adding a tangent vector pushed forward from the boundary does not change whether an ambient
tangent vector at a boundary point points outward, since boundary tangent vectors have zero
constrained coordinate. -/
theorem isOutwardPointing_add_mfderiv_subtypeVal_boundary (x : (𝓡∂ (n + 1)).boundary M)
    (v : TangentSpace (𝓡∂ (n + 1)) (x : M))
    (w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    IsOutwardPointing (x : M)
      (v + mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x w) ↔
      IsOutwardPointing (x : M) v := by
  let _ := isManifold_boundary (n := n) (k := 1) M one_ne_zero
  rw [isOutwardPointing_iff, isOutwardPointing_iff, and_iff_right x.property,
    and_iff_right x.property, map_add, map_add, PiLp.add_apply]
  have hz : (NormedSpace.fromTangentSpace (𝕜 := ℝ) (extChartAt (𝓡∂ (n + 1)) (x : M) (x : M))
      (mfderiv (𝓡∂ (n + 1)) 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))
        (extChartAt (𝓡∂ (n + 1)) (x : M)) (x : M)
        (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
          (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x w))) 0 = 0 := by
    rw [mfderiv_subtypeVal_boundary, mfderiv_extChartAt_self]
    exact euclideanHalfSpaceBoundaryParam_apply_zero w
  rw [hz, add_zero]

/-- In any tangent-bundle trivialization at `α` containing a boundary point `y`, the image of
`-e₀` under `symmL` points outward at `y`. -/
theorem isOutwardPointing_trivializationAt_symmL_neg_single_zero
    {α : M} {y : (𝓡∂ (n + 1)).boundary M}
    (hy : (y : M) ∈ (trivializationAt (EuclideanSpace ℝ (Fin (n + 1)))
      (TangentSpace (𝓡∂ (n + 1))) α).baseSet) :
    IsOutwardPointing (y : M)
      ((trivializationAt (EuclideanSpace ℝ (Fin (n + 1)))
        (TangentSpace (𝓡∂ (n + 1))) α).symmL ℝ (y : M) (-EuclideanSpace.single 0 1)) := by
  let e := trivializationAt (EuclideanSpace ℝ (Fin (n + 1))) (TangentSpace (𝓡∂ (n + 1))) α
  let v₀ : EuclideanSpace ℝ (Fin (n + 1)) := -EuclideanSpace.single 0 1
  have hyc : (y : M) ∈ (chartAt (EuclideanHalfSpace (n + 1)) α).source := by
    simpa only [e, TangentBundle.trivializationAt_baseSet] using hy
  have hy' : (y : M) ∈ (extChartAt (𝓡∂ (n + 1)) α).source := by rwa [extChartAt_source]
  rw [isOutwardPointing_iff_tangentCoordChange y.property hy']
  have hWs : (e.symmL ℝ (y : M) v₀ : EuclideanSpace ℝ (Fin (n + 1))) =
      tangentCoordChange (𝓡∂ (n + 1)) α (y : M) (y : M) v₀ :=
    congrArg (fun L ↦ L v₀) (TangentBundle.symmL_trivializationAt_eq_core (I := 𝓡∂ (n + 1)) hyc)
  have hcoord : tangentCoordChange (𝓡∂ (n + 1)) (y : M) α (y : M) (e.symmL ℝ (y : M) v₀) = v₀ := by
    rw [hWs, tangentCoordChange_comp ⟨⟨hy', mem_extChartAt_source (y : M)⟩, hy'⟩,
      tangentCoordChange_self hy']
  rw [hcoord]; simp [v₀]

variable [RiemannianBundle (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]

/-- Orthogonal projection onto the normal complement of `T_x(∂M)` in `T_x M` preserves
outwardness at `x`. -/
theorem IsOutwardPointing.starProjection_orthogonal_range_mfderiv_subtypeVal
    {x : (𝓡∂ (n + 1)).boundary M} {v : TangentSpace (𝓡∂ (n + 1)) (x : M)}
    (hv : IsOutwardPointing (x : M) v) :
    IsOutwardPointing (x : M)
      ((mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x).rangeᗮ.starProjection v) := by
  set dι := mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
    (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x
  have hmem : dι.range.starProjection v ∈ dι.range := (dι.range.orthogonalProjectionOnto v).property
  obtain ⟨w, hw⟩ := hmem
  have hsub : dι.rangeᗮ.starProjection v = v + dι (-w) := by
    rw [Submodule.starProjection_orthogonal_val, ← hw, map_neg, sub_eq_add_neg]; rfl
  rwa [hsub, isOutwardPointing_add_mfderiv_subtypeVal_boundary]

/-- Unnormalized local outward normal near a boundary chart center `α`. -/
private noncomputable def localOutwardNormalAux (α y : (𝓡∂ (n + 1)).boundary M) :
    TangentSpace (𝓡∂ (n + 1)) (y : M) :=
  (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
    (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) y).rangeᗮ.starProjection
      ((trivializationAt (EuclideanSpace ℝ (Fin (n + 1)))
        (TangentSpace (𝓡∂ (n + 1))) (α : M)).symmL ℝ (y : M) (-EuclideanSpace.single 0 1))

private theorem isOutwardPointing_localOutwardNormalAux {α y : (𝓡∂ (n + 1)).boundary M}
    (hy : (y : M) ∈ (trivializationAt (EuclideanSpace ℝ (Fin (n + 1)))
      (TangentSpace (𝓡∂ (n + 1))) (α : M)).baseSet) :
    IsOutwardPointing (y : M) (localOutwardNormalAux α y) :=
  IsOutwardPointing.starProjection_orthogonal_range_mfderiv_subtypeVal
    (isOutwardPointing_trivializationAt_symmL_neg_single_zero hy)

private theorem inner_localOutwardNormalAux_mfderiv_subtypeVal (α y : (𝓡∂ (n + 1)).boundary M)
    (w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) y) :
    inner ℝ (localOutwardNormalAux α y)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) y w) = 0 := by
  rw [localOutwardNormalAux, Submodule.starProjection_orthogonal_val]
  exact (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
    (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) y).range.starProjection_inner_eq_zero _ _
      (LinearMap.mem_range_self _ w)

/-- The **outward-pointing unit normal** along the boundary of a Riemannian manifold modeled on
`𝓡∂ (n + 1)`: at each boundary point `x`, the unique ambient tangent vector of norm `1` that
points outward (`TauCeti.IsOutwardPointing`) and is orthogonal to `mfderiv Subtype.val x`. -/
noncomputable def halfSpaceOutwardUnitNormal (x : (𝓡∂ (n + 1)).boundary M) :
    TangentSpace (𝓡∂ (n + 1)) (x : M) :=
  ‖localOutwardNormalAux x x‖⁻¹ • localOutwardNormalAux x x

/-- The outward unit normal has norm `1` at every boundary point. -/
@[simp]
theorem norm_halfSpaceOutwardUnitNormal (x : (𝓡∂ (n + 1)).boundary M) :
    ‖halfSpaceOutwardUnitNormal x‖ = 1 := by
  have hne : localOutwardNormalAux x x ≠ 0 :=
    (isOutwardPointing_localOutwardNormalAux
      (FiberBundle.mem_baseSet_trivializationAt' (x : M))).ne_zero
  rw [halfSpaceOutwardUnitNormal, norm_smul, norm_inv, norm_norm,
    inv_mul_cancel₀ (norm_ne_zero_iff.2 hne)]

/-- The outward unit normal points outward at every boundary point. -/
theorem isOutwardPointing_halfSpaceOutwardUnitNormal (x : (𝓡∂ (n + 1)).boundary M) :
    IsOutwardPointing (x : M) (halfSpaceOutwardUnitNormal x) := by
  have hout := isOutwardPointing_localOutwardNormalAux
    (FiberBundle.mem_baseSet_trivializationAt' (x : M))
  exact hout.smul_pos (inv_pos.2 (norm_pos_iff.2 hout.ne_zero))

/-- The outward unit normal is orthogonal to every tangent vector pushed forward from the
boundary. -/
@[simp]
theorem inner_halfSpaceOutwardUnitNormal_mfderiv_subtypeVal (x : (𝓡∂ (n + 1)).boundary M)
    (w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    inner ℝ (halfSpaceOutwardUnitNormal x)
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x w) = 0 := by
  rw [halfSpaceOutwardUnitNormal, real_inner_smul_left,
    inner_localOutwardNormalAux_mfderiv_subtypeVal, mul_zero]

/-- Symmetric form of `TauCeti.inner_halfSpaceOutwardUnitNormal_mfderiv_subtypeVal`. -/
@[simp]
theorem inner_mfderiv_subtypeVal_halfSpaceOutwardUnitNormal (x : (𝓡∂ (n + 1)).boundary M)
    (w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :
    inner ℝ
      (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x w)
      (halfSpaceOutwardUnitNormal x) = 0 := by
  rw [real_inner_comm, inner_halfSpaceOutwardUnitNormal_mfderiv_subtypeVal]

/-- **Uniqueness of the outward unit normal.** Any ambient tangent vector at `x ∈ ∂M` of norm `1`
that points outward and is orthogonal to `mfderiv Subtype.val x` equals
`TauCeti.halfSpaceOutwardUnitNormal x`. -/
theorem eq_halfSpaceOutwardUnitNormal_of_norm_eq_one {x : (𝓡∂ (n + 1)).boundary M}
    {v : TangentSpace (𝓡∂ (n + 1)) (x : M)} (hnorm : ‖v‖ = 1)
    (hout : IsOutwardPointing (x : M) v)
    (horth : ∀ w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x,
      inner ℝ v (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
        (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x w) = 0) :
    v = halfSpaceOutwardUnitNormal x := by
  let _ := isManifold_boundary (n := n) (k := 1) M one_ne_zero
  set dι := mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1))
    (Subtype.val : (𝓡∂ (n + 1)).boundary M → M) x
  set N := halfSpaceOutwardUnitNormal x
  have hvW : v ∈ dι.rangeᗮ := (Submodule.mem_orthogonal' _ _).2 fun _ ⟨w, hw⟩ ↦ hw ▸ horth w
  have hNW : N ∈ dι.rangeᗮ := (Submodule.mem_orthogonal' _ _).2 fun _ ⟨w, hw⟩ ↦
    hw ▸ inner_halfSpaceOutwardUnitNormal_mfderiv_subtypeVal x w
  have hinj := (isImmersion_subtypeVal_boundary (n := n) (k := 1) M one_ne_zero).mfderiv_injective
    one_ne_zero x
  have hdimOrth : Module.finrank ℝ dι.rangeᗮ = 1 := by
    have hsum := dι.range.finrank_add_finrank_orthogonal
    rw [LinearMap.finrank_range_of_inj hinj, TauCeti.finrank_tangentSpace,
      TauCeti.finrank_tangentSpace] at hsum
    simp only [finrank_euclideanSpace_fin] at hsum
    omega
  have hNne : (⟨N, hNW⟩ : dι.rangeᗮ) ≠ 0 := fun h0 ↦ by
    have hnormN := norm_halfSpaceOutwardUnitNormal x
    rw [show halfSpaceOutwardUnitNormal x = 0 from congrArg Subtype.val h0, norm_zero] at hnormN
    exact zero_ne_one hnormN
  have htop : Submodule.span ℝ ({⟨N, hNW⟩} : Set dι.rangeᗮ) = ⊤ :=
    Submodule.eq_top_of_finrank_eq ((finrank_span_singleton hNne).trans hdimOrth.symm)
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1
    (htop.symm ▸ Submodule.mem_top (x := (⟨v, hvW⟩ : dι.rangeᗮ)))
  have hvc : v = c • N := (congrArg Subtype.val hc).symm
  have habs : |c| = 1 := by
    simpa [N, hvc, norm_smul, norm_halfSpaceOutwardUnitNormal, Real.norm_eq_abs] using hnorm
  rcases (abs_eq (by positivity : (0 : ℝ) ≤ 1)).1 habs with rfl | rfl
  · simp [hvc]
  · exfalso
    exact ((isOutwardPointing_halfSpaceOutwardUnitNormal x).add hout).ne_zero (by
      rw [hvc, neg_one_smul, add_neg_cancel])

private theorem contMDiffAt_localOutwardNormalAux {k : ℕ∞ω}
    [IsManifold (𝓡∂ (n + 1)) (k + 1) M]
    [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) k (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)]
    (α : (𝓡∂ (n + 1)).boundary M) :
    ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
      ((𝓡∂ (n + 1)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) k
      (fun y : (𝓡∂ (n + 1)).boundary M ↦
        TotalSpace.mk' (EuclideanSpace ℝ (Fin (n + 1)))
          (E := fun z : M ↦ TangentSpace (𝓡∂ (n + 1)) z) (y : M)
          (localOutwardNormalAux α y)) α := by
  have _ := isManifold_boundary (n := n) (k := k + 1) M (by simp)
  have _ : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 1 ((𝓡∂ (n + 1)).boundary M) :=
    IsManifold.of_le (n := k + 1) (ENat.one_le_iff_ne_zero_withTop.2 (by simp))
  have hι := (isSmoothEmbedding_subtypeVal_boundary (n := n) (k := k + 1) M (by simp)).contMDiff
  have hinj := (isImmersion_subtypeVal_boundary (n := n) (k := k + 1) M
    (by simp)).mfderiv_injective (by simp) α
  let e := trivializationAt (EuclideanSpace ℝ (Fin (n + 1))) (TangentSpace (𝓡∂ (n + 1))) (α : M)
  let v₀ : EuclideanSpace ℝ (Fin (n + 1)) := -EuclideanSpace.single 0 1
  have hW_ambient : ContMDiffAt (𝓡∂ (n + 1))
      ((𝓡∂ (n + 1)).prod 𝓘(ℝ, EuclideanSpace ℝ (Fin (n + 1)))) k
      (fun z : M ↦ TotalSpace.mk' (EuclideanSpace ℝ (Fin (n + 1)))
        (E := fun z : M ↦ TangentSpace (𝓡∂ (n + 1)) z) z (e.symmL ℝ z v₀)) (α : M) := by
    rw [contMDiffAt_section_iff]
    refine (contMDiffAt_const (c := v₀)).congr_of_eventuallyEq ?_
    filter_upwards [e.open_baseSet.mem_nhds
      (FiberBundle.mem_baseSet_trivializationAt' (α : M))] with z hz
    change (e ⟨z, e.symmL ℝ z v₀⟩).2 = v₀
    rw [e.symmL_apply hz, e.apply_mk_symm hz]
  exact (hι α).starProjection_orthogonal_range_mfderiv_apply le_rfl hinj
    (hW_ambient.comp α ((hι α).of_le le_self_add))

/-- **Regularity of the outward unit normal.** On a `C^(k + 1)` manifold with boundary carrying a
`C^k` Riemannian metric, the outward unit normal is a `C^k` map into the ambient tangent bundle. -/
theorem contMDiff_halfSpaceOutwardUnitNormal {k : ℕ∞ω}
    [IsManifold (𝓡∂ (n + 1)) (k + 1) M]
    [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) k (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)] :
    ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)).tangent k
      (fun x : (𝓡∂ (n + 1)).boundary M ↦
        (⟨(x : M), halfSpaceOutwardUnitNormal x⟩ : TangentBundle (𝓡∂ (n + 1)) M)) := by
  intro α
  have hU := contMDiffAt_localOutwardNormalAux (k := k) α
  have hα_ne : localOutwardNormalAux α α ≠ 0 :=
    (isOutwardPointing_localOutwardNormalAux
      (FiberBundle.mem_baseSet_trivializationAt' (α : M))).ne_zero
  have hnorm : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) k
      (fun y : (𝓡∂ (n + 1)).boundary M ↦ ‖localOutwardNormalAux α y‖) α := by
    have hinner : ContMDiffAt 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) 𝓘(ℝ) k
        (fun y : (𝓡∂ (n + 1)).boundary M ↦
          inner ℝ (localOutwardNormalAux α y) (localOutwardNormalAux α y)) α :=
      ContMDiffAt.inner_bundle hU hU
    simpa only [Function.comp_def, ← norm_eq_sqrt_real_inner] using
      (Real.contDiffAt_sqrt (inner_self_ne_zero.mpr hα_ne)).comp_contMDiffAt
        (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
        (f := fun y : (𝓡∂ (n + 1)).boundary M ↦
          inner ℝ (localOutwardNormalAux α y) (localOutwardNormalAux α y)) hinner
  have hloc := (hnorm.inv₀ (norm_ne_zero_iff.mpr hα_ne)).smul_totalSpace hU
  refine hloc.congr_of_eventuallyEq ?_
  have hU_nhds : Subtype.val ⁻¹' (trivializationAt (EuclideanSpace ℝ (Fin (n + 1)))
      (TangentSpace (𝓡∂ (n + 1))) (α : M)).baseSet ∈ 𝓝 α :=
    continuous_subtype_val.continuousAt.preimage_mem_nhds
      ((trivializationAt (EuclideanSpace ℝ (Fin (n + 1)))
        (TangentSpace (𝓡∂ (n + 1))) (α : M)).open_baseSet.mem_nhds
          (FiberBundle.mem_baseSet_trivializationAt' (α : M)))
  filter_upwards [hU_nhds] with y hy
  apply congrArg (fun v : TangentSpace (𝓡∂ (n + 1)) (y : M) ↦
    (⟨(y : M), v⟩ : TangentBundle (𝓡∂ (n + 1)) M))
  have hy_out := isOutwardPointing_localOutwardNormalAux hy
  symm
  refine eq_halfSpaceOutwardUnitNormal_of_norm_eq_one ?_
    (hy_out.smul_pos (inv_pos.2 (norm_pos_iff.2 hy_out.ne_zero))) fun w ↦ ?_
  · rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.2 hy_out.ne_zero)]
  · rw [real_inner_smul_left, inner_localOutwardNormalAux_mfderiv_subtypeVal, mul_zero]

/-- For a continuous Riemannian metric on a `C¹` manifold with boundary, the outward unit normal
is continuous into the ambient tangent bundle. -/
theorem continuous_halfSpaceOutwardUnitNormal
    [IsContinuousRiemannianBundle (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)] :
    Continuous (fun x : (𝓡∂ (n + 1)).boundary M ↦
      (⟨(x : M), halfSpaceOutwardUnitNormal x⟩ : TangentBundle (𝓡∂ (n + 1)) M)) := by
  have _ : IsManifold (𝓡∂ (n + 1)) (0 + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡∂ (n + 1)) 1 M)
  have _ : IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) 0 (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x) :=
    IsContinuousRiemannianBundle.toIsContMDiffZero
  exact (contMDiff_halfSpaceOutwardUnitNormal (n := n) (M := M) (k := 0)).continuous

/-- **Existence of a smooth outward unit normal** along the boundary of a smooth Riemannian
manifold with boundary: there is a smooth section along the boundary inclusion of norm `1`,
pointing outward, and orthogonal to the boundary tangent space at every boundary point. -/
theorem exists_halfSpaceOutwardUnitNormal
    [IsManifold (𝓡∂ (n + 1)) ∞ M]
    [IsContMDiffRiemannianBundle (𝓡∂ (n + 1)) ∞ (EuclideanSpace ℝ (Fin (n + 1)))
      (fun x : M ↦ TangentSpace (𝓡∂ (n + 1)) x)] :
    ∃ N : (x : (𝓡∂ (n + 1)).boundary M) → TangentSpace (𝓡∂ (n + 1)) (x : M),
      ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)).tangent ∞
        (fun x : (𝓡∂ (n + 1)).boundary M ↦
          (⟨(x : M), N x⟩ : TangentBundle (𝓡∂ (n + 1)) M)) ∧
      ∀ x, ‖N x‖ = 1 ∧ IsOutwardPointing (x : M) (N x) ∧
        ∀ w : TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x,
          inner ℝ (N x)
            (mfderiv 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) (𝓡∂ (n + 1)) Subtype.val x w) = 0 := by
  have _ : IsManifold (𝓡∂ (n + 1)) (∞ + 1) M := by
    simpa using (inferInstance : IsManifold (𝓡∂ (n + 1)) ∞ M)
  exact ⟨halfSpaceOutwardUnitNormal, contMDiff_halfSpaceOutwardUnitNormal (k := ∞), fun x ↦
    ⟨norm_halfSpaceOutwardUnitNormal x, isOutwardPointing_halfSpaceOutwardUnitNormal x,
      inner_halfSpaceOutwardUnitNormal_mfderiv_subtypeVal x⟩⟩

end OutwardUnitNormal

end TauCeti
