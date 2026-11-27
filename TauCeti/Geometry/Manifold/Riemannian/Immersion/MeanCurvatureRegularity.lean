/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.Immersion.MeanCurvature
public import TauCeti.Geometry.Manifold.VectorBundle.CovariantDerivative.AlongMap.Regularity
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv
import TauCeti.Geometry.Manifold.Riemannian.Immersion.Projection
import TauCeti.Geometry.Manifold.VectorBundle.GramSchmidt
import TauCeti.Geometry.Manifold.VectorBundle.SectionAlongMap.Regularity

/-!
# Regularity of the mean curvature vector

The mean curvature vector `H` of a map `f : M → N` (`TauCeti.immersionMeanCurvatureVector`) is a
field along `f`. Near a point `x` where `df_x` is injective, take a local orthonormal frame
`(Xᵢ)` of `TM`; then `H = (1 / m) ∑ᵢ (∇_{Xᵢ} (df Xᵢ))^⊥`, a finite sum of normal projections of
covariant derivatives along `f`. Each term loses one derivative of `f` for the covariant
derivative and one for the normal projection, so `H` is `C^k` where `f` is `C^{k+2}`, the
covariant derivative is `C^k`, and the metrics are `C^{k+1}` on `M` and `C^k` on `N`. This holds
at boundary and corner points of the source as well. In particular `H` is a smooth normal field
along a smooth immersion.

## Main results

* `TauCeti.contMDiffAt_immersionMeanCurvatureVector`: `H` is `C^k` at points where `f` is
  `C^{k+2}` with injective differential.
* `TauCeti.contMDiff_immersionMeanCurvatureVector`: `H` is `C^k` along a `C^{k+2}` immersion.
-/

public section

open Bundle CovariantDerivative Manifold Module
open scoped ContDiff Manifold Topology

namespace TauCeti

open TauCeti.Manifold

variable
  {E H M F G N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F] [TopologicalSpace G]
  {J : ModelWithCorners ℝ F G} [TopologicalSpace N] [ChartedSpace G N]
  [RiemannianBundle (fun y : N ↦ TangentSpace J y)] [IsManifold J ∞ N] [T2Space N]
  [RiemannianBundle (fun y : M ↦ TangentSpace I y)]
  [IsManifold I 2 M] {k : ℕ∞ω} [ENat.LEInfty k] [IsManifold I (k + 1 + 1) M]
  [IsContMDiffRiemannianBundle I (k + 1) E (fun y : M ↦ TangentSpace I y)]
  [IsContMDiffRiemannianBundle J k F (fun y : N ↦ TangentSpace J y)]
  {cov : CovariantDerivative J F (TangentSpace J : N → Type _)} [ContMDiffCovariantDerivative cov k]
  {f : M → N} {x : M}

/-- **The mean curvature vector is `C^k`** at a point where `f` is `C^{k+2}` with injective
differential, for a `C^k` covariant derivative, a `C^{k+1}` metric on `M` and a `C^k` metric on
`N`. This includes boundary and corner points of the source. -/
theorem contMDiffAt_immersionMeanCurvatureVector (hf : ContMDiffAt I J (k + 1 + 1) f x)
    (hinj : Function.Injective (mfderiv I J f x)) :
    ContMDiffAt I J.tangent k
      (fun y ↦ TotalSpace.mk' F (f y) (immersionMeanCurvatureVector (I := I) cov f y)) x := by
  have : ContMDiffVectorBundle (k + 1) E (TangentSpace I : M → Type _) I :=
    TangentBundle.contMDiffVectorBundle
  obtain ⟨s, hs, hx, X, hX, ho⟩ := exists_isLocalFrameOn_orthonormal
    (I := I) (n := k + 1) (F := E) (V := TangentSpace I) x
  set c : ℝ := (finrank ℝ E : ℝ)⁻¹
  have hval (i : Fin (finrank ℝ E)) :
      ContMDiffAt I J.tangent k
        (fun y ↦ TotalSpace.mk' F (f y) ((orthogonalNormalSpace I J f y).starProjection
          (cov.alongMap I f (fun z ↦ mfderiv I J f z (X i z)) y (c • X i y)))) x := by
    have hdf : ContMDiffAt I J.tangent (k + 1)
        (fun y ↦ TotalSpace.mk' F (f y) (mfderiv I J f y (X i y))) x := by
      simpa only [id_eq] using
        hf.mfderiv_apply_sectionAlong (b := id) (hX.contMDiffAt hs hx i) le_rfl
    have hcX : ContMDiffAt I I.tangent k (fun y ↦ TotalSpace.mk' E y (c • X i y)) x :=
      ((hX.contMDiffAt hs hx i).of_le le_self_add).const_smul_section
    have hder := cov.contMDiffAt_alongMap_apply (n := k) hdf hcX
    simpa only [orthogonalNormalSpace_def] using
      hf.starProjection_orthogonal_range_mfderiv_apply le_self_add hinj hder
  have hsum := ContMDiffAt.sum_sectionAlong Finset.univ _
    (hf.of_le (le_self_add.trans le_self_add)) fun i _ ↦ hval i
  apply hsum.congr_of_eventuallyEq
  have h2 : (2 : ℕ∞ω) ≤ k + 1 + 1 := by
    rw [← one_add_one_eq_two]; gcongr; exact le_add_self
  have hfn := (contMDiffAt_iff_contMDiffAt_nhds (n := 2) (by simp)).1 (hf.of_le h2)
  filter_upwards [hs.mem_nhds hx, hfn] with y hy hyf2
  let b := OrthonormalBasis.mk (ho y hy) (hX.generating hy).ge
  refine congrArg (TotalSpace.mk' F (f y)) ?_
  rw [immersionMeanCurvatureVector_eq_sum b, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  have hXi := ((hX.contMDiffAt hs hy i).mdifferentiableAt (by simp))
  simp only [b, OrthonormalBasis.coe_mk]
  rw [immersionSecondFundamentalFormAt_apply (cov := cov) hyf2 hXi hXi,
    immersionSecondFundamentalForm_def, map_smul, map_smul]

/-- **The mean curvature vector of a `C^{k+2}` immersion is a `C^k` field along it**, for a `C^k`
covariant derivative, a `C^{k+1}` metric on `M` and a `C^k` metric on `N`. -/
theorem contMDiff_immersionMeanCurvatureVector (hf : ContMDiff I J (k + 1 + 1) f)
    (hinj : ∀ y, Function.Injective (mfderiv I J f y)) :
    ContMDiff I J.tangent k
      (fun y ↦ TotalSpace.mk' F (f y) (immersionMeanCurvatureVector (I := I) cov f y)) :=
  fun y ↦ contMDiffAt_immersionMeanCurvatureVector (hf y) (hinj y)

end TauCeti
