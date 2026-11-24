/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Axel Delaval, Zhiyuan Zhang, Leheng Chen
-/
module

public import TauCeti.Geometry.Manifold.Riemannian.IndexForm.Comparison
public import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Basic
import TauCeti.Geometry.Manifold.Riemannian.Geodesic.Normal.Parallel

/-!
# Upper Jacobi comparison on a normal radial segment

For a Jacobi field vanishing at the initial point of a normal radial segment, a radial
curvature operator bounded between `κ` and zero gives the upper model-cotangent bound
on its terminal pairing. The parallel comparison field is constructed by transporting
the terminal value backwards with the native radial parallel isometry. No parallel field
or index-nonnegativity assumption is supplied by the caller.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, second edition, Chapter 10.
* [lean-eval-submissions](https://github.com/frenzymath/lean-eval-submissions).
* [PoincareConjecture](https://github.com/frenzymath/PoincareConjecture).
-/

public noncomputable section

open Bundle CovariantDerivative Set
open scoped ContDiff Manifold Topology InnerProductSpace

namespace TauCeti.Manifold

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [T2Space M] [IsManifold I ∞ M]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
  {p : M} {U : Set (TangentSpace I p)} {v : TangentSpace I p} {T κ : ℝ}

/-- Upper model-cotangent comparison for a Jacobi field on a normal radial segment with
radial curvature operator bounded between `κ` and zero. The bounds are required only on
the open segment, and the field need only vanish at the initial point. -/
theorem IsNormalDomain.inner_alongCurveWithin_self_le_curvatureCotangent_mul_norm_sq
    (h : IsNormalDomain I M p U) (hT : 0 ≤ T)
    (hTv : T • v ∈ U)
    {V : ∀ t, TangentSpace I (riemannianExp I M p (t • v))} {s : Set ℝ}
    (hV : IsJacobiFieldOn I (fun t ↦ riemannianExp I M p (t • v)) V s)
    (hs : Icc 0 T ⊆ s) (hV0 : V 0 = 0)
    (hupper : ∀ t ∈ Ioo 0 T, ∀ u : TangentSpace I (riemannianExp I M p (t • v)),
      inner ℝ ((leviCivitaConnection I M).curvatureTensor
        (riemannianExp I M p (t • v)) u
        (curveVelocity I (fun r ↦ riemannianExp I M p (r • v)) t)
        (curveVelocity I (fun r ↦ riemannianExp I M p (r • v)) t)) u ≤ 0)
    (hlower : ∀ t ∈ Ioo 0 T, ∀ u : TangentSpace I (riemannianExp I M p (t • v)),
      κ * ‖u‖ ^ 2 ≤ inner ℝ ((leviCivitaConnection I M).curvatureTensor
        (riemannianExp I M p (t • v)) u
        (curveVelocity I (fun r ↦ riemannianExp I M p (r • v)) t)
        (curveVelocity I (fun r ↦ riemannianExp I M p (r • v)) t)) u) :
    inner ℝ (alongCurveWithin (leviCivitaConnection I M)
      (fun r ↦ riemannianExp I M p (r • v)) V s T) (V T) ≤
      curvatureCotangent κ T * ‖V T‖ ^ 2 := by
  obtain rfl | hTpos := hT.eq_or_lt
  · simp [hV0]
  have hseg (t : ℝ) (ht : t ∈ Icc 0 T) : t • v ∈ U := by
    simpa only [smul_smul, div_mul_cancel₀ _ hTpos.ne'] using
      h.smul_mem hTv (div_nonneg ht.1 hT) ((div_le_one hTpos).2 ht.2)
  let b := stdOrthonormalBasis ℝ (TangentSpace I p)
  let e := h.radialParallelIsometry b v hTpos hseg (left_mem_Icc.mpr hT)
    (right_mem_Icc.mpr hT)
  let a := e.symm (V T)
  let P := fun t ↦ h.radialParallelLinearMap b v hT hseg t a
  have hP (t : ℝ) (ht : t ∈ Icc 0 T) : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent 1
      (fun r ↦ TotalSpace.mk' E (riemannianExp I M p (r • v)) (P r)) t :=
    (h.contMDiffAt_radialParallelLinearMap_apply b v hT hseg a (hseg t ht)).of_le (by simp)
  have hP1 : ContMDiffOn 𝓘(ℝ, ℝ) I.tangent 1
      (fun t ↦ TotalSpace.mk' E (riemannianExp I M p (t • v)) (P t)) (uIcc 0 T) := by
    rw [uIcc_of_le hT]
    exact fun t ht ↦ (hP t ht).contMDiffWithinAt
  have hparallel : ∀ t ∈ uIcc 0 T, alongCurveWithin (leviCivitaConnection I M)
      (fun r ↦ riemannianExp I M p (r • v)) P (uIcc 0 T) t = 0 := by
    intro t ht
    rw [uIcc_of_le hT] at ht ⊢
    have hcoord := differentiableAt_sectionCoord
      (fun r ↦ riemannianExp I M p (r • v)) P
      ((hP t ht).mdifferentiableAt one_ne_zero)
      (FiberBundle.mem_baseSet_trivializationAt E (TangentSpace I)
        (riemannianExp I M p (t • v)))
    have hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I
        (fun r ↦ riemannianExp I M p (r • v)) t :=
      ((Bundle.contMDiff_proj (fun x : M ↦ TangentSpace I x)
        (IB := I) (n := 1)).contMDiffAt.comp t (hP t ht)).mdifferentiableAt one_ne_zero
    have hchart : DifferentiableAt ℝ
        (extChartAt I (riemannianExp I M p (t • v)) ∘
          fun r ↦ riemannianExp I M p (r • v)) t :=
      ((mdifferentiableAt_extChartAt (I := I)
        (mem_chart_source H (riemannianExp I M p (t • v)))).comp t hγ).differentiableAt
    rw [alongCurveWithin_subset _ _ P (subset_univ _) (uniqueDiffOn_Icc hTpos t ht)
      hcoord.differentiableWithinAt hchart.differentiableWithinAt,
      alongCurveWithin_univ]
    simpa only [P, radialParallelLinearMap_apply] using
      h.alongCurve_radialParallel_eq_zero b v hT hseg a ht
  have hPT : P T = V T :=
    (h.radialParallelIsometry_apply b v hTpos hseg (left_mem_Icc.mpr hT)
      (right_mem_Icc.mpr hT) a).symm.trans (e.apply_symm_apply (V T))
  have hs' : uIcc 0 T ⊆ s := by rwa [uIcc_of_le hT]
  simpa only [sub_zero] using
    hV.inner_alongCurveWithin_self_le_curvatureCotangent_mul_norm_sq_of_nonpos
      hT hs' hV0 hP1 hparallel hPT hupper (fun t ht ↦ hlower t ht (P t))

end TauCeti.Manifold
