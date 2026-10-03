/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace
public import Mathlib.Geometry.Manifold.Riemannian.Basic

/-!
# Riemannian metrics induced by immersions into inner product spaces

A `C^(n+1)` map `f : M → F` from a finite-dimensional manifold to a real inner product space whose
differential is injective at every point pulls the inner product of `F` back to a `C^n` Riemannian
metric on `M`:

`g_x(v, w) = ⟪df_x v, df_x w⟫`.

This is the first fundamental form of an immersed submanifold of Euclidean space, and the way
the classical model spaces such as the round sphere receive their metrics.

## Main definitions

* `TauCeti.inducedRiemannianMetric`: the `C^n` Riemannian metric induced by such a map.

## Main statements

* `TauCeti.inducedRiemannianMetric_inner`: the induced inner product of two tangent vectors is the
  inner product of their images under the differential.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (induced metrics on immersed submanifolds).
-/

public section

open Bundle Manifold Filter
open scoped ContDiff Manifold Topology

noncomputable section

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] {n : ℕ∞ω}

/-- The inner product of `F` pulled back along a continuous linear map `A : E →L[ℝ] F`, the
fibrewise building block of the induced metric. -/
private def pullbackInner (A : E →L[ℝ] F) : E →L[ℝ] E →L[ℝ] ℝ :=
  (innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ).bilinearComp A A

private theorem contDiff_pullbackInner : ContDiff ℝ n (pullbackInner (E := E) (F := F)) := by
  have h : (pullbackInner (E := E) (F := F)) = fun A ↦
      ((ContinuousLinearMap.compL ℝ E F ℝ).flip A).comp
        ((innerSL ℝ : F →L[ℝ] F →L[ℝ] ℝ).comp A) := by
    ext A v w
    rfl
  rw [h]
  exact (ContinuousLinearMap.compL ℝ E F ℝ).flip.contDiff.clm_comp
    (contDiff_const.clm_comp contDiff_id)

private theorem pullbackInner_self_pos {A : E →L[ℝ] F} (hA : Function.Injective A) {v : E}
    (hv : v ≠ 0) : 0 < pullbackInner A v v := by
  rw [pullbackInner, ContinuousLinearMap.bilinearComp_apply, innerSL_apply_apply]
  exact real_inner_self_pos.2 ((map_ne_zero_iff A hA).2 hv)

/-- The unit ball of the pulled-back inner product is bounded: an injective linear map out of a
finite-dimensional space is antilipschitz. -/
private theorem isVonNBounded_pullbackInner [FiniteDimensional ℝ E] {A : E →L[ℝ] F}
    (hA : Function.Injective A) :
    Bornology.IsVonNBounded ℝ {v : E | pullbackInner A v v < 1} := by
  obtain ⟨K, -, hK⟩ := (A : E →ₗ[ℝ] F).exists_antilipschitzWith (LinearMap.ker_eq_bot.2 hA)
  refine (NormedSpace.isVonNBounded_closedBall ℝ E K).subset fun v hv ↦ ?_
  rw [Set.mem_ofPred_eq, pullbackInner, ContinuousLinearMap.bilinearComp_apply,
    innerSL_apply_apply, real_inner_self_eq_norm_sq] at hv
  have h1 : ‖A v‖ ≤ 1 := by nlinarith [norm_nonneg (A v)]
  rw [Metric.mem_closedBall, dist_zero_right]
  calc ‖v‖ ≤ K * ‖A v‖ := ZeroHomClass.bound_of_antilipschitz (A : E →ₗ[ℝ] F) hK v
    _ ≤ K * 1 := by gcongr
    _ = K := mul_one _

variable [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

/-- The Riemannian metric induced on `M` by a `C^(n+1)` map `f : M → F` into a real inner product
space whose differential is injective at every point: the inner product of two tangent vectors is
the inner product of their images under the differential `mvfderiv I f x` of `f`, read in `F`. -/
def inducedRiemannianMetric (f : M → F) (hf : ContMDiff I 𝓘(ℝ, F) (n + 1) f)
    (hinj : ∀ x, Function.Injective (mvfderiv I f x)) :
    ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x) where
  inner x := pullbackInner (E := E) (F := F) (mvfderiv I f x)
  symm _ _ _ := real_inner_comm _ _
  pos x _ hv := pullbackInner_self_pos (E := E) (F := F) (hinj x) hv
  isVonNBounded x := isVonNBounded_pullbackInner (E := E) (F := F) (hinj x)
  contMDiff x := by
    refine (contMDiffAt_section x).2 ?_
    -- In the tangent coordinates centred at `x`, the metric is the inner product pulled back along
    -- the differential of `f` read in those coordinates, which is `C^n` by `mfderiv_const`.
    apply (contDiff_pullbackInner.contMDiff.contMDiffAt.comp x
      ((hf x).mfderiv_const le_rfl)).congr_of_eventuallyEq
    filter_upwards [(trivializationAt E (TangentSpace I : M → Type _) x).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x)] with y hy
    have hyhom : y ∈ (trivializationAt (E →L[ℝ] ℝ)
        (fun z : M ↦ TangentSpace I z →L[ℝ] ℝ) x).baseSet := by
      simpa using hy
    ext v w
    simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, inTangentCoordinates,
      Function.comp_apply, ContinuousLinearMap.coe_comp, id,
      TangentBundle.continuousLinearMapAt_model_space,
      Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_apply, hyhom, ite_true,
      Trivial.fiberBundle_trivializationAt', Trivial.trivialization_baseSet, Set.mem_univ,
      Trivial.trivialization_apply]
    -- Both sides are `⟪df_y (e.symm y v), df_y (e.symm y w)⟫` for the tangent trivialization `e`
    -- at `x`, up to the identity coordinate change of the model space `F`.
    rfl

/-- The induced inner product of two tangent vectors is the inner product of their images under
the differential. -/
@[simp]
theorem inducedRiemannianMetric_inner (f : M → F) (hf : ContMDiff I 𝓘(ℝ, F) (n + 1) f)
    (hinj : ∀ x, Function.Injective (mvfderiv I f x)) (x : M) (v w : TangentSpace I x) :
    (inducedRiemannianMetric f hf hinj).inner x v w =
      inner ℝ (mvfderiv I f x v) (mvfderiv I f x w) :=
  (rfl)

end TauCeti
