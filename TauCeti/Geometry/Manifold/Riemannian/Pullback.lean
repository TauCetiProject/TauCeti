/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Smoothness of pulled-back Riemannian metrics

Let `g` be a `C^n` Riemannian metric on a manifold `N` and `f : M → N` a map that is `C^(n+1)` at a
point `x₀`. Pulling `g` back along the differential of `f` gives at each point `x` the bilinear form
`(v, w) ↦ g_{f x}(df_x v, df_x w)` on `T_x M`. This file proves that the family of these forms is
`C^n` at `x₀`, as a section of the bundle of bilinear forms on the tangent bundle of `M`.

No injectivity of the differential is assumed: the statement is only about smoothness, and the
pulled-back forms are positive definite exactly where `df` is injective. This is the regularity
input for Riemannian metrics that are defined by pulling back along local diffeomorphisms, such as
the metric that a manifold with a geometric structure receives through its charts.

## Main results

* `Bundle.ContMDiffRiemannianMetric.contMDiffAt_pullback`: the pullback of a `C^n` Riemannian
  metric along a map that is `C^(n+1)` at `x₀` is a `C^n` section at `x₀`.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (pullback metrics).
-/

public section

open Bundle Manifold Filter
open scoped ContDiff Manifold Topology

noncomputable section

namespace Bundle.ContMDiffRiemannianMetric

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N] {n : ℕ∞ω}

/-- Pulling a bilinear form back along a continuous linear map depends smoothly on both. -/
private theorem contDiff_precomp_comp :
    ContDiff ℝ n fun p : (F →L[ℝ] F →L[ℝ] ℝ) × (E →L[ℝ] F) ↦
      (ContinuousLinearMap.precomp ℝ p.2).comp (p.1.comp p.2) := by
  have h : (fun p : (F →L[ℝ] F →L[ℝ] ℝ) × (E →L[ℝ] F) ↦
      (ContinuousLinearMap.precomp ℝ p.2).comp (p.1.comp p.2)) = fun p ↦
      ((ContinuousLinearMap.compL ℝ E F ℝ).flip p.2).comp (p.1.comp p.2) := by
    ext p v w
    rfl
  rw [h]
  exact ((ContinuousLinearMap.compL ℝ E F ℝ).flip.contDiff.comp contDiff_snd).clm_comp
    (contDiff_fst.clm_comp contDiff_snd)

/-- The pullback of a `C^n` Riemannian metric `g` along a map `f` that is `C^(n+1)` at `x₀`, the
family of bilinear forms `(v, w) ↦ g_{f x}(df_x v, df_x w)`, is a `C^n` section at `x₀`. -/
theorem contMDiffAt_pullback
    (g : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y)) {f : M → N} {x₀ : M}
    (hf : ContMDiffAt I J (n + 1) f x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x
        ((ContinuousLinearMap.precomp ℝ (mfderiv I J f x)).comp
          ((g.inner (f x)).comp (mfderiv I J f x)))) x₀ := by
  refine (contMDiffAt_section x₀).2 ?_
  have hg := (contMDiffAt_section (f x₀)).1 (g.contMDiff (f x₀))
  have hfn : ContMDiffAt I J n f x₀ := hf.of_le le_self_add
  -- In the coordinates centred at `x₀` and `f x₀`, the pulled-back form is the coordinate
  -- expression of `g` at `f x` pulled back along the differential of `f` read in those
  -- coordinates.
  apply (contDiff_precomp_comp.contMDiff.contMDiffAt.comp x₀
    ((hg.comp x₀ hfn).prodMk_space (hf.mfderiv_const le_rfl))).congr_of_eventuallyEq
  filter_upwards [(trivializationAt E (TangentSpace I : M → Type _) x₀).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I : M → Type _) x₀),
    hfn.continuousAt.preimage_mem_nhds
      ((trivializationAt F (TangentSpace J : N → Type _) (f x₀)).open_baseSet.mem_nhds
        (mem_baseSet_trivializationAt F (TangentSpace J : N → Type _) (f x₀)))] with y hy hfy
  have hyhom : y ∈ (trivializationAt (E →L[ℝ] ℝ)
      (fun z : M ↦ TangentSpace I z →L[ℝ] ℝ) x₀).baseSet := by
    simpa using hy
  have hfyhom : f y ∈ (trivializationAt (F →L[ℝ] ℝ)
      (fun z : N ↦ TangentSpace J z →L[ℝ] ℝ) (f x₀)).baseSet := by
    simpa using hfy
  ext v w
  simp only [hom_trivializationAt_apply, ContinuousLinearMap.inCoordinates, inTangentCoordinates,
    Function.comp_apply, ContinuousLinearMap.coe_comp,
    Trivialization.continuousLinearMapAt_apply, Trivialization.linearMapAt_apply, hyhom, hfyhom,
    ite_true, Trivial.fiberBundle_trivializationAt', Trivial.trivialization_baseSet, Set.mem_univ,
    Trivial.trivialization_apply, id, Set.mem_preimage.1 hfy, ContinuousLinearMap.precomp_apply]
  -- Reading `df_y v` in the trivialization at `f x₀` and back recovers it.
  have key (u : TangentSpace J (f y)) :
      (trivializationAt F (TangentSpace J) (f x₀)).symmL ℝ (f y)
        ((trivializationAt F (TangentSpace J) (f x₀)) ⟨f y, u⟩).2 = u := by
    rw [Trivialization.symmL_apply _ hfy]
    exact Trivialization.symm_apply_apply_mk _ hfy u
  rw [key, key]

end Bundle.ContMDiffRiemannianMetric
