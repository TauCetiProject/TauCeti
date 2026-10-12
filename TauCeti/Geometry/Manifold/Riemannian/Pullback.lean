/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import TauCeti.Analysis.Calculus.Bilinear
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian

/-!
# Smoothness of pulled-back Riemannian metrics

Let `b` be a family of bilinear forms on the tangent spaces of a manifold `N`, for instance a
Riemannian metric, that is a `C^n` section near `f x₀`, where `f : M → N` is a map that is
`C^(n+1)` at a point `x₀`. Pulling `b` back along the differential of `f` gives at each point `x`
the bilinear form `(v, w) ↦ b_{f x}(df_x v, df_x w)` on `T_x M`. This file proves that the family
of these forms is `C^n` at `x₀`, as a section of the bundle of bilinear forms on the tangent bundle
of `M`.

No injectivity of the differential is assumed: the statement is only about smoothness. When `b` is
positive definite (for instance a Riemannian metric), the pulled-back forms are positive definite
exactly where `df` is injective. This is the regularity
input for Riemannian metrics that are defined by pulling back along local diffeomorphisms, such as
the metric that a manifold with a geometric structure receives through its charts.

## Main results

* `Bundle.contMDiffAt_bilinearForm_pullback`: the pullback of a family of bilinear forms that is
  `C^n` at `f x₀`, along a map `f` that is `C^(n+1)` at `x₀`, is a `C^n` section at `x₀`.
* `Bundle.ContMDiffRiemannianMetric.contMDiffAt_pullback`: the special case of a `C^n` Riemannian
  metric.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 2
  (pullback metrics).
-/

public section

open Bundle Manifold Filter
open scoped ContDiff Manifold Topology

noncomputable section

namespace Bundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ F H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J 1 N] {n : ℕ∞ω}

/- The proof of `Bundle.contMDiffAt_bilinearForm_pullback`, which reads the pulled-back section in
tangent coordinates through `ContMDiffAt.mfderiv_const`, follows the proof pattern of
`TauCeti.inducedRiemannianMetric` in https://github.com/TauCetiProject/TauCeti/pull/11460, which
treats the case of a flat target. -/

/-- The pullback of a family `b` of bilinear forms on the tangent spaces of `N` that is a `C^n`
section at `f x₀`, along a map `f` that is `C^(n+1)` at `x₀`, is a `C^n` section at `x₀`: the family
of bilinear forms `(v, w) ↦ b_{f x}(df_x v, df_x w)`. -/
theorem contMDiffAt_bilinearForm_pullback
    {b : ∀ y : N, TangentSpace J y →L[ℝ] TangentSpace J y →L[ℝ] ℝ} {f : M → N} {x₀ : M}
    (hb : ContMDiffAt J (J.prod 𝓘(ℝ, F →L[ℝ] F →L[ℝ] ℝ)) n
      (fun y ↦ TotalSpace.mk' (F →L[ℝ] F →L[ℝ] ℝ)
        (E := fun y : N ↦ TangentSpace J y →L[ℝ] TangentSpace J y →L[ℝ] ℝ) y (b y)) (f x₀))
    (hf : ContMDiffAt I J (n + 1) f x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x
        ((ContinuousLinearMap.precomp ℝ (mfderiv I J f x)).comp
          ((b (f x)).comp (mfderiv I J f x)))) x₀ := by
  refine (contMDiffAt_section x₀).2 ?_
  have hg := (contMDiffAt_section (f x₀)).1 hb
  have hfn : ContMDiffAt I J n f x₀ := hf.of_le le_self_add
  -- In the coordinates centred at `x₀` and `f x₀`, the pulled-back form is the coordinate
  -- expression of `g` at `f x` pulled back along the differential of `f` read in those
  -- coordinates.
  apply (ContinuousLinearMap.contDiff_precomp_comp.contMDiff.contMDiffAt.comp x₀
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

namespace ContMDiffRiemannianMetric

/-- The pullback of a `C^n` Riemannian metric `g` along a map `f` that is `C^(n+1)` at `x₀`, the
family of bilinear forms `(v, w) ↦ g_{f x}(df_x v, df_x w)`, is a `C^n` section at `x₀`. -/
theorem contMDiffAt_pullback
    (g : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y)) {f : M → N} {x₀ : M}
    (hf : ContMDiffAt I J (n + 1) f x₀) :
    ContMDiffAt I (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) n
      (fun x ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) x
        ((ContinuousLinearMap.precomp ℝ (mfderiv I J f x)).comp
          ((g.inner (f x)).comp (mfderiv I J f x)))) x₀ :=
  contMDiffAt_bilinearForm_pullback (g.contMDiff (f x₀)) hf

end ContMDiffRiemannianMetric

end Bundle
