/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.ContMDiffMFDeriv
public import TauCeti.Analysis.Calculus.Bilinear
public import TauCeti.Geometry.Manifold.Riemannian.Basic
public import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
public import TauCeti.Geometry.Manifold.VectorBundle.Riemannian.Conformal

/-!
# Pullback Riemannian metrics

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
* `Bundle.ContMDiffRiemannianMetric.pullback`: the `C^n` Riemannian metric obtained from an
  immersion by pulling back the target metric.
* `Bundle.ContMDiffRiemannianMetric.pullback_id` and
  `Bundle.ContMDiffRiemannianMetric.pullback_comp`: the functoriality laws for pullback metrics.
* `Bundle.ContMDiffRiemannianMetric.pullback_rescale`: pulling back commutes with conformal
  rescaling, `f^* (h g) = (h ∘ f) f^* g`.
* `Bundle.ContMDiffRiemannianMetric.conformalClass_pullback`: along a map with a `C^n` left
  inverse, such as a diffeomorphism, the conformal class of `f^* g` is the pullback of the
  conformal class of `g`.

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

variable [FiniteDimensional ℝ E]

/-- Pull back a smooth Riemannian metric along a smooth immersion. At `x`, the inner product is
the target metric at `f x` evaluated on the two images under the manifold derivative of `f`.
Injectivity of the derivative makes this form positive definite. -/
noncomputable def pullback
    (g : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y)) (f : M → N)
    (hf : ContMDiff I J (n + 1) f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x)) :
    ContMDiffRiemannianMetric I n E (fun x : M ↦ TangentSpace I x) where
  inner x :=
    (ContinuousLinearMap.precomp ℝ (mfderiv I J f x)).comp
      ((g.inner (f x)).comp (mfderiv I J f x))
  symm x v w := by
    simpa only [ContinuousLinearMap.precomp_apply, ContinuousLinearMap.comp_apply] using
      g.symm (f x) (mfderiv I J f x v) (mfderiv I J f x w)
  pos x v hv := by
    apply g.pos (f x)
    exact (map_ne_zero_iff (mfderiv I J f x) (hinj x)).2 hv
  isVonNBounded x := by
    -- TangentSpace deliberately has only its bundle topology; use the model norms while proving
    -- boundedness of the positive unit ball.
    let _ : NormedAddCommGroup (TangentSpace I x) := inferInstanceAs (NormedAddCommGroup E)
    let _ : NormedSpace ℝ (TangentSpace I x) := inferInstanceAs (NormedSpace ℝ E)
    let _ : NormedAddCommGroup (TangentSpace J (f x)) := inferInstanceAs (NormedAddCommGroup F)
    let _ : NormedSpace ℝ (TangentSpace J (f x)) := inferInstanceAs (NormedSpace ℝ F)
    let A : TangentSpace I x →L[ℝ] TangentSpace J (f x) := mfderiv I J f x
    obtain ⟨K, -, hK⟩ := A.toLinearMap.exists_antilipschitzWith
      (LinearMap.ker_eq_bot.2 (hinj x))
    refine NormedSpace.isVonNBounded_of_isBounded ℝ
      ((hK.isBounded_preimage
        ((NormedSpace.isVonNBounded_iff ℝ).mp (g.isVonNBounded (f x)))).subset ?_)
    intro v hv
    -- The defining inequality is exactly membership in the preimage above.
    change g.inner (f x) (A v) (A v) < 1
    exact hv
  contMDiff x := g.contMDiffAt_pullback (hf x)

/-- The pullback metric is obtained by applying the target metric to the two differentials. -/
@[simp]
theorem pullback_inner
    (g : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y)) (f : M → N)
    (hf : ContMDiff I J (n + 1) f)
    (hinj : ∀ x, Function.Injective (mfderiv I J f x)) (x : M)
    (v w : TangentSpace I x) :
    (g.pullback f hf hinj).inner x v w =
      g.inner (f x) (mfderiv I J f x v) (mfderiv I J f x w) :=
  (rfl)

/-- Pulling a Riemannian metric back along the identity leaves it unchanged. -/
@[simp]
theorem pullback_id
    (g : ContMDiffRiemannianMetric I n E (fun y : M ↦ TangentSpace I y))
    (hf : ContMDiff I I (n + 1) id)
    (hinj : ∀ x, Function.Injective (mfderiv I I id x)) :
    g.pullback id hf hinj = g := by
  apply ext
  intro x v w
  rw [pullback_inner]
  simp only [mfderiv_id, ContinuousLinearMap.id_apply, id_eq]

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  {H'' : Type*} [TopologicalSpace H''] {K : ModelWithCorners ℝ G H''}
  {P : Type*} [TopologicalSpace P] [ChartedSpace H'' P] [IsManifold K 1 P]

/-- Pulling a metric back along a composite is the same as pulling it back successively. -/
theorem pullback_comp
    [FiniteDimensional ℝ F]
    (g : ContMDiffRiemannianMetric K n G (fun z : P ↦ TangentSpace K z))
    (h : N → P) (f : M → N)
    (hh : ContMDiff J K (n + 1) h) (hf : ContMDiff I J (n + 1) f)
    (hinjh : ∀ y, Function.Injective (mfderiv J K h y))
    (hinjf : ∀ x, Function.Injective (mfderiv I J f x)) :
    g.pullback (h ∘ f) (hh.comp hf)
        (fun x ↦ by
          rw [mfderiv_comp x (hh.mdifferentiableAt (by simp))
            (hf.mdifferentiableAt (by simp))]
          exact (hinjh (f x)).comp (hinjf x)) =
      (g.pullback h hh hinjh).pullback f hf hinjf := by
  apply ext
  intro x v w
  rw [pullback_inner, pullback_inner, pullback_inner]
  rw [mfderiv_comp x (hh.mdifferentiableAt (by simp)) (hf.mdifferentiableAt (by simp))]
  simp only [ContinuousLinearMap.comp_apply]
  rw [Function.comp_apply]

variable {g : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y)} {f : M → N}
  {hf : ContMDiff I J (n + 1) f} {hinj : ∀ x, Function.Injective (mfderiv I J f x)}

/-- Pulling back commutes with conformal rescaling: the pullback of `h g` is `(h ∘ f)` times the
pullback of `g`. -/
@[simp]
theorem pullback_rescale (h : N → ℝ) (hh : ContMDiff J 𝓘(ℝ) n h) (hh_pos : ∀ y, 0 < h y) :
    (g.rescale h hh hh_pos).pullback f hf hinj =
      (g.pullback f hf hinj).rescale (h ∘ f) (hh.comp (hf.of_le le_self_add))
        (fun x ↦ hh_pos (f x)) := by
  ext x v w
  simp

/-- The pullback of a metric conformal to `g` is conformal to the pullback of `g`. -/
theorem pullback_mem_conformalClass_pullback
    {g' : ContMDiffRiemannianMetric J n F (fun y : N ↦ TangentSpace J y)}
    (h : g' ∈ g.conformalClass) :
    g'.pullback f hf hinj ∈ (g.pullback f hf hinj).conformalClass := by
  obtain ⟨h, hh, hh_pos, rfl⟩ := mem_conformalClass_iff.1 h
  rw [pullback_rescale]
  exact rescale_mem_conformalClass _

/-- Along a map `f` with a `C^n` left inverse, for instance a `C^(n+1)` diffeomorphism, the
conformal class of the pullback of `g` is the pullback of the conformal class of `g`. -/
theorem conformalClass_pullback {f' : N → M} (hf' : ContMDiff J I n f')
    (hff' : Function.LeftInverse f' f) :
    (g.pullback f hf hinj).conformalClass = (·.pullback f hf hinj) '' g.conformalClass := by
  refine Set.Subset.antisymm ?_ ?_
  · intro _ hg
    obtain ⟨h, hh, hh_pos, rfl⟩ := mem_conformalClass_iff.1 hg
    refine ⟨g.rescale (h ∘ f') (hh.comp hf') (fun y ↦ hh_pos (f' y)),
      rescale_mem_conformalClass g, ?_⟩
    ext x v w
    simp [hff' x]
  · rintro _ ⟨g', hg', rfl⟩
    exact pullback_mem_conformalClass_pullback hg'


end ContMDiffRiemannianMetric

end Bundle
