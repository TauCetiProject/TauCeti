/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Geometry.Manifold.Algebra.Monoid
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import TauCeti.Geometry.Manifold.ContMDiff.Prod

/-!
# Integrals over a compact set of parameters in a manifold

Let `f : M → N → F` be a function of a point of a manifold `M` and of a parameter in a manifold
`N`, both modelled over `𝕜 = ℝ` or `𝕜 = ℂ`, with values in a normed space over `𝕜`, and let `μ`
be a measure on `N`. If `(x, a) ↦ f x a` is `C^n` and `s` is a subset of finite measure contained
in a compact set `K ⊆ N`, then so is the function

`x ↦ ∫ a in s, f x a ∂μ`.

This is the manifold counterpart of Mathlib's `ContDiffOn.parametric_integral`, where the
parameter ranges over a compact subset of a normed space. When `N` is compact and `μ` is finite,
the integral over all of `N` is `C^n`. The typical use is averaging over a compact Lie group with
its Haar measure, for instance to produce invariant Riemannian metrics.

## Main results

* `TauCeti.contMDiffAt_parametric_integral`, `ContMDiff.parametric_integral`: the integral over a
  finite-measure subset of a compact set of parameters is `C^n`.
* `TauCeti.contMDiffAt_parametric_integral_of_compactSpace`,
  `ContMDiff.parametric_integral_of_compactSpace`: the integral over a compact manifold of
  parameters against a finite measure is `C^n`.

The proof is local. Replacing `μ` by its restriction to `s`, it suffices to integrate over `K`
against a finite measure. For `n` finite, the tube lemma `TauCeti.exists_isOpen_prod_contMDiffOn`
makes `f` a `C^n` map on `U × V` for an open neighbourhood `U` of the base point and an open set
`V ⊇ K`. The set `K` is covered by finitely many compact sets each contained in `V` and in one
chart. On such a compact set `L`, the chart `ψ` of `N` transports the integral over a measurable
subset `r ⊆ L` to the integral, against the pushforward of the measure restricted to `r`, of a
function that is `C^n` on the product of an open set and the compact set `ψ '' L` of the model
spaces. Mathlib's `ContDiffOn.parametric_integral` applies there. Integrals over the finitely many
pieces are then added up by induction on the cover.

The manifold `M` is assumed boundaryless, so that its chart targets are open in the model space.
The parameter manifold `N` may have boundary and corners.
-/

public section

open Set Filter MeasureTheory Function
open scoped Topology ContDiff Manifold

namespace TauCeti

variable {𝕜 : Type*} [RCLike 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners 𝕜 E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners 𝕜 E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [MeasurableSpace N] [OpensMeasurableSpace N]
  {μ : Measure N}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace 𝕜 F]
  {f : M → N → F} {x₀ : M}

/-- The integral of a `C^m` function, against a finite measure, over a measurable set of parameters
contained in a compact subset `K` of one chart of the parameter manifold is `C^m` at `x₀`,
provided the function is `C^m` on `U × V` for an open neighbourhood `U` of `x₀` and a set
`V ⊇ K`. -/
private theorem contMDiffAt_setIntegral_of_subset_chart {m : ℕ} [IsFiniteMeasure μ]
    [IsManifold I m M] [IsManifold J m N] {U : Set M} {V : Set N} (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (hf : ContMDiffOn (I.prod J) 𝓘(𝕜, F) m (uncurry f) (U ×ˢ V))
    {b : N} {K : Set N} (hK : IsCompact K) (hKb : K ⊆ (chartAt H' b).source) (hKV : K ⊆ V)
    {s : Set N} (hs : MeasurableSet s) (hsK : s ⊆ K) :
    ContMDiffAt I 𝓘(𝕜, F) m (fun x ↦ ∫ a in s, f x a ∂μ) x₀ := by
  borelize E'
  set φ := extChartAt I x₀
  set ψ := extChartAt J b
  have hKψ : K ⊆ ψ.source := by rwa [extChartAt_source]
  have hψc : ContinuousOn ψ K := (continuousOn_extChartAt b).mono hKψ
  set k := ψ '' K
  have hk : IsCompact k := hK.image_of_continuousOn hψc
  set u := φ.target ∩ φ.symm ⁻¹' U
  have hu : IsOpen u :=
    (continuousOn_extChartAt_symm x₀).isOpen_inter_preimage (isOpen_extChartAt_target x₀) hU
  have hxu : φ x₀ ∈ u := ⟨mem_extChartAt_target x₀, by simpa [φ] using hx₀⟩
  -- In the product chart at `(x₀, b)`, the function is `C^m` on `u ×ˢ k`.
  have hΦ : ContDiffOn 𝕜 m (uncurry fun (y : E) (z : E') ↦ f (φ.symm y) (ψ.symm z)) (u ×ˢ k) := by
    have h := (contMDiffOn_iff.1 hf).2 (x₀, b) 0
    simp only [extChartAt_prod, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      PartialEquiv.prod_target, PartialEquiv.prod_symm, PartialEquiv.refl_source,
      preimage_univ, inter_univ] at h
    refine h.mono ?_
    rintro ⟨y, z⟩ ⟨⟨hy, hyU⟩, ⟨a, ha, rfl⟩⟩
    refine ⟨⟨hy, (extChartAt J b).map_source (hKψ ha)⟩, hyU, ?_⟩
    have : (extChartAt J b).symm (ψ a) = a := ψ.left_inv (hKψ ha)
    simpa only [PartialEquiv.prod_coe, this] using hKV ha
  -- Transport the integral over `s` to the pushforward measure on the model space.
  set ν := (μ.restrict s).map ψ
  have hψm : AEMeasurable ψ (μ.restrict s) := (hψc.mono hsK).aemeasurable hs
  have hνk : ν.restrict k = ν :=
    Measure.restrict_eq_self_of_ae_mem <| (ae_map_iff hψm hk.measurableSet).2 <|
      ae_restrict_of_forall_mem hs fun a ha ↦ mem_image_of_mem ψ (hsK ha)
  have heq : ∀ y ∈ u, ∫ z in k, f (φ.symm y) (ψ.symm z) ∂ν = ∫ a in s, f (φ.symm y) a ∂μ := by
    intro y hy
    have hc : ContinuousOn (fun z ↦ f (φ.symm y) (ψ.symm z)) k :=
      hΦ.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) fun z hz ↦ ⟨hy, hz⟩
    have hm : AEStronglyMeasurable (fun z ↦ f (φ.symm y) (ψ.symm z)) ν := by
      simpa only [hνk] using hc.aestronglyMeasurable_of_isCompact (μ := ν) hk hk.measurableSet
    rw [hνk, integral_map hψm hm]
    refine setIntegral_congr_fun hs fun a ha ↦ ?_
    simp only [ψ.left_inv (hKψ (hsK ha))]
  have hint : ContDiffOn 𝕜 m (fun y ↦ ∫ z in k, f (φ.symm y) (ψ.symm z) ∂ν) u :=
    ContDiffOn.parametric_integral hu hk subset_rfl (mod_cast hΦ) (measure_ne_top _ _)
  have hdiff : ContDiffAt 𝕜 m (fun y ↦ ∫ a in s, f (φ.symm y) a ∂μ) (φ x₀) :=
    (hint.contDiffAt (hu.mem_nhds hxu)).congr_of_eventuallyEq <|
      eventually_of_mem (hu.mem_nhds hxu) fun y hy ↦ (heq y hy).symm
  -- Read the coordinate statement back on `M`.
  rw [contMDiffAt_iff, I.range_eq_univ, contDiffWithinAt_univ, extChartAt_model_space_eq_id,
    PartialEquiv.refl_coe, Function.id_comp]
  refine ⟨?_, hdiff⟩
  refine (hdiff.continuousAt.comp (continuousAt_extChartAt x₀)).congr_of_eventuallyEq ?_
  filter_upwards [extChartAt_source_mem_nhds (I := I) x₀] with x hx
  simp only [comp_apply, φ.left_inv hx]

variable [T2Space N] {n : ℕ∞} [IsManifold I n M] [IsManifold J n N]

/-- **Smoothness of an integral over a compact set of parameters.** If `(x, a) ↦ f x a` is `C^n`
at every point `(x₀, a)` with `a` in a compact subset `K` of the parameter manifold, then
`x ↦ ∫ a in s, f x a ∂μ` is `C^n` at `x₀` for every subset `s ⊆ K` of finite measure. -/
theorem contMDiffAt_parametric_integral {K s : Set N} (hK : IsCompact K) (hsK : s ⊆ K)
    (hμs : μ s ≠ ⊤) (hf : ∀ a ∈ K, ContMDiffAt (I.prod J) 𝓘(𝕜, F) n (uncurry f) (x₀, a)) :
    ContMDiffAt I 𝓘(𝕜, F) n (fun x ↦ ∫ a in s, f x a ∂μ) x₀ := by
  classical
  have hKm : MeasurableSet K := hK.isClosed.measurableSet
  -- The integral over `s` is the integral over `K` against the finite measure `μ.restrict s`.
  have hres : (μ.restrict s).restrict K = μ.restrict s := by
    rw [Measure.restrict_restrict hKm, inter_eq_right.2 hsK]
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hμs
  rw [show (fun x ↦ ∫ a in s, f x a ∂μ) = fun x ↦ ∫ a in K, f x a ∂(μ.restrict s) by
    simp_rw [hres]]
  generalize μ.restrict s = ν at this ⊢
  refine contMDiffAt_iff_nat.2 fun m hm ↦ ?_
  have hm' : (m : ℕ∞ω) ≤ n := by exact_mod_cast hm
  have : IsManifold I m M := .of_le hm'
  have : IsManifold J m N := .of_le hm'
  -- A tube `U × V` around `{x₀} × K` on which `f` is `C^m`.
  obtain ⟨U, V, hU, hV, hx₀U, hKV, hfU⟩ := exists_isOpen_prod_contMDiffOn (I' := I.prod J)
    (J := 𝓘(𝕜, F)) (f := uncurry f) hK (by simp) fun a ha ↦ (hf a ha).of_le hm'
  have hint : ∀ x ∈ U, IntegrableOn (f x) K ν := fun x hx ↦
    ContinuousOn.integrableOn_compact hK <|
      hfU.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) fun a ha ↦
        ⟨hx, hKV ha⟩
  -- Cover `K` by finitely many compact sets, each inside `V` and one chart.
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun b ↦ (chartAt H' b).source ∩ V)
    (fun b ↦ (chartAt H' b).open_source.inter hV) fun a ha ↦
      mem_iUnion.2 ⟨a, mem_chart_source H' a, hKV ha⟩
  obtain ⟨L, hLc, hLs, hKL⟩ := hK.finite_compact_cover t _
    (fun b _ ↦ (chartAt H' b).open_source.inter hV) ht
  have key : ∀ t : Finset N, ∀ r, MeasurableSet r → r ⊆ K → r ⊆ ⋃ b ∈ t, L b →
      ContMDiffAt I 𝓘(𝕜, F) m (fun x ↦ ∫ a in r, f x a ∂ν) x₀ := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro r _ _ hrt
      simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, subset_empty_iff] at hrt
      simp only [hrt, Measure.restrict_empty, integral_zero_measure]
      exact contMDiffAt_const
    | insert b t _ ih =>
      intro r hr hrK hrt
      have hLm : MeasurableSet (L b) := (hLc b).isClosed.measurableSet
      have h₁ := contMDiffAt_setIntegral_of_subset_chart (μ := ν) hU hx₀U hfU (hLc b)
        (fun a ha ↦ (hLs b ha).1) (fun a ha ↦ (hLs b ha).2) (hr.inter hLm) inter_subset_right
      have h₂ := ih (r \ L b) (hr.diff hLm) (sdiff_subset.trans hrK) fun a ha ↦ by
        have := hrt ha.1
        simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left, mem_union] at this
        exact this.resolve_left ha.2
      refine (h₁.add h₂).congr_of_eventuallyEq ?_
      filter_upwards [hU.mem_nhds hx₀U] with x hx
      exact (integral_inter_add_sdiff hLm ((hint x hx).mono_set hrK)).symm
  exact key t K hKm subset_rfl hKL.subset

/-- **Smoothness of an integral over a compact set of parameters.** If `(x, a) ↦ f x a` is `C^n`,
then `x ↦ ∫ a in s, f x a ∂μ` is `C^n` for every subset `s` of finite measure contained in a
compact subset of the parameter manifold. -/
theorem _root_.ContMDiff.parametric_integral {K s : Set N} (hK : IsCompact K) (hsK : s ⊆ K)
    (hμs : μ s ≠ ⊤) (hf : ContMDiff (I.prod J) 𝓘(𝕜, F) n (uncurry f)) :
    ContMDiff I 𝓘(𝕜, F) n (fun x ↦ ∫ a in s, f x a ∂μ) := fun _ ↦
  contMDiffAt_parametric_integral hK hsK hμs fun _ _ ↦ hf _

variable [CompactSpace N] [IsFiniteMeasure μ]

/-- **Smoothness of an integral over a compact manifold of parameters.** If `(x, a) ↦ f x a` is
`C^n` at every point `(x₀, a)`, with the parameter `a` ranging over a compact manifold carrying a
finite measure `μ`, then `x ↦ ∫ a, f x a ∂μ` is `C^n` at `x₀`. -/
theorem contMDiffAt_parametric_integral_of_compactSpace
    (hf : ∀ a, ContMDiffAt (I.prod J) 𝓘(𝕜, F) n (uncurry f) (x₀, a)) :
    ContMDiffAt I 𝓘(𝕜, F) n (fun x ↦ ∫ a, f x a ∂μ) x₀ := by
  simpa using contMDiffAt_parametric_integral (μ := μ) isCompact_univ subset_rfl
    (measure_ne_top μ univ) fun a _ ↦ hf a

/-- **Smoothness of an integral over a compact manifold of parameters.** If `(x, a) ↦ f x a` is
`C^n`, with the parameter `a` ranging over a compact manifold carrying a finite measure `μ`, then
`x ↦ ∫ a, f x a ∂μ` is `C^n`. -/
theorem _root_.ContMDiff.parametric_integral_of_compactSpace
    (hf : ContMDiff (I.prod J) 𝓘(𝕜, F) n (uncurry f)) :
    ContMDiff I 𝓘(𝕜, F) n (fun x ↦ ∫ a, f x a ∂μ) := fun _ ↦
  contMDiffAt_parametric_integral_of_compactSpace fun _ ↦ hf _

end TauCeti
