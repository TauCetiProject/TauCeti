/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Geometry.Manifold.Algebra.LieGroup
public import Mathlib.Geometry.Manifold.Algebra.Monoid
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import TauCeti.Geometry.Manifold.ContMDiff.Prod

/-!
# Integrals over a manifold of parameters

Let `f : M → N → F` be a function of a point of a manifold `M` and of a parameter in a compact
manifold `N`, with values in a real normed space, and let `μ` be a finite measure on `N`. If
`(x, a) ↦ f x a` is `C^n`, then so is the averaged function

`x ↦ ∫ a, f x a ∂μ`.

This is the manifold counterpart of Mathlib's `ContDiff.parametric_integral`, where the
parameter ranges over a compact subset of a normed space. The typical use is averaging over a
compact Lie group with its Haar measure, for instance to produce invariant Riemannian metrics.

The proof is local. For `n` finite, the tube lemma `TauCeti.exists_isOpen_prod_contMDiffOn` makes
`f` a `C^n` map on `U × N` for an open neighbourhood `U` of the base point. The parameter space is
covered by finitely many compact sets each contained in one chart. On such a compact set `K`, the
chart `ψ` of `N` transports the integral over a measurable subset `s ⊆ K` to the integral, against
the pushforward of `μ` restricted to `s`, of a function that is `C^n` on the product of an open set
and the compact set `ψ '' K` of the model spaces. Mathlib's `ContDiffOn.parametric_integral`
applies there. Integrals over the finitely many pieces are then added up by induction on the
cover.

The same argument applies when the parameter manifold is not compact but `f x` vanishes outside a
fixed compact set `K` for all `x` near the base point, and `μ K` is finite
(`IsCompact.contMDiffAt_parametric_integral`), and to the integral over a compact set `K` of
finite measure (`IsCompact.contMDiffAt_parametric_setIntegral`). In particular a `C^n` function
`(x, a) ↦ f x a` with compact support has `C^n` integral against a measure that is finite on
compact sets (`ContMDiff.parametric_integral_of_hasCompactSupport`).

The manifold `M` is assumed boundaryless, so that its chart targets are open in the model space.
The parameter manifold `N` may have boundary and corners.

Differentiation under the integral sign is in
`TauCeti.Geometry.Manifold.ContMDiff.ParametricIntegral.Deriv`.
-/

public section

open Set Filter MeasureTheory Function
open scoped Topology ContDiff Manifold

namespace TauCeti

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  {H' : Type*} [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'}
  {N : Type*} [TopologicalSpace N] [ChartedSpace H' N] [MeasurableSpace N] [OpensMeasurableSpace N]
  {μ : Measure N}
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : M → N → F} {x₀ : M}

/-- The integral of a `C^m` function over a measurable set of parameters contained in a compact
subset of one chart of the parameter manifold is `C^m` at `x₀`, provided the function is `C^m`
on `U × V` for an open neighbourhood `U` of `x₀` and a set `V` containing that compact subset. -/
private theorem contMDiffAt_setIntegral_of_subset_chart {m : ℕ} [IsManifold I m M]
    [IsManifold J m N] {U : Set M} {V : Set N} (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (hf : ContMDiffOn (I.prod J) 𝓘(ℝ, F) m (uncurry f) (U ×ˢ V))
    {b : N} {K : Set N} (hK : IsCompact K) (hKb : K ⊆ (chartAt H' b).source) (hKV : K ⊆ V)
    {s : Set N} (hs : MeasurableSet s) (hsK : s ⊆ K) (hμs : μ s ≠ ⊤) :
    ContMDiffAt I 𝓘(ℝ, F) m (fun x ↦ ∫ a in s, f x a ∂μ) x₀ := by
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
  have hΦ : ContDiffOn ℝ m (uncurry fun (y : E) (z : E') ↦ f (φ.symm y) (ψ.symm z)) (u ×ˢ k) := by
    have h := (contMDiffOn_iff.1 hf).2 (x₀, b) 0
    simp only [extChartAt_prod, extChartAt_model_space_eq_id, PartialEquiv.refl_coe,
      PartialEquiv.prod_target, PartialEquiv.prod_symm, PartialEquiv.refl_source,
      preimage_univ, inter_univ] at h
    refine h.mono ?_
    rintro ⟨y, z⟩ ⟨⟨hy, hyU⟩, ⟨a, ha, rfl⟩⟩
    exact ⟨⟨hy, (extChartAt J b).map_source (hKψ ha)⟩, hyU, by
      simp only [PartialEquiv.prod_coe]; rw [ψ.left_inv (hKψ ha)]; exact hKV ha⟩
  -- Transport the integral over `s` to the pushforward measure on the model space.
  set ν := (μ.restrict s).map ψ
  have : IsFiniteMeasure (μ.restrict s) := isFiniteMeasure_restrict.2 hμs
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
  have hint : ContDiffOn ℝ m (fun y ↦ ∫ z in k, f (φ.symm y) (ψ.symm z) ∂ν) u :=
    ContDiffOn.parametric_integral hu hk subset_rfl (mod_cast hΦ) (measure_ne_top _ _)
  have hdiff : ContDiffAt ℝ m (fun y ↦ ∫ a in s, f (φ.symm y) a ∂μ) (φ x₀) :=
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

/-- **Smoothness of an integral over a compact set of parameters.** Let `K` be a compact set of
parameters with `μ K < ∞`. If `(x, a) ↦ f x a` is `C^n` at every point `(x₀, a)` with `a ∈ K`,
then `x ↦ ∫ a in K, f x a ∂μ` is `C^n` at `x₀`. -/
theorem _root_.IsCompact.contMDiffAt_parametric_setIntegral {K : Set N} (hK : IsCompact K)
    (hμK : μ K ≠ ⊤) (hf : ∀ a ∈ K, ContMDiffAt (I.prod J) 𝓘(ℝ, F) n (uncurry f) (x₀, a)) :
    ContMDiffAt I 𝓘(ℝ, F) n (fun x ↦ ∫ a in K, f x a ∂μ) x₀ := by
  classical
  refine contMDiffAt_iff_nat.2 fun m hm ↦ ?_
  have hm' : (m : ℕ∞ω) ≤ n := by exact_mod_cast hm
  have : IsManifold I m M := .of_le hm'
  have : IsManifold J m N := .of_le hm'
  -- A tube `U × V` around `{x₀} × K` on which `f` is `C^m`.
  obtain ⟨U, V, hU, -, hx₀U, hKV, hfU⟩ := exists_isOpen_prod_contMDiffOn (I' := I.prod J)
    (J := 𝓘(ℝ, F)) (f := uncurry f) hK (by simp) fun a ha ↦ (hf a ha).of_le hm'
  have : IsFiniteMeasure (μ.restrict K) := isFiniteMeasure_restrict.2 hμK
  have hint : ∀ x ∈ U, IntegrableOn (f x) K μ := fun x hx ↦ by
    rw [IntegrableOn, ← Measure.restrict_restrict_of_subset subset_rfl]
    exact ContinuousOn.integrableOn_compact hK <|
      hfU.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) fun a ha ↦
        ⟨hx, hKV ha⟩
  -- Cover `K` by finitely many compact sets, each inside one chart.
  obtain ⟨t, ht⟩ := hK.elim_finite_subcover (fun b : N ↦ (chartAt H' b).source)
    (fun b ↦ (chartAt H' b).open_source) fun a _ ↦ mem_iUnion.2 ⟨a, mem_chart_source H' a⟩
  obtain ⟨L, hLc, hLs, hKL⟩ := hK.finite_compact_cover t (fun b : N ↦ (chartAt H' b).source)
    (fun b _ ↦ (chartAt H' b).open_source) ht
  have key : ∀ t : Finset N, ∀ s, MeasurableSet s → s ⊆ K → s ⊆ ⋃ b ∈ t, L b →
      ContMDiffAt I 𝓘(ℝ, F) m (fun x ↦ ∫ a in s, f x a ∂μ) x₀ := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro s _ _ hst
      simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, subset_empty_iff] at hst
      simp only [hst, Measure.restrict_empty, integral_zero_measure]
      exact contMDiffAt_const
    | insert b t _ ih =>
      intro s hs hsK hst
      have hLm : MeasurableSet (L b) := (hLc b).isClosed.measurableSet
      have h₁ := contMDiffAt_setIntegral_of_subset_chart (μ := μ) hU hx₀U hfU
        ((hLc b).inter hK) (inter_subset_left.trans (hLs b)) (inter_subset_right.trans hKV)
        (hs.inter hLm) (fun a ha ↦ ⟨ha.2, hsK ha.1⟩)
        (ne_top_of_le_ne_top hμK (measure_mono fun a ha ↦ hsK ha.1))
      have h₂ := ih (s \ L b) (hs.diff hLm) (sdiff_subset.trans hsK) fun a ha ↦ by
        have := hst ha.1
        simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left, mem_union] at this
        exact this.resolve_left ha.2
      refine (h₁.add h₂).congr_of_eventuallyEq ?_
      filter_upwards [hU.mem_nhds hx₀U] with x hx
      exact (integral_inter_add_sdiff hLm ((hint x hx).mono_set hsK)).symm
  exact key t K hK.measurableSet subset_rfl hKL.subset

/-- **Smoothness of an integral with compact support in the parameter.** Let `K` be a compact set
of parameters with `μ K < ∞` such that, for `x` near `x₀`, the function `f x` vanishes outside
`K`. If `(x, a) ↦ f x a` is `C^n` at every point `(x₀, a)` with `a ∈ K`, then
`x ↦ ∫ a, f x a ∂μ` is `C^n` at `x₀`. -/
theorem _root_.IsCompact.contMDiffAt_parametric_integral {K : Set N} (hK : IsCompact K)
    (hμK : μ K ≠ ⊤) (hf : ∀ a ∈ K, ContMDiffAt (I.prod J) 𝓘(ℝ, F) n (uncurry f) (x₀, a))
    (hfK : ∀ᶠ x in 𝓝 x₀, ∀ a ∉ K, f x a = 0) :
    ContMDiffAt I 𝓘(ℝ, F) n (fun x ↦ ∫ a, f x a ∂μ) x₀ := by
  refine (hK.contMDiffAt_parametric_setIntegral hμK hf).congr_of_eventuallyEq ?_
  filter_upwards [hfK] with x hx
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero hx).symm

/-- **Smoothness of the integral of a compactly supported function.** If `(x, a) ↦ f x a` is `C^n`
and compactly supported, and `μ` is finite on compact sets, then `x ↦ ∫ a, f x a ∂μ` is `C^n`:
every `f x` vanishes off the second projection of the support, a compact set of finite measure. -/
theorem _root_.ContMDiff.parametric_integral_of_hasCompactSupport [IsFiniteMeasureOnCompacts μ]
    (hf : ContMDiff (I.prod J) 𝓘(ℝ, F) n (uncurry f)) (hfc : HasCompactSupport (uncurry f)) :
    ContMDiff I 𝓘(ℝ, F) n (fun x ↦ ∫ a, f x a ∂μ) := fun _ ↦
  (hfc.isCompact.image continuous_snd).contMDiffAt_parametric_integral
    (hfc.isCompact.image continuous_snd).measure_lt_top.ne (fun _ _ ↦ hf _)
    (.of_forall fun x a ha ↦ image_eq_zero_of_notMem_tsupport (f := uncurry f) (x := (x, a))
      fun h ↦ ha ⟨(x, a), h, rfl⟩)

/-- **Smoothness of an integral over a compact manifold of parameters.** If `(x, a) ↦ f x a` is
`C^n` at every point `(x₀, a)`, with the parameter `a` ranging over a compact manifold carrying a
finite measure `μ`, then `x ↦ ∫ a, f x a ∂μ` is `C^n` at `x₀`. -/
theorem contMDiffAt_parametric_integral [CompactSpace N] [IsFiniteMeasure μ]
    (hf : ∀ a, ContMDiffAt (I.prod J) 𝓘(ℝ, F) n (uncurry f) (x₀, a)) :
    ContMDiffAt I 𝓘(ℝ, F) n (fun x ↦ ∫ a, f x a ∂μ) x₀ :=
  isCompact_univ.contMDiffAt_parametric_integral (measure_ne_top μ univ) (fun a _ ↦ hf a)
    (.of_forall fun _ a ha ↦ (ha (mem_univ a)).elim)

/-- **Smoothness of an integral over a compact manifold of parameters.** If `(x, a) ↦ f x a` is
`C^n`, with the parameter `a` ranging over a compact manifold carrying a finite measure `μ`, then
`x ↦ ∫ a, f x a ∂μ` is `C^n`. -/
theorem _root_.ContMDiff.parametric_integral [CompactSpace N] [IsFiniteMeasure μ]
    (hf : ContMDiff (I.prod J) 𝓘(ℝ, F) n (uncurry f)) :
    ContMDiff I 𝓘(ℝ, F) n (fun x ↦ ∫ a, f x a ∂μ) := fun _ ↦
  contMDiffAt_parametric_integral fun _ ↦ hf _

end TauCeti
