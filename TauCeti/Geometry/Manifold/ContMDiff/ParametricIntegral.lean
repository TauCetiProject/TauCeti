/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.DifferentialForm.Basic
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Geometry.Manifold.Algebra.Monoid
public import Mathlib.MeasureTheory.Function.LocallyIntegrable
public import TauCeti.Geometry.Manifold.ContMDiff.Prod
import TauCeti.Geometry.Manifold.ContMDiff.MFDeriv

/-!
# Integrals over a compact manifold of parameters

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

The manifold `M` is assumed boundaryless, so that its chart targets are open in the model space.
The parameter manifold `N` may have boundary and corners.

The derivative itself can be taken under the integral sign. If `(z, a) ↦ g z a` is `C¹` on
`u × N` for an open subset `u` of a normed space, its derivative in `z` is jointly continuous
there (`TauCeti.continuousOn_fderiv_of_contMDiffOn`), and Mathlib's
`hasFDerivAt_integral_of_continuousOn_fderiv` computes the derivative of `z ↦ ∫ a, g z a ∂μ` as
the integral of the derivatives (`TauCeti.hasFDerivAt_integral_of_contMDiffOn`). Since the flat
exterior derivative `extDeriv` is the alternation of the derivative, a continuous linear
operation, the same holds for it (`TauCeti.extDeriv_integral_of_contMDiffOn`).
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
  {μ : Measure N} [IsFiniteMeasure μ]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  {f : M → N → F} {x₀ : M}

/-- The integral of a `C^m` function over a measurable set of parameters contained in a compact
subset of one chart of the parameter manifold is `C^m` at `x₀`, provided the function is `C^m`
on `U × N` for an open neighbourhood `U` of `x₀`. -/
private theorem contMDiffAt_setIntegral_of_subset_chart {m : ℕ} [IsManifold I m M]
    [IsManifold J m N] {U : Set M} (hU : IsOpen U) (hx₀ : x₀ ∈ U)
    (hf : ContMDiffOn (I.prod J) 𝓘(ℝ, F) m (uncurry f) (U ×ˢ univ))
    {b : N} {K : Set N} (hK : IsCompact K) (hKb : K ⊆ (chartAt H' b).source)
    {s : Set N} (hs : MeasurableSet s) (hsK : s ⊆ K) :
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
    exact ⟨⟨hy, (extChartAt J b).map_source (hKψ ha)⟩, hyU, mem_univ _⟩
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

variable [CompactSpace N] [T2Space N] {n : ℕ∞} [IsManifold I n M] [IsManifold J n N]

/-- **Smoothness of an integral over a compact manifold of parameters.** If `(x, a) ↦ f x a` is
`C^n` at every point `(x₀, a)`, with the parameter `a` ranging over a compact manifold carrying a
finite measure `μ`, then `x ↦ ∫ a, f x a ∂μ` is `C^n` at `x₀`. -/
theorem contMDiffAt_parametric_integral
    (hf : ∀ a, ContMDiffAt (I.prod J) 𝓘(ℝ, F) n (uncurry f) (x₀, a)) :
    ContMDiffAt I 𝓘(ℝ, F) n (fun x ↦ ∫ a, f x a ∂μ) x₀ := by
  classical
  refine contMDiffAt_iff_nat.2 fun m hm ↦ ?_
  have hm' : (m : ℕ∞ω) ≤ n := by exact_mod_cast hm
  have : IsManifold I m M := .of_le hm'
  have : IsManifold J m N := .of_le hm'
  -- A tube `U × N` on which `f` is `C^m`.
  obtain ⟨U, V, hU, -, hx₀U, hV, hfU⟩ := exists_isOpen_prod_contMDiffOn (I' := I.prod J)
    (J := 𝓘(ℝ, F)) (f := uncurry f) isCompact_univ (by simp)
    fun a _ ↦ (hf a).of_le hm'
  rw [univ_subset_iff.1 hV] at hfU
  have hint : ∀ x ∈ U, Integrable (f x) μ := fun x hx ↦
    integrableOn_univ.1 <| ContinuousOn.integrableOn_compact isCompact_univ <|
      hfU.continuousOn.comp (continuousOn_const.prodMk continuousOn_id) fun a _ ↦
        ⟨hx, mem_univ a⟩
  -- Cover the parameter space by finitely many compact sets, each inside one chart.
  choose K hKc hbK hKs using fun b : N ↦
    exists_compact_subset (chartAt H' b).open_source (mem_chart_source H' b)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun b ↦ interior (K b))
    (fun _ ↦ isOpen_interior) fun b _ ↦ mem_iUnion.2 ⟨b, hbK b⟩
  have key : ∀ t : Finset N, ∀ s, MeasurableSet s → s ⊆ ⋃ b ∈ t, K b →
      ContMDiffAt I 𝓘(ℝ, F) m (fun x ↦ ∫ a in s, f x a ∂μ) x₀ := by
    intro t
    induction t using Finset.induction_on with
    | empty =>
      intro s _ hst
      simp only [Finset.notMem_empty, iUnion_of_empty, iUnion_empty, subset_empty_iff] at hst
      simp only [hst, Measure.restrict_empty, integral_zero_measure]
      exact contMDiffAt_const
    | insert b t _ ih =>
      intro s hs hst
      have hKm : MeasurableSet (K b) := (hKc b).isClosed.measurableSet
      have h₁ := contMDiffAt_setIntegral_of_subset_chart (μ := μ) hU hx₀U hfU (hKc b) (hKs b)
        (hs.inter hKm) inter_subset_right
      have h₂ := ih (s \ K b) (hs.diff hKm) fun a ha ↦ by
        have := hst ha.1
        simp only [Finset.mem_insert, iUnion_iUnion_eq_or_left, mem_union] at this
        exact this.resolve_left ha.2
      refine (h₁.add h₂).congr_of_eventuallyEq ?_
      filter_upwards [hU.mem_nhds hx₀U] with x hx
      exact (integral_inter_add_sdiff hKm (hint x hx).integrableOn).symm
  simpa using key t univ MeasurableSet.univ fun a _ ↦ by
    obtain ⟨b, hb, hab⟩ := mem_iUnion₂.1 (ht (mem_univ a))
    exact mem_iUnion₂.2 ⟨b, hb, interior_subset hab⟩

/-- **Smoothness of an integral over a compact manifold of parameters.** If `(x, a) ↦ f x a` is
`C^n`, with the parameter `a` ranging over a compact manifold carrying a finite measure `μ`, then
`x ↦ ∫ a, f x a ∂μ` is `C^n`. -/
theorem _root_.ContMDiff.parametric_integral
    (hf : ContMDiff (I.prod J) 𝓘(ℝ, F) n (uncurry f)) :
    ContMDiff I 𝓘(ℝ, F) n (fun x ↦ ∫ a, f x a ∂μ) := fun _ ↦
  contMDiffAt_parametric_integral fun _ ↦ hf _

/-! ### Differentiation under the integral sign -/

section Deriv

-- Cache the canonical alternating-map instances: instance search for the measure-theoretic
-- structure on the nested operator space `E →L[ℝ] E [⋀^Fin k]→L[ℝ] F` otherwise fails.
private noncomputable local instance {k : ℕ} : NormedAddCommGroup (E [⋀^Fin k]→L[ℝ] F) :=
  ContinuousAlternatingMap.instNormedAddCommGroup
private noncomputable local instance {k : ℕ} : NormedSpace ℝ (E [⋀^Fin k]→L[ℝ] F) :=
  ContinuousAlternatingMap.instNormedSpace

variable [IsManifold J 1 N] {g : E → N → F} {u : Set E} {z₀ : E}

omit [I.Boundaryless] [MeasurableSpace N] [OpensMeasurableSpace N] [CompactSpace N] [T2Space N] in
/-- The derivative in the first variable of a function on `E × N` that is `C¹` on `u × N`, for an
open set `u`, is jointly continuous on `u × N`. -/
theorem continuousOn_fderiv_of_contMDiffOn (hu : IsOpen u)
    (hg : ContMDiffOn (𝓘(ℝ, E).prod J) 𝓘(ℝ, F) 1 (uncurry g) (u ×ˢ univ)) :
    ContinuousOn (fun p : E × N ↦ fderiv ℝ (fun z ↦ g z p.2) p.1) (u ×ˢ univ) := by
  intro p hp
  have hg' : ContMDiffAt (J.prod 𝓘(ℝ, E)) 𝓘(ℝ, F) 1 (uncurry fun (a : N) (z : E) ↦ g z a)
      p.swap :=
    (hg.contMDiffAt ((hu.prod isOpen_univ).mem_nhds hp)).comp p.swap
      (contMDiffAt_snd.prodMk contMDiffAt_fst)
  have h := (hg'.fderiv_right (n := 0) (by norm_num)).continuousAt.comp
    continuous_swap.continuousAt
  exact h.continuousWithinAt

omit [I.Boundaryless] [T2Space N] in
/-- **Differentiation under the integral sign over a compact manifold of parameters.** If
`(z, a) ↦ g z a` is `C¹` on `u × N` for an open set `u ∋ z₀`, with the parameter `a` ranging over a
compact manifold carrying a finite measure `μ`, then the derivative of `z ↦ ∫ a, g z a ∂μ` at `z₀`
is the integral of the derivatives of the functions `z ↦ g z a`. -/
theorem hasFDerivAt_integral_of_contMDiffOn (hu : IsOpen u) (hz₀ : z₀ ∈ u)
    (hg : ContMDiffOn (𝓘(ℝ, E).prod J) 𝓘(ℝ, F) 1 (uncurry g) (u ×ˢ univ)) :
    HasFDerivAt (fun z ↦ ∫ a, g z a ∂μ) (∫ a, fderiv ℝ (fun z ↦ g z a) z₀ ∂μ) z₀ := by
  have hdiff (a : N) : DifferentiableOn ℝ (fun z ↦ g z a) u := by
    have h : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ, F) 1 (fun z ↦ g z a) u :=
      hg.comp (contMDiffOn_id.prodMk contMDiffOn_const) fun z hz ↦ ⟨hz, mem_univ a⟩
    exact (contMDiffOn_iff_contDiffOn.1 h).differentiableOn one_ne_zero
  simpa only [Measure.restrict_univ] using
    hasFDerivAt_integral_of_continuousOn_fderiv (μ := μ) (hu.mem_nhds hz₀) isCompact_univ
      MeasurableSet.univ (measure_ne_top μ univ) subset_rfl hg.continuousOn
      (fun a _ ↦ hdiff a) (continuousOn_fderiv_of_contMDiffOn hu hg)

omit [I.Boundaryless] [T2Space N] in
/-- **Exterior derivative under the integral sign.** For a family of flat differential forms
`φ · a` on a normed space, depending on a parameter `a` in a compact manifold carrying a finite
measure `μ`, and jointly `C¹` in the point and the parameter on `u × N` for an open set `u ∋ z₀`,
the exterior derivative of `z ↦ ∫ a, φ z a ∂μ` at `z₀` is the integral of the exterior derivatives
of the forms `φ · a`. -/
theorem extDeriv_integral_of_contMDiffOn [CompleteSpace F] {k : ℕ}
    {φ : E → N → E [⋀^Fin k]→L[ℝ] F} (hu : IsOpen u) (hz₀ : z₀ ∈ u)
    (hφ : ContMDiffOn (𝓘(ℝ, E).prod J) 𝓘(ℝ, E [⋀^Fin k]→L[ℝ] F) 1 (uncurry φ) (u ×ˢ univ)) :
    extDeriv (fun z ↦ ∫ a, φ z a ∂μ) z₀ = ∫ a, extDeriv (fun z ↦ φ z a) z₀ ∂μ := by
  have hint : Integrable (fun a ↦ fderiv ℝ (fun z ↦ φ z a) z₀) μ :=
    integrableOn_univ.1 <| ContinuousOn.integrableOn_compact' isCompact_univ MeasurableSet.univ <|
      (continuousOn_fderiv_of_contMDiffOn hu hφ).comp (continuousOn_const.prodMk continuousOn_id)
        fun a _ ↦ ⟨hz₀, mem_univ a⟩
  simp only [extDeriv, (hasFDerivAt_integral_of_contMDiffOn hu hz₀ hφ).fderiv,
    ← ContinuousAlternatingMap.alternatizeUncurryFinCLM_apply]
  exact (ContinuousLinearMap.integral_comp_comm
    (ContinuousAlternatingMap.alternatizeUncurryFinCLM ℝ E F) hint).symm

end Deriv

end TauCeti
