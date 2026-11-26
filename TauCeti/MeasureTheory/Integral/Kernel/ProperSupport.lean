/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.ContDiff.Defs
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import TauCeti.Topology.Maps.Proper.KernelSupport
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.Calculus.ParametricIntegral.Basic

/-!
# Integral operators with properly supported kernels

This file develops the mapping, regularity, and transposition properties of integral operators
`(T_K u)(x) = ∫ y, K x y (u y) ∂μ` whose operator-valued kernel `K : X → Y → V →L[𝕜] W` has
one-sided proper support:

* **Proper output support** preserves compact support
  (`TauCeti.HasProperOutputSupport.hasCompactSupport_integral`) without smoothness or separation.
* **Proper input support** of a `C^n` kernel sends every continuous `u` to a `C^n` function when
  `μ` is finite on compact subsets (`TauCeti.HasProperInputSupport.contDiff_integral`).
* **Transposition**: when `W` is complete and `μ`, `ν` are finite on compact subsets, proper
  input support pairs compactly supported continuous `v` with arbitrary continuous `u`
  (`TauCeti.HasProperInputSupport.integral_apply_integral_swap`), and proper output support pairs
  compactly supported continuous `u` with arbitrary continuous `v`
  (`TauCeti.HasProperOutputSupport.integral_apply_integral_swap`).

## Main declarations

* `TauCeti.HasProperOutputSupport.hasCompactSupport_integral`.
* `TauCeti.HasProperInputSupport.contDiff_integral`.
* `TauCeti.HasProperInputSupport.hasCompactSupport_integral_comp`.
* `TauCeti.HasProperInputSupport.integral_apply_integral_swap`,
  `TauCeti.HasProperOutputSupport.integral_apply_integral_swap`.
-/

public section

open Filter Function MeasureTheory Set
open scoped ContDiff Topology

namespace TauCeti

/-- **Proper output support preserves compact support.** For any binary operator kernel
`K : X → Y → V →L[𝕜] W` with proper output support, the integral operator
`u ↦ (x ↦ ∫ y, K x y (u y) ∂μ)` maps compactly supported functions to compactly supported
functions. No smoothness or separation axiom is needed. -/
theorem HasProperOutputSupport.hasCompactSupport_integral {X Y 𝕜 V W : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [MeasurableSpace Y] [Semiring 𝕜] [AddCommMonoid V]
    [Module 𝕜 V] [TopologicalSpace V] [NormedAddCommGroup W] [NormedSpace ℝ W] [Module 𝕜 W]
    {K : X → Y → V →L[𝕜] W} (hK : HasProperOutputSupport K) {u : Y → V}
    (hu : HasCompactSupport u) (μ : Measure Y := by volume_tac) :
    HasCompactSupport fun x ↦ ∫ y, K x y (u y) ∂μ := by
  obtain ⟨C, hC, hCc, hCK⟩ := hK.exists_isCompact_isClosed_forall_eq_zero hu
  refine HasCompactSupport.intro' hC hCc fun x hx ↦ ?_
  have hzero : (fun y ↦ K x y (u y)) = 0 := funext fun y ↦ by
    by_cases hy : y ∈ tsupport u
    · simp [hCK x hx y hy]
    · simp [image_eq_zero_of_notMem_tsupport hy]
  simp [hzero]

private theorem exists_open_isCompact_forall_eq_zero {X Y M : Type*} [TopologicalSpace X]
    [NormedAddCommGroup Y] [TopologicalSpace M] [Zero M] [T1Space M]
    {K : X → Y → M} (hK : HasProperInputSupport K) (hKc : Continuous (uncurry K))
    {x₁ : X} {y₁ : Y} (hne : K x₁ y₁ ≠ 0) (x₀ : X) :
    ∃ (U : Set X) (L : Set Y), IsOpen U ∧ x₀ ∈ U ∧ IsCompact L ∧
      ∀ x ∈ U, ∀ y ∉ L, K x y = 0 := by
  obtain ⟨L₁, hL₁, hL₁c, hKL₁⟩ :=
    hK.exists_isCompact_isClosed_forall_eq_zero (isCompact_singleton (x := x₁))
  have hc₁ : HasCompactSupport fun y ↦ K x₁ y :=
    HasCompactSupport.intro' hL₁ hL₁c fun y hy ↦ hKL₁ x₁ rfl y hy
  have hcont₁ : Continuous fun y ↦ K x₁ y := hKc.comp (continuous_const.prodMk continuous_id)
  have : LocallyCompactSpace Y :=
    (hc₁.eq_zero_or_locallyCompactSpace_of_addGroup hcont₁).resolve_left
      fun h0 ↦ hne (congrFun h0 y₁)
  let S := tsupport (uncurry K)
  have hKp := hasProperInputSupport_iff_isProperMap.mp hK
  obtain ⟨L, hL, hFL⟩ := exists_compact_superset
    ((hKp.isCompact_preimage (isCompact_singleton (x := x₀))).image
      (continuous_snd.comp continuous_subtypeVal))
  let Z : Set S := (fun p : S ↦ p.val.2) ⁻¹' (interior L)ᶜ
  have hZc : IsClosed Z :=
    isOpen_interior.isClosed_compl.preimage (continuous_snd.comp continuous_subtypeVal)
  refine ⟨((fun p : S ↦ p.val.1) '' Z)ᶜ, L, (hKp.isClosedMap Z hZc).isOpen_compl,
    fun ⟨p, hpZ, hp1⟩ ↦ hpZ (hFL ⟨p, hp1, rfl⟩), hL, fun x hxU y hyL ↦ ?_⟩
  exact image_eq_zero_of_notMem_tsupport (f := uncurry K) fun hmem ↦
    hxU ⟨⟨(x, y), hmem⟩, fun hy_int ↦ hyL (interior_subset hy_int), rfl⟩

/-- **Proper input support gives smoothness on arbitrary continuous inputs.** If `K` is `C^n` on
`X × Y` and has proper input support, where `μ` is finite on compact subsets of `Y`, then
`x ↦ ∫ y, K x y (u y) ∂μ` is `C^n` for every continuous `u : Y → V` (with no support assumption on
`u` and no finite-dimensionality assumption on `X` or `Y`). -/
theorem HasProperInputSupport.contDiff_integral {X Y 𝕜 V W : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [MeasurableSpace Y] [OpensMeasurableSpace Y] [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedSpace 𝕜 V] [IsScalarTower ℝ 𝕜 V]
    [NormedAddCommGroup W] [NormedSpace ℝ W] [NormedSpace 𝕜 W] [IsScalarTower ℝ 𝕜 W]
    {n : ℕ∞} {K : X → Y → V →L[𝕜] W} (hK : HasProperInputSupport K)
    (hK_diff : ContDiff ℝ n (uncurry K)) {u : Y → V} (hu : Continuous u)
    (μ : Measure Y := by volume_tac) [IsFiniteMeasureOnCompacts μ] :
    ContDiff ℝ n fun x ↦ ∫ y, K x y (u y) ∂μ := by
  by_cases hne : ∃ x₁ y₁, K x₁ y₁ ≠ 0
  · obtain ⟨x₁, y₁, hne⟩ := hne
    refine contDiff_iff_contDiffAt.2 fun x₀ ↦ ?_
    obtain ⟨U, L, hUo, hx₀U, hL, hKL⟩ :=
      exists_open_isCompact_forall_eq_zero hK hK_diff.continuous hne x₀
    have : CompactSpace L := isCompact_iff_compactSpace.mp hL
    have hmeasL : MeasurableSet L := hL.isClosed.measurableSet
    let μL : Measure L := μ.comap Subtype.val
    have : IsFiniteMeasure μL := ⟨by
      rw [(MeasurableEmbedding.subtypeVal hmeasL).comap_apply, image_univ, Subtype.range_coe]
      exact hL.measure_lt_top⟩
    have hF : ContDiff ℝ n fun q : X × (Y × V) ↦ (K q.1 q.2.1) q.2.2 :=
      ((ContinuousLinearMap.restrictScalarsL 𝕜 V W ℝ ℝ).contDiff.comp
        (hK_diff.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd)))).clm_apply
          (contDiff_snd.comp contDiff_snd)
    have hon := contDiffOn_integral_smul_of_contDiffOn (μ := μL) (g := fun _ : L ↦ (1 : ℝ))
      (ι := fun y : L ↦ (y.val, u y.val)) (W := univ) (U := U)
      (integrable_const 1) (continuous_subtypeVal.prodMk (hu.comp continuous_subtypeVal))
      isOpen_univ hF.contDiffOn (fun _ _ _ ↦ mem_univ _)
    refine (hon.contDiffAt (hUo.mem_nhds hx₀U)).congr_of_eventuallyEq ?_
    filter_upwards [hUo.mem_nhds hx₀U] with x hx
    simp only [one_smul]
    rw [integral_subtype_comap hmeasL (fun y ↦ K x y (u y)),
      setIntegral_eq_integral_of_forall_compl_eq_zero fun y hy ↦ by simp [hKL x hx y hy]]
  · push Not at hne
    have h0 : (fun x ↦ ∫ y, K x y (u y) ∂μ) = 0 := funext fun x ↦ by simp [hne x]
    exact h0 ▸ contDiff_const

/-- When `K` has proper input support and `v : X → W →L[𝕜] M` has compact support, the transposed
operator `y ↦ ∫ x, (v x).comp (K x y) ∂μ` has compact support. -/
theorem HasProperInputSupport.hasCompactSupport_integral_comp {X Y 𝕜 V W M : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [TopologicalSpace Y] [NontriviallyNormedField 𝕜]
    [NormedAlgebra ℝ 𝕜] [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W]
    [NormedSpace 𝕜 W] [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedSpace 𝕜 M]
    [IsScalarTower ℝ 𝕜 M] {K : X → Y → V →L[𝕜] W} (hK : HasProperInputSupport K)
    {v : X → W →L[𝕜] M} (hv : HasCompactSupport v) (μ : Measure X := by volume_tac) :
    HasCompactSupport fun y ↦ ∫ x, (v x).comp (K x y) ∂μ := by
  let L := (ContinuousLinearMap.compL 𝕜 V W M).flip
  have hK' : HasProperOutputSupport fun y x ↦ L (K x y) :=
    hK.flip.of_tsupport_subset (tsupport_comp_subset (map_zero L) (uncurry (_root_.flip K)))
  exact hK'.hasCompactSupport_integral hv μ

private theorem integral_apply_integral_swap_of_isCompact_isClosed {X Y 𝕜 V W M : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace 𝕜 W] [IsScalarTower ℝ 𝕜 W] [CompleteSpace W]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedSpace 𝕜 M] [IsScalarTower ℝ 𝕜 M]
    {K : X → Y → V →L[𝕜] W} (hKc : Continuous (uncurry K)) {u : Y → V} (hu : Continuous u)
    {v : X → W →L[𝕜] M} (hv : Continuous v) (μ : Measure X) (ν : Measure Y)
    [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] {C : Set X} {L : Set Y}
    (hC : IsCompact C) (hCc : IsClosed C) (hL : IsCompact L) (hLc : IsClosed L)
    (hx_out : ∀ x ∉ C, v x = 0 ∨ ∀ y, K x y (u y) = 0)
    (hy_in : ∀ x ∈ C, ∀ y ∉ L, v x = 0 ∨ K x y (u y) = 0)
    (hy_out : ∀ y ∉ L, u y = 0 ∨ ∀ x, (v x).comp (K x y) = 0)
    (hx_in : ∀ y ∈ L, ∀ x ∉ C, u y = 0 ∨ (v x).comp (K x y) = 0) :
    (∫ x, v x (∫ y, K x y (u y) ∂ν) ∂μ) = ∫ y, (∫ x, (v x).comp (K x y) ∂μ) (u y) ∂ν := by
  by_cases hM : CompleteSpace M; swap
  · simp [integral_of_not_completeSpace hM]
  have hcont_comp : Continuous fun p : X × Y ↦ (v p.1).comp (K p.1 p.2) :=
    ((ContinuousLinearMap.compL 𝕜 V W M).continuous.comp (hv.comp continuous_fst)).clm_apply hKc
  have hcont_prod : Continuous fun p : X × Y ↦ v p.1 (K p.1 p.2 (u p.2)) :=
    hcont_comp.clm_apply (hu.comp continuous_snd)
  have hcs_prod : HasCompactSupport fun p : X × Y ↦ v p.1 (K p.1 p.2 (u p.2)) :=
    HasCompactSupport.intro' (hC.prod hL) (hCc.prod hLc) fun ⟨x, y⟩ hxy ↦ by
      by_cases hx : x ∈ C
      · exact (hy_in x hx y fun hy ↦ hxy ⟨hx, hy⟩).elim (fun hv0 ↦ by simp [hv0])
          (fun hK0 ↦ by simp [hK0])
      · exact (hx_out x hx).elim (fun hv0 ↦ by simp [hv0]) fun hK0 ↦ by simp [hK0]
  have hLHS : (∫ x, v x (∫ y, K x y (u y) ∂ν) ∂μ) = ∫ x, ∫ y, v x (K x y (u y)) ∂ν ∂μ := by
    refine integral_congr_ae (.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ C
    · by_cases hv0 : v x = 0
      · simp [hv0]
      · have hint : Integrable (fun y ↦ K x y (u y)) ν :=
          ((hKc.comp (continuous_const.prodMk continuous_id)).clm_apply
            hu).integrable_of_hasCompactSupport
            (HasCompactSupport.intro' hL hLc fun y hy ↦ (hy_in x hx y hy).resolve_left hv0)
        exact (((v x).restrictScalars ℝ).integral_comp_comm hint).symm
    · exact (hx_out x hx).elim (fun hv0 ↦ by simp [hv0]) fun hK0 ↦ by simp [hK0]
  have hRHS : (∫ y, ∫ x, v x (K x y (u y)) ∂μ ∂ν) =
      ∫ y, (∫ x, (v x).comp (K x y) ∂μ) (u y) ∂ν := by
    refine integral_congr_ae (.of_forall fun y ↦ ?_)
    by_cases hy : y ∈ L
    · by_cases hu0 : u y = 0
      · simp [hu0]
      · have hint : Integrable (fun x ↦ (v x).comp (K x y)) μ :=
          (hcont_comp.comp (continuous_id.prodMk continuous_const)).integrable_of_hasCompactSupport
            (HasCompactSupport.intro' hC hCc fun x hx ↦ (hx_in y hy x hx).resolve_left hu0)
        exact ((ContinuousLinearMap.apply 𝕜 M (u y)).restrictScalars ℝ).integral_comp_comm hint
    · refine (hy_out y hy).elim (fun hu0 ↦ by simp [hu0]) fun hc0 ↦ ?_
      have h0 : ∀ x, v x (K x y (u y)) = 0 := fun x ↦ by
        simpa using ContinuousLinearMap.ext_iff.mp (hc0 x) (u y)
      simp [hc0, h0]
  exact hLHS.trans ((MeasureTheory.integral_integral_swap_of_hasCompactSupport
    hcont_prod hcs_prod).trans hRHS)

/-- **Transposition identity under proper input support.** If `K` is continuous with proper input
support, `W` is complete, `μ` and `ν` are finite on compact subsets, and `v : X → W →L[𝕜] M` is
continuous with compact support, then for *every* continuous input `u : Y → V` (with no support
assumption on `u`), pairing `(T_K u)(x)` with `v(x)` equals pairing `u(y)` with the transposed
operator `(T_K^t v)(y) = ∫ x, (v x).comp (K x y) ∂μ`. -/
theorem HasProperInputSupport.integral_apply_integral_swap {X Y 𝕜 V W M : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace 𝕜 W] [IsScalarTower ℝ 𝕜 W] [CompleteSpace W]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedSpace 𝕜 M] [IsScalarTower ℝ 𝕜 M]
    {K : X → Y → V →L[𝕜] W} (hK : HasProperInputSupport K) (hKc : Continuous (uncurry K))
    {u : Y → V} (hu : Continuous u) {v : X → W →L[𝕜] M} (hv : Continuous v)
    (hvc : HasCompactSupport v) (μ : Measure X := by volume_tac)
    (ν : Measure Y := by volume_tac) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] :
    (∫ x, v x (∫ y, K x y (u y) ∂ν) ∂μ) = ∫ y, (∫ x, (v x).comp (K x y) ∂μ) (u y) ∂ν := by
  obtain ⟨L, hL, hLc, hKL⟩ :=
    hK.exists_isCompact_isClosed_forall_eq_zero_or_eq_zero_of_hasCompactSupport hvc
  exact integral_apply_integral_swap_of_isCompact_isClosed hKc hu hv μ ν hvc (isClosed_tsupport v)
    hL hLc (fun x hx ↦ Or.inl (image_eq_zero_of_notMem_tsupport hx))
    (fun x _ y hy ↦ (hKL y hy x).elim (fun h ↦ Or.inr (by simp [h])) Or.inl)
    (fun y hy ↦ Or.inr fun x ↦ (hKL y hy x).elim (fun h ↦ by simp [h]) (fun h ↦ by simp [h]))
    (fun _ _ x hx ↦ Or.inr (by simp [image_eq_zero_of_notMem_tsupport hx]))

/-- **Transposition identity under proper output support.** Symmetrically, if `K` is continuous with
proper output support, `W` is complete, `μ` and `ν` are finite on compact subsets, and
`u : Y → V` is continuous with compact support, then the transposition identity holds for *every*
continuous `v : X → W →L[𝕜] M`. -/
theorem HasProperOutputSupport.integral_apply_integral_swap {X Y 𝕜 V W M : Type*}
    [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
    [TopologicalSpace Y] [MeasurableSpace Y] [OpensMeasurableSpace Y]
    [NontriviallyNormedField 𝕜] [NormedAlgebra ℝ 𝕜]
    [NormedAddCommGroup V] [NormedSpace 𝕜 V] [NormedAddCommGroup W] [NormedSpace ℝ W]
    [NormedSpace 𝕜 W] [IsScalarTower ℝ 𝕜 W] [CompleteSpace W]
    [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedSpace 𝕜 M] [IsScalarTower ℝ 𝕜 M]
    {K : X → Y → V →L[𝕜] W} (hK : HasProperOutputSupport K) (hKc : Continuous (uncurry K))
    {u : Y → V} (hu : Continuous u) (huc : HasCompactSupport u)
    {v : X → W →L[𝕜] M} (hv : Continuous v) (μ : Measure X := by volume_tac)
    (ν : Measure Y := by volume_tac) [IsFiniteMeasureOnCompacts μ] [IsFiniteMeasureOnCompacts ν] :
    (∫ x, v x (∫ y, K x y (u y) ∂ν) ∂μ) = ∫ y, (∫ x, (v x).comp (K x y) ∂μ) (u y) ∂ν := by
  obtain ⟨C, hC, hCc, hCK⟩ :=
    hK.exists_isCompact_isClosed_forall_eq_zero_or_eq_zero_of_hasCompactSupport huc
  exact integral_apply_integral_swap_of_isCompact_isClosed hKc hu hv μ ν hC hCc
    huc (isClosed_tsupport u)
    (fun x hx ↦ Or.inr fun y ↦ (hCK x hx y).elim (fun h ↦ by simp [h]) (fun h ↦ by simp [h]))
    (fun _ _ y hy ↦ Or.inr (by simp [image_eq_zero_of_notMem_tsupport hy]))
    (fun y hy ↦ Or.inl (image_eq_zero_of_notMem_tsupport hy))
    (fun y _ x hx ↦ (hCK x hx y).elim (fun h ↦ Or.inr (by simp [h])) Or.inl)

end TauCeti
