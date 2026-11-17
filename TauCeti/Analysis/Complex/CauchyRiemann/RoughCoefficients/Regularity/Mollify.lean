/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.BumpFunction.Convolution
public import Mathlib.Analysis.Distribution.TestFunction
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import TauCeti.Analysis.Sobolev.Local.Basic
import TauCeti.Analysis.Complex.OperatorNorm
import TauCeti.Analysis.Convolution.Basic
import TauCeti.Analysis.Distribution.TestFunction.Inner
import TauCeti.Analysis.Sobolev.Mollification.Interior
import TauCeti.Data.ENNReal.Holder
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity

/-!
# Mollification limits for Hilbert adjoint pairings

When proving interior Sobolev regularity for linear Cauchy–Riemann operators with rough Sobolev
coefficients `J ∈ W^{1,p}_loc(Ω)` (McDuff–Salamon, Appendix B.4), we test weak equations against
smooth approximations involving the Hilbert adjoint `J_nᵀ` of a normalized-bump mollification
`J_n = ρ_n ⋆ (W'.indicator J)`.

This file establishes the commutation of Hilbert adjoint evaluation with mollification and weak
differentiation, and proves the two integral limit lemmas used both in the divergence-form Laplace
reduction (Lemma B.4.6) and in the commutator identity for the weak differentiated system
(Proposition B.4.9).

## Main declarations

* `TauCeti.tendsto_integral_smul_inner_mollify`: passes to the limit in
  `∫ ⟪α z • v, (ρ_n ⋆ W'.indicator J) z (u z)⟫` for `J ∈ L^∞(W')` and locally integrable `u`.
* `TauCeti.tendsto_integral_smul_inner_fderiv_mollify`: passes to the limit in
  `∫ ⟪α z • v, fderiv ℝ (ρ_n ⋆ W'.indicator J) z w (u z)⟫` for `J ∈ W^{1,p}_loc(Ω) ∩ L^∞(W')`
  and `u ∈ L^q_loc(Ω)` with `p⁻¹ + q⁻¹ ≤ 1`.
-/

public noncomputable section

open Complex Filter MeasureTheory Set TopologicalSpace
open scoped ContDiff Convolution Distributions ENNReal InnerProductSpace Topology

namespace TauCeti

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [CompleteSpace V]
  {Ω : Opens ℂ}

/-- Evaluating the Hilbert adjoint at a fixed vector `v : V`, as a continuous linear map
`(V →L[ℝ] V) →L[ℝ] V`. -/
private def adjointApplyL (v : V) : (V →L[ℝ] V) →L[ℝ] V :=
  (ContinuousLinearMap.apply ℝ V v).comp
    (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := V)
      (F := V)).toContinuousLinearEquiv.toContinuousLinearMap

private theorem adjointApplyL_apply (v : V) (A : V →L[ℝ] V) :
    adjointApplyL v A = ContinuousLinearMap.adjoint A v := rfl

/-- Applying `adjointApplyL v` commutes with normalized-bump mollification of `W'.indicator J`. -/
private theorem adjointApplyL_mollify_eq (v : V) (ρ : ContDiffBump (0 : ℂ)) {W' : Opens ℂ}
    {J : ℂ → V →L[ℝ] V} (hJ : MemLp J ∞ (volume.restrict (W' : Set ℂ))) (z : ℂ) :
    ContinuousLinearMap.adjoint ((ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      ((W' : Set ℂ).indicator J)) z) v =
      (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        ((W' : Set ℂ).indicator (fun x => ContinuousLinearMap.adjoint (J x) v))) z := by
  have hloc : LocallyIntegrable ((W' : Set ℂ).indicator J) volume :=
    ((memLp_indicator_iff_restrict W'.isOpen.measurableSet.nullMeasurableSet).2
      hJ).locallyIntegrable le_top
  have hex := (ρ.hasCompactSupport_normed (μ := volume)).convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (ρ.contDiff_normed (n := (⊤ : ℕ∞))).continuous hloc z
  rw [← adjointApplyL_apply v, ← (adjointApplyL v).convolution_lsmul_comp_comm hex]
  congr 1; ext x
  by_cases hx : x ∈ (W' : Set ℂ) <;> simp [indicator, hx, adjointApplyL_apply]

/-- On `W ⋐ W'`, evaluating `(fderiv ℝ J_n z w)ᵀ v` equals the mollification of
`W'.indicator (fun x => (DJ x w)ᵀ v)`. -/
private theorem adjoint_fderiv_mollify_eq (v : V) (w : ℂ) (ρ : ContDiffBump (0 : ℂ))
    {W W' : Opens ℂ} {p : ℝ≥0∞} (hp1 : 1 ≤ p)
    (hsupp : ∀ z ∈ (W : Set ℂ), ∀ y ∈ tsupport (ρ.normed volume), z - y ∈ (W' : Set ℂ))
    (hW'c : IsCompact (closure (W' : Set ℂ))) (hW'Ω : closure (W' : Set ℂ) ⊆ Ω)
    {J : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    (hJ : HasWeakFDerivOn volume Ω J DJ) (hJinf : MemLp J ∞ (volume.restrict (W' : Set ℂ)))
    (hDJp : MemLpLoc p Ω DJ) {z : ℂ} (hz : z ∈ (W : Set ℂ)) :
    ContinuousLinearMap.adjoint (fderiv ℝ (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      ((W' : Set ℂ).indicator J)) z w) v =
      (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        ((W' : Set ℂ).indicator (fun x => ContinuousLinearMap.adjoint (DJ x w) v))) z := by
  have hloc : LocallyIntegrable ((W' : Set ℂ).indicator J) volume :=
    ((memLp_indicator_iff_restrict W'.isOpen.measurableSet.nullMeasurableSet).2
      hJinf).locallyIntegrable le_top
  have hJsmooth : ContDiff ℝ ∞ (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      ((W' : Set ℂ).indicator J)) :=
    (ρ.hasCompactSupport_normed (μ := volume)).contDiff_convolution_left
      (ContinuousLinearMap.lsmul ℝ ℝ) (ρ.contDiff_normed (n := (⊤ : ℕ∞))) hloc
  have hL : (fun x => adjointApplyL v ((ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
      ((W' : Set ℂ).indicator J)) x)) =
      ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
        ((W' : Set ℂ).indicator (fun x => ContinuousLinearMap.adjoint (J x) v)) :=
    funext fun x => adjointApplyL_mollify_eq v ρ hJinf x
  have h1 : fderiv ℝ (fun x => adjointApplyL v
      ((ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume] ((W' : Set ℂ).indicator J)) x))
      z w = ContinuousLinearMap.adjoint (fderiv ℝ
        (ρ.normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          ((W' : Set ℂ).indicator J)) z w) v := by
    have hd := ((adjointApplyL v).hasFDerivAt.comp z
      (hJsmooth.differentiable (by simp) z).hasFDerivAt).fderiv
    simpa [Function.comp_def, adjointApplyL_apply] using congr($hd w)
  rw [← h1, hL]
  have hJv : HasWeakFDerivOn volume W' (fun x => adjointApplyL v (J x))
      (fun x => (adjointApplyL v).comp (DJ x)) :=
    (hJ.mono (subset_closure.trans hW'Ω)).clm_comp (adjointApplyL v)
  have hJv_inf : MemLp (fun x => adjointApplyL v (J x)) ∞ (volume.restrict (W' : Set ℂ)) :=
    (adjointApplyL v).comp_memLp' hJinf
  have hDJv_loc : MemLpLoc p Ω (fun x => (adjointApplyL v).comp (DJ x)) := by
    rw [ContinuousLinearMap.fun_eq_smulRightL_reCLM_add_smulRightL_imCLM
      (fun x => (adjointApplyL v).comp (DJ x))]
    have h1' : MemLpLoc p Ω (fun x => ((adjointApplyL v).comp (DJ x)) 1) :=
      (hDJp.clm_comp (G := V →L[ℝ] V) (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) 1)).clm_comp
        (adjointApplyL v)
    have hI' : MemLpLoc p Ω (fun x => ((adjointApplyL v).comp (DJ x)) I) :=
      (hDJp.clm_comp (G := V →L[ℝ] V) (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) I)).clm_comp
        (adjointApplyL v)
    exact (h1'.clm_comp (ContinuousLinearMap.smulRightL ℝ ℂ V Complex.reCLM)).add
      (hI'.clm_comp (ContinuousLinearMap.smulRightL ℝ ℂ V Complex.imCLM))
  have hDJv_p : MemLp (fun x => (adjointApplyL v).comp (DJ x)) p (volume.restrict (W' : Set ℂ)) :=
    hDJv_loc.memLp_of_closure_subset hW'c hW'Ω
  have hf := hJv.fderiv_indicator_convolution_right hJv_inf hDJv_p le_top hp1 (ρ.normed volume)
    (ρ.contDiff_normed (n := (⊤ : ℕ∞))) (ρ.hasCompactSupport_normed (μ := volume)) z (hsupp z hz)
  simp only [convolution_flip] at hf
  have hcomp : (fun x => adjointApplyL v (J x)) =
      fun x => ContinuousLinearMap.adjoint (J x) v := rfl
  rw [hcomp] at hf
  rw [hf]
  have hlocD : LocallyIntegrable
      ((W' : Set ℂ).indicator (fun x => (adjointApplyL v).comp (DJ x))) volume :=
    ((memLp_indicator_iff_restrict W'.isOpen.measurableSet.nullMeasurableSet).2
      hDJv_p).locallyIntegrable hp1
  have hexD := (ρ.hasCompactSupport_normed (μ := volume)).convolutionExists_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (ρ.contDiff_normed (n := (⊤ : ℕ∞))).continuous hlocD z
  rw [← ContinuousLinearMap.apply_apply (𝕜 := ℝ) (v := w),
    ← (ContinuousLinearMap.apply ℝ V w).convolution_lsmul_comp_comm hexD]
  congr 1; ext x
  by_cases hx : x ∈ (W' : Set ℂ) <;> simp [indicator, hx, adjointApplyL_apply]

/-- Passing to the limit in `∫ ⟪α z • v, (ρ_n ⋆ W'.indicator J) z (u z)⟫` for a scalar test
function `α ∈ 𝓓(Ω, ℝ)` supported in `W ⊆ W'`, fixed `v ∈ V`, bounded `J`, and locally integrable
`u`. Works in any real Hilbert space without finite-dimensionality. -/
theorem tendsto_integral_smul_inner_mollify {W W' : Opens ℂ} (hWW' : (W : Set ℂ) ⊆ W')
    {ρ : ℕ → ContDiffBump (0 : ℂ)} (hρ : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0))
    {J : ℂ → V →L[ℝ] V} (hJ : MemLp J ∞ (volume.restrict (W' : Set ℂ)))
    (α : 𝓓(Ω, ℝ)) (hαW : tsupport (α : ℂ → ℝ) ⊆ W) (v : V)
    {u : ℂ → V} (hu : LocallyIntegrableOn u Ω volume) :
    Tendsto (fun n => ∫ z, ⟪(α : ℂ → ℝ) z • v,
        ((ρ n).normed volume ⋆[ContinuousLinearMap.lsmul ℝ ℝ, volume]
          ((W' : Set ℂ).indicator J)) z (u z)⟫_ℝ)
      atTop (𝓝 (∫ z, ⟪(α : ℂ → ℝ) z • v, J z (u z)⟫_ℝ)) := by
  let B : V →L[ℝ] V →L[ℝ] ℝ := innerSL ℝ
  have hB (x y : V) : B x y = ⟪x, y⟫_ℝ := rfl
  have hf_inf : MemLp ((W' : Set ℂ).indicator (fun x => ContinuousLinearMap.adjoint (J x) v))
      ∞ volume :=
    (memLp_indicator_iff_restrict W'.isOpen.measurableSet.nullMeasurableSet).2
      ((adjointApplyL v).comp_memLp' hJ)
  have hlim := B.tendsto_integral_bilin_normed_convolution_top hρ (α.integrable_smul hu) hf_inf
  have hEq_lim : (∫ z, B ((α : ℂ → ℝ) z • u z)
      ((W' : Set ℂ).indicator (fun x => ContinuousLinearMap.adjoint (J x) v) z)) =
      ∫ z, ⟪(α : ℂ → ℝ) z • v, J z (u z)⟫_ℝ := by
    refine integral_congr_ae (.of_forall fun z => ?_)
    dsimp only
    by_cases hz : z ∈ tsupport (α : ℂ → ℝ)
    · rw [hB, indicator_of_mem (hWW' (hαW hz)), ContinuousLinearMap.adjoint_inner_right,
        map_smul, inner_smul_left, inner_smul_left, RCLike.conj_to_real, real_inner_comm]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  rw [← hEq_lim]
  refine hlim.congr fun n => integral_congr_ae (.of_forall fun z => ?_)
  dsimp only
  rw [hB, ← adjointApplyL_mollify_eq v (ρ n) hJ z, ContinuousLinearMap.adjoint_inner_right,
    map_smul, inner_smul_left, inner_smul_left, RCLike.conj_to_real, real_inner_comm]

/-- Passing to the limit in `∫ ⟪α z • v, fderiv ℝ J_n z w (u z)⟫` for a scalar test function
`α ∈ 𝓓(Ω, ℝ)` supported in `W ⊆ W'`, fixed `v ∈ V`, `J ∈ W^{1,p}` bounded on `W'`, and
`u ∈ L^q_loc(Ω)` with `p⁻¹ + q⁻¹ ≤ 1`. -/
theorem tendsto_integral_smul_inner_fderiv_mollify {W W' : Opens ℂ}
    (hWW' : (W : Set ℂ) ⊆ W') {p q : ℝ≥0∞} (hp1 : 1 ≤ p) (hpq : p⁻¹ + q⁻¹ ≤ 1)
    {ρ : ℕ → ContDiffBump (0 : ℂ)} (hρ : Tendsto (fun n => (ρ n).rOut) atTop (𝓝 0))
    (hsupp : ∀ n, ∀ z ∈ (W : Set ℂ), ∀ y ∈ tsupport ((ρ n).normed volume), z - y ∈ (W' : Set ℂ))
    (hW'c : IsCompact (closure (W' : Set ℂ))) (hW'Ω : closure (W' : Set ℂ) ⊆ Ω)
    {J : ℂ → V →L[ℝ] V} {DJ : ℂ → ℂ →L[ℝ] V →L[ℝ] V}
    (hJ : HasWeakFDerivOn volume Ω J DJ) (hJinf : MemLp J ∞ (volume.restrict (W' : Set ℂ)))
    (hDJp : MemLpLoc p Ω DJ) (α : 𝓓(Ω, ℝ)) (hαW : tsupport (α : ℂ → ℝ) ⊆ W) (v : V)
    {u : ℂ → V} (hu : MemLpLoc q Ω u) (w : ℂ) :
    Tendsto (fun n => ∫ z, ⟪(α : ℂ → ℝ) z • v, fderiv ℝ ((ρ n).normed volume ⋆[
        ContinuousLinearMap.lsmul ℝ ℝ, volume] ((W' : Set ℂ).indicator J)) z w (u z)⟫_ℝ)
      atTop (𝓝 (∫ z, ⟪(α : ℂ → ℝ) z • v, DJ z w (u z)⟫_ℝ)) := by
  let B : V →L[ℝ] V →L[ℝ] ℝ := innerSL ℝ
  have hB (x y : V) : B x y = ⟪x, y⟫_ℝ := rfl
  let p' : ℝ≥0∞ := (1 - p⁻¹)⁻¹
  have : p.HolderConjugate p' := by
    simpa only [ENNReal.HolderConjugate, inv_one] using ENNReal.HolderTriple.of_le hp1
  have hp'q : p' ≤ q := by
    have hinv : q⁻¹ ≤ 1 - p⁻¹ :=
      ENNReal.le_sub_of_add_le_left (ENNReal.inv_ne_top.2 (zero_lt_one.trans_le hp1).ne') hpq
    rw [← inv_inv q]
    exact ENNReal.inv_le_inv.2 hinv
  have ha_memLp : MemLp (fun z => (α : ℂ → ℝ) z • u z) p' volume := by
    have hα_top : MemLp (α : ℂ → ℝ) ∞ volume := by
      obtain ⟨C, hC⟩ := α.hasCompactSupport.exists_bound_of_continuousOn α.continuous.continuousOn
      refine memLp_top_of_bound α.continuous.aestronglyMeasurable (max C 0) (.of_forall fun z => ?_)
      by_cases hz : z ∈ tsupport (α : ℂ → ℝ)
      · exact (hC z hz).trans (le_max_left C 0)
      · simp [image_eq_zero_of_notMem_tsupport hz]
    have huK : MemLp ((tsupport (α : ℂ → ℝ)).indicator u) p' volume :=
      (memLp_indicator_iff_restrict (isClosed_tsupport _).measurableSet.nullMeasurableSet).2
        (memLpLoc_iff.1 (hu.mono_exponent hp'q) _ α.tsupport_subset α.hasCompactSupport)
    have : ENNReal.HolderTriple ∞ p' p' := ⟨by simp⟩
    refine ((ContinuousLinearMap.lsmul ℝ ℝ).memLp_of_bilin p' hα_top huK).ae_eq
      (.of_forall fun z => ?_)
    by_cases hz : z ∈ tsupport (α : ℂ → ℝ)
    · simp [indicator_of_mem hz]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  have hDJw : MemLpLoc p Ω (fun x => DJ x w) :=
    hDJp.clm_comp (G := V →L[ℝ] V) (ContinuousLinearMap.apply ℝ (V →L[ℝ] V) w)
  have hf_p : MemLp ((W' : Set ℂ).indicator (fun x => ContinuousLinearMap.adjoint (DJ x w) v))
      p volume :=
    (memLp_indicator_iff_restrict W'.isOpen.measurableSet.nullMeasurableSet).2
      ((hDJw.clm_comp (adjointApplyL v)).memLp_of_closure_subset hW'c hW'Ω)
  have hlim := B.tendsto_integral_bilin_normed_convolution (p := p) (q := p') hρ ha_memLp hf_p
  have hEq_lim : (∫ z, B ((α : ℂ → ℝ) z • u z)
      ((W' : Set ℂ).indicator (fun x => ContinuousLinearMap.adjoint (DJ x w) v) z)) =
      ∫ z, ⟪(α : ℂ → ℝ) z • v, DJ z w (u z)⟫_ℝ := by
    refine integral_congr_ae (.of_forall fun z => ?_)
    dsimp only
    by_cases hz : z ∈ tsupport (α : ℂ → ℝ)
    · rw [hB, indicator_of_mem (hWW' (hαW hz)), ContinuousLinearMap.adjoint_inner_right,
        map_smul, inner_smul_left, inner_smul_left, RCLike.conj_to_real, real_inner_comm]
    · simp [image_eq_zero_of_notMem_tsupport hz]
  rw [← hEq_lim]
  refine hlim.congr fun n => integral_congr_ae (.of_forall fun z => ?_)
  dsimp only
  by_cases hz : z ∈ tsupport (α : ℂ → ℝ)
  · rw [hB, ← adjoint_fderiv_mollify_eq v w (ρ n) hp1 (hsupp n) hW'c hW'Ω hJ hJinf hDJp (hαW hz),
      ContinuousLinearMap.adjoint_inner_right, map_smul, inner_smul_left, inner_smul_left,
      RCLike.conj_to_real, real_inner_comm]
  · simp [image_eq_zero_of_notMem_tsupport hz]

end TauCeti
