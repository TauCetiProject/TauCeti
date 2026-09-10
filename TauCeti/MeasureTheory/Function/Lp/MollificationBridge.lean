/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
public import TauCeti.MeasureTheory.Function.Lp.Restriction
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Pointwise representatives of smooth `Lᵖ` mollification

This file connects the `Lᵖ`-valued average in
`TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity` with the usual pointwise convolution
formula when the input has a continuous compactly supported representative.  The representative
case is the bridge needed to pass between `Lᵖ`-valued mollification and classical convolution in
subsequent density and localization arguments.

## Attribution

The design follows LeanPool's `RellichKondrachov/L2Compactness/Smoothing.lean`, especially its
`smoothFun` and `smoothL2` constructions, and Tau Ceti's
`RepresentationTheory/Compact/Convolution.lean`, especially
`convolutionCLM_toLp_apply`.  The proof also uses Mathlib's
`integral_integral_swap_of_hasCompactSupport` from
`Mathlib/MeasureTheory/Integral/Prod.lean` and
`Lp.ae_eq_of_forall_setIntegral_eq` from
`Mathlib/MeasureTheory/Function/AEEqOfIntegral.lean`.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter MeasureTheory Set
open scoped Convolution ENNReal Pointwise

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [BorelSpace E] [ProperSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {mu : Measure E} [mu.IsAddHaarMeasure] {p : ENNReal} [Fact (1 ≤ p)]

local instance : FiniteDimensional ℝ E := .of_locallyCompactSpace ℝ

omit [CompleteSpace F] in
private theorem setIntegral_normedConvolution (phi : ContDiffBump (0 : E)) {f : E → F}
    (hf : Continuous f) (hfc : HasCompactSupport f) (s : Set E) :
    (∫ t, phi.normed mu t • ∫ x in s, f (x - t) ∂mu ∂mu) =
      ∫ x in s, (phi.normed mu ⋆[lsmul ℝ ℝ, mu] f) x ∂mu := by
  have hF_cont : Continuous (Function.uncurry fun t x : E => phi.normed mu t • f (x - t)) := by
    exact (phi.continuous_normed.comp continuous_fst).smul
      (hf.comp (continuous_snd.sub continuous_fst))
  have hF_cpt : HasCompactSupport
      (Function.uncurry fun t x : E => phi.normed mu t • f (x - t)) := by
    apply HasCompactSupport.intro
      ((phi.hasCompactSupport_normed (μ := mu)).isCompact.prod
        (hfc.isCompact.add (phi.hasCompactSupport_normed (μ := mu)).isCompact))
    intro x hx
    -- Expose the pairwise integrand before using the support of either factor.
    change phi.normed mu x.1 • f (x.2 - x.1) = 0
    by_cases ht : x.1 ∈ tsupport (phi.normed mu)
    · have hxsum : x.2 ∉ tsupport f + tsupport (phi.normed mu) := by
        intro hxsum
        exact hx ⟨ht, hxsum⟩
      have hsub : x.2 - x.1 ∉ tsupport f := by
        intro hsub
        apply hxsum
        exact Set.mem_add.mpr ⟨x.2 - x.1, hsub, x.1, ht, sub_add_cancel _ _⟩
      rw [image_eq_zero_of_notMem_tsupport hsub, smul_zero]
    · rw [image_eq_zero_of_notMem_tsupport ht, zero_smul]
  calc
    (∫ t, phi.normed mu t • ∫ x in s, f (x - t) ∂mu ∂mu) =
        ∫ t, ∫ x in s, phi.normed mu t • f (x - t) ∂mu ∂mu := by
      apply integral_congr_ae
      filter_upwards with t
      rw [integral_smul]
    _ = ∫ x in s, ∫ t, phi.normed mu t • f (x - t) ∂mu ∂mu :=
      integral_integral_swap_of_hasCompactSupport
        (μ := mu) (ν := mu.restrict s) hF_cont hF_cpt
    _ = ∫ x in s, (phi.normed mu ⋆[lsmul ℝ ℝ, mu] f) x ∂mu := by
      apply integral_congr_ae
      filter_upwards with x
      rw [convolution_lsmul]

/-- The `Lᵖ` approximate identity is represented almost everywhere by the usual pointwise
convolution whenever the input is continuous and compactly supported. -/
theorem normedBumpLp_ae_eq_convolution (hp_ne_top : p ≠ ∞) (phi : ContDiffBump (0 : E))
    {f : E → F} (hf : Continuous f) (hfc : HasCompactSupport f) :
    (normedBumpLp hp_ne_top phi mu
      (MemLp.toLp f (hf.memLp_of_hasCompactSupport hfc))) =ᵐ[mu]
      (phi.normed mu ⋆[lsmul ℝ ℝ, mu] f) := by
  let hfLp : MemLp f p mu := hf.memLp_of_hasCompactSupport hfc
  let conv : E → F := phi.normed mu ⋆[lsmul ℝ ℝ, mu] f
  have hconv_cont : Continuous conv := by
    exact phi.hasCompactSupport_normed.continuous_convolution_left
      (lsmul ℝ ℝ) phi.continuous_normed hf.locallyIntegrable
  have hconv_cpt : HasCompactSupport conv := by
    exact phi.hasCompactSupport_normed.convolution (lsmul ℝ ℝ) hfc
  let hconvLp : MemLp conv p mu := hconv_cont.memLp_of_hasCompactSupport hconv_cpt
  suffices hEq : (normedBumpLp hp_ne_top phi mu (hfLp.toLp f)) =ᵐ[mu]
      (hconvLp.toLp conv) by
    exact hEq.trans hconvLp.coeFn_toLp
  apply Lp.ae_eq_of_forall_setIntegral_eq
    (normedBumpLp hp_ne_top phi mu (hfLp.toLp f)) (hconvLp.toLp conv)
    (zero_lt_one.trans_le Fact.out).ne' hp_ne_top
  · intro s hs hμs
    exact integrableOn_Lp_of_measure_ne_top _ Fact.out hμs.ne
  · intro s hs hμs
    exact integrableOn_Lp_of_measure_ne_top _ Fact.out hμs.ne
  · intro s hs hμs
    have hLp_int : Integrable
        (fun t => phi.normed mu t • mu.translateLp p (-t) (hfLp.toLp f)) mu := by
      apply Continuous.integrable_of_hasCompactSupport
      · exact phi.continuous_normed.smul
          ((Measure.continuous_translateLp (mu := mu) hp_ne_top (hfLp.toLp f)).comp continuous_neg)
      · exact phi.hasCompactSupport_normed.smul_right
    calc
      ∫ x in s, (normedBumpLp hp_ne_top phi mu (hfLp.toLp f)) x ∂mu =
          setIntegralLp s hμs
            (normedBumpLp hp_ne_top phi mu (hfLp.toLp f)) :=
        (setIntegralLp_apply s hμs _).symm
      _ = ∫ t, setIntegralLp s hμs
            (phi.normed mu t • mu.translateLp p (-t) (hfLp.toLp f)) ∂mu := by
        rw [normedBumpLp_apply]
        exact (setIntegralLp s hμs).integral_comp_comm hLp_int |>.symm
      _ = ∫ t, phi.normed mu t • ∫ x in s, f (x - t) ∂mu ∂mu := by
        apply integral_congr_ae
        filter_upwards with t
        rw [map_smul, setIntegralLp_apply, setIntegral_translateLp_toLp s hfLp t]
      _ = ∫ x in s, conv x ∂mu := by
        exact setIntegral_normedConvolution phi hf hfc s
      _ = ∫ x in s, (hconvLp.toLp conv) x ∂mu := by
        apply integral_congr_ae
        exact ae_restrict_of_ae hconvLp.coeFn_toLp.symm

end TauCeti
