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
formula when the input has a compactly supported `MemLp` representative.  The representative
case is the bridge needed to pass between `Lᵖ`-valued mollification and classical convolution in
subsequent density and localization arguments.

## Attribution

The design follows LeanPool's `RellichKondrachov/L2Compactness/Smoothing.lean`, especially its
`smoothFun` and `smoothL2` constructions, and Tau Ceti's
`RepresentationTheory/Compact/Convolution.lean`, especially
`convolutionCLM_toLp_apply`.
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
    (hf : Integrable f mu) (s : Set E) :
    (∫ t, phi.normed mu t • ∫ x in s, f (x - t) ∂mu ∂mu) =
      ∫ x in s, (phi.normed mu ⋆[lsmul ℝ ℝ, mu] f) x ∂mu := by
  have hbase : Integrable (Function.uncurry fun t x : E => phi.normed mu t • f x) (mu.prod mu) :=
    (phi.continuous_normed.integrable_of_hasCompactSupport
      (phi.hasCompactSupport_normed (μ := mu))).smul_prod hf
  have hF_int : Integrable (Function.uncurry fun t x : E => phi.normed mu t • f (x - t))
      (mu.prod mu) := by
    have hshear := measurePreserving_prod_sub mu mu
    have hcomp := hshear.integrable_comp hbase.aestronglyMeasurable |>.mpr hbase
    convert hcomp using 1; rfl
  calc
    (∫ t, phi.normed mu t • ∫ x in s, f (x - t) ∂mu ∂mu) =
        ∫ t, ∫ x in s, phi.normed mu t • f (x - t) ∂mu ∂mu := by
      apply integral_congr_ae
      filter_upwards with t
      rw [integral_smul]
    _ = ∫ x in s, ∫ t, phi.normed mu t • f (x - t) ∂mu ∂mu := by
      apply integral_integral_swap
      have hi := hF_int.integrableOn (s := univ ×ˢ s)
      -- `IntegrableOn` is definitionally `Integrable` against a restricted measure, and this
      -- form is required to apply the product-measure restriction rewrite below.
      change Integrable _ ((mu.prod mu).restrict (univ ×ˢ s)) at hi
      rw [← Measure.prod_restrict univ s] at hi
      simpa only [Measure.restrict_univ] using hi
    _ = ∫ x in s, (phi.normed mu ⋆[lsmul ℝ ℝ, mu] f) x ∂mu := by
      apply integral_congr_ae
      filter_upwards with x
      rw [convolution_lsmul]

/-- The `Lᵖ` approximate identity is represented almost everywhere by the usual pointwise
convolution for a compactly supported `MemLp` representative. -/
theorem normedBumpLp_ae_eq_convolution (hp_ne_top : p ≠ ∞) (phi : ContDiffBump (0 : E))
    {f : E → F} (hfLp : MemLp f p mu) (hfc : HasCompactSupport f) :
    (normedBumpLp hp_ne_top phi mu
      (MemLp.toLp f hfLp)) =ᵐ[mu]
      (phi.normed mu ⋆[lsmul ℝ ℝ, mu] f) := by
  have hf_int : Integrable f mu := by
    apply (integrableOn_iff_integrable_of_support_subset (subset_tsupport f)).mp
    -- `IntegrableOn` is definitionally `Integrable` against a restricted measure; this
    -- conversion is needed because the support lemma produces the former while the Lp lemma
    -- expects the latter.
    change Integrable f (mu.restrict (tsupport f))
    exact (integrableOn_Lp_of_measure_ne_top (hfLp.toLp f) Fact.out
      hfc.measure_lt_top.ne).congr (ae_restrict_of_ae hfLp.coeFn_toLp)
  let conv : E → F := phi.normed mu ⋆[lsmul ℝ ℝ, mu] f
  have hconv_cont : Continuous conv := by
    exact phi.hasCompactSupport_normed.continuous_convolution_left
      (lsmul ℝ ℝ) phi.continuous_normed hf_int.locallyIntegrable
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
          Set.setIntegralLp (𝕜 := ℝ) s hμs
            (normedBumpLp hp_ne_top phi mu (hfLp.toLp f)) :=
        (Set.setIntegralLp_apply (𝕜 := ℝ) s hμs _).symm
      _ = ∫ t, Set.setIntegralLp (𝕜 := ℝ) s hμs
            (phi.normed mu t • mu.translateLp p (-t) (hfLp.toLp f)) ∂mu := by
        rw [normedBumpLp_apply]
        exact (Set.setIntegralLp (𝕜 := ℝ) s hμs).integral_comp_comm hLp_int |>.symm
      _ = ∫ t, phi.normed mu t • ∫ x in s, f (x - t) ∂mu ∂mu := by
        apply integral_congr_ae
        filter_upwards with t
        rw [map_smul, Set.setIntegralLp_apply (𝕜 := ℝ),
          Set.setIntegral_translateLp_toLp s hfLp t]
      _ = ∫ x in s, conv x ∂mu := by
        exact setIntegral_normedConvolution phi hf_int s
      _ = ∫ x in s, (hconvLp.toLp conv) x ∂mu := by
        apply integral_congr_ae
        exact ae_restrict_of_ae hconvLp.coeFn_toLp.symm

end TauCeti
