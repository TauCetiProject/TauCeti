/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Pointwise representatives of smooth `Lᵖ` mollification

This file connects the `Lᵖ`-valued average in
`TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity` with the usual pointwise convolution
formula when the input has a continuous compactly supported representative.  The representative
case is the bridge needed before the general Meyers--Serrin localization argument can be assembled.

The proof uses the local `Lᵖ`-to-`L¹` restriction map on finite-measure sets.  This makes the
Bochner integral in `Lᵖ` testable by set integrals without choosing a pointwise representative of
an arbitrary `Lᵖ` class.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter MeasureTheory Set
open scoped Convolution ENNReal Pointwise

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [BorelSpace E] [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] {mu : Measure E} [mu.IsAddHaarMeasure] {p : ENNReal} [Fact (1 ≤ p)]

private noncomputable def lpToL1Restrict (hp_ne_top : p ≠ ∞) (s : Set E) (hμs : mu s < ∞) :
    Lp F p mu →L[ℝ] Lp F 1 (mu.restrict s) := by
  letI : IsFiniteMeasure (mu.restrict s) := isFiniteMeasure_restrict.2 hμs.ne
  let hp : (1 : ENNReal) ≤ p := Fact.out
  let toFun : Lp F p mu → Lp F 1 (mu.restrict s) := fun f =>
    ((Lp.memLp f).restrict s).mono_exponent hp |>.toLp f
  let toLinearMap : Lp F p mu →ₗ[ℝ] Lp F 1 (mu.restrict s) :=
    { toFun := toFun
      map_add' := by
        intro f g
        apply Lp.ext
        dsimp only [toFun]
        filter_upwards [ae_restrict_of_ae (Lp.coeFn_add f g),
          MemLp.coeFn_toLp (((Lp.memLp (f + g)).restrict s).mono_exponent hp),
          MemLp.coeFn_toLp (((Lp.memLp f).restrict s).mono_exponent hp),
          MemLp.coeFn_toLp (((Lp.memLp g).restrict s).mono_exponent hp),
          Lp.coeFn_add
            (((Lp.memLp f).restrict s).mono_exponent hp |>.toLp f)
            (((Lp.memLp g).restrict s).mono_exponent hp |>.toLp g)] with
            x hfg h₁ h₂ h₃ hadd
        rw [h₁, hfg]
        simp only [Pi.add_apply] at ⊢
        rw [← h₂, ← h₃]
        simpa only [Pi.add_apply] using hadd.symm
      map_smul' := by
        intro c f
        apply Lp.ext
        dsimp only [toFun]
        filter_upwards [ae_restrict_of_ae (Lp.coeFn_smul c f),
          MemLp.coeFn_toLp (((Lp.memLp (c • f)).restrict s).mono_exponent hp),
          MemLp.coeFn_toLp (((Lp.memLp f).restrict s).mono_exponent hp),
          Lp.coeFn_smul c (((Lp.memLp f).restrict s).mono_exponent hp |>.toLp f)] with
            x hcf h₁ h₂ hsmul
        rw [h₁, hcf]
        simp only [Pi.smul_apply, RingHom.id_apply] at ⊢
        rw [← h₂]
        simpa only [Pi.smul_apply, RingHom.id_apply] using hsmul.symm }
  apply LinearMap.mkContinuous toLinearMap
    ((mu s).toReal ^ (1 - (1 / p.toReal)))
  intro f
  let f₁ : Lp F 1 (mu.restrict s) := toFun f
  have hnorm : ‖f₁‖ = ENNReal.toReal (eLpNorm f 1 (mu.restrict s)) := by
    rw [Lp.norm_def]
    exact congrArg ENNReal.toReal <| eLpNorm_congr_ae (MemLp.coeFn_toLp _)
  have hbound : eLpNorm f 1 (mu.restrict s) ≤
      eLpNorm f p (mu.restrict s) * (mu s) ^ (1 - (1 / p.toReal)) := by
    simpa [Measure.restrict_apply_univ, hμs.ne] using
      (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (f := f) (p := (1 : ENNReal)) (q := p)
        (μ := mu.restrict s) Fact.out
        ((Lp.aestronglyMeasurable f).mono_measure Measure.restrict_le_self))
  have hrestrict : eLpNorm f p (mu.restrict s) ≤ eLpNorm f p mu :=
    eLpNorm_mono_measure _ Measure.restrict_le_self
  have hfinite : (mu s) ^ (1 - (1 / p.toReal)) ≠ ∞ := by
    apply ENNReal.rpow_ne_top_of_nonneg
    · have hp0 : (0 : ENNReal) < p := (zero_lt_one.trans_le Fact.out)
      have hp_real : 1 ≤ p.toReal := by
        exact ENNReal.toReal_mono (a := (1 : ENNReal)) (b := p) hp_ne_top Fact.out
      exact sub_nonneg.mpr (by
        rw [one_div]
        exact (inv_le_one₀ (by positivity)).2 hp_real)
    exact hμs.ne
  have hnorm_le : ‖f₁‖ ≤
      (mu s).toReal ^ (1 - (1 / p.toReal)) * ‖f‖ := by
    rw [hnorm, Lp.norm_def]
    calc
      ENNReal.toReal (eLpNorm f 1 (mu.restrict s)) ≤
          ENNReal.toReal (eLpNorm f p mu * (mu s) ^ (1 - (1 / p.toReal))) := by
        apply ENNReal.toReal_mono
        · exact ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f) hfinite
        · exact hbound.trans (by gcongr)
      _ = (mu s).toReal ^ (1 - (1 / p.toReal)) * ENNReal.toReal (eLpNorm f p mu) := by
        simp only [ENNReal.toReal_mul, ENNReal.toReal_rpow]
        rw [mul_comm]
  exact hnorm_le

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]
  [CompleteSpace F] [mu.IsAddHaarMeasure] in
private theorem lpToL1Restrict_coeFn (hp_ne_top : p ≠ ∞) (s : Set E) (hμs : mu s < ∞)
    (f : Lp F p mu) :
    lpToL1Restrict hp_ne_top s hμs f =ᵐ[mu.restrict s] f := by
  let _ : IsFiniteMeasure (mu.restrict s) := isFiniteMeasure_restrict.2 hμs.ne
  -- Unfold the restriction map so that its chosen `L¹` representative is visible.
  change ((Lp.memLp f).restrict s).mono_exponent Fact.out |>.toLp f =ᵐ[mu.restrict s] f
  exact MemLp.coeFn_toLp _

private noncomputable def setIntegralLp (hp_ne_top : p ≠ ∞) (s : Set E) (hμs : mu s < ∞) :
    Lp F p mu →L[ℝ] F :=
  (L1.integralCLM (α := E) (E := F) (μ := mu.restrict s)).comp
    (lpToL1Restrict hp_ne_top s hμs)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E]
  [mu.IsAddHaarMeasure] in
private theorem setIntegralLp_apply (hp_ne_top : p ≠ ∞) (s : Set E) (hμs : mu s < ∞)
    (f : Lp F p mu) :
    setIntegralLp hp_ne_top s hμs f = ∫ x in s, f x ∂mu := by
  rw [setIntegralLp, ContinuousLinearMap.comp_apply, ← L1.integral_eq, L1.integral_eq_integral]
  exact integral_congr_ae (lpToL1Restrict_coeFn hp_ne_top s hμs f)

omit [NormedSpace ℝ E] [FiniteDimensional ℝ E] in
private theorem setIntegralLp_translateLp (hp_ne_top : p ≠ ∞) (s : Set E) (hμs : mu s < ∞)
    {f : E → F} (hfLp : MemLp f p mu) (t : E) :
    setIntegralLp hp_ne_top s hμs (mu.translateLp p (-t) (hfLp.toLp f)) =
      ∫ x in s, f (x - t) ∂mu := by
  rw [setIntegralLp_apply]
  apply integral_congr_ae
  filter_upwards [ae_restrict_of_ae
      ((Measure.coeFn_translateLp (mu := mu) (-t) (hfLp.toLp f)).trans
        ((measurePreserving_add_right mu (-t)).quasiMeasurePreserving.ae_eq_comp
          hfLp.coeFn_toLp))] with x hx
  simpa only [Function.comp_apply, sub_eq_add_neg] using hx

omit [CompleteSpace F] in
private theorem setIntegral_convolution (phi : ContDiffBump (0 : E)) {f : E → F}
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
          setIntegralLp hp_ne_top s hμs
            (normedBumpLp hp_ne_top phi mu (hfLp.toLp f)) :=
        (setIntegralLp_apply hp_ne_top s hμs _).symm
      _ = ∫ t, setIntegralLp hp_ne_top s hμs
            (phi.normed mu t • mu.translateLp p (-t) (hfLp.toLp f)) ∂mu := by
        rw [normedBumpLp_apply]
        exact (setIntegralLp hp_ne_top s hμs).integral_comp_comm hLp_int |>.symm
      _ = ∫ t, phi.normed mu t • ∫ x in s, f (x - t) ∂mu ∂mu := by
        apply integral_congr_ae
        filter_upwards with t
        rw [map_smul, setIntegralLp_translateLp hp_ne_top s hμs hfLp t]
      _ = ∫ x in s, conv x ∂mu := by
        exact setIntegral_convolution phi hf hfc s
      _ = ∫ x in s, (hconvLp.toLp conv) x ∂mu := by
        apply integral_congr_ae
        exact ae_restrict_of_ae hconvLp.coeFn_toLp.symm

end TauCeti
