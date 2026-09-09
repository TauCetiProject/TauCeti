/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.Lp.Translation
import Mathlib.MeasureTheory.Function.AEEqOfIntegral

/-!
# Restriction and set integration on finite-measure sets

This file provides the continuous map from `Lᵖ` to `L¹` obtained by restricting to a
finite-measure set, together with the corresponding set-integral map.  These constructions are
useful whenever an `Lᵖ` identity is tested against integrals on finite-measure sets.

## Main declarations

* `TauCeti.lpToL1Restrict`: restriction from `Lᵖ` to `L¹` on a finite-measure set.
* `TauCeti.lpToL1Restrict_coeFn`: the restricted class has the original representative almost
  everywhere.
* `TauCeti.setIntegralLp`: integration on a finite-measure set as a continuous linear map on
  `Lᵖ`.
* `TauCeti.setIntegralLp_apply` and `TauCeti.setIntegralLp_translateLp`: pointwise formulas for
  this map and for translated representatives.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter MeasureTheory Set
open scoped ENNReal

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {mu : Measure E} {p : ENNReal} [Fact (1 ≤ p)]

/-- Restrict an `Lᵖ` class to a finite-measure set and view it as an `L¹` class. -/
noncomputable def lpToL1Restrict (hp_ne_top : p ≠ ∞) (s : Set E) (hμs : mu s < ∞) :
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

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace F] in
/-- The restricted `L¹` class agrees almost everywhere with the original `Lᵖ` class. -/
theorem lpToL1Restrict_coeFn (hp_ne_top : p ≠ ∞) (s : Set E) (hμs : mu s < ∞)
    (f : Lp F p mu) :
    lpToL1Restrict hp_ne_top s hμs f =ᵐ[mu.restrict s] f := by
  let _ : IsFiniteMeasure (mu.restrict s) := isFiniteMeasure_restrict.2 hμs.ne
  change ((Lp.memLp f).restrict s).mono_exponent Fact.out |>.toLp f =ᵐ[mu.restrict s] f
  exact MemLp.coeFn_toLp _

/-- Integrate an `Lᵖ` class over a finite-measure set as a continuous linear map. -/
noncomputable def setIntegralLp (hp_ne_top : p ≠ ∞) (s : Set E) (hμs : mu s < ∞) :
    Lp F p mu →L[ℝ] F :=
  (L1.integralCLM (α := E) (E := F) (μ := mu.restrict s)).comp
    (lpToL1Restrict hp_ne_top s hμs)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The set integral of an `Lᵖ` class agrees with the integral of its representative. -/
theorem setIntegralLp_apply (hp_ne_top : p ≠ ∞) (s : Set E) (hμs : mu s < ∞)
    (f : Lp F p mu) :
    setIntegralLp hp_ne_top s hμs f = ∫ x in s, f x ∂mu := by
  rw [setIntegralLp, ContinuousLinearMap.comp_apply, ← L1.integral_eq, L1.integral_eq_integral]
  exact integral_congr_ae (lpToL1Restrict_coeFn hp_ne_top s hμs f)

omit [NormedSpace ℝ E] in
/-- The set integral of a translated `Lᵖ` class is the integral of its translated representative. -/
theorem setIntegralLp_translateLp [BorelSpace E] [mu.IsAddHaarMeasure]
    (hp_ne_top : p ≠ ∞) (s : Set E) (hμs : mu s < ∞)
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

end TauCeti
