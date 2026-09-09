/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Set

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
* `TauCeti.setIntegralLp_apply`: the pointwise formula for this map.
-/

public section

noncomputable section

namespace TauCeti

open ContinuousLinearMap Filter MeasureTheory Set
open scoped ENNReal

variable {E F : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
  {mu : Measure E} {p : ENNReal} [Fact (1 ≤ p)]

/-- The continuous inclusion from `Lᵖ` to `L¹` on a finite-measure space. -/
noncomputable def lpToLpOneCLM (μ : Measure E) (p : ENNReal) [IsFiniteMeasure μ]
    [Fact (1 ≤ p)] : Lp F p μ →L[ℝ] Lp F 1 μ := by
  let hp : (1 : ENNReal) ≤ p := Fact.out
  let toFun : Lp F p μ → Lp F 1 μ := fun f =>
    (Lp.memLp f).mono_exponent hp |>.toLp f
  let toLinearMap : Lp F p μ →ₗ[ℝ] Lp F 1 μ :=
    { toFun := toFun
      map_add' := by
        intro f g
        apply Lp.ext
        dsimp only [toFun]
        filter_upwards [Lp.coeFn_add f g,
          MemLp.coeFn_toLp ((Lp.memLp (f + g)).mono_exponent hp),
          MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent hp),
          MemLp.coeFn_toLp ((Lp.memLp g).mono_exponent hp),
          Lp.coeFn_add
            ((Lp.memLp f).mono_exponent hp |>.toLp f)
            ((Lp.memLp g).mono_exponent hp |>.toLp g)] with x hfg h₁ h₂ h₃ hadd
        rw [h₁, hfg]
        simp only [Pi.add_apply] at ⊢
        rw [← h₂, ← h₃]
        simpa only [Pi.add_apply] using hadd.symm
      map_smul' := by
        intro c f
        apply Lp.ext
        dsimp only [toFun]
        filter_upwards [Lp.coeFn_smul c f,
          MemLp.coeFn_toLp ((Lp.memLp (c • f)).mono_exponent hp),
          MemLp.coeFn_toLp ((Lp.memLp f).mono_exponent hp),
          Lp.coeFn_smul c ((Lp.memLp f).mono_exponent hp |>.toLp f)] with x hcf h₁ h₂ hsmul
        rw [h₁, hcf]
        simp only [Pi.smul_apply, RingHom.id_apply] at ⊢
        rw [← h₂]
        simpa only [Pi.smul_apply, RingHom.id_apply] using hsmul.symm }
  apply LinearMap.mkContinuous toLinearMap
    ((μ Set.univ).toReal ^ (1 - (1 / p.toReal)))
  intro f
  let f₁ : Lp F 1 μ := toFun f
  have hnorm : ‖f₁‖ = ENNReal.toReal (eLpNorm f 1 μ) := by
    rw [Lp.norm_def]
    exact congrArg ENNReal.toReal <| eLpNorm_congr_ae (MemLp.coeFn_toLp _)
  have hbound : eLpNorm f 1 μ ≤
      eLpNorm f p μ * (μ Set.univ) ^ (1 - (1 / p.toReal)) :=
    by
      simpa [ENNReal.toReal_one] using
        (eLpNorm_le_eLpNorm_mul_rpow_measure_univ (f := f) (p := (1 : ENNReal)) (q := p)
          (μ := μ) Fact.out (Lp.aestronglyMeasurable f))
  have hfinite : (μ Set.univ) ^ (1 - (1 / p.toReal)) ≠ ∞ := by
    by_cases hp_top : p = ∞
    · simp [hp_top, measure_ne_top μ Set.univ]
    · apply ENNReal.rpow_ne_top_of_nonneg
      · have hp0 : (0 : ENNReal) < p := (zero_lt_one.trans_le Fact.out)
        have hp_real : 1 ≤ p.toReal := by
          exact ENNReal.toReal_mono (a := (1 : ENNReal)) (b := p) hp_top Fact.out
        exact sub_nonneg.mpr (by
          rw [one_div]
          exact (inv_le_one₀ (by positivity)).2 hp_real)
      exact measure_ne_top μ Set.univ
  have hnorm_le : ‖f₁‖ ≤
      (μ Set.univ).toReal ^ (1 - (1 / p.toReal)) * ‖f‖ := by
    rw [hnorm, Lp.norm_def]
    calc
      ENNReal.toReal (eLpNorm f 1 μ) ≤
          ENNReal.toReal (eLpNorm f p μ * (μ Set.univ) ^ (1 - (1 / p.toReal))) := by
        apply ENNReal.toReal_mono
        · exact ENNReal.mul_ne_top (Lp.eLpNorm_ne_top f) hfinite
        · exact hbound
      _ = (μ Set.univ).toReal ^ (1 - (1 / p.toReal)) * ENNReal.toReal (eLpNorm f p μ) := by
        simp only [ENNReal.toReal_mul, ENNReal.toReal_rpow]
        rw [mul_comm]
  exact hnorm_le

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace F] in
/-- The finite-measure `Lᵖ` to `L¹` inclusion has the original representative almost everywhere. -/
theorem lpToLpOneCLM_coeFn (μ : Measure E) (p : ENNReal) [IsFiniteMeasure μ]
    [Fact (1 ≤ p)] (f : Lp F p μ) : lpToLpOneCLM μ p f =ᵐ[μ] f := by
  -- No stable rewrite theorem exposes the representative of `LinearMap.mkContinuous`, so this
  -- conversion unfolds the definition to apply `MemLp.coeFn_toLp`.
  change (Lp.memLp f).mono_exponent Fact.out |>.toLp f =ᵐ[μ] f
  exact MemLp.coeFn_toLp _

/-- Restrict an `Lᵖ` class to a finite-measure set and view it as an `L¹` class. -/
noncomputable def lpToL1Restrict (s : Set E) (hμs : mu s < ∞) :
    Lp F p mu →L[ℝ] Lp F 1 (mu.restrict s) := by
  letI : IsFiniteMeasure (mu.restrict s) := isFiniteMeasure_restrict.2 hμs.ne
  exact (lpToLpOneCLM (μ := mu.restrict s) p).comp
    (LpToLpRestrictCLM E F ℝ mu p s)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace F] in
/-- The restricted `L¹` class agrees almost everywhere with the original `Lᵖ` class. -/
theorem lpToL1Restrict_coeFn (s : Set E) (hμs : mu s < ∞)
    (f : Lp F p mu) :
    lpToL1Restrict s hμs f =ᵐ[mu.restrict s] f := by
  let _ : IsFiniteMeasure (mu.restrict s) := isFiniteMeasure_restrict.2 hμs.ne
  -- Unfold the composition so the public inclusion and restriction representative lemmas apply.
  change lpToLpOneCLM (mu.restrict s) p
      (LpToLpRestrictCLM E F ℝ mu p s f) =ᵐ[mu.restrict s] f
  exact (lpToLpOneCLM_coeFn (mu.restrict s) p _).trans
    (LpToLpRestrictCLM_coeFn ℝ s f)

/-- Integrate an `Lᵖ` class over a finite-measure set as a continuous linear map. -/
noncomputable def setIntegralLp (s : Set E) (hμs : mu s < ∞) :
    Lp F p mu →L[ℝ] F :=
  (L1.integralCLM (α := E) (E := F) (μ := mu.restrict s)).comp
    (lpToL1Restrict s hμs)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The set integral of an `Lᵖ` class agrees with the integral of its representative. -/
@[simp]
theorem setIntegralLp_apply (s : Set E) (hμs : mu s < ∞)
    (f : Lp F p mu) :
    setIntegralLp s hμs f = ∫ x in s, f x ∂mu := by
  rw [setIntegralLp, ContinuousLinearMap.comp_apply, ← L1.integral_eq, L1.integral_eq_integral]
  exact integral_congr_ae (lpToL1Restrict_coeFn s hμs f)

end TauCeti
