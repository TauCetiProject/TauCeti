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

* `MeasureTheory.Measure.LpToL1CLM`: the continuous inclusion from `Lᵖ` to `L¹` on
  a finite-measure space.
* `MeasureTheory.Measure.LpToL1CLM_coeFn`: the inclusion has the original representative almost
  everywhere.
* `Set.LpToL1RestrictCLM`: restriction from `Lᵖ` to `L¹` on a finite-measure set.
* `Set.LpToL1RestrictCLM_coeFn`: the restricted class has the original representative almost
  everywhere.
* `Set.setIntegralLp`: integration on a finite-measure set as a continuous linear map on
  `Lᵖ`.
* `Set.setIntegralLp_apply`: the pointwise formula for this map.
-/

public section

noncomputable section

namespace MeasureTheory.Measure

open ContinuousLinearMap Filter MeasureTheory Set
open scoped ENNReal

variable {E F 𝕜 : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedRing 𝕜] [Module 𝕜 F]
  [IsBoundedSMul 𝕜 F] [CompleteSpace F]
  {mu : Measure E} {p : ENNReal} [Fact (1 ≤ p)]

/-- The continuous inclusion from `Lᵖ` to `L¹` on a finite-measure space. -/
noncomputable def LpToL1CLM (μ : Measure E) (p : ENNReal) [IsFiniteMeasure μ]
    [Fact (1 ≤ p)] : Lp F p μ →L[𝕜] Lp F 1 μ := by
  let hp : (1 : ENNReal) ≤ p := Fact.out
  let toFun : Lp F p μ → Lp F 1 μ := fun f =>
    (Lp.memLp f).mono_exponent hp |>.toLp f
  let toLinearMap : Lp F p μ →ₗ[𝕜] Lp F 1 μ :=
    { toFun := toFun
      map_add' := by
        intro f g
        dsimp only [toFun]
        rw [← MemLp.toLp_add]
        apply MemLp.toLp_congr
        exact Lp.coeFn_add f g
      map_smul' := by
        intro c f
        dsimp only [toFun]
        rw [RingHom.id_apply, ← MemLp.toLp_const_smul]
        apply MemLp.toLp_congr
        exact Lp.coeFn_smul c f }
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

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] [CompleteSpace F] in
/-- The finite-measure `Lᵖ` to `L¹` inclusion has the original representative almost everywhere. -/
theorem LpToL1CLM_coeFn (μ : Measure E) (p : ENNReal) [IsFiniteMeasure μ]
    [Fact (1 ≤ p)] (f : Lp F p μ) : LpToL1CLM (𝕜 := 𝕜) μ p f =ᵐ[μ] f := by
  -- No stable rewrite theorem exposes the representative of `LinearMap.mkContinuous`, so this
  -- conversion unfolds the definition to apply `MemLp.coeFn_toLp`.
  change (Lp.memLp f).mono_exponent Fact.out |>.toLp f =ᵐ[μ] f
  exact MemLp.coeFn_toLp _

end MeasureTheory.Measure

namespace Set

open ContinuousLinearMap Filter MeasureTheory Set
open scoped ENNReal

variable {E F 𝕜 : Type*} [MeasurableSpace E] [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedRing 𝕜] [Module 𝕜 F]
  [IsBoundedSMul 𝕜 F] [SMulCommClass ℝ 𝕜 F] [CompleteSpace F]
  {mu : Measure E} {p : ENNReal} [Fact (1 ≤ p)]

/-- Restrict an `Lᵖ` class to a finite-measure set and view it as an `L¹` class. -/
noncomputable def LpToL1RestrictCLM (s : Set E) (hμs : mu s < ∞) :
    Lp F p mu →L[𝕜] Lp F 1 (mu.restrict s) := by
  letI : IsFiniteMeasure (mu.restrict s) := isFiniteMeasure_restrict.2 hμs.ne
  exact (Measure.LpToL1CLM (𝕜 := 𝕜) (μ := mu.restrict s) p).comp
    (LpToLpRestrictCLM E F 𝕜 mu p s)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedSpace ℝ F] [SMulCommClass ℝ 𝕜 F]
    [CompleteSpace F] in
/-- The restricted `L¹` class agrees almost everywhere with the original `Lᵖ` class. -/
theorem LpToL1RestrictCLM_coeFn (s : Set E) (hμs : mu s < ∞)
    (f : Lp F p mu) :
    LpToL1RestrictCLM (𝕜 := 𝕜) s hμs f =ᵐ[mu.restrict s] f := by
  let _ : IsFiniteMeasure (mu.restrict s) := isFiniteMeasure_restrict.2 hμs.ne
  -- Unfold the composition so the public inclusion and restriction representative lemmas apply.
  change Measure.LpToL1CLM (𝕜 := 𝕜) (mu.restrict s) p
      (LpToLpRestrictCLM E F 𝕜 mu p s f) =ᵐ[mu.restrict s] f
  exact (Measure.LpToL1CLM_coeFn (𝕜 := 𝕜) (mu.restrict s) p _).trans
    (LpToLpRestrictCLM_coeFn 𝕜 s f)

/-- Integrate an `Lᵖ` class over a finite-measure set as a continuous linear map. -/
noncomputable def setIntegralLp (s : Set E) (hμs : mu s < ∞) :
    Lp F p mu →L[𝕜] F :=
  (L1.integralCLM' 𝕜 (α := E) (E := F) (μ := mu.restrict s)).comp
    (LpToL1RestrictCLM (𝕜 := 𝕜) s hμs)

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- The set integral of an `Lᵖ` class agrees with the integral of its representative. -/
@[simp]
theorem setIntegralLp_apply (s : Set E) (hμs : mu s < ∞)
    (f : Lp F p mu) :
    setIntegralLp (𝕜 := 𝕜) s hμs f = ∫ x in s, f x ∂mu := by
  rw [setIntegralLp, ContinuousLinearMap.comp_apply, ← L1.integral_eq' 𝕜,
    L1.integral_eq_integral]
  exact integral_congr_ae (LpToL1RestrictCLM_coeFn s hμs f)

end Set
