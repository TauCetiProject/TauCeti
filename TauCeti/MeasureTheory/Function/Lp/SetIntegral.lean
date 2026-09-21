/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# Integrating an `Lᵖ` function over a set of finite measure

Hölder's inequality against the constant function `1` bounds the integral of a function over a
set `s` by its `Lᵖ` seminorm there, at the cost of the factor `μ s ^ (1 - 1 / p)`.  The bound is
what makes `f ↦ ∫ y in s, f y ∂μ` a continuous functional on `Lᵖ`, so that a limit of `Lᵖ`
approximations may be taken inside a mean over `s`.

## Main declarations

* `TauCeti.enorm_setIntegral_le_eLpNorm_mul_rpow`: the bound.
* `TauCeti.lipschitzWith_setIntegral`: integration over `s` is Lipschitz on `Lᵖ`.
-/

public section

namespace TauCeti

open MeasureTheory
open scoped ENNReal

variable {α F : Type*} [MeasurableSpace α] [NormedAddCommGroup F] [NormedSpace ℝ F]
  {μ : Measure α} {p : ℝ≥0∞}

/-- The integral of a function over a set is bounded by its `Lᵖ` seminorm there, times
`μ s ^ (1 - 1 / p)`. -/
theorem enorm_setIntegral_le_eLpNorm_mul_rpow {f : α → F} {s : Set α} (hp : 1 ≤ p)
    (hf : AEStronglyMeasurable f (μ.restrict s)) :
    ‖∫ y in s, f y ∂μ‖ₑ ≤ eLpNorm f p (μ.restrict s) * μ s ^ (1 - 1 / p.toReal) :=
  calc ‖∫ y in s, f y ∂μ‖ₑ
      ≤ ∫⁻ y in s, ‖f y‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
    _ = eLpNorm f 1 (μ.restrict s) := eLpNorm_one_eq_lintegral_enorm.symm
    _ ≤ eLpNorm f p (μ.restrict s) *
          (μ.restrict s) Set.univ ^ (1 / (1 : ℝ≥0∞).toReal - 1 / p.toReal) :=
        eLpNorm_le_eLpNorm_mul_rpow_measure_univ hp hf
    _ = eLpNorm f p (μ.restrict s) * μ s ^ (1 - 1 / p.toReal) := by
        rw [Measure.restrict_apply_univ]; norm_num

/-- **Integration over a set of finite measure is Lipschitz on `Lᵖ`.**  Its Lipschitz constant
is `μ s ^ (1 - 1 / p)`, the factor in `TauCeti.enorm_setIntegral_le_eLpNorm_mul_rpow`. -/
theorem lipschitzWith_setIntegral [Fact (1 ≤ p)] {s : Set α} (hp : p ≠ ∞)
    (hs : μ s ≠ ∞) :
    LipschitzWith (μ s ^ (1 - 1 / p.toReal)).toNNReal fun f : Lp F p μ => ∫ y in s, f y ∂μ := by
  have hp1 : (1 : ℝ≥0∞) ≤ p := Fact.out
  have hpR : (1 : ℝ) ≤ p.toReal := by simpa using ENNReal.toReal_mono hp hp1
  have hres : μ.restrict s ≤ μ := Measure.restrict_le_self
  have : IsFiniteMeasure (μ.restrict s) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact hs.lt_top⟩
  have hmem : ∀ f : Lp F p μ, MemLp f p (μ.restrict s) := fun f => (Lp.memLp f).mono_measure hres
  have hcoe : ((μ s ^ (1 - 1 / p.toReal)).toNNReal : ℝ≥0∞) = μ s ^ (1 - 1 / p.toReal) :=
    ENNReal.coe_toNNReal (ENNReal.rpow_ne_top_of_nonneg (by
      have : 1 / p.toReal ≤ 1 := by rw [div_le_one (by linarith)]; exact hpR
      linarith) hs)
  intro f g
  rw [edist_eq_enorm_sub, edist_eq_enorm_sub, hcoe,
    ← integral_sub ((hmem f).integrable hp1) ((hmem g).integrable hp1)]
  have key : eLpNorm (fun y => f y - g y) p (μ.restrict s) ≤ ‖f - g‖ₑ :=
    calc eLpNorm (fun y => f y - g y) p (μ.restrict s)
        ≤ eLpNorm (fun y => f y - g y) p μ := eLpNorm_mono_measure _ hres
      _ = ‖f - g‖ₑ := by
          rw [Lp.enorm_def]
          exact (eLpNorm_congr_ae (Lp.coeFn_sub f g)).symm
  calc ‖∫ y in s, (f y - g y) ∂μ‖ₑ
      ≤ eLpNorm (fun y => f y - g y) p (μ.restrict s) * μ s ^ (1 - 1 / p.toReal) :=
        enorm_setIntegral_le_eLpNorm_mul_rpow hp1
          (((Lp.aestronglyMeasurable f).sub (Lp.aestronglyMeasurable g)).mono_measure hres)
    _ ≤ ‖f - g‖ₑ * μ s ^ (1 - 1 / p.toReal) := by gcongr
    _ = μ s ^ (1 - 1 / p.toReal) * ‖f - g‖ₑ := mul_comm _ _

end TauCeti
