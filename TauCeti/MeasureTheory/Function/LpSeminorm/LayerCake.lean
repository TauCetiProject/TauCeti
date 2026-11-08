/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import TauCeti.MeasureTheory.Integral.MinkowskiIntegral

/-!
# An integral bound by superlevel-set norms

Integral Minkowski applied to the layer-cake representation bounds the `Lᵖ` seminorm of a
function by the integral of the `Lᵖ` seminorms of its superlevel indicators. This form is
useful when geometric inequalities control the measures of superlevel sets. Both sides
are extended nonnegative numbers, so no integrability or finite-norm hypothesis is needed.
The integral comparison is `TauCeti.lintegral_Lp_lintegral_le`.
-/

public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace TauCeti

variable {α F : Type*} [MeasurableSpace α] {μ : Measure α} [SigmaFinite μ]
  [NormedAddCommGroup F] {f : α → F}

/-- The `Lᵖ` seminorm is bounded by the integral of the `p`th roots of the measures of
norm-superlevel sets. This is integral Minkowski for the layer-cake representation,
valid also when either side is infinite. -/
theorem eLpNorm_le_lintegral_measure_norm_gt (hf : AEStronglyMeasurable f μ)
    {p : ℝ≥0∞} (hp : 1 ≤ p) (hp_top : p ≠ ∞) :
    eLpNorm f p μ ≤ ∫⁻ t in Ioi (0 : ℝ), μ {x | t < ‖f x‖} ^ (1 / p.toReal) := by
  let g := hf.norm.aemeasurable.mk (fun x ↦ ‖f x‖)
  have hg : Measurable g := hf.norm.aemeasurable.measurable_mk
  have hfg : (fun x ↦ ‖f x‖) =ᵐ[μ] g := hf.norm.aemeasurable.ae_eq_mk
  let H : α → ℝ → ℝ≥0∞ := fun x t ↦ (Iio (g x)).indicator 1 t
  have hH : Measurable (Function.uncurry H) := by
    have hset : MeasurableSet {z : α × ℝ | z.2 < g z.1} :=
      measurableSet_lt measurable_snd (hg.comp measurable_fst)
    convert (measurable_const (a := (1 : ℝ≥0∞))).indicator hset using 1
    ext ⟨x, t⟩
    by_cases ht : t < g x <;> simp [Function.uncurry, H, ht]
  have hlayer (x : α) : ∫⁻ t in Ioi (0 : ℝ), H x t = ENNReal.ofReal (g x) := by
    simp [H, lintegral_indicator, Measure.restrict_apply, Iio_inter_Ioi]
  have hnorm : eLpNorm f p μ =
      (∫⁻ x, (∫⁻ t in Ioi (0 : ℝ), H x t) ^ p.toReal ∂μ) ^ (1 / p.toReal) := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (zero_lt_one.trans_le hp).ne' hp_top hf]
    simp_rw [hlayer]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [hfg] with x hx
    rw [← hx, ofReal_norm]
  rw [hnorm]
  refine (lintegral_Lp_lintegral_le
    (hH.aemeasurable : AEMeasurable (Function.uncurry H)
      (μ.prod (volume.restrict (Ioi (0 : ℝ)))))
    (by simpa using ENNReal.toReal_mono hp_top hp)).trans_eq ?_
  apply setLIntegral_congr_fun measurableSet_Ioi
  intro t ht
  have hpow : (fun x ↦ H x t ^ p.toReal) = {x | t < g x}.indicator 1 := by
    ext x
    by_cases hx : t < g x <;> simp [H, hx, ENNReal.toReal_pos
      (zero_lt_one.trans_le hp).ne' hp_top]
  dsimp only
  rw [hpow, lintegral_indicator_one (measurableSet_lt measurable_const hg)]
  congr 1
  exact measure_congr (hfg.mono fun x hx ↦ by simp only [mem_ofPred_eq, hx])

end TauCeti
