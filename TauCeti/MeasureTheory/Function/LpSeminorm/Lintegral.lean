/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic

/-!
# The `Lᵖ` integral is bounded by the `p`-th power of the `Lᵖ` seminorm

For a finite exponent `p ≠ 0`, Mathlib's `MeasureTheory.eLpNorm_nnreal_pow_eq_lintegral` identifies
`eLpNorm f p μ ^ p` with `∫⁻ ‖f‖ₑ ^ p ∂μ` for an almost everywhere strongly measurable `f`. Without
measurability the seminorm is `∞` by convention, so the inequality
`∫⁻ ‖f‖ₑ ^ p ∂μ ≤ eLpNorm f p μ ^ p` holds for every `f`
(`TauCeti.lintegral_rpow_enorm_le_rpow_eLpNorm`). This is the form in which a bound on the `Lᵖ`
seminorm is used to bound an integral, with no measurability side condition.

Consequently a function in `Lᵖ` for `p ≠ 0` is finite almost everywhere
(`MeasureTheory.MemLp.ae_enorm_lt_top`), including for `p = ∞`.

The same identification gives monotone convergence for the seminorm: the `Lᵖ` seminorm of the
supremum of an increasing sequence of functions with values in `[0, ∞]` is the supremum of their
seminorms (`MeasureTheory.eLpNorm_iSup_eq_iSup_eLpNorm`), also for `p = ∞`.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

variable {α ε : Type*} [MeasurableSpace α] {μ : Measure α} [TopologicalSpace ε] [ContinuousENorm ε]

namespace TauCeti

/-- For `p ≠ 0`, the integral `∫⁻ ‖f‖ₑ ^ p ∂μ` is at most `eLpNorm f p μ ^ p`, whether or not `f` is
almost everywhere strongly measurable. -/
theorem lintegral_rpow_enorm_le_rpow_eLpNorm {p : ℝ≥0} (hp : p ≠ 0) (f : α → ε) :
    ∫⁻ x, ‖f x‖ₑ ^ (p : ℝ) ∂μ ≤ eLpNorm f p μ ^ (p : ℝ) := by
  by_cases hf : AEStronglyMeasurable f μ
  · exact (eLpNorm_nnreal_pow_eq_lintegral hp hf).ge
  · rw [eLpNorm_of_not_aestronglyMeasurable hf,
      ENNReal.top_rpow_of_pos (NNReal.coe_pos.2 (pos_iff_ne_zero.2 hp))]
    exact le_top

end TauCeti

namespace MeasureTheory

/-- **Monotone convergence for the `Lᵖ` seminorm.** The `Lᵖ` seminorm of the pointwise supremum
of an almost everywhere increasing sequence of almost everywhere measurable functions with values
in `[0, ∞]` is the supremum of their `Lᵖ` seminorms. -/
theorem eLpNorm_iSup_eq_iSup_eLpNorm {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, AEMeasurable (f n) μ)
    (hmono : ∀ᵐ x ∂μ, Monotone fun n ↦ f n x) {p : ℝ≥0∞} :
    eLpNorm (fun x ↦ ⨆ n, f n x) p μ = ⨆ n, eLpNorm (f n) p μ := by
  rcases eq_or_ne p ∞ with rfl | hp
  · -- At `p = ∞` each `f n` is bounded almost everywhere by its essential supremum.
    refine le_antisymm ?_ (iSup_le fun n ↦
      eLpNorm_mono_enorm (hf n).aestronglyMeasurable fun x ↦ ?_)
    · rw [eLpNorm_exponent_top (AEMeasurable.iSup hf).aestronglyMeasurable, eLpNormEssSup]
      refine essSup_le_of_ae_le _ ?_
      filter_upwards [ae_all_iff.2 fun n ↦ ae_le_eLpNormEssSup (f := f n) (μ := μ)] with x hx
      simp only [enorm_eq_self] at hx ⊢
      exact iSup_mono fun n ↦
        (hx n).trans_eq (eLpNorm_exponent_top (hf n).aestronglyMeasurable).symm
    · simpa only [enorm_eq_self] using le_iSup (fun n ↦ f n x) n
  rcases eq_or_ne p 0 with rfl | hp0
  · simp only [eLpNorm_exponent_zero (AEMeasurable.iSup hf).aestronglyMeasurable,
      eLpNorm_exponent_zero (hf _).aestronglyMeasurable, iSup_const]
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  simp_rw [eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp
      (AEMeasurable.iSup hf).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_enorm_toReal hp0 hp (hf _).aestronglyMeasurable, enorm_eq_self,
    ENNReal.iSup_rpow_of_pos hr]
  rw [lintegral_iSup' (fun n ↦ (hf n).pow_const _)
    (hmono.mono fun x hx m n hmn ↦ ENNReal.rpow_le_rpow (hx hmn) hr.le),
    ENNReal.iSup_rpow_of_pos (by positivity)]

end MeasureTheory

namespace MeasureTheory.MemLp

/-- A function in `Lᵖ` with `p ≠ 0` is finite almost everywhere. -/
theorem ae_enorm_lt_top {f : α → ε} {p : ℝ≥0∞} (hf : MemLp f p μ) (hp : p ≠ 0) :
    ∀ᵐ x ∂μ, ‖f x‖ₑ < ∞ := by
  rcases eq_or_ne p ∞ with rfl | hp_top
  · filter_upwards [ae_le_eLpNormEssSup (f := f) (μ := μ)] with x hx
    exact hx.trans_lt (eLpNormEssSup_le_eLpNorm_top.trans_lt hf.eLpNorm_lt_top)
  have hlt := lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp hp_top hf.eLpNorm_lt_top
  filter_upwards [ae_lt_top' (hf.aestronglyMeasurable.enorm.pow_const _) hlt.ne] with x hx
  exact (ENNReal.rpow_lt_top_iff_of_pos (ENNReal.toReal_pos hp hp_top)).1 hx

end MeasureTheory.MemLp
