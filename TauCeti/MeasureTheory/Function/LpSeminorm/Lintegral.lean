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
seminorm is used to bound an integral, with no measurability side condition. For a natural
exponent `n ≠ 0` and measurable `f` the identity reads `∫⁻ ‖f‖ₑ ^ n ∂μ = eLpNorm f n μ ^ n`
(`TauCeti.lintegral_enorm_pow_eq_eLpNorm_pow`). For an almost everywhere strongly measurable `f`
and `p ≠ 0, ∞` in `ℝ≥0∞`, the two sides agree
(`MeasureTheory.lintegral_rpow_enorm_eq_eLpNorm_rpow`), so `∫⁻ ‖f‖ₑ ^ p ∂μ ≤ t ^ p` gives
`eLpNorm f p μ ≤ t` (`MeasureTheory.eLpNorm_le_of_lintegral_rpow_le`). In particular a pointwise
bound `‖k x‖ ^ q ≤ t ^ (q - p) ‖f x‖ ^ p` with `t = ‖f‖_p` integrates to `‖k‖_q ≤ t`
(`MeasureTheory.eLpNorm_le_of_rpow_le_rpow_mul`).

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

/-- For `n ≠ 0`, the `n`-th power of the `Lⁿ` seminorm of an almost everywhere strongly measurable
function is the integral of `‖f‖ₑ ^ n`. -/
theorem lintegral_enorm_pow_eq_eLpNorm_pow {n : ℕ} (hn : n ≠ 0) {f : α → ε}
    (hf : AEStronglyMeasurable f μ) : ∫⁻ x, ‖f x‖ₑ ^ n ∂μ = eLpNorm f n μ ^ n := by
  simpa only [ENNReal.coe_natCast, NNReal.coe_natCast, ENNReal.rpow_natCast] using
    (eLpNorm_nnreal_pow_eq_lintegral (p := (n : ℝ≥0)) (Nat.cast_ne_zero.2 hn) hf).symm

end TauCeti

namespace MeasureTheory

/-- For `p ≠ 0, ∞`, the integral of `‖f‖ₑ ^ p` is the `p`-th power of the `Lᵖ` seminorm of `f`. -/
theorem lintegral_rpow_enorm_eq_eLpNorm_rpow {f : α → ε} {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ∞) (hf : AEStronglyMeasurable f μ) :
    ∫⁻ x, ‖f x‖ₑ ^ p.toReal ∂μ = eLpNorm f p μ ^ p.toReal := by
  rw [eLpNorm_eq_eLpNorm' hp0 hp hf,
    lintegral_rpow_eNorm_eq_rpow_eLpNorm' (ENNReal.toReal_pos hp0 hp)]

/-- If `∫ ‖k‖ ^ q ≤ t ^ q` then `‖k‖_q ≤ t`. -/
theorem eLpNorm_le_of_lintegral_rpow_le {k : α → ε} {q : ℝ≥0∞} {t : ℝ≥0∞} (hq0 : q ≠ 0)
    (hq : q ≠ ∞) (hk : AEStronglyMeasurable k μ) (h : ∫⁻ x, ‖k x‖ₑ ^ q.toReal ∂μ ≤ t ^ q.toReal) :
    eLpNorm k q μ ≤ t := by
  have hq' : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [← ENNReal.rpow_le_rpow_iff hq', ← lintegral_rpow_enorm_eq_eLpNorm_rpow hq0 hq hk]
  exact h

/-- If `‖f‖_q ≤ M` for `M ≠ 0, ∞`, then `∫ M ^ (r - q) ‖f‖ ^ q ≤ M ^ r` for every real `r`. -/
theorem lintegral_rpow_sub_mul_rpow_enorm_le {f : α → ε} {q M : ℝ≥0∞} (r : ℝ) (hq0 : q ≠ 0)
    (hq : q ≠ ∞) (hM0 : M ≠ 0) (hM : M ≠ ∞) (hf : AEStronglyMeasurable f μ)
    (hfM : eLpNorm f q μ ≤ M) :
    ∫⁻ x, M ^ (r - q.toReal) * ‖f x‖ₑ ^ q.toReal ∂μ ≤ M ^ r := by
  rw [lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_ne_zero hM0 hM),
    lintegral_rpow_enorm_eq_eLpNorm_rpow hq0 hq hf]
  calc M ^ (r - q.toReal) * eLpNorm f q μ ^ q.toReal
      ≤ M ^ (r - q.toReal) * M ^ q.toReal := by gcongr
    _ = M ^ r := by rw [← ENNReal.rpow_add _ _ hM0 hM, sub_add_cancel]

/-- If `‖k x‖ ^ q ≤ t ^ (q - p) ‖f x‖ ^ p` pointwise, where `t = ‖f‖_p`, then `‖k‖_q ≤ t`. -/
theorem eLpNorm_le_of_rpow_le_rpow_mul {f k : α → ε} {p q : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ∞) (hq0 : q ≠ 0) (hq : q ≠ ∞) (hf : AEStronglyMeasurable f μ)
    (hk : AEStronglyMeasurable k μ) (ht0 : eLpNorm f p μ ≠ 0) (ht : eLpNorm f p μ ≠ ∞)
    (hkf : ∀ x, ‖k x‖ₑ ^ q.toReal ≤
      eLpNorm f p μ ^ (q.toReal - p.toReal) * ‖f x‖ₑ ^ p.toReal) :
    eLpNorm k q μ ≤ eLpNorm f p μ :=
  eLpNorm_le_of_lintegral_rpow_le hq0 hq hk <| (lintegral_mono hkf).trans <|
    lintegral_rpow_sub_mul_rpow_enorm_le _ hp0 hp ht0 ht hf le_rfl

/-- **Monotone convergence for the `Lᵖ` seminorm.** The `Lᵖ` seminorm of the pointwise supremum
of an almost everywhere increasing sequence of almost everywhere measurable functions with values
in `[0, ∞]` is the supremum of their `Lᵖ` seminorms. -/
theorem eLpNorm_iSup_eq_iSup_eLpNorm {f : ℕ → α → ℝ≥0∞} (hf : ∀ n, AEMeasurable (f n) μ)
    (hmono : ∀ᵐ x ∂μ, Monotone fun n ↦ f n x) {p : ℝ≥0∞} :
    eLpNorm (fun x ↦ ⨆ n, f n x) p μ = ⨆ n, eLpNorm (f n) p μ := by
  rcases eq_or_ne p ∞ with rfl | hp
  · -- At `p = ∞` each `f n` is bounded almost everywhere by its essential supremum.
    refine le_antisymm ?_ (iSup_le fun n ↦
      eLpNorm_mono_eNorm (hf n).aestronglyMeasurable fun x ↦ ?_)
    · rw [eLpNorm_exponent_top (AEMeasurable.iSup hf).aestronglyMeasurable, eLpNormEssSup]
      refine essSup_le_of_ae_le _ ?_
      filter_upwards [ae_all_iff.2 fun n ↦ ae_le_eLpNormEssSup (f := f n) (μ := μ)] with x hx
      simp only [eNorm_eq_self] at hx ⊢
      exact iSup_mono fun n ↦
        (hx n).trans_eq (eLpNorm_exponent_top (hf n).aestronglyMeasurable).symm
    · simpa only [eNorm_eq_self] using le_iSup (fun n ↦ f n x) n
  rcases eq_or_ne p 0 with rfl | hp0
  · simp only [eLpNorm_exponent_zero (AEMeasurable.iSup hf).aestronglyMeasurable,
      eLpNorm_exponent_zero (hf _).aestronglyMeasurable, iSup_const]
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  simp_rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp
      (AEMeasurable.iSup hf).aestronglyMeasurable,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp (hf _).aestronglyMeasurable, eNorm_eq_self,
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
  have hlt := lintegral_rpow_eNorm_lt_top_of_eLpNorm_lt_top hp hp_top hf.eLpNorm_lt_top
  filter_upwards [ae_lt_top' (hf.aestronglyMeasurable.eNorm.pow_const _) hlt.ne] with x hx
  exact (ENNReal.rpow_lt_top_iff_of_pos (ENNReal.toReal_pos hp hp_top)).1 hx

end MeasureTheory.MemLp
