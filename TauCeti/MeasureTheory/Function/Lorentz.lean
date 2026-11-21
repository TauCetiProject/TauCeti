/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.DecreasingRearrangement
public import TauCeti.MeasureTheory.Measure.Haar.MultHaar
import TauCeti.Analysis.SpecialFunctions.Pow.Integral
import TauCeti.MeasureTheory.Function.Lp.IntermediateExponent
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral

/-!
# Lorentz gauges and Lorentz function classes

For a measure `μ` on `α`, a function `f : α → ε`, and exponents `p, q ∈ [0, ∞]`, the **Lorentz
gauge** `TauCeti.eLorentzNorm f p q μ` (`‖f‖_{p, q}`) is the `L^q(dt / t)` seminorm of
`t ↦ t ^ (1 / p) f*(t)`, where `f*` is `μ.decreasingRearrangement (‖f ·‖ₑ)` and `dt / t` is
`TauCeti.multHaar`. A function belongs to `TauCeti.MemLorentz f p q μ` when
`eLorentzNorm f p q μ < ∞`.

Following `MeasureTheory.eLpNorm`, `eLorentzNorm f p q μ` is `∞` when `f` is not `μ`-a.e. strongly
measurable, and `0` when `f` is a.e. strongly measurable and `p = 0` or `q = 0`. On the diagonal
`q = p`, equimeasurability gives `eLorentzNorm f p p μ = eLpNorm f p μ` unconditionally
(`TauCeti.eLorentzNorm_self`). For `μ`-a.e. strongly measurable `f` at `q = ∞`, right continuity
identifies `‖f‖_{p, ∞}` with `⨆ t > 0, t ^ (1 / p) f*(t)` when `p ≠ 0`
(`TauCeti.eLorentzNorm_top_eq_iSup_Ioi`), and with `⨆ c, c * μ {‖f‖ > c} ^ (1 / p)` when
`0 < p < ∞` (`TauCeti.eLorentzNorm_top_eq_iSup_mul_measure_rpow`). Monotonicity of `f*` and
log-convexity give `‖f‖_{p, q₁} ≤ (q₀ / p) ^ (1 / q₀ - 1 / q₁) ‖f‖_{p, q₀}` for `0 < p < ∞` and
`0 < q₀ ≤ q₁ ≤ ∞` (`TauCeti.eLorentzNorm_le_of_exponent_le`).

Shifted subadditivity gives the quasi-triangle inequality with constant `2 ^ (1 / p)` for
`1 ≤ q ≤ ∞` (`TauCeti.eLorentzNorm_add_le`), while cyclic shifts on `Fin 3` show non-subadditivity
at `q = ∞` (`TauCeti.exists_lt_eLorentzNorm_add_top`). On `(0, ∞)`, `t ↦ t ^ (-1 / p)` separates
`L^p` from `L^{p, ∞}` (`TauCeti.eLorentzNorm_rpow_neg_inv_Ioi`, `TauCeti.eLpNorm_rpow_neg_inv_Ioi`).

## Main declarations

* `TauCeti.eLorentzNorm`, `TauCeti.eLorentzNorm_def`, `TauCeti.MemLorentz`: Lorentz gauge
  `‖f‖_{p, q}` and membership class.
* `TauCeti.eLorentzNorm_self`, `TauCeti.memLorentz_self`: `‖f‖_{p, p} = ‖f‖_p`.
* `TauCeti.eLorentzNorm_decreasingRearrangement_eNorm`, `TauCeti.eLorentzNorm_eNorm_rpow`:
  rearrangement invariance and power rescaling.
* `TauCeti.eLorentzNorm_indicator_const`: explicit formula for `‖c 1_A‖_{p, q}`.
* `TauCeti.eLorentzNorm_top_eq_iSup_Ioi`, `TauCeti.eLorentzNorm_top_eq_iSup_mul_measure_rpow`,
  `TauCeti.measure_gt_le_eLorentzNorm_top_div_rpow`: weak-`L^p` formulas and Chebyshev's bound.
* `TauCeti.eLorentzNorm_le_of_exponent_le`, `TauCeti.MemLorentz.mono_exponent`: secondary-exponent
  embeddings `L^{p, q₀} ⊆ L^{p, q₁}`.
* `TauCeti.rpow_mul_decreasingRearrangement_le_eLpNorm`,
  `MeasureTheory.MemLp.decreasingRearrangement_lt_top`,
  `MeasureTheory.MemLp.tendsto_decreasingRearrangement_atTop_nhds_zero`: size of the decreasing
  rearrangement of an `Lᵖ` function.
* `TauCeti.tsum_rpow_mul_decreasingRearrangement_sq_le`: the dyadic form of `L^q ⊆ L^{q, 2}` for
  `q ≤ 2`, square summability of the normalized levels `2^{k/q} f*(2ᵏ)`.
* `TauCeti.eLorentzNorm_add_le`, `TauCeti.eLorentzNorm_add_le'`, `TauCeti.MemLorentz.add`:
  quasi-triangle inequalities and closure under addition.
* `TauCeti.eLorentzNorm_rpow_neg_inv_Ioi`, `TauCeti.eLpNorm_rpow_neg_inv_Ioi`,
  `TauCeti.exists_lt_eLorentzNorm_add_top`: concrete separation and non-subadditivity witnesses.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §1.3.
* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., GTM 249, Springer, 2014, §1.4.
* R. A. Hunt, *On L(p, q) spaces*, Enseign. Math. (2) **12** (1966), 249–276.
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace TauCeti

section Defs

variable {α ε : Type*} {mα : MeasurableSpace α} [TopologicalSpace ε] [ENorm ε]
  {μ : Measure α} {f g : α → ε} {p q : ℝ≥0∞}

/-- The **Lorentz gauge** `‖f‖_{p, q}` of `f : α → ε` with respect to `μ`, valued in `ℝ≥0∞`:
for `p ≠ 0` and an almost everywhere strongly measurable `f`, the `L^q(dt / t)` seminorm of
`t ↦ t ^ (1 / p) f*(t)`, where `f*` is the decreasing rearrangement of `‖f ·‖ₑ` and `dt / t` is
`TauCeti.multHaar`. It equals `0` when `p = 0` and `f` is a.e. strongly measurable, and `∞` when
`f` is not a.e. strongly measurable. -/
noncomputable def eLorentzNorm (f : α → ε) (p q : ℝ≥0∞)
    (μ : Measure α := by volume_tac) : ℝ≥0∞ :=
  open scoped Classical in
  if AEStronglyMeasurable f μ then
    if p = 0 then 0
    else eLpNorm (fun t : ℝ ↦
      ENNReal.ofReal (t ^ (p⁻¹).toReal) * μ.decreasingRearrangement (‖f ·‖ₑ) t) q multHaar
  else ∞

/-- The defining case split of `TauCeti.eLorentzNorm`. -/
theorem eLorentzNorm_def (f : α → ε) (p q : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm f p q μ = open scoped Classical in
      if AEStronglyMeasurable f μ then
        if p = 0 then 0
        else eLpNorm (fun t : ℝ ↦
          ENNReal.ofReal (t ^ (p⁻¹).toReal) * μ.decreasingRearrangement (‖f ·‖ₑ) t) q multHaar
      else ∞ := (rfl)

/-- Membership in the **Lorentz class** `L^{p, q}(μ)`: `eLorentzNorm f p q μ < ∞`. Because
`eLorentzNorm` assigns `∞` to functions that are not a.e. strongly measurable, `MemLorentz f p q μ`
implies `AEStronglyMeasurable f μ` (`TauCeti.MemLorentz.aestronglyMeasurable`). -/
def MemLorentz (f : α → ε) (p q : ℝ≥0∞) (μ : Measure α := by volume_tac) : Prop :=
  eLorentzNorm f p q μ < ∞

theorem eLorentzNorm_of_not_aestronglyMeasurable (hf : ¬AEStronglyMeasurable f μ) :
    eLorentzNorm f p q μ = ∞ := by simp [eLorentzNorm_def, hf]

theorem eLorentzNorm_eq_eLpNorm (hf : AEStronglyMeasurable f μ) (hp : p ≠ 0) :
    eLorentzNorm f p q μ = eLpNorm (fun t : ℝ ↦
      ENNReal.ofReal (t ^ (p⁻¹).toReal) * μ.decreasingRearrangement (‖f ·‖ₑ) t) q multHaar := by
  simp [eLorentzNorm_def, hf, hp]

theorem aestronglyMeasurable_of_eLorentzNorm_ne_top (h : eLorentzNorm f p q μ ≠ ∞) :
    AEStronglyMeasurable f μ :=
  not_imp_comm.1 eLorentzNorm_of_not_aestronglyMeasurable h

theorem MemLorentz.eLorentzNorm_lt_top (hf : MemLorentz f p q μ) : eLorentzNorm f p q μ < ∞ := hf
theorem MemLorentz.eLorentzNorm_ne_top (hf : MemLorentz f p q μ) : eLorentzNorm f p q μ ≠ ∞ := hf.ne

theorem MemLorentz.aestronglyMeasurable (hf : MemLorentz f p q μ) : AEStronglyMeasurable f μ :=
  aestronglyMeasurable_of_eLorentzNorm_ne_top hf.ne

theorem memLorentz_iff : MemLorentz f p q μ ↔ eLorentzNorm f p q μ < ∞ := Iff.rfl

@[simp]
theorem eLorentzNorm_exponent_zero_left (hf : AEStronglyMeasurable f μ) :
    eLorentzNorm f 0 q μ = 0 := by simp [eLorentzNorm_def, hf]

@[simp]
theorem eLorentzNorm_exponent_zero_right (hf : AEStronglyMeasurable f μ) :
    eLorentzNorm f p 0 μ = 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [hf]
  · exact (eLorentzNorm_eq_eLpNorm hf hp).trans <|
      eLpNorm_exponent_zero (μ.measurable_rpow_mul_decreasingRearrangement _ _).aestronglyMeasurable

@[simp]
theorem memLorentz_zero_left : MemLorentz f 0 q μ ↔ AEStronglyMeasurable f μ :=
  ⟨MemLorentz.aestronglyMeasurable, fun hf ↦ by simp [MemLorentz, hf]⟩

@[simp]
theorem memLorentz_zero_right : MemLorentz f p 0 μ ↔ AEStronglyMeasurable f μ :=
  ⟨MemLorentz.aestronglyMeasurable, fun hf ↦ by simp [MemLorentz, hf]⟩

@[simp]
theorem eLorentzNorm_measure_zero : eLorentzNorm f p q (0 : Measure α) = 0 := by
  have hf : AEStronglyMeasurable f (0 : Measure α) := aestronglyMeasurable_zero_measure f
  rcases eq_or_ne p 0 with rfl | hp
  · simp [hf]
  · simp [eLorentzNorm_eq_eLpNorm hf hp]

@[simp]
theorem memLorentz_measure_zero : MemLorentz f p q (0 : Measure α) := by simp [MemLorentz]

/-! ### Congruence, monotonicity, and rearrangement invariance -/

theorem eLorentzNorm_congr_eNorm_ae {ε' : Type*} [TopologicalSpace ε'] [ENorm ε'] {g : α → ε'}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (h : (‖f ·‖ₑ) =ᵐ[μ] (‖g ·‖ₑ)) :
    eLorentzNorm f p q μ = eLorentzNorm g p q μ := by
  simp only [eLorentzNorm_def, hf, hg, ↓reduceIte, μ.decreasingRearrangement_congr_ae h]

theorem eLorentzNorm_congr_ae (h : f =ᵐ[μ] g) :
    eLorentzNorm f p q μ = eLorentzNorm g p q μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · exact eLorentzNorm_congr_eNorm_ae hf (hf.congr h) (h.mono fun _ hx ↦ congrArg eNorm hx)
  · rw [eLorentzNorm_of_not_aestronglyMeasurable hf,
      eLorentzNorm_of_not_aestronglyMeasurable fun hg ↦ hf (hg.congr h.symm)]

theorem memLorentz_congr_ae (h : f =ᵐ[μ] g) : MemLorentz f p q μ ↔ MemLorentz g p q μ := by
  simp only [MemLorentz, eLorentzNorm_congr_ae h]

theorem MemLorentz.ae_eq (h : f =ᵐ[μ] g) (hf : MemLorentz f p q μ) : MemLorentz g p q μ :=
  (memLorentz_congr_ae h).1 hf

@[simp]
theorem eLorentzNorm_eNorm {ε' : Type*} [TopologicalSpace ε'] [ContinuousENorm ε'] {f : α → ε'}
    (hf : AEStronglyMeasurable f μ) :
    eLorentzNorm (fun x ↦ ‖f x‖ₑ) p q μ = eLorentzNorm f p q μ :=
  eLorentzNorm_congr_eNorm_ae hf.eNorm.aestronglyMeasurable hf
    (Eventually.of_forall fun _ ↦ eNorm_eNorm _)

theorem MemLorentz.eNorm {ε' : Type*} [TopologicalSpace ε'] [ContinuousENorm ε'] {f : α → ε'}
    (hf : MemLorentz f p q μ) : MemLorentz (fun x ↦ ‖f x‖ₑ) p q μ := by
  simpa [MemLorentz, hf.aestronglyMeasurable] using hf

theorem memLorentz_eNorm_iff {ε' : Type*} [TopologicalSpace ε'] [ContinuousENorm ε'] {f : α → ε'}
    (hf : AEStronglyMeasurable f μ) :
    MemLorentz (fun x ↦ ‖f x‖ₑ) p q μ ↔ MemLorentz f p q μ := by simp [MemLorentz, hf]

theorem eLorentzNorm_mono_eNorm_ae {ε' : Type*} [TopologicalSpace ε'] [ENorm ε'] {g : α → ε'}
    (hf : AEStronglyMeasurable f μ) (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    eLorentzNorm f p q μ ≤ eLorentzNorm g p q μ := by
  by_cases hg : AEStronglyMeasurable g μ; swap
  · simp [eLorentzNorm_of_not_aestronglyMeasurable hg]
  rcases eq_or_ne p 0 with rfl | hp
  · simp [hf, hg]
  rw [eLorentzNorm_eq_eLpNorm hf hp, eLorentzNorm_eq_eLpNorm hg hp]
  exact eLpNorm_mono_eNorm_ae
    (μ.measurable_rpow_mul_decreasingRearrangement _ _).aestronglyMeasurable
    (Eventually.of_forall fun t ↦ by
      simpa using mul_le_mul_right (μ.decreasingRearrangement_mono_ae h t) _)

theorem MemLorentz.of_le_eNorm {ε' : Type*} [TopologicalSpace ε'] [ENorm ε'] {g : α → ε'}
    (hg : MemLorentz g p q μ) (hf : AEStronglyMeasurable f μ) (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    MemLorentz f p q μ :=
  (eLorentzNorm_mono_eNorm_ae hf h).trans_lt hg

/-- Taking the decreasing rearrangement of `‖f ·‖ₑ` onto `(0, ∞)` preserves the Lorentz gauge. -/
theorem eLorentzNorm_decreasingRearrangement_eNorm (hf : AEStronglyMeasurable f μ) :
    eLorentzNorm (μ.decreasingRearrangement (‖f ·‖ₑ)) p q (volume.restrict (Ioi 0)) =
      eLorentzNorm f p q μ := by
  have hm : AEStronglyMeasurable (μ.decreasingRearrangement (‖f ·‖ₑ)) (volume.restrict (Ioi 0)) :=
    (μ.measurable_decreasingRearrangement _).aestronglyMeasurable
  simp only [eLorentzNorm_def, hm, hf, ↓reduceIte, eNorm_eq_self,
    μ.decreasingRearrangement_decreasingRearrangement]

/-- **Diagonal identity:** at `q = p`, the Lorentz gauge agrees with the `L^p` seminorm for every
function, exponent `p ∈ [0, ∞]`, and measure `μ`. -/
@[simp]
theorem eLorentzNorm_self {ε' : Type*} [TopologicalSpace ε'] [ContinuousENorm ε'] (f : α → ε')
    (p : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm f p p μ = eLpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ; swap
  · rw [eLorentzNorm_of_not_aestronglyMeasurable hf, eLpNorm_of_not_aestronglyMeasurable hf]
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [eLorentzNorm_exponent_zero_left hf, eLpNorm_exponent_zero hf]
  have hmeas := (μ.measurable_rpow_mul_decreasingRearrangement (‖f ·‖ₑ) (p⁻¹).toReal)
    |>.aestronglyMeasurable (μ := multHaar)
  rcases eq_or_ne p ∞ with rfl | hptop
  · rw [eLorentzNorm_eq_eLpNorm hf hp0, eLpNorm_exponent_top hmeas, eLpNorm_exponent_top hf,
      eLpNormEssSup_eq_essSup_eNorm, eLpNormEssSup_eq_essSup_eNorm]
    simp only [ENNReal.inv_top, ENNReal.toReal_zero, Real.rpow_zero, ENNReal.ofReal_one, one_mul,
      eNorm_eq_self, essSup_multHaar_eq_iSup_Ioi fun t _ ↦
        μ.continuousWithinAt_decreasingRearrangement (‖f ·‖ₑ) t]
    exact le_antisymm (iSup₂_le fun t _ ↦ μ.decreasingRearrangement_le_essSup (‖f ·‖ₑ) t) <|
      le_of_tendsto (μ.tendsto_decreasingRearrangement_nhdsGT_zero (‖f ·‖ₑ))
        (eventually_nhdsWithin_of_forall fun t ht ↦ le_iSup₂_of_le t ht le_rfl)
  · have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
    rw [eLorentzNorm_eq_eLpNorm hf hp0, eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hptop hmeas,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hptop hf]
    congr 1
    rw [lintegral_multHaar_eq_setLIntegral, ← μ.lintegral_rpow_decreasingRearrangement hf.eNorm hr]
    refine setLIntegral_congr_fun measurableSet_Ioi fun t (ht : 0 < t) ↦ ?_
    simp only [eNorm_eq_self, ENNReal.toReal_inv]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le,
      ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos ht _), ← Real.rpow_mul ht.le,
      inv_mul_cancel₀ hr.ne', Real.rpow_one, ← mul_assoc,
      ← ENNReal.ofReal_mul (inv_nonneg.2 ht.le), inv_mul_cancel₀ ht.ne', ENNReal.ofReal_one,
      one_mul]

/-- On the diagonal `q = p`, membership in `L^{p, p}(μ)` coincides with `MemLp f p μ`. -/
@[simp]
theorem memLorentz_self {ε' : Type*} [TopologicalSpace ε'] [ContinuousENorm ε'] {f : α → ε'} :
    MemLorentz f p p μ ↔ MemLp f p μ := by
  rw [MemLorentz, memLp_iff, eLorentzNorm_self]

/-- Positive powers of the extended norm rescale both Lorentz exponents:
`‖‖f ·‖ₑ ^ r‖_{p, q} = ‖f‖_{p r, q r} ^ r`. -/
theorem eLorentzNorm_eNorm_rpow {ε' : Type*} [TopologicalSpace ε'] [ContinuousENorm ε']
    (f : α → ε') (hf : AEStronglyMeasurable f μ) {r : ℝ} (hr : 0 < r) :
    eLorentzNorm (‖f ·‖ₑ ^ r) p q μ =
      eLorentzNorm f (p * ENNReal.ofReal r) (q * ENNReal.ofReal r) μ ^ r := by
  have hfr : AEStronglyMeasurable (‖f ·‖ₑ ^ r) μ := (hf.eNorm.pow_const r).aestronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp
  · simp [hf, hfr, ENNReal.zero_rpow_of_pos hr]
  have hr_ne : ENNReal.ofReal r ≠ 0 := (ENNReal.ofReal_pos.2 hr).ne'
  have hpr : p * ENNReal.ofReal r ≠ 0 := mul_ne_zero hp hr_ne
  rw [eLorentzNorm_eq_eLpNorm hfr hp, eLorentzNorm_eq_eLpNorm hf hpr]
  have hexp : ((p * ENNReal.ofReal r)⁻¹).toReal * r = (p⁻¹).toReal := by
    rw [ENNReal.mul_inv (Or.inl hp) (Or.inr hr_ne), ENNReal.toReal_mul, ENNReal.toReal_inv,
      ENNReal.toReal_inv, ENNReal.toReal_ofReal hr.le, mul_assoc, inv_mul_cancel₀ hr.ne', mul_one]
  set g : ℝ → ℝ≥0∞ := fun t ↦
    ENNReal.ofReal (t ^ ((p * ENNReal.ofReal r)⁻¹).toReal) * μ.decreasingRearrangement (‖f ·‖ₑ) t
  have hae : (fun t : ℝ ↦ ENNReal.ofReal (t ^ (p⁻¹).toReal) *
      μ.decreasingRearrangement (‖(‖f ·‖ₑ ^ r) ·‖ₑ) t) =ᵐ[multHaar] (‖g ·‖ₑ ^ r) := by
    filter_upwards [ae_pos_multHaar] with t ht
    simp only [eNorm_eq_self, μ.decreasingRearrangement_rpow (‖f ·‖ₑ) hr t, g]
    rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le,
      ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos ht _), ← Real.rpow_mul ht.le, hexp]
  exact (eLpNorm_congr_ae hae).trans <|
    eLpNorm_eNorm_rpow g (μ.measurable_rpow_mul_decreasingRearrangement _ _).aestronglyMeasurable hr

/-! ### Weak `L^p` (`q = ∞`) and Chebyshev's inequality -/

/-- For `p ≠ 0` and an a.e. strongly measurable `f`, `‖f‖_{p, ∞}` is the pointwise supremum of
`t ^ (1 / p) f*(t)` over `t > 0`. -/
theorem eLorentzNorm_top_eq_iSup_Ioi (hf : AEStronglyMeasurable f μ) (hp : p ≠ 0) :
    eLorentzNorm f p ∞ μ =
      ⨆ t > 0, ENNReal.ofReal (t ^ (p⁻¹).toReal) * μ.decreasingRearrangement (‖f ·‖ₑ) t := by
  have hmeas := (μ.measurable_rpow_mul_decreasingRearrangement (‖f ·‖ₑ) (p⁻¹).toReal)
    |>.aestronglyMeasurable (μ := multHaar)
  rw [eLorentzNorm_eq_eLpNorm hf hp, eLpNorm_exponent_top hmeas, eLpNormEssSup_eq_essSup_eNorm]
  exact essSup_multHaar_eq_iSup_Ioi fun t ht ↦
    μ.continuousWithinAt_rpow_mul_decreasingRearrangement _ _ ht

/-- **Distribution-function formula for weak `L^p`.** For `0 < p < ∞` and an a.e. strongly
measurable `f`, `‖f‖_{p, ∞} = ⨆ c, c * μ {‖f‖ > c} ^ (1 / p)`. -/
theorem eLorentzNorm_top_eq_iSup_mul_measure_rpow (hf : AEStronglyMeasurable f μ)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    eLorentzNorm f p ∞ μ = ⨆ c : ℝ≥0∞, c * μ {y | c < ‖f y‖ₑ} ^ (p⁻¹).toReal := by
  set r := (p⁻¹).toReal
  have hr : 0 < r := ENNReal.toReal_pos (ENNReal.inv_ne_zero.2 hptop) (ENNReal.inv_ne_top.2 hp0)
  rw [eLorentzNorm_top_eq_iSup_Ioi hf hp0]
  refine le_antisymm (iSup₂_le fun t ht ↦ ?_) (iSup_le fun c ↦ ?_)
  · simp_rw [Measure.decreasingRearrangement_def, ENNReal.mul_iSup]
    refine iSup_le fun c ↦ iSup_le fun hct ↦ le_iSup_of_le c ?_
    rw [mul_comm, ← ENNReal.ofReal_rpow_of_pos ht]
    exact mul_le_mul_right (ENNReal.rpow_le_rpow hct.le hr.le) c
  · set M := μ {y | c < ‖f y‖ₑ}
    have hM : M ^ r ≤ ⨆ (t : ℝ) (_ : 0 < t) (_ : ENNReal.ofReal t < M), ENNReal.ofReal (t ^ r) := by
      refine le_of_forall_lt_imp_le_of_dense fun a ha ↦ ?_
      rcases eq_or_ne a 0 with rfl | ha0
      · exact bot_le
      have haM : a ^ r⁻¹ < M := by
        rwa [← ENNReal.rpow_lt_rpow_iff hr, ← ENNReal.rpow_mul, inv_mul_cancel₀ hr.ne',
          ENNReal.rpow_one]
      have hafin : a ^ r⁻¹ ≠ ∞ := ENNReal.rpow_ne_top_of_nonneg (inv_nonneg.2 hr.le) ha.ne_top
      set t := (a ^ r⁻¹).toReal
      have ht0 : 0 < t :=
        ENNReal.toReal_pos (ENNReal.rpow_pos (pos_iff_ne_zero.2 ha0) ha.ne_top).ne' hafin
      have ht_eq : ENNReal.ofReal t = a ^ r⁻¹ := ENNReal.ofReal_toReal hafin
      have ha_eq : a = ENNReal.ofReal (t ^ r) := by
        rw [← ENNReal.ofReal_rpow_of_pos ht0, ht_eq, ← ENNReal.rpow_mul, inv_mul_cancel₀ hr.ne',
          ENNReal.rpow_one]
      exact ha_eq.le.trans <| le_iSup₂_of_le t ht0 <| le_iSup_of_le (i := ht_eq ▸ haM) le_rfl
    refine (mul_le_mul_right hM c).trans ?_
    simp_rw [ENNReal.mul_iSup]
    refine iSup₂_le fun t ht0 ↦ iSup_le fun htM ↦ le_iSup₂_of_le t ht0 ?_
    exact mul_comm c _ ▸ mul_le_mul_right (μ.lt_decreasingRearrangement_iff.2 htM).le _

/-- **Chebyshev's inequality for weak `L^p`.** For `0 < p < ∞` and finite `c > 0`,
`μ {‖f‖ > c} ≤ (‖f‖_{p, ∞} / c) ^ p`. No measurability hypothesis on `f` is needed. -/
theorem measure_gt_le_eLorentzNorm_top_div_rpow (hp0 : p ≠ 0) (hptop : p ≠ ∞)
    {c : ℝ≥0∞} (hc0 : c ≠ 0) (hctop : c ≠ ∞) :
    μ {y | c < ‖f y‖ₑ} ≤ (eLorentzNorm f p ∞ μ / c) ^ p.toReal := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  by_cases hf : AEStronglyMeasurable f μ; swap
  · simp [eLorentzNorm_of_not_aestronglyMeasurable hf, ENNReal.top_div_of_ne_top hctop,
      ENNReal.top_rpow_of_pos hp]
  have hle : c * μ {y | c < ‖f y‖ₑ} ^ (p⁻¹).toReal ≤ eLorentzNorm f p ∞ μ :=
    eLorentzNorm_top_eq_iSup_mul_measure_rpow hf hp0 hptop ▸
      le_iSup (fun c : ℝ≥0∞ ↦ c * μ {y | c < ‖f y‖ₑ} ^ (p⁻¹).toReal) c
  have hdiv : μ {y | c < ‖f y‖ₑ} ^ (p⁻¹).toReal ≤ eLorentzNorm f p ∞ μ / c :=
    ENNReal.le_div_iff_mul_le (Or.inl hc0) (Or.inl hctop) |>.2 (mul_comm c _ ▸ hle)
  exact (ENNReal.rpow_le_rpow hdiv hp.le).trans' <| by
    rw [← ENNReal.rpow_mul, ENNReal.toReal_inv, inv_mul_cancel₀ hp.ne', ENNReal.rpow_one]

/-! ### Scalar multiplication in `ℝ≥0∞`, indicators, and secondary-exponent embeddings -/

/-- Multiplication by a constant in `ℝ≥0∞` commutes with the Lorentz gauge of an a.e. measurable
function. -/
theorem eLorentzNorm_const_mul_ennreal {h : α → ℝ≥0∞} (c : ℝ≥0∞)
    (hh : AEStronglyMeasurable h μ) :
    eLorentzNorm (fun x ↦ c * h x) p q μ = c * eLorentzNorm h p q μ := by
  have hch := (hh.aemeasurable.const_mul c).aestronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp
  · simp [hh, hch]
  rw [eLorentzNorm_eq_eLpNorm hch hp, eLorentzNorm_eq_eLpNorm hh hp,
    ← eLpNorm_const_mul_ennreal
      (μ.measurable_rpow_mul_decreasingRearrangement _ _).aestronglyMeasurable]
  congr 1 with t
  simp only [eNorm_eq_self, μ.decreasingRearrangement_const_mul, mul_left_comm]

private theorem eLorentzNorm_indicator_one {A : Set α} (hA : NullMeasurableSet A μ)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) (hq0 : q ≠ 0) :
    eLorentzNorm (A.indicator fun _ ↦ (1 : ℝ≥0∞)) p q μ =
      ENNReal.ofReal ((p.toReal / q.toReal) ^ q.toReal⁻¹) * μ A ^ (p⁻¹).toReal := by
  have h1 : AEStronglyMeasurable (A.indicator fun _ ↦ (1 : ℝ≥0∞)) μ :=
    aestronglyMeasurable_const.indicator₀ hA
  have hrp : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  set r := (p⁻¹).toReal
  have hr : 0 < r := by simpa [r] using inv_pos.2 hrp
  rcases eq_or_ne q ∞ with rfl | hqtop
  · simp only [ENNReal.toReal_top, div_zero, inv_zero, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
    rw [eLorentzNorm_top_eq_iSup_mul_measure_rpow h1 hp0 hptop]
    have hlt {b : ℝ≥0∞} (hb : b < 1) :
        {y | b < ‖A.indicator (fun _ ↦ (1 : ℝ≥0∞)) y‖ₑ} = A := by
      ext y; by_cases hy : y ∈ A <;> simp [hy, hb]
    refine le_antisymm (iSup_le fun b ↦ ?_)
      (ENNReal.le_of_forall_lt_one_mul_le fun b hb ↦ le_iSup_of_le b (by rw [hlt hb]))
    rcases lt_or_ge b 1 with hb | hb
    · rw [hlt hb]; exact (mul_le_mul' hb.le le_rfl).trans_eq (one_mul _)
    · have h0 : {y | b < ‖A.indicator (fun _ ↦ (1 : ℝ≥0∞)) y‖ₑ} = ∅ := by
        ext y; by_cases hy : y ∈ A <;> simp [hy, not_lt.2 hb]
      rw [h0, measure_empty, ENNReal.zero_rpow_of_pos hr, mul_zero]; exact bot_le
  · have hrq : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
    have hmeas := (μ.measurable_rpow_mul_decreasingRearrangement
      (‖A.indicator (fun _ ↦ (1 : ℝ≥0∞)) ·‖ₑ) r).aestronglyMeasurable (μ := multHaar)
    rw [eLorentzNorm_eq_eLpNorm h1 hp0, eLpNorm_eq_lintegral_rpow_eNorm_toReal hq0 hqtop hmeas,
      lintegral_multHaar_eq_setLIntegral]
    simp only [eNorm_eq_self, one_div]
    have hcongr : ∀ t ∈ Ioi (0 : ℝ),
        ENNReal.ofReal t⁻¹ * (ENNReal.ofReal (t ^ r) *
          μ.decreasingRearrangement (A.indicator fun _ ↦ (1 : ℝ≥0∞)) t) ^ q.toReal =
        {t : ℝ | ENNReal.ofReal (1 * t) < μ A}.indicator
          (fun t ↦ ENNReal.ofReal (t ^ (r * q.toReal - 1))) t := fun t ht ↦ by
      rw [μ.decreasingRearrangement_indicator]
      by_cases htA : ENNReal.ofReal t < μ A
      · have hmem : t ∈ {t : ℝ | ENNReal.ofReal (1 * t) < μ A} := by simpa using htA
        simp only [htA, ↓reduceIte, indicator_of_mem hmem, mul_one]
        rw [ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos ht r), ← Real.rpow_mul ht.le,
          ← ENNReal.ofReal_mul (inv_nonneg.2 ht.le), Real.rpow_sub ht, Real.rpow_one,
          inv_mul_eq_div]
      · simp [htA, ENNReal.zero_rpow_of_pos hrq]
    have hα : 0 < r * q.toReal := mul_pos hr hrq
    have hdiv : 1 / (r * q.toReal) = p.toReal / q.toReal := by
      simp only [r, ENNReal.toReal_inv]; field_simp
    rw [setLIntegral_congr_fun measurableSet_Ioi hcongr,
      lintegral_indicator_ofReal_rpow_Ioi (by linarith) one_pos (μ A),
      Real.one_rpow, sub_add_cancel, hdiv, ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hrq.le),
      ENNReal.ofReal_rpow_of_pos (div_pos hrp hrq), ← ENNReal.rpow_mul, mul_assoc,
      mul_inv_cancel₀ hrq.ne', mul_one]

/-- Pointwise control of the rearrangement by any Lorentz gauge: for `0 < p < ∞`, `q₀ ≠ 0`, and
`t > 0`, `t ^ (1 / p) f*(t) ≤ (q₀ / p) ^ (1 / q₀) ‖f‖_{p, q₀}`. -/
theorem rpow_mul_decreasingRearrangement_le_eLorentzNorm (hf : AEStronglyMeasurable f μ)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) {q₀ : ℝ≥0∞} (hq₀ : q₀ ≠ 0) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (p⁻¹).toReal) * μ.decreasingRearrangement (‖f ·‖ₑ) t ≤
      ENNReal.ofReal ((q₀.toReal / p.toReal) ^ q₀.toReal⁻¹) * eLorentzNorm f p q₀ μ := by
  rcases eq_or_ne q₀ ∞ with rfl | hq₀top
  · simp only [ENNReal.toReal_top, zero_div, inv_zero, Real.rpow_zero, ENNReal.ofReal_one, one_mul,
      eLorentzNorm_top_eq_iSup_Ioi hf hp0]
    exact le_iSup₂_of_le t ht le_rfl
  set ν := volume.restrict (Ioi (0 : ℝ))
  set c := μ.decreasingRearrangement (‖f ·‖ₑ) t
  have hrp : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hrq : 0 < q₀.toReal := ENNReal.toReal_pos hq₀ hq₀top
  have h1 : AEStronglyMeasurable ((Ioo 0 t).indicator fun _ ↦ (1 : ℝ≥0∞)) ν :=
    aestronglyMeasurable_const.indicator measurableSet_Ioo
  have hstep : c * (ENNReal.ofReal ((p.toReal / q₀.toReal) ^ q₀.toReal⁻¹) *
      ENNReal.ofReal (t ^ (p⁻¹).toReal)) ≤ eLorentzNorm f p q₀ μ := by
    have hν : ν (Ioo 0 t) = ENNReal.ofReal t := by
      rw [Measure.restrict_apply measurableSet_Ioo,
        inter_eq_self_of_subset_left Ioo_subset_Ioi_self, Real.volume_Ioo, sub_zero]
    rw [← ENNReal.ofReal_rpow_of_pos ht, ← hν,
      ← eLorentzNorm_indicator_one measurableSet_Ioo.nullMeasurableSet hp0 hptop hq₀,
      ← eLorentzNorm_const_mul_ennreal c h1, ← eLorentzNorm_decreasingRearrangement_eNorm hf]
    refine eLorentzNorm_mono_eNorm_ae (h1.aemeasurable.const_mul c).aestronglyMeasurable
      (Eventually.of_forall fun s ↦ ?_)
    by_cases hs : s ∈ Ioo 0 t
    · simpa [hs] using μ.antitone_decreasingRearrangement (‖f ·‖ₑ) hs.2.le
    · simp [hs]
  have hinv : ENNReal.ofReal ((q₀.toReal / p.toReal) ^ q₀.toReal⁻¹) *
      ENNReal.ofReal ((p.toReal / q₀.toReal) ^ q₀.toReal⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow (by positivity) (by positivity),
      div_mul_div_cancel₀ hrp.ne', div_self hrq.ne', Real.one_rpow, ENNReal.ofReal_one]
  exact (mul_le_mul_right hstep _).trans' <| by
    rw [mul_left_comm c, ← mul_assoc, hinv, one_mul, mul_comm]

/-- Weak-`L^p` embedding `‖f‖_{p, ∞} ≤ (q₀ / p) ^ (1 / q₀) ‖f‖_{p, q₀}` for `0 < p < ∞` and
`q₀ ≠ 0`. -/
theorem eLorentzNorm_top_le_eLorentzNorm (hp0 : p ≠ 0) (hptop : p ≠ ∞) {q₀ : ℝ≥0∞}
    (hq₀ : q₀ ≠ 0) :
    eLorentzNorm f p ∞ μ ≤
      ENNReal.ofReal ((q₀.toReal / p.toReal) ^ q₀.toReal⁻¹) * eLorentzNorm f p q₀ μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · rw [eLorentzNorm_top_eq_iSup_Ioi hf hp0]
    exact iSup₂_le fun t ht ↦ rpow_mul_decreasingRearrangement_le_eLorentzNorm hf hp0 hptop hq₀ ht
  · rcases eq_or_ne q₀ ∞ with rfl | hq₀top
    · simp [eLorentzNorm_of_not_aestronglyMeasurable hf]
    · have hpos := div_pos (ENNReal.toReal_pos hq₀ hq₀top) (ENNReal.toReal_pos hp0 hptop)
      simp [eLorentzNorm_of_not_aestronglyMeasurable hf,
        ENNReal.mul_top (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hpos _)).ne']

/-- **Secondary-exponent embedding** for Lorentz gauges: for `0 < p < ∞` and `0 < q₀ ≤ q₁ ≤ ∞`,
`‖f‖_{p, q₁} ≤ (q₀ / p) ^ (1 / q₀ - 1 / q₁) ‖f‖_{p, q₀}`. The constant `(q₀ / p) ^ (1 / q₀)` at
`q₁ = ∞` is attained by every indicator function of finite positive measure. -/
theorem eLorentzNorm_le_of_exponent_le (hp0 : p ≠ 0) (hptop : p ≠ ∞) {q₀ q₁ : ℝ≥0∞}
    (hq₀ : q₀ ≠ 0) (hq : q₀ ≤ q₁) :
    eLorentzNorm f p q₁ μ ≤
      ENNReal.ofReal ((q₀.toReal / p.toReal) ^ (q₀.toReal⁻¹ - q₁.toReal⁻¹)) *
        eLorentzNorm f p q₀ μ := by
  rcases eq_or_ne q₁ ∞ with rfl | hq₁top
  · simpa using eLorentzNorm_top_le_eLorentzNorm hp0 hptop hq₀ (f := f) (μ := μ)
  have hq₀top : q₀ ≠ ∞ := ne_top_of_le_ne_top hq₁top hq
  have hq₁0 : q₁ ≠ 0 := (pos_iff_ne_zero.2 hq₀ |>.trans_le hq).ne'
  have hrp : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hr₀ : 0 < q₀.toReal := ENNReal.toReal_pos hq₀ hq₀top
  have hr₁ : 0 < q₁.toReal := ENNReal.toReal_pos hq₁0 hq₁top
  have hrle : q₀.toReal ≤ q₁.toReal := ENNReal.toReal_mono hq₁top hq
  by_cases hf : AEStronglyMeasurable f μ; swap
  · simp [eLorentzNorm_of_not_aestronglyMeasurable hf,
      ENNReal.mul_top (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos (div_pos hr₀ hrp) _)).ne']
  set θ : ℝ := 1 - q₀.toReal / q₁.toReal
  have hθ0 : 0 ≤ θ := sub_nonneg.2 ((div_le_one hr₁).2 hrle)
  have hθ1 : θ ≤ 1 := sub_le_self 1 (div_nonneg hr₀.le hr₁.le)
  have h1θ : 1 - θ = q₀.toReal / q₁.toReal := sub_sub_cancel 1 _
  have hinv : q₁⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * ∞⁻¹ := by
    rw [ENNReal.inv_top, mul_zero, add_zero, h1θ,
      ENNReal.ofReal_div_of_pos hr₁, ENNReal.ofReal_toReal hq₀top,
      ENNReal.ofReal_toReal hq₁top, div_eq_mul_inv, mul_right_comm,
      ENNReal.mul_inv_cancel hq₀ hq₀top, one_mul]
  set g : ℝ → ℝ≥0∞ := fun t ↦
    ENNReal.ofReal (t ^ (p⁻¹).toReal) * μ.decreasingRearrangement (‖f ·‖ₑ) t
  have htop := eLorentzNorm_top_le_eLorentzNorm (f := f) (μ := μ) hp0 hptop hq₀
  simp_rw [eLorentzNorm_eq_eLpNorm hf hp0] at htop ⊢
  calc eLpNorm g q₁ multHaar
      ≤ eLpNorm g q₀ multHaar ^ (1 - θ) * eLpNorm g ∞ multHaar ^ θ :=
        eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow ⟨hθ0, hθ1⟩ hinv
    _ ≤ eLpNorm g q₀ multHaar ^ (1 - θ) *
          (ENNReal.ofReal ((q₀.toReal / p.toReal) ^ q₀.toReal⁻¹) *
            eLpNorm g q₀ multHaar) ^ θ := by gcongr
    _ = ENNReal.ofReal ((q₀.toReal / p.toReal) ^ (q₀.toReal⁻¹ - q₁.toReal⁻¹)) *
          eLpNorm g q₀ multHaar := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hθ0, mul_left_comm,
          ← ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.2 hθ1) hθ0, sub_add_cancel,
          ENNReal.rpow_one, ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos (div_pos hr₀ hrp) _),
          ← Real.rpow_mul (div_nonneg hr₀.le hrp.le)]
        congr 3
        simp only [θ]
        field_simp

/-- **Secondary-exponent embedding** for Lorentz classes: for `0 < p < ∞` (`p ≠ 0`, `p ≠ ∞`) and
`0 < q₀ ≤ q₁ ≤ ∞` (`q₀ ≠ 0`, `q₀ ≤ q₁`), `L^{p, q₀}(μ)` embeds into `L^{p, q₁}(μ)`. -/
theorem MemLorentz.mono_exponent (hp0 : p ≠ 0) (hptop : p ≠ ∞) {q₀ q₁ : ℝ≥0∞}
    (hq₀ : q₀ ≠ 0) (hq : q₀ ≤ q₁) (hf : MemLorentz f p q₀ μ) :
    MemLorentz f p q₁ μ :=
  (eLorentzNorm_le_of_exponent_le hp0 hptop hq₀ hq).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf)

end Defs

/-! ### Size of the decreasing rearrangement of an `Lᵖ` function -/

section Lp

variable {α ε : Type*} {mα : MeasurableSpace α} [TopologicalSpace ε] [ContinuousENorm ε]
  {μ : Measure α} {f : α → ε} {p : ℝ≥0∞}

/-- **Chebyshev's inequality for the decreasing rearrangement**: for `0 < p < ∞` and `t > 0`,
`t ^ (1 / p) f*(t) ≤ ‖f‖_p`. This is `TauCeti.rpow_mul_decreasingRearrangement_le_eLorentzNorm` at
the secondary exponent `p`, where the Lorentz gauge is the `Lᵖ` norm. -/
theorem rpow_mul_decreasingRearrangement_le_eLpNorm (hf : AEStronglyMeasurable f μ) (hp0 : p ≠ 0)
    (hptop : p ≠ ∞) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ (p⁻¹).toReal) * μ.decreasingRearrangement (‖f ·‖ₑ) t ≤ eLpNorm f p μ := by
  have h := rpow_mul_decreasingRearrangement_le_eLorentzNorm hf hp0 hptop hp0 ht
  simpa [(ENNReal.toReal_pos hp0 hptop).ne'] using h

/-- The decreasing rearrangement of a function in `Lᵖ`, `p ≠ 0`, is finite at positive
arguments. For `p = ∞` it is bounded by the essential supremum of `‖f‖ₑ`. -/
theorem _root_.MeasureTheory.MemLp.decreasingRearrangement_lt_top (hf : MemLp f p μ)
    (hp0 : p ≠ 0) {t : ℝ} (ht : 0 < t) :
    μ.decreasingRearrangement (‖f ·‖ₑ) t < ∞ := by
  rcases eq_or_ne p ∞ with rfl | hptop
  · refine (μ.decreasingRearrangement_le_essSup _ t).trans_lt ?_
    rw [← eLpNormEssSup_eq_essSup_eNorm, ← eLpNorm_exponent_top hf.aestronglyMeasurable]
    exact hf.eLpNorm_lt_top
  exact ENNReal.lt_top_of_mul_ne_top_right
    ((rpow_mul_decreasingRearrangement_le_eLpNorm hf.aestronglyMeasurable hp0 hptop ht).trans_lt
      hf.eLpNorm_lt_top).ne
    (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos ht _)).ne'

/-- The decreasing rearrangement of a function in `Lᵖ`, `0 < p < ∞`, tends to zero at infinity. -/
theorem _root_.MeasureTheory.MemLp.tendsto_decreasingRearrangement_atTop_nhds_zero
    (hf : MemLp f p μ) (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    Tendsto (μ.decreasingRearrangement (‖f ·‖ₑ)) atTop (𝓝 0) := by
  have hp : 0 < (p⁻¹).toReal :=
    ENNReal.toReal_pos (ENNReal.inv_ne_zero.2 hptop) (ENNReal.inv_ne_top.2 hp0)
  -- `f*(t) ≤ ‖f‖_p / t ^ (1 / p)`, which tends to `0`.
  have hlim : Tendsto (fun t : ℝ ↦ eLpNorm f p μ / ENNReal.ofReal (t ^ (p⁻¹).toReal)) atTop
      (𝓝 0) := by
    simpa using ENNReal.Tendsto.const_div
      (ENNReal.tendsto_ofReal_atTop.comp (tendsto_rpow_atTop hp)) (Or.inr hf.eLpNorm_ne_top)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim
    (Eventually.of_forall fun _ ↦ bot_le) ?_
  filter_upwards [eventually_gt_atTop 0] with t ht
  rw [ENNReal.le_div_iff_mul_le (Or.inl (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos ht _)).ne')
    (Or.inl ENNReal.ofReal_ne_top), mul_comm]
  exact rpow_mul_decreasingRearrangement_le_eLpNorm hf.aestronglyMeasurable hp0 hptop ht

/-! ### Square summability of the dyadic levels -/

/-- Dyadic sum and Lorentz gauge: with `φ(t) = t^{1/q} f*(t)`, the shifted levels
`2^{(k-1)/q} f*(2ᵏ)` have squared sum at most `(log 2)⁻¹ ∫ φ² dt / t`. -/
private theorem ofReal_log_two_mul_tsum_le_eLpNorm_multHaar {f : α → ε} {q : ℝ≥0∞}
    (hq : 0 < q.toReal) :
    ENNReal.ofReal (Real.log 2) * ∑' k : ℤ, (ENNReal.ofReal ((2 : ℝ) ^ (k - 1)) ^ q.toReal⁻¹ *
        μ.decreasingRearrangement (fun x ↦ ‖f x‖ₑ) ((2 : ℝ) ^ k)) ^ (2 : ℝ) ≤
      eLpNorm (fun t ↦ ENNReal.ofReal (t ^ q.toReal⁻¹) *
        μ.decreasingRearrangement (fun x ↦ ‖f x‖ₑ) t) 2 multHaar ^ (2 : ℝ) := by
  set φ : ℝ → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (t ^ q.toReal⁻¹) *
    μ.decreasingRearrangement (fun x ↦ ‖f x‖ₑ) t
  have hφ2 : ∫⁻ t, φ t ^ (2 : ℝ) ∂multHaar = eLpNorm φ 2 multHaar ^ (2 : ℝ) := by
    simpa only [ENNReal.rpow_two] using (eLpNorm_two_sq_eq_lintegral_sq
      (μ.measurable_rpow_mul_decreasingRearrangement _ _).aemeasurable).symm
  -- On `[2ᵏ⁻¹, 2ᵏ)` the `k`-th term is at most `φ²`.
  have hcmp := ofReal_mul_tsum_int_le_lintegral_multHaar (b := 2) (c := 2⁻¹) (μ := 1)
    one_le_two (by norm_num) (f := fun t ↦ φ t ^ (2 : ℝ))
    (g := fun k ↦ (ENNReal.ofReal ((2 : ℝ) ^ (k - 1)) ^ q.toReal⁻¹ *
      μ.decreasingRearrangement (fun x ↦ ‖f x‖ₑ) ((2 : ℝ) ^ k)) ^ (2 : ℝ)) fun k r hr ↦ by
      have hk : (2 : ℝ)⁻¹ * 2 ^ ((1 : ℝ) * k) = 2 ^ (k - 1) := by
        rw [one_mul, Real.rpow_intCast, zpow_sub₀ two_ne_zero, zpow_one, mul_comm, div_eq_mul_inv]
      have hk' : (2 : ℝ)⁻¹ * 2 ^ ((1 : ℝ) * k + |1|) = 2 ^ k := by
        rw [abs_one, one_mul, Real.rpow_add two_pos, Real.rpow_intCast, Real.rpow_one]
        field_simp
      rw [hk, hk'] at hr
      simp only [φ]
      rw [ENNReal.ofReal_rpow_of_nonneg (zpow_pos two_pos _).le (inv_nonneg.2 hq.le)]
      gcongr ?_ ^ _
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (zpow_pos two_pos _).le hr.1
        (inv_nonneg.2 hq.le))) (μ.antitone_decreasingRearrangement _ hr.2.le)
  rwa [abs_one, one_mul, hφ2] at hcmp

/-- `(2^{k/q} a)² = 2^{2/q} (2^{(k-1)/q} a)²`. -/
private theorem ofReal_two_zpow_rpow_mul_rpow_two {q : ℝ} (hq : 0 < q) (k : ℤ) (a : ℝ≥0∞) :
    (ENNReal.ofReal ((2 : ℝ) ^ k) ^ q⁻¹ * a) ^ (2 : ℝ) =
      ENNReal.ofReal (2 ^ (2 / q)) * (ENNReal.ofReal ((2 : ℝ) ^ (k - 1)) ^ q⁻¹ * a) ^ (2 : ℝ) := by
  have h2k : (2 : ℝ) ^ k = 2 * 2 ^ (k - 1) := by
    rw [zpow_sub₀ two_ne_zero, zpow_one]
    field_simp
  rw [h2k, ENNReal.ofReal_mul zero_le_two, ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hq.le),
    mul_assoc, ENNReal.mul_rpow_of_nonneg _ _ zero_le_two, ← ENNReal.rpow_mul,
    ENNReal.ofReal_rpow_of_nonneg zero_le_two (by positivity), inv_mul_eq_div]

/-- **Square summability of the normalized dyadic levels.** For `0 < q ≤ 2` and an almost
everywhere strongly measurable `f`, the levels `f*(2ᵏ)` of the decreasing rearrangement of `‖f‖ₑ`
satisfy

`∑ₖ (2^{k/q} f*(2ᵏ))² ≤ 2^{2/q} (log 2)⁻¹ ‖f‖_q²`.

The left side is a dyadic discretization of the square of the Lorentz gauge `‖f‖_{q,2}`, which is
at most `‖f‖_q` since `q ≤ 2`. -/
theorem tsum_rpow_mul_decreasingRearrangement_sq_le {f : α → ε} (hf : AEStronglyMeasurable f μ)
    {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq2 : q ≤ 2) :
    ∑' k : ℤ, (ENNReal.ofReal ((2 : ℝ) ^ k) ^ q.toReal⁻¹ *
        μ.decreasingRearrangement (fun x ↦ ‖f x‖ₑ) ((2 : ℝ) ^ k)) ^ (2 : ℝ) ≤
      ENNReal.ofReal (2 ^ (2 / q.toReal) / Real.log 2) * eLpNorm f q μ ^ (2 : ℝ) := by
  have hqtop : q ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofNat_ne_top hq2
  have hq : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  -- The Lorentz gauge `‖f‖_{q,2}` is at most `‖f‖_q`.
  have hlor : eLpNorm (fun t ↦ ENNReal.ofReal (t ^ q.toReal⁻¹) *
      μ.decreasingRearrangement (fun x ↦ ‖f x‖ₑ) t) 2 multHaar ≤ eLpNorm f q μ := by
    have h := eLorentzNorm_le_of_exponent_le (f := f) (μ := μ) hq0 hqtop hq0 hq2
    simpa [hq.ne', eLorentzNorm_eq_eLpNorm hf hq0, ENNReal.toReal_inv] using h
  rw [tsum_congr fun k ↦ ofReal_two_zpow_rpow_mul_rpow_two hq k
    (μ.decreasingRearrangement (fun x ↦ ‖f x‖ₑ) ((2 : ℝ) ^ k)), ENNReal.tsum_mul_left]
  calc _ ≤ ENNReal.ofReal (2 ^ (2 / q.toReal)) * ((ENNReal.ofReal (Real.log 2))⁻¹ *
        eLpNorm (fun t ↦ ENNReal.ofReal (t ^ q.toReal⁻¹) *
          μ.decreasingRearrangement (fun x ↦ ‖f x‖ₑ) t) 2 multHaar ^ (2 : ℝ)) := by
        gcongr
        rw [← ENNReal.div_eq_inv_mul, ENNReal.le_div_iff_mul_le (Or.inl (by simpa using hlog))
          (Or.inl ENNReal.ofReal_ne_top), mul_comm]
        exact ofReal_log_two_mul_tsum_le_eLpNorm_multHaar hq
    _ ≤ ENNReal.ofReal (2 ^ (2 / q.toReal)) *
          ((ENNReal.ofReal (Real.log 2))⁻¹ * eLpNorm f q μ ^ (2 : ℝ)) := by
        gcongr
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_inv_of_pos hlog, ← ENNReal.ofReal_mul (by positivity),
          ← div_eq_mul_inv]

end Lp

/-! ### Zero, indicators, scalar multiplication, and quasi-triangle inequality -/

section Algebraic

variable {α : Type*} {mα : MeasurableSpace α} {μ : Measure α} {p q : ℝ≥0∞}

section ESeminormedAddMonoid

variable {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε] {f g : α → ε}

@[simp]
theorem eLorentzNorm_zero : eLorentzNorm (0 : α → ε) p q μ = 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [aestronglyMeasurable_zero]
  · have h0 : (‖(0 : α → ε) ·‖ₑ) = 0 := by ext; simp
    rw [eLorentzNorm_eq_eLpNorm aestronglyMeasurable_zero hp, h0]; simp

@[simp]
theorem MemLorentz.zero : MemLorentz (0 : α → ε) p q μ := by simp [MemLorentz]

/-- **Indicator formula for Lorentz gauges.** For `0 < p < ∞`, `0 < q ≤ ∞`, and a `μ`-null
measurable set `A`, `‖c 1_A‖_{p, q} = ‖c‖ₑ * (p / q) ^ (1 / q) * (μ A) ^ (1 / p)` (where the
middle factor is `1` at `q = ∞`). -/
theorem eLorentzNorm_indicator_const {A : Set α} (hA : NullMeasurableSet A μ) (c : ε)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) (hq0 : q ≠ 0) :
    eLorentzNorm (A.indicator fun _ ↦ c) p q μ =
      ‖c‖ₑ * ENNReal.ofReal ((p.toReal / q.toReal) ^ q.toReal⁻¹) * μ A ^ (p⁻¹).toReal := by
  have heq : (fun x ↦ ‖A.indicator (fun _ ↦ c) x‖ₑ) =
      fun x ↦ ‖c‖ₑ * A.indicator (fun _ ↦ (1 : ℝ≥0∞)) x := by
    ext x; by_cases hx : x ∈ A <;> simp [hx]
  rw [← eLorentzNorm_eNorm (aestronglyMeasurable_const.indicator₀ hA), heq,
    eLorentzNorm_const_mul_ennreal ‖c‖ₑ (aestronglyMeasurable_const.indicator₀ hA),
    eLorentzNorm_indicator_one hA hp0 hptop hq0, mul_assoc]

/-- At `q = ∞` and `0 < p < ∞`, `‖c 1_A‖_{p, ∞} = ‖c‖ₑ * (μ A) ^ (1 / p)`. -/
theorem eLorentzNorm_indicator_const_top {A : Set α} (hA : NullMeasurableSet A μ) (c : ε)
    (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    eLorentzNorm (A.indicator fun _ ↦ c) p ∞ μ = ‖c‖ₑ * μ A ^ (p⁻¹).toReal := by
  simpa using eLorentzNorm_indicator_const hA c hp0 hptop ENNReal.top_ne_zero

theorem eLorentzNorm_indicator_le (f : α → ε) {A : Set α} (hA : NullMeasurableSet A μ) :
    eLorentzNorm (A.indicator f) p q μ ≤ eLorentzNorm f p q μ := by
  by_cases hf : AEStronglyMeasurable f μ; swap
  · simp [eLorentzNorm_of_not_aestronglyMeasurable hf]
  refine eLorentzNorm_mono_eNorm_ae (hf.indicator₀ hA) (Eventually.of_forall fun x ↦ ?_)
  by_cases hx : x ∈ A <;> simp [hx]

theorem MemLorentz.indicator {A : Set α} (hA : NullMeasurableSet A μ) (hf : MemLorentz f p q μ) :
    MemLorentz (A.indicator f) p q μ :=
  (eLorentzNorm_indicator_le f hA).trans_lt hf

/-- The indicator of a `μ`-null measurable set of finite measure with a finite-norm value belongs
to `L^{p, q}(μ)` whenever `p ≠ ∞` or `q = ∞`. -/
theorem memLorentz_indicator_const {A : Set α} (hA : NullMeasurableSet A μ) (c : ε)
    (hp : p ≠ ∞ ∨ q = ∞) (hc : ‖c‖ₑ ≠ ∞) (hμA : μ A ≠ ∞) :
    MemLorentz (A.indicator fun _ ↦ c) p q μ := by
  have hf : AEStronglyMeasurable (A.indicator fun _ ↦ c) μ :=
    aestronglyMeasurable_const.indicator₀ hA
  rcases eq_or_ne p 0 with rfl | hp0
  · exact memLorentz_zero_left.2 hf
  rcases eq_or_ne q 0 with rfl | hq0
  · exact memLorentz_zero_right.2 hf
  rcases hp with hptop | rfl
  · rw [MemLorentz, eLorentzNorm_indicator_const hA c hp0 hptop hq0]
    exact ENNReal.mul_lt_top (ENNReal.mul_lt_top hc.lt_top ENNReal.ofReal_lt_top)
      (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg hμA)
  · rcases eq_or_ne p ∞ with rfl | hptop
    · rw [memLorentz_self, memLp_iff]
      exact (eLpNorm_indicator_const_le c ∞ hA).trans_lt (by simpa using hc.lt_top)
    · rw [MemLorentz, eLorentzNorm_indicator_const_top hA c hp0 hptop]
      exact ENNReal.mul_lt_top hc.lt_top (ENNReal.rpow_lt_top_of_nonneg ENNReal.toReal_nonneg hμA)

private theorem rpow_mul_decreasingRearrangement_add_le (f g : α → ε) (r : ℝ) {t : ℝ}
    (ht : 0 < t) :
    ENNReal.ofReal (t ^ r) * μ.decreasingRearrangement (‖(f + g) ·‖ₑ) t ≤
      ENNReal.ofReal (2 ^ r) *
        (ENNReal.ofReal ((2⁻¹ * t) ^ r) * μ.decreasingRearrangement (‖f ·‖ₑ) (2⁻¹ * t) +
          ENNReal.ofReal ((2⁻¹ * t) ^ r) * μ.decreasingRearrangement (‖g ·‖ₑ) (2⁻¹ * t)) := by
  have hdr : μ.decreasingRearrangement (‖(f + g) ·‖ₑ) t ≤
      μ.decreasingRearrangement (‖f ·‖ₑ) (2⁻¹ * t) +
        μ.decreasingRearrangement (‖g ·‖ₑ) (2⁻¹ * t) := by
    calc μ.decreasingRearrangement (‖(f + g) ·‖ₑ) t
        ≤ μ.decreasingRearrangement ((fun x ↦ ‖f x‖ₑ) + fun x ↦ ‖g x‖ₑ) (2⁻¹ * t + 2⁻¹ * t) := by
          rw [← two_mul, mul_inv_cancel_left₀ two_ne_zero]
          exact μ.decreasingRearrangement_mono_ae
            (Eventually.of_forall fun x ↦ eNorm_add_le (f x) (g x)) t
      _ ≤ _ := μ.decreasingRearrangement_add_le _ _ (by positivity) (by positivity)
  have htr : ENNReal.ofReal (t ^ r) =
      ENNReal.ofReal (2 ^ r) * ENNReal.ofReal ((2⁻¹ * t) ^ r) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow zero_le_two (by positivity),
      mul_inv_cancel_left₀ two_ne_zero]
  rw [htr]
  exact (mul_le_mul_right hdr _).trans_eq (by simp only [mul_add, mul_assoc])

section ContinuousAdd

variable [ContinuousAdd ε]

/-- **Quasi-triangle inequality for Lorentz gauges** across all `p, q ∈ [0, ∞]`:
`‖f + g‖_{p, q} ≤ LpAddConst q * 2 ^ (1 / p) * (‖f‖_{p, q} + ‖g‖_{p, q})`. -/
theorem eLorentzNorm_add_le' (p q : ℝ≥0∞) :
    eLorentzNorm (f + g) p q μ ≤
      ENNReal.LpAddConst q * ENNReal.ofReal (2 ^ (p⁻¹).toReal) *
        (eLorentzNorm f p q μ + eLorentzNorm g p q μ) := by
  have hC0 : ENNReal.LpAddConst q * ENNReal.ofReal (2 ^ (p⁻¹).toReal) ≠ 0 :=
    mul_ne_zero (ENNReal.LpAddConst_ne_zero q)
      (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos zero_lt_two _)).ne'
  by_cases hf : AEStronglyMeasurable f μ; swap
  · rw [eLorentzNorm_of_not_aestronglyMeasurable hf, top_add, ENNReal.mul_top hC0]; exact le_top
  by_cases hg : AEStronglyMeasurable g μ; swap
  · rw [eLorentzNorm_of_not_aestronglyMeasurable hg, add_top, ENNReal.mul_top hC0]; exact le_top
  have hfg : AEStronglyMeasurable (f + g) μ := hf.add hg
  rcases eq_or_ne p 0 with rfl | hp
  · simp [hfg]
  set r := (p⁻¹).toReal
  set F : ℝ → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (t ^ r) * μ.decreasingRearrangement (‖f ·‖ₑ) t
  set G : ℝ → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (t ^ r) * μ.decreasingRearrangement (‖g ·‖ₑ) t
  have hF : Measurable F := μ.measurable_rpow_mul_decreasingRearrangement (‖f ·‖ₑ) r
  have hG : Measurable G := μ.measurable_rpow_mul_decreasingRearrangement (‖g ·‖ₑ) r
  rw [eLorentzNorm_eq_eLpNorm hfg hp, eLorentzNorm_eq_eLpNorm hf hp, eLorentzNorm_eq_eLpNorm hg hp]
  calc eLpNorm (fun t ↦ ENNReal.ofReal (t ^ r) *
          μ.decreasingRearrangement (‖(f + g) ·‖ₑ) t) q multHaar
      ≤ eLpNorm (fun t ↦ ENNReal.ofReal (2 ^ r) * (F (2⁻¹ * t) + G (2⁻¹ * t))) q multHaar :=
        eLpNorm_mono_eNorm_ae
          (μ.measurable_rpow_mul_decreasingRearrangement _ _).aestronglyMeasurable
          (ae_pos_multHaar.mono fun t ht ↦ by
            simpa only [eNorm_eq_self, F, G] using
              rpow_mul_decreasingRearrangement_add_le (μ := μ) f g r ht)
      _ = ENNReal.ofReal (2 ^ r) *
          eLpNorm ((fun t ↦ F (2⁻¹ * t)) + fun t ↦ G (2⁻¹ * t)) q multHaar :=
        eLpNorm_const_mul_ennreal
          ((hF.comp (measurable_const_mul _)).add
            (hG.comp (measurable_const_mul _))).aestronglyMeasurable
      _ ≤ ENNReal.ofReal (2 ^ r) * (ENNReal.LpAddConst q *
          (eLpNorm (fun t ↦ F (2⁻¹ * t)) q multHaar +
            eLpNorm (fun t ↦ G (2⁻¹ * t)) q multHaar)) :=
        mul_le_mul_right (eLpNorm_add_le' q) _
      _ = _ := by
        rw [eLpNorm_comp_mul_left_multHaar F (by positivity),
          eLpNorm_comp_mul_left_multHaar G (by positivity),
          ← mul_assoc, mul_comm (ENNReal.ofReal (2 ^ r))]

/-- For `1 ≤ q ≤ ∞`, the Lorentz gauge satisfies the quasi-triangle inequality with constant
`2 ^ (1 / p)`: `‖f + g‖_{p, q} ≤ 2 ^ (1 / p) (‖f‖_{p, q} + ‖g‖_{p, q})`. -/
theorem eLorentzNorm_add_le (hq : 1 ≤ q) :
    eLorentzNorm (f + g) p q μ ≤
      ENNReal.ofReal (2 ^ (p⁻¹).toReal) * (eLorentzNorm f p q μ + eLorentzNorm g p q μ) := by
  simpa [ENNReal.LpAddConst_of_one_le hq] using eLorentzNorm_add_le' (f := f) (g := g) (μ := μ) p q

/-- The Lorentz class `L^{p, q}(μ)` is closed under addition for all `p, q ∈ [0, ∞]`. -/
theorem MemLorentz.add (hf : MemLorentz f p q μ) (hg : MemLorentz g p q μ) :
    MemLorentz (f + g) p q μ :=
  (eLorentzNorm_add_le' p q).trans_lt <| ENNReal.mul_lt_top
    (ENNReal.mul_lt_top (ENNReal.LpAddConst_lt_top q) ENNReal.ofReal_lt_top)
    (ENNReal.add_lt_top.2 ⟨hf, hg⟩)

end ContinuousAdd

end ESeminormedAddMonoid

section SeminormedAddCommGroup

variable {F : Type*} [SeminormedAddCommGroup F] {f g : α → F}

@[simp]
theorem eLorentzNorm_neg (f : α → F) (p q : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm (-f) p q μ = eLorentzNorm f p q μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · exact eLorentzNorm_congr_eNorm_ae hf.neg hf (Eventually.of_forall fun x ↦ eNorm_neg (f x))
  · rw [eLorentzNorm_of_not_aestronglyMeasurable fun h ↦ hf (neg_neg f ▸ h.neg),
      eLorentzNorm_of_not_aestronglyMeasurable hf]

theorem MemLorentz.neg (hf : MemLorentz f p q μ) : MemLorentz (-f) p q μ := by
  simpa [MemLorentz] using hf

@[simp]
theorem memLorentz_neg_iff : MemLorentz (-f) p q μ ↔ MemLorentz f p q μ :=
  ⟨fun h ↦ neg_neg f ▸ h.neg, MemLorentz.neg⟩

theorem eLorentzNorm_sub_le' (p q : ℝ≥0∞) :
    eLorentzNorm (f - g) p q μ ≤
      ENNReal.LpAddConst q * ENNReal.ofReal (2 ^ (p⁻¹).toReal) *
        (eLorentzNorm f p q μ + eLorentzNorm g p q μ) := by
  simpa only [sub_eq_add_neg, eLorentzNorm_neg] using
    eLorentzNorm_add_le' (f := f) (g := -g) (μ := μ) p q

theorem eLorentzNorm_sub_le (hq : 1 ≤ q) :
    eLorentzNorm (f - g) p q μ ≤
      ENNReal.ofReal (2 ^ (p⁻¹).toReal) * (eLorentzNorm f p q μ + eLorentzNorm g p q μ) := by
  simpa [ENNReal.LpAddConst_of_one_le hq] using eLorentzNorm_sub_le' (f := f) (g := g) (μ := μ) p q

theorem MemLorentz.sub (hf : MemLorentz f p q μ) (hg : MemLorentz g p q μ) :
    MemLorentz (f - g) p q μ :=
  sub_eq_add_neg f g ▸ hf.add hg.neg

@[simp]
theorem eLorentzNorm_norm (hf : AEStronglyMeasurable f μ) :
    eLorentzNorm (fun x ↦ ‖f x‖) p q μ = eLorentzNorm f p q μ :=
  eLorentzNorm_congr_eNorm_ae hf.norm hf (Eventually.of_forall fun x ↦ eNorm_norm (f x))

theorem MemLorentz.norm (hf : MemLorentz f p q μ) : MemLorentz (fun x ↦ ‖f x‖) p q μ := by
  simpa [MemLorentz, hf.aestronglyMeasurable] using hf

theorem memLorentz_norm_iff (hf : AEStronglyMeasurable f μ) :
    MemLorentz (fun x ↦ ‖f x‖) p q μ ↔ MemLorentz f p q μ := by simp [MemLorentz, hf]

section IsBoundedSMul

variable {𝕜 : Type*} [NormedRing 𝕜] [MulActionWithZero 𝕜 F] [IsBoundedSMul 𝕜 F]

theorem eLorentzNorm_const_smul_le (c : 𝕜) (f : α → F) (p q : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm (c • f) p q μ ≤ ‖c‖ₑ * eLorentzNorm f p q μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · refine (eLorentzNorm_mono_eNorm_ae (g := fun x ↦ ‖c‖ₑ * ‖f x‖ₑ) (hf.const_smul c)
      (Eventually.of_forall fun x ↦ by simpa using eNorm_smul_le)).trans_eq ?_
    rw [eLorentzNorm_const_mul_ennreal ‖c‖ₑ hf.eNorm.aestronglyMeasurable, eLorentzNorm_eNorm hf]
  · rw [eLorentzNorm_of_not_aestronglyMeasurable hf]
    rcases eq_or_ne c 0 with rfl | hc
    · simp
    · rw [ENNReal.mul_top (by simpa using hc)]; exact le_top

theorem MemLorentz.const_smul (hf : MemLorentz f p q μ) (c : 𝕜) : MemLorentz (c • f) p q μ :=
  (eLorentzNorm_const_smul_le c f p q μ).trans_lt (ENNReal.mul_lt_top eNorm_lt_top hf)

end IsBoundedSMul

section NormedSpace

variable {𝕜 : Type*} [NormedDivisionRing 𝕜] [Module 𝕜 F] [NormSMulClass 𝕜 F]

theorem eLorentzNorm_const_smul (c : 𝕜) (f : α → F) (p q : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm (c • f) p q μ = ‖c‖ₑ * eLorentzNorm f p q μ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp
  refine le_antisymm (eLorentzNorm_const_smul_le c f p q μ) <| ENNReal.mul_le_of_le_div' ?_
  simpa [eNorm_inv, hc, ENNReal.div_eq_inv_mul] using eLorentzNorm_const_smul_le c⁻¹ (c • f) p q μ

end NormedSpace

end SeminormedAddCommGroup

end Algebraic

/-! ### Concrete checks: `L^p` vs. `L^{p, ∞}` and non-subadditivity of `‖·‖_{2, ∞}` -/

section Checks

/-- On `(0, ∞)`, the power `t ↦ t ^ (-1 / p)` (`0 < p < ∞`) has weak-`L^p` gauge equal to `1`. -/
theorem eLorentzNorm_rpow_neg_inv_Ioi {p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    eLorentzNorm (fun t : ℝ ↦ t ^ (-(p⁻¹).toReal)) p ∞ (volume.restrict (Ioi 0)) = 1 := by
  set r := (p⁻¹).toReal
  have hr : 0 < r := ENNReal.toReal_pos (ENNReal.inv_ne_zero.2 hptop) (ENNReal.inv_ne_top.2 hp0)
  have hf : AEStronglyMeasurable (fun t : ℝ ↦ t ^ (-r)) (volume.restrict (Ioi 0)) :=
    (measurable_id.pow_const (-r)).aestronglyMeasurable
  have hae : (fun t : ℝ ↦ ‖t ^ (-r)‖ₑ) =ᵐ[volume.restrict (Ioi 0)]
      fun t : ℝ ↦ ENNReal.ofReal (t ^ (-r)) :=
    (ae_restrict_mem measurableSet_Ioi).mono fun t (ht : 0 < t) ↦
      Real.eNorm_of_nonneg (Real.rpow_nonneg ht.le _)
  have hanti : AntitoneOn (fun t : ℝ ↦ ENNReal.ofReal (t ^ (-r))) (Ioi 0) :=
    fun t₁ (ht₁ : 0 < t₁) _ _ hle ↦
      ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow_of_nonpos ht₁ hle (neg_nonpos.2 hr.le))
  have hcont : ∀ t > 0, ContinuousWithinAt (fun s : ℝ ↦ ENNReal.ofReal (s ^ (-r))) (Ici t) t :=
    fun t ht ↦ (ENNReal.continuous_ofReal.continuousAt.comp
      (Real.continuousAt_rpow_const t (-r) (Or.inl ht.ne'))).continuousWithinAt
  rw [eLorentzNorm_top_eq_iSup_Ioi hf hp0]
  have hterm (s : ℝ) (hs : 0 < s) :
      ENNReal.ofReal (s ^ r) *
        (volume.restrict (Ioi 0)).decreasingRearrangement (fun t : ℝ ↦ ‖t ^ (-r)‖ₑ) s = 1 := by
    rw [Measure.decreasingRearrangement_congr_ae _ hae,
      Measure.decreasingRearrangement_eq_of_antitoneOn hanti hcont hs,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.le r), ← Real.rpow_add hs, add_neg_cancel,
      Real.rpow_zero, ENNReal.ofReal_one]
  exact le_antisymm (iSup₂_le fun s hs ↦ (hterm s hs).le)
    ((hterm 1 one_pos).symm.le.trans (le_iSup₂_of_le 1 one_pos le_rfl))

/-- On `(0, ∞)`, the power `t ↦ t ^ (-1 / p)` (`0 < p < ∞`) has infinite `L^p` norm, separating
`L^p` from `L^{p, ∞}`. -/
theorem eLpNorm_rpow_neg_inv_Ioi {p : ℝ≥0∞} (hp0 : p ≠ 0) (hptop : p ≠ ∞) :
    eLpNorm (fun t : ℝ ↦ t ^ (-(p⁻¹).toReal)) p (volume.restrict (Ioi 0)) = ∞ := by
  have hp : 0 < p.toReal := ENNReal.toReal_pos hp0 hptop
  have hf : AEStronglyMeasurable (fun t : ℝ ↦ t ^ (-(p⁻¹).toReal)) (volume.restrict (Ioi 0)) :=
    (measurable_id.pow_const _).aestronglyMeasurable
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hptop hf]
  have hcongr : ∀ t ∈ Ioi (0 : ℝ),
      ‖t ^ (-(p⁻¹).toReal)‖ₑ ^ p.toReal = ENNReal.ofReal (t ^ (-1 : ℝ)) := fun t ht ↦ by
    rw [Real.eNorm_of_nonneg (Real.rpow_nonneg ht.le _),
      ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos ht _), ← Real.rpow_mul ht.le,
      ENNReal.toReal_inv, neg_mul, inv_mul_cancel₀ hp.ne']
  rw [setLIntegral_congr_fun measurableSet_Ioi hcongr, lintegral_ofReal_rpow_Ioi,
    ENNReal.top_rpow_of_pos (one_div_pos.2 hp)]

private theorem eLorentzNorm_fin_three_le (f : Fin 3 → ℝ) (σ : Equiv.Perm (Fin 3))
    (hσ₀ : |f (σ 0)| ≤ 4) (hσ₁ : |f (σ 1)| ≤ 3) (hσ₂ : |f (σ 2)| ≤ 2) :
    eLorentzNorm f 2 ∞ Measure.count ≤ ENNReal.ofReal (17 / 4) := by
  rw [eLorentzNorm_top_eq_iSup_mul_measure_rpow Measurable.of_discrete.aestronglyMeasurable
    two_ne_zero ENNReal.ofNat_ne_top]
  refine iSup_le fun c ↦ ?_
  have hbd (k : Fin 3) {b : ℝ} (hk : |f (σ k)| ≤ b) : ‖f (σ k)‖ₑ ≤ ENNReal.ofReal b :=
    (Real.eNorm_eq_ofReal_abs _).le.trans (ENNReal.ofReal_le_ofReal hk)
  have hstep (a m : ℝ) (ha : 0 < a) (hc : c ≤ ENNReal.ofReal a)
      (hμ : Measure.count {y : Fin 3 | c < ‖f y‖ₑ} ≤ ENNReal.ofReal m)
      (hnum : a ^ (2 : ℝ) * m ≤ (17 / 4 : ℝ) ^ (2 : ℝ)) :
      c ^ (2 : ℝ) * Measure.count {y : Fin 3 | c < ‖f y‖ₑ} ≤
        ENNReal.ofReal ((17 / 4 : ℝ) ^ (2 : ℝ)) :=
    (mul_le_mul' (ENNReal.rpow_le_rpow hc zero_le_two) hμ).trans <| by
      rw [ENNReal.ofReal_rpow_of_pos ha, ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal hnum
  rw [ENNReal.toReal_inv, ENNReal.toReal_ofNat,
    ← ENNReal.rpow_le_rpow_iff (z := 2) zero_lt_two,
    ENNReal.mul_rpow_of_nonneg _ _ zero_le_two, ← ENNReal.rpow_mul,
    inv_mul_cancel₀ two_ne_zero, ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_pos (by positivity)]
  rcases le_or_gt (ENNReal.ofReal 4) c with hc4 | hc4
  · have hempty : {y : Fin 3 | c < ‖f y‖ₑ} = ∅ := eq_empty_of_forall_notMem fun y hy ↦ by
      obtain ⟨k, rfl⟩ := σ.surjective y; fin_cases k
      · exact hy.not_ge ((hbd 0 hσ₀).trans hc4)
      · exact hy.not_ge ((hbd 1 (hσ₁.trans (by norm_num))).trans hc4)
      · exact hy.not_ge ((hbd 2 (hσ₂.trans (by norm_num))).trans hc4)
    simp [hempty]
  rcases le_or_gt (ENNReal.ofReal 3) c with hc3 | hc3
  · have hsub : {y : Fin 3 | c < ‖f y‖ₑ} ⊆ {σ 0} := fun y hy ↦ by
      obtain ⟨k, rfl⟩ := σ.surjective y; fin_cases k
      · simp
      · exact absurd hy (not_lt.2 ((hbd 1 hσ₁).trans hc3))
      · exact absurd hy (not_lt.2 ((hbd 2 (hσ₂.trans (by norm_num))).trans hc3))
    exact hstep 4 1 (by norm_num) hc4.le ((measure_mono hsub).trans_eq (by simp)) (by norm_num)
  rcases le_or_gt (ENNReal.ofReal 2) c with hc2 | hc2
  · have hsub : {y : Fin 3 | c < ‖f y‖ₑ} ⊆ {σ 0, σ 1} := fun y hy ↦ by
      obtain ⟨k, rfl⟩ := σ.surjective y; fin_cases k
      · simp
      · simp
      · exact absurd hy (not_lt.2 ((hbd 2 hσ₂).trans hc2))
    exact hstep 3 2 (by norm_num) hc3.le
      ((measure_mono hsub).trans ((measure_union_le {σ 0} {σ 1}).trans_eq (by simp; norm_num)))
      (by norm_num)
  · exact hstep 2 3 (by norm_num) hc2.le ((measure_mono (subset_univ _)).trans_eq (by simp))
      (by norm_num)

/-- The rearrangement gauge `eLorentzNorm · 2 ∞` fails the constant-`1` triangle inequality:
cyclic shifts of `![4, 3, 2]` on `Fin 3` satisfy
`‖f‖_{2, ∞} + ‖g‖_{2, ∞} < ‖f + g‖_{2, ∞}` (`2 √18 < 5 √3`). -/
theorem exists_lt_eLorentzNorm_add_top :
    ∃ f g : Fin 3 → ℝ,
      eLorentzNorm f 2 ∞ Measure.count + eLorentzNorm g 2 ∞ Measure.count <
        eLorentzNorm (f + g) 2 ∞ Measure.count := by
  set f₀ : Fin 3 → ℝ := ![4, 3, 2]
  set g₀ : Fin 3 → ℝ := ![2, 4, 3]
  refine ⟨f₀, g₀, ?_⟩
  have hf : eLorentzNorm f₀ 2 ∞ Measure.count ≤ ENNReal.ofReal (17 / 4) :=
    eLorentzNorm_fin_three_le f₀ (Equiv.refl _) (by norm_num [f₀]) (by norm_num [f₀])
      (by norm_num [f₀])
  have hg : eLorentzNorm g₀ 2 ∞ Measure.count ≤ ENNReal.ofReal (17 / 4) :=
    eLorentzNorm_fin_three_le g₀ (Equiv.addRight 1) (by simp [g₀]) (by simp [g₀]) (by simp [g₀])
  have hsum : eLorentzNorm f₀ 2 ∞ Measure.count +
      eLorentzNorm g₀ 2 ∞ Measure.count ≤ ENNReal.ofReal (17 / 2) :=
    (add_le_add hf hg).trans_eq (by
      rw [← ENNReal.ofReal_add (by positivity) (by positivity)]; norm_num)
  refine hsum.trans_lt ?_
  rw [eLorentzNorm_top_eq_iSup_mul_measure_rpow Measurable.of_discrete.aestronglyMeasurable
    two_ne_zero ENNReal.ofNat_ne_top]
  have huniv : {y : Fin 3 | ENNReal.ofReal (99 / 20) < ‖(f₀ + g₀) y‖ₑ} = univ := by
    ext y; simp only [mem_ofPred_eq, mem_univ, iff_true, Pi.add_apply]
    fin_cases y
    all_goals rw [Real.eNorm_of_nonneg (by norm_num [f₀, g₀])]
    all_goals exact (ENNReal.ofReal_lt_ofReal_iff (by norm_num [f₀, g₀])).2 (by norm_num [f₀, g₀])
  have hcount : Measure.count (univ : Set (Fin 3)) = ENNReal.ofReal 3 := by simp
  have hlt : ENNReal.ofReal (17 / 2) <
      ENNReal.ofReal (99 / 20) * (Measure.count (univ : Set (Fin 3))) ^ ((2 : ℝ≥0∞)⁻¹).toReal := by
    rw [hcount, ENNReal.toReal_inv, ENNReal.toReal_ofNat,
      ← ENNReal.rpow_lt_rpow_iff (z := 2) zero_lt_two,
      ENNReal.mul_rpow_of_nonneg _ _ zero_le_two, ← ENNReal.rpow_mul,
      inv_mul_cancel₀ two_ne_zero, ENNReal.rpow_one,
      ENNReal.ofReal_rpow_of_pos (by positivity), ENNReal.ofReal_rpow_of_pos (by positivity),
      ← ENNReal.ofReal_mul (by positivity)]
    exact ENNReal.ofReal_lt_ofReal_iff (by positivity) |>.2 (by norm_num)
  exact hlt.trans_le (le_iSup_of_le (ENNReal.ofReal (99 / 20)) (by rw [huniv]))

end Checks

end TauCeti
