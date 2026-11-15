/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import TauCeti.MeasureTheory.Function.DecreasingRearrangement
public import TauCeti.MeasureTheory.Measure.Haar.MultHaar
-- `Mathlib.MeasureTheory.Function.SpecialFunctions.Basic` is imported privately: it supplies Borel
-- measurability of real powers and products in `ℝ≥0∞`.
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic
-- `TauCeti.Analysis.SpecialFunctions.Pow.Integral` is imported privately: it supplies the half-line
-- power integrals used for indicator functions, power laws, and the pointwise rearrangement bound.
import TauCeti.Analysis.SpecialFunctions.Pow.Integral
-- `TauCeti.MeasureTheory.Function.Lp.IntermediateExponent` is imported privately: logarithmic
-- convexity of `L^q(dt / t)` gives the sharp secondary-exponent embedding.
import TauCeti.MeasureTheory.Function.Lp.IntermediateExponent

/-!
# The Lorentz rearrangement seminorm and weak-`L^p` gauges

For a function `f : α → ε` on a measure space `(α, μ)` and exponents `p, q ∈ [0, ∞]`, the Lorentz
rearrangement seminorm `TauCeti.eLorentzNorm f p q μ` is the `L^q(dt / t)` seminorm of
`t ↦ t ^ (1 / p) f* t` against the multiplicative Haar measure `dt / t` (`TauCeti.multHaar`), where
`f*` is the decreasing rearrangement `μ.decreasingRearrangement (‖f ·‖ₑ)`:

`‖f‖_{p,q} = (∫₀^∞ (t ^ (1 / p) f* t) ^ q dt / t) ^ (1 / q)`.

Following `MeasureTheory.eLpNorm`, it is set to `0` when `p = 0` and `f` is almost everywhere
strongly measurable, and to `∞` when `f` is not almost everywhere strongly measurable. Because
`∞.toReal = 0`, the single formula covers both `p = ∞` (where `t ^ (1 / p) = 1`) and `q = ∞` (where
the `L^∞(dt / t)` seminorm is the weak-`L^p` supremum gauge `sup_{t > 0} t ^ (1 / p) f* t`); the
predicate `TauCeti.MemLorentz f p q μ` is `eLorentzNorm f p q μ < ∞`.

Key properties proved in this file:

* **Diagonal `q = p` (`eLorentzNorm_self`, `memLorentz_self_iff`)**: equimeasurability of `f*` with
  `‖f ·‖ₑ` identifies `‖f‖_{p,p}` with `eLpNorm f p μ` for every `p ∈ [0, ∞]`.
* **Weak-`L^p` (`eLorentzNorm_top_right`, `eLorentzNorm_top_right_eq_iSup_measure`)**: at `q = ∞`
  the essential supremum against `dt / t` coincides with the pointwise supremum
  `⨆ t > 0, t ^ (1 / p) f* t` and, for `0 < p < ∞`, with the superlevel supremum
  `⨆ c, c * μ {‖f‖ > c} ^ (1 / p)`.
* **Secondary-exponent embeddings (`eLorentzNorm_le_of_second_exponent_le`,
  `MemLorentz.mono_exponent`)**: for `0 < p < ∞` and `0 < q₀ ≤ q₁ ≤ ∞`, monotonicity of `f*` bounds
  `t ^ (1 / p) f* t` by `(q₀ / p) ^ (1 / q₀) ‖f‖_{p,q₀}`, and logarithmic convexity of `L^q(dt / t)`
  gives the sharp Holmstedt–Calderón bound
  `‖f‖_{p,q₁} ≤ (q₀ / p) ^ (1 / q₀ - 1 / q₁) ‖f‖_{p,q₀}` (hence `L^{p,q₀} ⊆ L^{p,q₁}`, and in
  particular `‖f‖_{p,∞} ≤ ‖f‖_p` at `q₀ = p, q₁ = ∞`).
* **Indicators and power laws (`eLorentzNorm_indicator_const₀`, `eLorentzNorm_rpow_neg_inv`)**:
  `‖c 1_A‖_{p,q} = (p / q) ^ (1 / q) ‖c‖ₑ (μ A) ^ (1 / p)` for `0 < p < ∞` and `q ≠ 0`, while
  `t ↦ t ^ (-1 / p)` on `(0, ∞)` has weak-`L^p` gauge `1` and infinite `L^{p,q}` gauge for every
  finite `q ≠ 0`.
* **Quasi-triangle inequality and failure of subadditivity (`eLorentzNorm_add_le`,
  `exists_lt_eLorentzNorm_add`)**: shifted subadditivity `(f + g)* t ≤ f* (t / 2) + g* (t / 2)`
  gives `‖f + g‖_{p,q} ≤ 2 ^ (1 / p) LpAddConst q (‖f‖_{p,q} + ‖g‖_{p,q})`, whereas two-valued
  functions on `Bool` witness `‖f‖_{2,∞} + ‖g‖_{2,∞} < ‖f + g‖_{2,∞}`.

## References

* R. A. Hunt, *On `L(p, q)` spaces*, L'Enseignement Math. (2) **12** (1966), 249–276.
* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §1.3 and §5.2.
* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., GTM 249, Springer, 2014, §1.4.
-/

public noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace TauCeti

section Defs

variable {α ε : Type*} {mα : MeasurableSpace α} [TopologicalSpace ε] [ENorm ε]

/-- The Lorentz rearrangement seminorm `‖f‖_{p,q}` in `[0, ∞]`, equal for an almost everywhere
strongly measurable `f` with `p ≠ 0` to the `L^q(dt / t)` seminorm of
`t ↦ t ^ (1 / p) * μ.decreasingRearrangement (‖f ·‖ₑ) t`, to `0` when `p = 0`, and to `∞` when `f`
is not almost everywhere strongly measurable. -/
def eLorentzNorm (f : α → ε) (p q : ℝ≥0∞) (μ : Measure α := by volume_tac) : ℝ≥0∞ :=
  open scoped Classical in
  if AEStronglyMeasurable f μ then
    if p = 0 then 0
    else eLpNorm
      (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t)
      q TauCeti.multHaar
  else ∞

/-- `MemLorentz f p q μ` means that `f` is almost everywhere strongly measurable and has finite
Lorentz seminorm `eLorentzNorm f p q μ < ∞`. -/
def MemLorentz (f : α → ε) (p q : ℝ≥0∞) (μ : Measure α := by volume_tac) : Prop :=
  eLorentzNorm f p q μ < ∞

variable {μ : Measure α} {f g : α → ε} {p q : ℝ≥0∞}

theorem eLorentzNorm_def (f : α → ε) (p q : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm f p q μ =
      open scoped Classical in
      if AEStronglyMeasurable f μ then
        if p = 0 then 0
        else eLpNorm
          (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t)
          q TauCeti.multHaar
      else ∞ :=
  (rfl)

theorem memLorentz_iff : MemLorentz f p q μ ↔ eLorentzNorm f p q μ < ∞ :=
  Iff.rfl

private theorem measurable_rpow_mul_decreasingRearrangement (μ : Measure α) (h : α → ℝ≥0∞)
    (p : ℝ≥0∞) :
    Measurable fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement h t :=
  (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).mul
    (μ.measurable_decreasingRearrangement h)

theorem eLorentzNorm_of_not_aestronglyMeasurable (hf : ¬ AEStronglyMeasurable f μ) :
    eLorentzNorm f p q μ = ∞ := by
  simp [eLorentzNorm, hf]

theorem aestronglyMeasurable_of_eLorentzNorm_ne_top (h : eLorentzNorm f p q μ ≠ ∞) :
    AEStronglyMeasurable f μ := by
  contrapose h
  exact eLorentzNorm_of_not_aestronglyMeasurable h

theorem MemLorentz.aestronglyMeasurable (hf : MemLorentz f p q μ) : AEStronglyMeasurable f μ :=
  aestronglyMeasurable_of_eLorentzNorm_ne_top hf.ne

theorem MemLorentz.eLorentzNorm_lt_top (hf : MemLorentz f p q μ) : eLorentzNorm f p q μ < ∞ :=
  hf

theorem MemLorentz.eLorentzNorm_ne_top (hf : MemLorentz f p q μ) : eLorentzNorm f p q μ ≠ ∞ :=
  hf.ne

theorem eLorentzNorm_eq_eLpNorm (hp : p ≠ 0) (hf : AEStronglyMeasurable f μ) :
    eLorentzNorm f p q μ =
      eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t)
        q TauCeti.multHaar := by
  simp [eLorentzNorm, hf, hp]

@[simp]
theorem eLorentzNorm_exponent_zero_left (hf : AEStronglyMeasurable f μ) :
    eLorentzNorm f 0 q μ = 0 := by
  simp [eLorentzNorm, hf]

@[simp]
theorem eLorentzNorm_exponent_zero_right (hf : AEStronglyMeasurable f μ) :
    eLorentzNorm f p 0 μ = 0 := by
  rcases eq_or_ne p 0 with rfl | hp
  · exact eLorentzNorm_exponent_zero_left hf
  · rw [eLorentzNorm_eq_eLpNorm hp hf, eLpNorm_exponent_zero
      (measurable_rpow_mul_decreasingRearrangement μ _ p).aestronglyMeasurable]

theorem eLorentzNorm_eq_lintegral_rpow (hp : p ≠ 0) (hq0 : q ≠ 0) (hq : q ≠ ∞)
    (hf : AEStronglyMeasurable f μ) :
    eLorentzNorm f p q μ =
      (∫⁻ t, (ENNReal.ofReal (t ^ p.toReal⁻¹) *
        μ.decreasingRearrangement (‖f ·‖ₑ) t) ^ q.toReal ∂TauCeti.multHaar) ^ (1 / q.toReal) := by
  rw [eLorentzNorm_eq_eLpNorm hp hf, eLpNorm_eq_lintegral_rpow_eNorm_toReal hq0 hq
    (measurable_rpow_mul_decreasingRearrangement μ _ p).aestronglyMeasurable]
  simp only [eNorm_eq_self]

theorem eLorentzNorm_congr_eNorm_ae {ε' : Type*} [TopologicalSpace ε'] [ENorm ε'] {g : α → ε'}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hfg : (‖f ·‖ₑ) =ᵐ[μ] (‖g ·‖ₑ)) :
    eLorentzNorm f p q μ = eLorentzNorm g p q μ := by
  rcases eq_or_ne p 0 with rfl | hp
  · simp [hf, hg]
  · rw [eLorentzNorm_eq_eLpNorm hp hf, eLorentzNorm_eq_eLpNorm hp hg,
      μ.decreasingRearrangement_congr_ae hfg]

theorem eLorentzNorm_congr_ae (hfg : f =ᵐ[μ] g) :
    eLorentzNorm f p q μ = eLorentzNorm g p q μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · exact eLorentzNorm_congr_eNorm_ae hf (hf.congr hfg) (hfg.mono fun _ hx ↦ congrArg (‖·‖ₑ) hx)
  · rw [eLorentzNorm_of_not_aestronglyMeasurable hf,
      eLorentzNorm_of_not_aestronglyMeasurable fun hg ↦ hf (hg.congr hfg.symm)]

theorem MemLorentz.congr_ae (hf : MemLorentz f p q μ) (hfg : f =ᵐ[μ] g) :
    MemLorentz g p q μ := by
  rwa [MemLorentz, ← eLorentzNorm_congr_ae hfg]

theorem eLorentzNorm_mono_eNorm_ae {ε' : Type*} [TopologicalSpace ε'] [ENorm ε'] {g : α → ε'}
    (hf : AEStronglyMeasurable f μ) (hfg : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    eLorentzNorm f p q μ ≤ eLorentzNorm g p q μ := by
  by_cases hg : AEStronglyMeasurable g μ
  swap
  · rw [eLorentzNorm_of_not_aestronglyMeasurable hg]
    exact le_top
  rcases eq_or_ne p 0 with rfl | hp
  · simp [hf]
  rw [eLorentzNorm_eq_eLpNorm hp hf, eLorentzNorm_eq_eLpNorm hp hg]
  refine eLpNorm_mono_eNorm
    (measurable_rpow_mul_decreasingRearrangement μ _ p).aestronglyMeasurable fun t ↦ ?_
  simp only [eNorm_eq_self]
  gcongr
  exact μ.decreasingRearrangement_mono_ae hfg t

theorem MemLorentz.mono_eNorm_ae {ε' : Type*} [TopologicalSpace ε'] [ENorm ε'] {g : α → ε'}
    (hg : MemLorentz g p q μ) (hf : AEStronglyMeasurable f μ)
    (hfg : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) : MemLorentz f p q μ :=
  (eLorentzNorm_mono_eNorm_ae hf hfg).trans_lt hg

@[simp]
theorem eLorentzNorm_measure_zero : eLorentzNorm f p q (0 : Measure α) = 0 := by
  have h0 : ∀ t, (0 : Measure α).decreasingRearrangement (‖f ·‖ₑ) t = 0 := fun t ↦
    le_antisymm ((Measure.decreasingRearrangement_le_iff 0).2 (by simp)) bot_le
  rcases eq_or_ne p 0 with rfl | hp
  · simp [eLorentzNorm, aestronglyMeasurable_zero_measure]
  · simp [eLorentzNorm_eq_eLpNorm hp (aestronglyMeasurable_zero_measure f), h0]

@[simp]
theorem memLorentz_measure_zero : MemLorentz f p q (0 : Measure α) := by
  simp [MemLorentz]

end Defs

theorem eLorentzNorm_eNorm {α ε : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε} {p q : ℝ≥0∞}
    (hf : AEStronglyMeasurable f μ) :
    eLorentzNorm (fun x ↦ ‖f x‖ₑ) p q μ = eLorentzNorm f p q μ :=
  eLorentzNorm_congr_eNorm_ae hf.eNorm.aestronglyMeasurable hf (ae_of_all _ fun _ ↦ eNorm_eNorm _)

section Algebraic

variable {α ε F 𝕜 : Type*} {mα : MeasurableSpace α} {μ : Measure α} {p q : ℝ≥0∞}

section Zero

variable [TopologicalSpace ε] [ESeminormedAddMonoid ε]

@[simp]
theorem eLorentzNorm_zero : eLorentzNorm (0 : α → ε) p q μ = 0 := by
  have h0 : ∀ t, μ.decreasingRearrangement (fun _ : α ↦ (0 : ℝ≥0∞)) t = 0 := fun t ↦
    le_antisymm (μ.decreasingRearrangement_le_iff.2 (by simp)) bot_le
  rcases eq_or_ne p 0 with rfl | hp
  · simp [eLorentzNorm, aestronglyMeasurable_zero]
  · simp [eLorentzNorm_eq_eLpNorm hp aestronglyMeasurable_zero, h0]

@[simp]
theorem eLorentzNorm_fun_zero : eLorentzNorm (fun _ : α ↦ (0 : ε)) p q μ = 0 :=
  eLorentzNorm_zero

@[simp]
theorem MemLorentz.zero : MemLorentz (0 : α → ε) p q μ := by
  simp [MemLorentz]

@[simp]
theorem MemLorentz.fun_zero : MemLorentz (fun _ : α ↦ (0 : ε)) p q μ :=
  MemLorentz.zero

end Zero

theorem eLorentzNorm_const_mul_ennreal {f : α → ℝ≥0∞} (hf : AEStronglyMeasurable f μ) (c : ℝ≥0∞) :
    eLorentzNorm (fun x ↦ c * f x) p q μ = c * eLorentzNorm f p q μ := by
  have hcf : AEStronglyMeasurable (fun x ↦ c * f x) μ :=
    (hf.aemeasurable.const_mul c).aestronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp
  · simp [hf, hcf]
  rw [eLorentzNorm_eq_eLpNorm hp hcf, eLorentzNorm_eq_eLpNorm hp hf]
  have hpt : (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) *
        μ.decreasingRearrangement (fun x ↦ ‖c * f x‖ₑ) t) =
      fun t : ℝ ↦ c * (ENNReal.ofReal (t ^ p.toReal⁻¹) *
        μ.decreasingRearrangement (‖f ·‖ₑ) t) := by
    ext t
    simp only [eNorm_eq_self, μ.decreasingRearrangement_const_mul]
    ring
  rw [hpt, eLpNorm_const_mul_ennreal
    (measurable_rpow_mul_decreasingRearrangement μ _ p).aestronglyMeasurable]

section SMul

variable [NormedDivisionRing 𝕜] [NormedAddCommGroup F] [Module 𝕜 F] [NormSMulClass 𝕜 F]

theorem eLorentzNorm_const_smul (c : 𝕜) (f : α → F) (p q : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm (c • f) p q μ = ‖c‖ₑ * eLorentzNorm f p q μ := by
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  by_cases hf : AEStronglyMeasurable f μ
  · rw [← eLorentzNorm_eNorm (hf.const_smul c), ← eLorentzNorm_eNorm hf]
    simpa only [Pi.smul_apply, eNorm_smul] using
      eLorentzNorm_const_mul_ennreal (p := p) (q := q) hf.eNorm.aestronglyMeasurable ‖c‖ₑ
  · have hcf : ¬ AEStronglyMeasurable (c • f) μ :=
      fun h ↦ hf (by simpa [inv_smul_smul₀ hc] using h.const_smul c⁻¹)
    rw [eLorentzNorm_of_not_aestronglyMeasurable hcf, eLorentzNorm_of_not_aestronglyMeasurable hf,
      ENNReal.mul_top (by simpa using hc)]

theorem MemLorentz.const_smul {f : α → F} (hf : MemLorentz f p q μ) (c : 𝕜) :
    MemLorentz (c • f) p q μ := by
  rw [MemLorentz, eLorentzNorm_const_smul]
  exact ENNReal.mul_lt_top eNorm_lt_top hf

@[simp]
theorem eLorentzNorm_neg [NormedAddCommGroup ε] (f : α → ε) (p q : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm (-f) p q μ = eLorentzNorm f p q μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · exact eLorentzNorm_congr_eNorm_ae hf.neg hf (ae_of_all _ fun x ↦ eNorm_neg (f x))
  · have hnf : ¬ AEStronglyMeasurable (-f) μ := fun h ↦ hf (by simpa using h.neg)
    rw [eLorentzNorm_of_not_aestronglyMeasurable hnf, eLorentzNorm_of_not_aestronglyMeasurable hf]

@[simp]
theorem MemLorentz.neg_iff [NormedAddCommGroup ε] {f : α → ε} :
    MemLorentz (-f) p q μ ↔ MemLorentz f p q μ := by
  rw [MemLorentz, MemLorentz, eLorentzNorm_neg]

theorem MemLorentz.neg [NormedAddCommGroup ε] {f : α → ε} (hf : MemLorentz f p q μ) :
    MemLorentz (-f) p q μ :=
  MemLorentz.neg_iff.2 hf

end SMul

end Algebraic

/-! ### Diagonal `q = p` and weak-`L^p` (`q = ∞`) -/

section DiagonalAndWeakLp

variable {α ε : Type*} {mα : MeasurableSpace α} {μ : Measure α} [TopologicalSpace ε]

/-- **Diagonal Lorentz seminorm.** For every `p ∈ [0, ∞]` and every `f`, the Lorentz seminorm
`eLorentzNorm f p p μ` coincides with `eLpNorm f p μ`. -/
@[simp]
theorem eLorentzNorm_self [ContinuousENorm ε] (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm f p p μ = eLpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  swap
  · rw [eLorentzNorm_of_not_aestronglyMeasurable hf, eLpNorm_of_not_aestronglyMeasurable hf]
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [eLorentzNorm_exponent_zero_left hf, eLpNorm_exponent_zero hf]
  rcases eq_or_ne p ∞ with rfl | hp
  · rw [eLorentzNorm_eq_eLpNorm hp0 hf]
    simp only [ENNReal.toReal_top, inv_zero, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
    rw [eLpNorm_exponent_top
        (μ.measurable_decreasingRearrangement _).aestronglyMeasurable,
      eLpNorm_exponent_top hf, eLpNormEssSup_eq_essSup_eNorm, eLpNormEssSup_eq_essSup_eNorm]
    simp only [eNorm_eq_self, TauCeti.essSup_multHaar, μ.essSup_decreasingRearrangement]
  have hr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  rw [eLorentzNorm_eq_lintegral_rpow hp0 hp0 hp hf,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hp0 hp hf,
    ← μ.lintegral_rpow_decreasingRearrangement hf.eNorm hr,
    TauCeti.setLIntegral_Ioi_eq_lintegral_multHaar]
  refine congrArg (· ^ (1 / p.toReal)) (lintegral_congr_ae ?_)
  filter_upwards [TauCeti.ae_pos_multHaar] with t ht
  rw [ENNReal.mul_rpow_of_nonneg _ _ hr.le,
    ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos ht _),
    ← Real.rpow_mul ht.le, inv_mul_cancel₀ hr.ne', Real.rpow_one]

@[simp]
theorem memLorentz_self_iff [ContinuousENorm ε] {f : α → ε} {p : ℝ≥0∞} :
    MemLorentz f p p μ ↔ MemLp f p μ := by
  rw [MemLorentz, MemLp, eLorentzNorm_self]

/-- Because `t ^ (1 / p)` is nondecreasing and `g*` is antitone, the essential supremum of
`t ↦ t ^ (1 / p) * g* t` against `dt / t` equals its pointwise supremum on `(0, ∞)`. -/
private theorem essSup_rpow_mul_decreasingRearrangement (μ : Measure α) (g : α → ℝ≥0∞)
    (p : ℝ≥0∞) :
    essSup (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement g t)
        TauCeti.multHaar =
      ⨆ (t : ℝ) (_ : 0 < t), ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement g t := by
  set E := essSup (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement g t)
    TauCeti.multHaar
  refine le_antisymm (essSup_le_of_ae_le _ (TauCeti.ae_pos_multHaar.mono fun t ht ↦
    le_iSup₂ (f := fun (t : ℝ) (_ : 0 < t) ↦
      ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement g t) t ht))
    (iSup₂_le fun t₀ ht₀ ↦ ?_)
  have hstep : ∀ r ∈ Ioo 0 t₀,
      ENNReal.ofReal (r ^ p.toReal⁻¹) * μ.decreasingRearrangement g t₀ ≤ E := by
    rintro r ⟨hr, hrt₀⟩
    by_contra! hlt
    have hnull := ae_iff.1 (ae_lt_of_essSup_lt hlt)
    have hpos : TauCeti.multHaar (Ico r t₀) ≠ 0 := by
      rw [TauCeti.multHaar_Ico hr hrt₀.le]
      exact (ENNReal.ofReal_pos.2 (sub_pos.2 (Real.log_lt_log hr hrt₀))).ne'
    refine hpos (measure_mono_null (fun s hs ↦ ?_) hnull)
    simp only [mem_ofPred_eq, not_lt]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal
      (Real.rpow_le_rpow hr.le hs.1 (inv_nonneg.2 ENNReal.toReal_nonneg)))
      (μ.antitone_decreasingRearrangement g hs.2.le)
  rcases eq_or_ne (μ.decreasingRearrangement g t₀) ∞ with htop | hfin
  · have hhalf := hstep (t₀ / 2) ⟨half_pos ht₀, half_lt_self ht₀⟩
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne'] at hhalf
    rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 (by positivity)).ne']
    exact hhalf
  · have htend : Tendsto (fun r : ℝ ↦
        ENNReal.ofReal (r ^ p.toReal⁻¹) * μ.decreasingRearrangement g t₀) (𝓝[<] t₀)
        (𝓝 (ENNReal.ofReal (t₀ ^ p.toReal⁻¹) * μ.decreasingRearrangement g t₀)) := by
      have hc : ContinuousAt (fun r : ℝ ↦ ENNReal.ofReal (r ^ p.toReal⁻¹)) t₀ :=
        ENNReal.continuous_ofReal.continuousAt.comp
          (continuousAt_id.rpow_const (Or.inl ht₀.ne'))
      exact ENNReal.Tendsto.mul_const (hc.mono_left nhdsWithin_le_nhds) (Or.inr hfin)
    exact le_of_tendsto htend
      (by filter_upwards [Ioo_mem_nhdsLT ht₀] with r hr using hstep r hr)

/-- **Weak-`L^p` rearrangement formula.** For `p ≠ 0` and an almost everywhere strongly measurable
`f`, `eLorentzNorm f p ∞ μ` is the pointwise supremum `⨆ t > 0, t ^ (1 / p) f* t`. -/
theorem eLorentzNorm_top_right [ENorm ε] {f : α → ε} {p : ℝ≥0∞} (hp : p ≠ 0)
    (hf : AEStronglyMeasurable f μ) :
    eLorentzNorm f p ∞ μ =
      ⨆ (t : ℝ) (_ : 0 < t),
        ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t := by
  rw [eLorentzNorm_eq_eLpNorm hp hf, eLpNorm_exponent_top
    (measurable_rpow_mul_decreasingRearrangement μ _ p).aestronglyMeasurable,
    eLpNormEssSup_eq_essSup_eNorm]
  simp only [eNorm_eq_self]
  exact essSup_rpow_mul_decreasingRearrangement μ _ p

/-- Any `M : ℝ≥0∞` is the supremum of `ENNReal.ofReal t` over `0 < t` with `ofReal t < M`. -/
private theorem eq_iSup_ofReal_of_lt (M : ℝ≥0∞) :
    M = ⨆ (t : ℝ) (_ : 0 < t ∧ ENNReal.ofReal t < M), ENNReal.ofReal t := by
  refine le_antisymm (le_of_forall_lt_imp_le_of_dense fun b hb ↦ ?_) (iSup₂_le fun _ h ↦ h.2.le)
  rcases eq_or_ne b 0 with rfl | hb0
  · exact bot_le
  have hbt : b ≠ ∞ := hb.ne_top
  have hpos : 0 < b.toReal := ENNReal.toReal_pos hb0 hbt
  exact (ENNReal.ofReal_toReal hbt).symm.trans_le
    (le_iSup₂_of_le (f := fun (t : ℝ) (_ : 0 < t ∧ ENNReal.ofReal t < M) ↦ ENNReal.ofReal t)
      b.toReal ⟨hpos, (ENNReal.ofReal_toReal hbt).trans_lt hb⟩ le_rfl)

/-- **Weak-`L^p` superlevel formula.** For `0 < p < ∞` and an almost everywhere strongly measurable
`f`, `eLorentzNorm f p ∞ μ = ⨆ c, c * μ {‖f‖ > c} ^ (1 / p)`. -/
theorem eLorentzNorm_top_right_eq_iSup_measure [ENorm ε] {f : α → ε} {p : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ∞) (hf : AEStronglyMeasurable f μ) :
    eLorentzNorm f p ∞ μ = ⨆ c : ℝ≥0∞, c * μ {x | c < ‖f x‖ₑ} ^ p.toReal⁻¹ := by
  have hr : 0 < p.toReal⁻¹ := inv_pos.2 (ENNReal.toReal_pos hp0 hp)
  rw [eLorentzNorm_top_right hp0 hf]
  refine le_antisymm (iSup₂_le fun t ht ↦ ?_) (iSup_le fun c ↦ ?_)
  · rw [μ.decreasingRearrangement_def, ENNReal.mul_iSup]
    refine iSup_le fun c ↦ ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun htc ↦ le_iSup_of_le c ?_
    rw [mul_comm, ← ENNReal.ofReal_rpow_of_pos ht]
    gcongr
  · conv_lhs => rw [eq_iSup_ofReal_of_lt (μ {x | c < ‖f x‖ₑ})]
    have hiso := (ENNReal.orderIsoRpow p.toReal⁻¹ hr).map_iSup
      (fun t : ℝ ↦ ⨆ (_ : 0 < t ∧ ENNReal.ofReal t < μ {x | c < ‖f x‖ₑ}), ENNReal.ofReal t)
    simp only [ENNReal.orderIsoRpow_apply] at hiso
    rw [hiso, ENNReal.mul_iSup]
    refine iSup_le fun t ↦ ?_
    by_cases h : 0 < t ∧ ENNReal.ofReal t < μ {x | c < ‖f x‖ₑ}
    · rw [ciSup_pos h, ENNReal.ofReal_rpow_of_pos h.1, mul_comm]
      refine le_iSup₂_of_le t h.1 ?_
      have hle := (μ.lt_decreasingRearrangement_iff.2 h.2).le
      gcongr
    · simp [h, ENNReal.zero_rpow_of_pos hr]

end DiagonalAndWeakLp

/-! ### Secondary-exponent embeddings -/

section CompareExp

variable {α ε : Type*} {mα : MeasurableSpace α} {μ : Measure α} [TopologicalSpace ε] [ENorm ε]

/-- Monotonicity of `f*` bounds every value of `t ^ (1 / p) f* t` by the Lorentz `(p, q)` seminorm:
`(p / q) ^ (1 / q) t ^ (1 / p) f* t ≤ ‖f‖_{p,q}` for `0 < p < ∞`, `q ≠ 0`, and `t > 0`. At
`q = ∞`, `(p / ∞.toReal) ^ 0 = 1`. -/
theorem ofReal_mul_decreasingRearrangement_le_eLorentzNorm {p q : ℝ≥0∞} (hp0 : p ≠ 0)
    (hp : p ≠ ∞) (hq0 : q ≠ 0) {t : ℝ} (ht : 0 < t) (f : α → ε) :
    ENNReal.ofReal ((p.toReal / q.toReal) ^ q.toReal⁻¹ * t ^ p.toReal⁻¹) *
        μ.decreasingRearrangement (‖f ·‖ₑ) t ≤
      eLorentzNorm f p q μ := by
  by_cases hf : AEStronglyMeasurable f μ
  swap
  · rw [eLorentzNorm_of_not_aestronglyMeasurable hf]
    exact le_top
  rcases eq_or_ne q ∞ with rfl | hq
  · simp only [ENNReal.toReal_top, div_zero, inv_zero, Real.rpow_zero, one_mul,
      eLorentzNorm_top_right hp0 hf]
    exact le_iSup₂ (f := fun (s : ℝ) (_ : 0 < s) ↦
      ENNReal.ofReal (s ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) s) t ht
  have hp' : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hq' : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [eLorentzNorm_eq_lintegral_rpow hp0 hq0 hq hf, one_div,
    ← ENNReal.rpow_le_rpow_iff hq', ← ENNReal.rpow_mul, inv_mul_cancel₀ hq'.ne',
    ENNReal.rpow_one, ENNReal.mul_rpow_of_nonneg _ _ hq'.le, TauCeti.lintegral_multHaar]
  calc ENNReal.ofReal ((p.toReal / q.toReal) ^ q.toReal⁻¹ * t ^ p.toReal⁻¹) ^ q.toReal *
        μ.decreasingRearrangement (‖f ·‖ₑ) t ^ q.toReal
      = (∫⁻ s in Ioo 0 t, ENNReal.ofReal (s ^ (q.toReal / p.toReal - 1))) *
          μ.decreasingRearrangement (‖f ·‖ₑ) t ^ q.toReal := by
        rw [TauCeti.lintegral_ofReal_rpow_Ioo (by linarith [div_pos hq' hp']) ht.le, sub_add_cancel]
        congr 1
        rw [ENNReal.ofReal_rpow_of_pos (by positivity), Real.mul_rpow (by positivity)
          (by positivity), ← Real.rpow_mul (by positivity), ← Real.rpow_mul ht.le,
          inv_mul_cancel₀ hq'.ne', Real.rpow_one]
        congr 1
        field_simp
    _ = ∫⁻ s in Ioo 0 t, ENNReal.ofReal s⁻¹ *
          (ENNReal.ofReal (s ^ p.toReal⁻¹) *
            μ.decreasingRearrangement (‖f ·‖ₑ) t) ^ q.toReal := by
        rw [← lintegral_mul_const'' _ (by fun_prop)]
        refine setLIntegral_congr_fun measurableSet_Ioo fun s ⟨hs, _⟩ ↦ ?_
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq'.le, ← mul_assoc,
          ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hs _),
          ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_mul hs.le, inv_mul_eq_div,
          Real.rpow_sub hs, Real.rpow_one]
        ring_nf
    _ ≤ ∫⁻ s in Ioo 0 t, ENNReal.ofReal s⁻¹ *
          (ENNReal.ofReal (s ^ p.toReal⁻¹) *
            μ.decreasingRearrangement (‖f ·‖ₑ) s) ^ q.toReal := by
        refine setLIntegral_mono' measurableSet_Ioo fun s ⟨_, hst⟩ ↦ ?_
        gcongr
        exact μ.antitone_decreasingRearrangement _ hst.le
    _ ≤ ∫⁻ s in Ioi 0, ENNReal.ofReal s⁻¹ *
          (ENNReal.ofReal (s ^ p.toReal⁻¹) *
            μ.decreasingRearrangement (‖f ·‖ₑ) s) ^ q.toReal :=
        lintegral_mono_set Ioo_subset_Ioi_self

/-- For `0 < p < ∞` and `q ≠ 0`, the weak-`L^p` gauge is bounded by `(q / p) ^ (1 / q)` times the
Lorentz `(p, q)` seminorm. -/
theorem eLorentzNorm_top_right_le {p q : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) (hq0 : q ≠ 0)
    (f : α → ε) :
    eLorentzNorm f p ∞ μ ≤
      ENNReal.ofReal ((q.toReal / p.toReal) ^ q.toReal⁻¹) * eLorentzNorm f p q μ := by
  rcases eq_or_ne q ∞ with rfl | hq
  · simp
  by_cases hf : AEStronglyMeasurable f μ
  swap
  · have hpos : 0 < (q.toReal / p.toReal) ^ q.toReal⁻¹ :=
      Real.rpow_pos_of_pos (div_pos (ENNReal.toReal_pos hq0 hq) (ENNReal.toReal_pos hp0 hp)) _
    rw [eLorentzNorm_of_not_aestronglyMeasurable hf, eLorentzNorm_of_not_aestronglyMeasurable hf,
      ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne']
  have hc : ENNReal.ofReal ((q.toReal / p.toReal) ^ q.toReal⁻¹) *
      ENNReal.ofReal ((p.toReal / q.toReal) ^ q.toReal⁻¹) = 1 := by
    have hp' := (ENNReal.toReal_pos hp0 hp).ne'
    have hq' := (ENNReal.toReal_pos hq0 hq).ne'
    have hdiv : q.toReal / p.toReal * (p.toReal / q.toReal) = 1 := by field_simp
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (div_nonneg ENNReal.toReal_nonneg
      ENNReal.toReal_nonneg) _),
      ← Real.mul_rpow (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
        (div_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg),
      hdiv, Real.one_rpow, ENNReal.ofReal_one]
  rw [eLorentzNorm_top_right hp0 hf]
  refine iSup₂_le fun t ht ↦ ?_
  calc ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t
      = ENNReal.ofReal ((q.toReal / p.toReal) ^ q.toReal⁻¹) *
          (ENNReal.ofReal ((p.toReal / q.toReal) ^ q.toReal⁻¹ * t ^ p.toReal⁻¹) *
            μ.decreasingRearrangement (‖f ·‖ₑ) t) := by
        rw [ENNReal.ofReal_mul (by positivity), ← mul_assoc, ← mul_assoc, hc, one_mul]
    _ ≤ ENNReal.ofReal ((q.toReal / p.toReal) ^ q.toReal⁻¹) * eLorentzNorm f p q μ := by
        gcongr
        exact ofReal_mul_decreasingRearrangement_le_eLorentzNorm hp0 hp hq0 ht f

/-- **Secondary-exponent embedding for Lorentz spaces** (Holmstedt–Calderón). For `0 < p < ∞` and
`0 < q₀ ≤ q₁ ≤ ∞`,
`‖f‖_{p,q₁} ≤ (q₀ / p) ^ (1 / q₀ - 1 / q₁) * ‖f‖_{p,q₀}`. -/
theorem eLorentzNorm_le_of_second_exponent_le {p q₀ q₁ : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hq₀ : q₀ ≠ 0) (hq : q₀ ≤ q₁) (f : α → ε) :
    eLorentzNorm f p q₁ μ ≤
      ENNReal.ofReal ((q₀.toReal / p.toReal) ^ (q₀.toReal⁻¹ - q₁.toReal⁻¹)) *
        eLorentzNorm f p q₀ μ := by
  rcases hq.eq_or_lt with rfl | hq_lt
  · simp
  have hq₀_top : q₀ ≠ ∞ := hq_lt.ne_top
  rcases eq_or_ne q₁ ∞ with rfl | hq₁_top
  · simpa using eLorentzNorm_top_right_le hp0 hp hq₀ f
  have hq₀' : 0 < q₀.toReal := ENNReal.toReal_pos hq₀ hq₀_top
  have hq₁' : 0 < q₁.toReal := ENNReal.toReal_pos (hq₀.bot_lt.trans hq_lt).ne' hq₁_top
  have hle : q₀.toReal ≤ q₁.toReal := ENNReal.toReal_mono hq₁_top hq
  by_cases hf : AEStronglyMeasurable f μ
  swap
  · have hpos : 0 < (q₀.toReal / p.toReal) ^ (q₀.toReal⁻¹ - q₁.toReal⁻¹) :=
      Real.rpow_pos_of_pos (div_pos hq₀' (ENNReal.toReal_pos hp0 hp)) _
    rw [eLorentzNorm_of_not_aestronglyMeasurable hf, eLorentzNorm_of_not_aestronglyMeasurable hf,
      ENNReal.mul_top (ENNReal.ofReal_pos.2 hpos).ne']
  set θ := 1 - q₀.toReal / q₁.toReal
  have hθ : θ ∈ Icc (0 : ℝ) 1 :=
    ⟨sub_nonneg.2 (div_le_one_of_le₀ hle hq₁'.le), sub_le_self _ (by positivity)⟩
  have hinv : q₁⁻¹ = ENNReal.ofReal (1 - θ) * q₀⁻¹ + ENNReal.ofReal θ * ∞⁻¹ := by
    rw [ENNReal.inv_top, mul_zero, add_zero, sub_sub_cancel,
      ← ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 hq₀),
      ← ENNReal.ofReal_toReal (ENNReal.inv_ne_top.2 (hq₀.bot_lt.trans hq_lt).ne'),
      ENNReal.toReal_inv, ENNReal.toReal_inv, ← ENNReal.ofReal_mul (by positivity),
      div_mul_eq_mul_div, mul_inv_cancel₀ hq₀'.ne', one_div]
  calc eLorentzNorm f p q₁ μ
      ≤ eLorentzNorm f p q₀ μ ^ (1 - θ) * eLorentzNorm f p ∞ μ ^ θ := by
        rw [eLorentzNorm_eq_eLpNorm hp0 hf, eLorentzNorm_eq_eLpNorm hp0 hf,
          eLorentzNorm_eq_eLpNorm hp0 hf]
        exact eLpNorm_le_eLpNorm_rpow_mul_eLpNorm_rpow hθ hinv
    _ ≤ eLorentzNorm f p q₀ μ ^ (1 - θ) *
          (ENNReal.ofReal ((q₀.toReal / p.toReal) ^ q₀.toReal⁻¹) *
            eLorentzNorm f p q₀ μ) ^ θ := by
        gcongr
        · exact hθ.1
        · exact eLorentzNorm_top_right_le hp0 hp hq₀ f
    _ = ENNReal.ofReal ((q₀.toReal / p.toReal) ^ (q₀.toReal⁻¹ - q₁.toReal⁻¹)) *
          eLorentzNorm f p q₀ μ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hθ.1, mul_left_comm,
          ← ENNReal.rpow_add_of_nonneg _ _ (sub_nonneg.2 hθ.2) hθ.1, sub_add_cancel,
          ENNReal.rpow_one,
          ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos
            (div_pos hq₀' (ENNReal.toReal_pos hp0 hp)) _),
          ← Real.rpow_mul (by positivity)]
        have hexp : q₀.toReal⁻¹ * θ = q₀.toReal⁻¹ - q₁.toReal⁻¹ := by
          simp only [θ]
          field_simp
        rw [hexp]

/-- Every initial half-line `(-∞, t]` with `t > 0` has infinite `dt / t`-measure. -/
private theorem multHaar_Iic_of_pos {t : ℝ} (ht : 0 < t) : TauCeti.multHaar (Iic t) = ∞ := by
  refine top_le_iff.1 (le_of_tendsto ENNReal.tendsto_nat_nhds_top (Eventually.of_forall fun n ↦ ?_))
  have ha : 0 < t * Real.exp (-n) := by positivity
  have hab : t * Real.exp (-n) ≤ t :=
    mul_le_of_le_one_right ht.le (Real.exp_le_one_iff.2 (by linarith))
  have hm : TauCeti.multHaar (Icc (t * Real.exp (-n)) t) = (n : ℝ≥0∞) := by
    rw [TauCeti.multHaar_Icc ha hab, Real.log_mul ht.ne' (Real.exp_ne_zero _), Real.log_exp]
    ring_nf
    exact ENNReal.ofReal_natCast n
  exact hm ▸ measure_mono Icc_subset_Iic_self

/-- Increasing a nonzero secondary exponent preserves `MemLorentz`: `L^{p,q₀} ⊆ L^{p,q₁}` for
`0 < q₀ ≤ q₁`. -/
theorem MemLorentz.mono_exponent {f : α → ε} {p q₀ q₁ : ℝ≥0∞} (hf : MemLorentz f p q₀ μ)
    (hq₀ : q₀ ≠ 0) (hq : q₀ ≤ q₁) : MemLorentz f p q₁ μ := by
  have hmeas := hf.aestronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp0
  · simp [MemLorentz, hmeas]
  rcases eq_or_ne p ∞ with rfl | hp
  · rcases eq_or_ne q₀ ∞ with rfl | hq₀_top
    · rwa [top_le_iff.1 hq]
    have hq₀' : 0 < q₀.toReal := ENNReal.toReal_pos hq₀ hq₀_top
    have hfin : ∫⁻ s, μ.decreasingRearrangement (‖f ·‖ₑ) s ^ q₀.toReal ∂TauCeti.multHaar < ∞ := by
      have h := hf.eLorentzNorm_lt_top
      rw [eLorentzNorm_eq_lintegral_rpow hp0 hq₀ hq₀_top hmeas, one_div,
        ENNReal.rpow_lt_top_iff_of_pos (inv_pos.2 hq₀')] at h
      simpa using h
    have hzero : ∀ t > 0, μ.decreasingRearrangement (‖f ·‖ₑ) t = 0 := fun t ht ↦ by
      by_contra hne
      have hpow : μ.decreasingRearrangement (‖f ·‖ₑ) t ^ q₀.toReal ≠ 0 := by
        intro h0
        rcases ENNReal.rpow_eq_zero_iff.1 h0 with ⟨h1, -⟩ | ⟨-, h2⟩
        · exact hne h1
        · linarith
      have hle : μ.decreasingRearrangement (‖f ·‖ₑ) t ^ q₀.toReal * TauCeti.multHaar (Iic t) ≤
          ∫⁻ s, μ.decreasingRearrangement (‖f ·‖ₑ) s ^ q₀.toReal ∂TauCeti.multHaar := by
        rw [← setLIntegral_const]
        exact (setLIntegral_mono' measurableSet_Iic fun s (hs : s ≤ t) ↦
          ENNReal.rpow_le_rpow (μ.antitone_decreasingRearrangement _ hs) hq₀'.le).trans
          (setLIntegral_le_lintegral _ _)
      rw [multHaar_Iic_of_pos ht, ENNReal.mul_top hpow, top_le_iff] at hle
      exact hfin.ne hle
    rw [MemLorentz, eLorentzNorm_eq_eLpNorm hp0 hmeas]
    have hae0 : (fun t : ℝ ↦ ENNReal.ofReal (t ^ (∞ : ℝ≥0∞).toReal⁻¹) *
        μ.decreasingRearrangement (‖f ·‖ₑ) t) =ᵐ[TauCeti.multHaar] 0 :=
      TauCeti.ae_pos_multHaar.mono fun t ht ↦ by simp [hzero t ht]
    rw [eLpNorm_congr_ae hae0, eLpNorm_zero]
    exact ENNReal.zero_lt_top
  · exact (eLorentzNorm_le_of_second_exponent_le hp0 hp hq₀ hq f).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf)

end CompareExp

/-- **Chebyshev's inequality** in Lorentz form: `‖f‖_{p,∞} ≤ ‖f‖_p` for `0 < p < ∞`. -/
theorem eLorentzNorm_top_right_le_eLpNorm {α ε : Type*} {_ : MeasurableSpace α} {μ : Measure α}
    [TopologicalSpace ε] [ContinuousENorm ε] {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) (f : α → ε) :
    eLorentzNorm f p ∞ μ ≤ eLpNorm f p μ := by
  have h := eLorentzNorm_top_right_le (μ := μ) hp0 hp hp0 f
  rw [div_self (ENNReal.toReal_pos hp0 hp).ne', Real.one_rpow, ENNReal.ofReal_one, one_mul] at h
  rwa [← eLorentzNorm_self]

/-! ### Indicator functions and power laws -/

section Examples

variable {α ε : Type*} {mα : MeasurableSpace α} {μ : Measure α}

private theorem eLpNorm_indicator_rpow_top_multHaar (A : Set α) {p : ℝ≥0∞} (hp : 0 < p.toReal) :
    eLpNorm
        ({t : ℝ | ENNReal.ofReal (1 * t) < μ A}.indicator fun u ↦ ENNReal.ofReal (u ^ p.toReal⁻¹))
        ∞ TauCeti.multHaar =
      μ A ^ p.toReal⁻¹ := by
  have hS : MeasurableSet {t : ℝ | ENNReal.ofReal (1 * t) < μ A} :=
    measurableSet_lt (by fun_prop) measurable_const
  have hφ : Measurable ({t : ℝ | ENNReal.ofReal (1 * t) < μ A}.indicator
      fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹)) :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).indicator hS
  rw [eLpNorm_exponent_top hφ.aestronglyMeasurable, eLpNormEssSup_eq_essSup_eNorm]
  have hpt : (fun t : ℝ ↦
        ‖{t : ℝ | ENNReal.ofReal (1 * t) < μ A}.indicator
          (fun u ↦ ENNReal.ofReal (u ^ p.toReal⁻¹)) t‖ₑ) =
      fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) *
        μ.decreasingRearrangement (A.indicator fun _ ↦ (1 : ℝ≥0∞)) t := by
    ext t
    simp only [eNorm_eq_self, μ.decreasingRearrangement_indicator, one_mul, indicator_apply,
      mem_ofPred_eq]
    split_ifs <;> simp
  rw [hpt, essSup_rpow_mul_decreasingRearrangement]
  conv_rhs => rw [eq_iSup_ofReal_of_lt (μ A)]
  have hiso := (ENNReal.orderIsoRpow p.toReal⁻¹ (inv_pos.2 hp)).map_iSup
    (fun t : ℝ ↦ ⨆ (_ : 0 < t ∧ ENNReal.ofReal t < μ A), ENNReal.ofReal t)
  simp only [ENNReal.orderIsoRpow_apply] at hiso
  rw [hiso]
  refine iSup_congr fun t ↦ ?_
  by_cases ht : 0 < t
  · by_cases hA' : ENNReal.ofReal t < μ A
    · rw [ciSup_pos ht, ciSup_pos ⟨ht, hA'⟩, μ.decreasingRearrangement_indicator,
        ENNReal.ofReal_rpow_of_pos ht]
      simp [hA']
    · simp [ht, hA', μ.decreasingRearrangement_indicator, ENNReal.zero_rpow_of_pos (inv_pos.2 hp)]
  · simp [ht, ENNReal.zero_rpow_of_pos (inv_pos.2 hp)]

private theorem eLpNorm_indicator_rpow_ne_top_multHaar (A : Set α) {p q : ℝ≥0∞}
    (hp : 0 < p.toReal) (hq0 : q ≠ 0) (hq : q ≠ ∞) :
    eLpNorm
        ({t : ℝ | ENNReal.ofReal (1 * t) < μ A}.indicator fun u ↦ ENNReal.ofReal (u ^ p.toReal⁻¹))
        q TauCeti.multHaar =
      ENNReal.ofReal ((p.toReal / q.toReal) ^ q.toReal⁻¹) * μ A ^ p.toReal⁻¹ := by
  set S : Set ℝ := {t : ℝ | ENNReal.ofReal (1 * t) < μ A}
  have hS : MeasurableSet S := measurableSet_lt (by fun_prop) measurable_const
  have hφ : Measurable (S.indicator fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹)) :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).indicator hS
  have hq' : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hq0 hq hφ.aestronglyMeasurable,
    TauCeti.lintegral_multHaar]
  have hcongr : ∀ t ∈ Ioi (0 : ℝ),
      ENNReal.ofReal t⁻¹ * ‖S.indicator (fun u ↦ ENNReal.ofReal (u ^ p.toReal⁻¹)) t‖ₑ ^ q.toReal =
        S.indicator (fun u ↦ ENNReal.ofReal (u ^ (q.toReal / p.toReal - 1))) t :=
    fun t (ht : 0 < t) ↦ by
      simp only [eNorm_eq_self]
      by_cases htS : t ∈ S
      · rw [indicator_of_mem htS, indicator_of_mem htS,
          ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos ht _),
          ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_mul ht.le, inv_mul_eq_div,
          Real.rpow_sub ht, Real.rpow_one]
        ring_nf
      · simp [htS, ENNReal.zero_rpow_of_pos hq']
  have hexp : q.toReal / p.toReal * q.toReal⁻¹ = p.toReal⁻¹ := by field_simp
  rw [setLIntegral_congr_fun measurableSet_Ioi hcongr,
    TauCeti.lintegral_indicator_ofReal_rpow_Ioi (by linarith [div_pos hq' hp]) one_pos (μ A),
    sub_add_cancel, Real.one_rpow, one_div (q.toReal / p.toReal), inv_div,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity),
    ENNReal.ofReal_rpow_of_pos (div_pos hp hq'), ← ENNReal.rpow_mul, one_div, hexp]

/-- **Lorentz seminorm of an indicator function.** For `0 < p < ∞`, `q ≠ 0`, and a null-measurable
set `A`,
`‖c 1_A‖_{p,q} = (p / q) ^ (1 / q) * ‖c‖ₑ * μ A ^ (1 / p)`. At `q = ∞`, `(p / ∞.toReal) ^ 0 = 1`,
recovering `‖c‖ₑ * μ A ^ (1 / p)`. -/
theorem eLorentzNorm_indicator_const₀ [TopologicalSpace ε] [ESeminormedAddMonoid ε] {A : Set α}
    (hA : NullMeasurableSet A μ) (c : ε) {p q : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) (hq0 : q ≠ 0) :
    eLorentzNorm (A.indicator fun _ ↦ c) p q μ =
      ENNReal.ofReal ((p.toReal / q.toReal) ^ q.toReal⁻¹) * ‖c‖ₑ * μ A ^ p.toReal⁻¹ := by
  have hf : AEStronglyMeasurable (A.indicator fun _ ↦ c) μ :=
    aestronglyMeasurable_const.indicator₀ hA
  have henorm : (fun x ↦ ‖A.indicator (fun _ ↦ c) x‖ₑ) = A.indicator fun _ ↦ ‖c‖ₑ := by
    ext x
    by_cases hx : x ∈ A <;> simp [hx]
  have hp' : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  set S : Set ℝ := {t : ℝ | ENNReal.ofReal (1 * t) < μ A}
  have hS : MeasurableSet S := measurableSet_lt (by fun_prop) measurable_const
  have hφ : Measurable (S.indicator fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹)) :=
    (ENNReal.measurable_ofReal.comp (measurable_id.pow_const _)).indicator hS
  have hpt : (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) *
        μ.decreasingRearrangement (‖A.indicator (fun _ ↦ c) ·‖ₑ) t) =
      fun t : ℝ ↦ ‖c‖ₑ * S.indicator (fun u ↦ ENNReal.ofReal (u ^ p.toReal⁻¹)) t := by
    ext t
    rw [henorm, μ.decreasingRearrangement_indicator]
    by_cases ht : ENNReal.ofReal t < μ A
    · have htS : t ∈ S := by simpa [S] using ht
      simp only [ht, ↓reduceIte, indicator_of_mem htS, mul_comm]
    · have htS : t ∉ S := by simpa [S] using ht
      simp only [ht, ↓reduceIte, indicator_of_notMem htS, mul_zero]
  rw [eLorentzNorm_eq_eLpNorm hp0 hf, hpt, eLpNorm_const_mul_ennreal hφ.aestronglyMeasurable,
    show ENNReal.ofReal ((p.toReal / q.toReal) ^ q.toReal⁻¹) * ‖c‖ₑ * μ A ^ p.toReal⁻¹ =
      ‖c‖ₑ * (ENNReal.ofReal ((p.toReal / q.toReal) ^ q.toReal⁻¹) * μ A ^ p.toReal⁻¹) by ring]
  congr 1
  rcases eq_or_ne q ∞ with rfl | hq
  · simp only [ENNReal.toReal_top, div_zero, inv_zero, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
    exact eLpNorm_indicator_rpow_top_multHaar A hp'
  · exact eLpNorm_indicator_rpow_ne_top_multHaar A hp' hq0 hq

/-- Measurable-set form of `eLorentzNorm_indicator_const₀`. -/
theorem eLorentzNorm_indicator_const [TopologicalSpace ε] [ESeminormedAddMonoid ε] {A : Set α}
    (hA : MeasurableSet A) (c : ε) {p q : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) (hq0 : q ≠ 0) :
    eLorentzNorm (A.indicator fun _ ↦ c) p q μ =
      ENNReal.ofReal ((p.toReal / q.toReal) ^ q.toReal⁻¹) * ‖c‖ₑ * μ A ^ p.toReal⁻¹ :=
  eLorentzNorm_indicator_const₀ hA.nullMeasurableSet c hp0 hp hq0

/-- A decreasing negative power `t ↦ t ^ (-a)` (`a > 0`) on `(0, ∞)` is its own decreasing
rearrangement for `s > 0`. -/
theorem _root_.MeasureTheory.Measure.decreasingRearrangement_rpow_neg {a : ℝ} (ha : 0 < a) {s : ℝ}
    (hs : 0 < s) :
    (volume.restrict (Ioi (0 : ℝ))).decreasingRearrangement
        (fun t ↦ ENNReal.ofReal (t ^ (-a))) s =
      ENNReal.ofReal (s ^ (-a)) := by
  refine eq_of_forall_lt_iff fun c ↦ ?_
  rw [Measure.lt_decreasingRearrangement_iff]
  rcases eq_or_ne c ∞ with rfl | hct
  · simp
  rcases eq_or_ne c 0 with rfl | hc0
  · have hpos : 0 < s ^ (-a) := Real.rpow_pos_of_pos hs _
    have huniv : {t : ℝ | 0 < ENNReal.ofReal (t ^ (-a))} ∩ Ioi 0 = Ioi 0 := by
      ext t
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, ENNReal.ofReal_pos, and_iff_right_iff_imp]
      exact fun ht ↦ Real.rpow_pos_of_pos ht _
    rw [Measure.restrict_apply (measurableSet_lt measurable_const (by fun_prop)), huniv,
      Real.volume_Ioi]
    simp [hpos]
  have hc : 0 < c.toReal := ENNReal.toReal_pos hc0 hct
  have hset : {t : ℝ | c < ENNReal.ofReal (t ^ (-a))} ∩ Ioi 0 = Ioo 0 (c.toReal ^ (-a⁻¹)) := by
    ext t
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, mem_Ioo]
    refine ⟨fun ⟨hlt, ht⟩ ↦ ⟨ht, ?_⟩, fun ⟨ht, hlt⟩ ↦ ⟨?_, ht⟩⟩
    · have hlt' : c.toReal < t ^ (-a) :=
        (ENNReal.lt_ofReal_iff_toReal_lt hct).1 hlt
      calc t = (t ^ (-a)) ^ (-a⁻¹) := by
            rw [← Real.rpow_mul ht.le, neg_mul_neg, mul_inv_cancel₀ ha.ne', Real.rpow_one]
        _ < c.toReal ^ (-a⁻¹) := Real.rpow_lt_rpow_of_neg hc hlt' (neg_neg_of_pos (inv_pos.2 ha))
    · refine (ENNReal.lt_ofReal_iff_toReal_lt hct).2 ?_
      calc c.toReal = (c.toReal ^ (-a⁻¹)) ^ (-a) := by
            rw [← Real.rpow_mul hc.le, neg_mul_neg, inv_mul_cancel₀ ha.ne', Real.rpow_one]
        _ < t ^ (-a) := Real.rpow_lt_rpow_of_neg ht hlt (neg_neg_of_pos ha)
  rw [Measure.restrict_apply (measurableSet_lt measurable_const (by fun_prop)), hset,
    Real.volume_Ioo, sub_zero, ENNReal.ofReal_lt_ofReal_iff (by positivity),
    ENNReal.lt_ofReal_iff_toReal_lt hct]
  refine ⟨fun hlt ↦ ?_, fun hlt ↦ ?_⟩
  · calc c.toReal = (c.toReal ^ (-a⁻¹)) ^ (-a) := by
          rw [← Real.rpow_mul hc.le, neg_mul_neg, inv_mul_cancel₀ ha.ne', Real.rpow_one]
      _ < s ^ (-a) := Real.rpow_lt_rpow_of_neg hs hlt (neg_neg_of_pos ha)
  · calc s = (s ^ (-a)) ^ (-a⁻¹) := by
          rw [← Real.rpow_mul hs.le, neg_mul_neg, mul_inv_cancel₀ ha.ne', Real.rpow_one]
      _ < c.toReal ^ (-a⁻¹) := Real.rpow_lt_rpow_of_neg hc hlt (neg_neg_of_pos (inv_pos.2 ha))

/-- **Power-law Lorentz seminorm.** On `(0, ∞)` with Lebesgue measure, `t ↦ t ^ (-1 / p)`
(`0 < p < ∞`) has weak-`L^p` gauge `1` (`q = ∞`) and Lorentz seminorm `∞` for every finite
`q ≠ 0` (in particular, it lies in `L^{p,∞}` and not in `L^p`). -/
theorem eLorentzNorm_rpow_neg_inv {p q : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) (hq0 : q ≠ 0) :
    eLorentzNorm (fun t : ℝ ↦ t ^ (-p.toReal⁻¹)) p q (volume.restrict (Ioi 0)) =
      if q = ∞ then 1 else ∞ := by
  have hp' : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hf : AEStronglyMeasurable (fun t : ℝ ↦ t ^ (-p.toReal⁻¹)) (volume.restrict (Ioi 0)) :=
    (continuousOn_id.rpow_const fun _ ht ↦ Or.inl (ne_of_gt ht)).aestronglyMeasurable
      measurableSet_Ioi
  have hrearr : ∀ s > 0, (volume.restrict (Ioi 0)).decreasingRearrangement
      (fun t : ℝ ↦ ‖t ^ (-p.toReal⁻¹)‖ₑ) s = ENNReal.ofReal (s ^ (-p.toReal⁻¹)) := fun s hs ↦ by
    have hae : (fun t : ℝ ↦ ‖t ^ (-p.toReal⁻¹)‖ₑ) =ᵐ[volume.restrict (Ioi 0)]
        fun t ↦ ENNReal.ofReal (t ^ (-p.toReal⁻¹)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t (ht : 0 < t)
      exact Real.eNorm_of_nonneg (Real.rpow_nonneg ht.le _)
    rw [Measure.decreasingRearrangement_congr_ae _ hae,
      Measure.decreasingRearrangement_rpow_neg (inv_pos.2 hp') hs]
  have hae1 : (fun s : ℝ ↦ ENNReal.ofReal (s ^ p.toReal⁻¹) *
      (volume.restrict (Ioi 0)).decreasingRearrangement
        (fun t : ℝ ↦ ‖t ^ (-p.toReal⁻¹)‖ₑ) s) =ᵐ[TauCeti.multHaar] fun _ ↦ (1 : ℝ≥0∞) := by
    filter_upwards [TauCeti.ae_pos_multHaar] with s hs
    rw [hrearr s hs, ← ENNReal.ofReal_mul (by positivity), ← Real.rpow_add hs, add_neg_cancel,
      Real.rpow_zero, ENNReal.ofReal_one]
  rw [eLorentzNorm_eq_eLpNorm hp0 hf, eLpNorm_congr_ae hae1]
  split_ifs with hq
  · subst hq
    rw [eLpNorm_exponent_top aestronglyMeasurable_const, eLpNormEssSup_eq_essSup_eNorm]
    simp only [eNorm_eq_self]
    exact essSup_const (1 : ℝ≥0∞) fun h0 ↦
      by simpa [h0] using TauCeti.multHaar_Icc_one_exp_one
  · have hq' : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
    rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hq0 hq aestronglyMeasurable_const,
      TauCeti.lintegral_multHaar]
    simp only [eNorm_eq_self, ENNReal.one_rpow, mul_one, ← Real.rpow_neg_one,
      TauCeti.lintegral_ofReal_rpow_Ioi]
    exact ENNReal.top_rpow_of_pos (by positivity)

end Examples

/-! ### Quasi-triangle inequality and failure of subadditivity -/

section QuasiTriangle

variable {α ε : Type*} {mα : MeasurableSpace α} {μ : Measure α}

private theorem ofReal_rpow_mul_decreasingRearrangement_add_le [TopologicalSpace ε]
    [ESeminormedAddMonoid ε] (f g : α → ε) (p : ℝ≥0∞) (μ : Measure α) {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖(f + g) ·‖ₑ) t ≤
      ENNReal.ofReal (2 ^ p.toReal⁻¹) *
        (ENNReal.ofReal ((2⁻¹ * t) ^ p.toReal⁻¹) *
            μ.decreasingRearrangement (‖f ·‖ₑ) (2⁻¹ * t) +
          ENNReal.ofReal ((2⁻¹ * t) ^ p.toReal⁻¹) *
            μ.decreasingRearrangement (‖g ·‖ₑ) (2⁻¹ * t)) := by
  have hsub : μ.decreasingRearrangement (‖(f + g) ·‖ₑ) t ≤
      μ.decreasingRearrangement (‖f ·‖ₑ) (2⁻¹ * t) +
        μ.decreasingRearrangement (‖g ·‖ₑ) (2⁻¹ * t) := by
    calc μ.decreasingRearrangement (‖(f + g) ·‖ₑ) t
        ≤ μ.decreasingRearrangement ((‖f ·‖ₑ) + (‖g ·‖ₑ)) (2⁻¹ * t + 2⁻¹ * t) := by
          rw [show 2⁻¹ * t + 2⁻¹ * t = t by ring]
          exact μ.decreasingRearrangement_mono (fun x ↦ eNorm_add_le (f x) (g x)) t
      _ ≤ _ := μ.decreasingRearrangement_add_le _ _ (by positivity) (by positivity)
  have hpow : ENNReal.ofReal (t ^ p.toReal⁻¹) =
      ENNReal.ofReal (2 ^ p.toReal⁻¹) * ENNReal.ofReal ((2⁻¹ * t) ^ p.toReal⁻¹) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow two_pos.le (by positivity)]
    ring_nf
  calc ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖(f + g) ·‖ₑ) t
      ≤ ENNReal.ofReal (t ^ p.toReal⁻¹) *
          (μ.decreasingRearrangement (‖f ·‖ₑ) (2⁻¹ * t) +
            μ.decreasingRearrangement (‖g ·‖ₑ) (2⁻¹ * t)) := by gcongr
    _ = _ := by
        rw [hpow]
        ring

/-- **Quasi-triangle inequality for the Lorentz seminorm.** Shifted subadditivity
`(f + g)* t ≤ f* (t / 2) + g* (t / 2)` together with dilation invariance of `dt / t` gives
`‖f + g‖_{p,q} ≤ 2 ^ (1 / p) * ENNReal.LpAddConst q * (‖f‖_{p,q} + ‖g‖_{p,q})` for all
`p, q ∈ [0, ∞]`. -/
theorem eLorentzNorm_add_le [TopologicalSpace ε] [ESeminormedAddMonoid ε] [ContinuousAdd ε]
    (f g : α → ε) (p q : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm (f + g) p q μ ≤
      ENNReal.ofReal (2 ^ p.toReal⁻¹) * ENNReal.LpAddConst q *
        (eLorentzNorm f p q μ + eLorentzNorm g p q μ) := by
  have hc0 : ENNReal.ofReal (2 ^ p.toReal⁻¹) * ENNReal.LpAddConst q ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.2 (by positivity)).ne' (ENNReal.LpAddConst_ne_zero q)
  by_cases hf : AEStronglyMeasurable f μ
  swap
  · rw [eLorentzNorm_of_not_aestronglyMeasurable hf, top_add, ENNReal.mul_top hc0]
    exact le_top
  by_cases hg : AEStronglyMeasurable g μ
  swap
  · rw [eLorentzNorm_of_not_aestronglyMeasurable hg, add_top, ENNReal.mul_top hc0]
    exact le_top
  rcases eq_or_ne p 0 with rfl | hp
  · simp [hf.add hg]
  set φf : ℝ → ℝ≥0∞ :=
    fun t ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t
  set φg : ℝ → ℝ≥0∞ :=
    fun t ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖g ·‖ₑ) t
  have hmp : MeasurePreserving (2⁻¹ * ·) TauCeti.multHaar TauCeti.multHaar :=
    ⟨measurable_const_mul _, TauCeti.map_multHaar_mul_left (by positivity)⟩
  have hφf : AEStronglyMeasurable φf TauCeti.multHaar :=
    (measurable_rpow_mul_decreasingRearrangement μ _ p).aestronglyMeasurable
  have hφg : AEStronglyMeasurable φg TauCeti.multHaar :=
    (measurable_rpow_mul_decreasingRearrangement μ _ p).aestronglyMeasurable
  have hsum : AEStronglyMeasurable (φf ∘ (2⁻¹ * ·) + φg ∘ (2⁻¹ * ·)) TauCeti.multHaar :=
    ((hφf.comp_measurePreserving hmp).aemeasurable.add
      (hφg.comp_measurePreserving hmp).aemeasurable).aestronglyMeasurable
  rw [eLorentzNorm_eq_eLpNorm hp (hf.add hg), eLorentzNorm_eq_eLpNorm hp hf,
    eLorentzNorm_eq_eLpNorm hp hg]
  calc eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) *
          μ.decreasingRearrangement (‖(f + g) ·‖ₑ) t) q TauCeti.multHaar
      ≤ eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (2 ^ p.toReal⁻¹) *
          (φf ∘ (2⁻¹ * ·) + φg ∘ (2⁻¹ * ·)) t) q TauCeti.multHaar := by
        refine eLpNorm_mono_eNorm_ae
          (measurable_rpow_mul_decreasingRearrangement μ _ p).aestronglyMeasurable ?_
        filter_upwards [TauCeti.ae_pos_multHaar] with t ht
        simpa only [eNorm_eq_self, Pi.add_apply, Function.comp_apply, φf, φg] using
          ofReal_rpow_mul_decreasingRearrangement_add_le f g p μ ht
    _ = ENNReal.ofReal (2 ^ p.toReal⁻¹) *
          eLpNorm (φf ∘ (2⁻¹ * ·) + φg ∘ (2⁻¹ * ·)) q TauCeti.multHaar :=
        eLpNorm_const_mul_ennreal hsum
    _ ≤ ENNReal.ofReal (2 ^ p.toReal⁻¹) *
          (ENNReal.LpAddConst q * (eLpNorm φf q TauCeti.multHaar +
            eLpNorm φg q TauCeti.multHaar)) := by
        gcongr
        exact (eLpNorm_add_le' q).trans_eq
          (by rw [eLpNorm_comp_measurePreserving hφf hmp, eLpNorm_comp_measurePreserving hφg hmp])
    _ = ENNReal.ofReal (2 ^ p.toReal⁻¹) * ENNReal.LpAddConst q *
          (eLpNorm φf q TauCeti.multHaar + eLpNorm φg q TauCeti.multHaar) :=
        (mul_assoc _ _ _).symm

/-- For `1 ≤ q`, the Lorentz seminorm satisfies the `2 ^ (1 / p)`-quasi-triangle inequality
`‖f + g‖_{p,q} ≤ 2 ^ (1 / p) * (‖f‖_{p,q} + ‖g‖_{p,q})`. -/
theorem eLorentzNorm_add_le_of_one_le [TopologicalSpace ε] [ESeminormedAddMonoid ε]
    [ContinuousAdd ε] {p q : ℝ≥0∞} (hq : 1 ≤ q) (f g : α → ε) (μ : Measure α) :
    eLorentzNorm (f + g) p q μ ≤
      ENNReal.ofReal (2 ^ p.toReal⁻¹) * (eLorentzNorm f p q μ + eLorentzNorm g p q μ) := by
  simpa [ENNReal.LpAddConst_of_one_le hq] using eLorentzNorm_add_le f g p q μ

theorem MemLorentz.add [TopologicalSpace ε] [ESeminormedAddMonoid ε] [ContinuousAdd ε]
    {f g : α → ε} {p q : ℝ≥0∞} (hf : MemLorentz f p q μ) (hg : MemLorentz g p q μ) :
    MemLorentz (f + g) p q μ :=
  (eLorentzNorm_add_le f g p q μ).trans_lt <|
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.LpAddConst_lt_top q))
      (ENNReal.add_lt_top.2 ⟨hf, hg⟩)

theorem MemLorentz.sub [NormedAddCommGroup ε] {f g : α → ε} {p q : ℝ≥0∞}
    (hf : MemLorentz f p q μ) (hg : MemLorentz g p q μ) :
    MemLorentz (f - g) p q μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

private theorem count_univ_bool : (Measure.count : Measure Bool) univ = 2 := by
  rw [Measure.count_apply_finite _ finite_univ]
  simp

/-- Bounds `eLorentzNorm h 2 ∞ Measure.count` by `2` for a nonnegative function on `Bool` bounded
by `2` that is at most `1` at one point. -/
private theorem eLorentzNorm_two_top_bool_le_two {h : Bool → ℝ}
    (hh : ∀ b, 0 ≤ h b ∧ h b ≤ 2) {b₀ : Bool} (hb₀ : h b₀ ≤ 1) :
    eLorentzNorm h 2 ∞ Measure.count ≤ 2 := by
  rw [eLorentzNorm_top_right_eq_iSup_measure (by norm_num) (by simp) .of_discrete]
  refine iSup_le fun c ↦ ?_
  simp only [ENNReal.toReal_ofNat]
  rcases le_or_gt 2 c with hc2 | hc2
  · have hemp : {b : Bool | c < ‖h b‖ₑ} = ∅ := by
      ext b
      simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt,
        Real.eNorm_of_nonneg (hh b).1]
      exact (ENNReal.ofReal_le_ofReal (hh b).2).trans (by simpa using hc2)
    simp [hemp]
  rcases le_or_gt 1 c with hc1 | hc1
  · have hsub : {b : Bool | c < ‖h b‖ₑ} ⊆ {!b₀} := fun b hb ↦ by
      simp only [mem_singleton_iff]
      by_contra hne
      have hbeq : b = b₀ := by cases b <;> cases b₀ <;> simp_all
      subst hbeq
      have hle : ‖h b‖ₑ ≤ 1 := by
        rw [Real.eNorm_of_nonneg (hh b).1, ENNReal.ofReal_le_one]
        exact hb₀
      exact (hle.trans hc1).not_gt hb
    calc c * (Measure.count {b : Bool | c < ‖h b‖ₑ}) ^ (2 : ℝ)⁻¹
        ≤ 2 * (Measure.count ({!b₀} : Set Bool)) ^ (2 : ℝ)⁻¹ :=
          mul_le_mul' hc2.le (ENNReal.rpow_le_rpow (measure_mono hsub) (by positivity))
      _ = 2 := by simp
  · have hcount : (Measure.count : Measure Bool) {b : Bool | c < ‖h b‖ₑ} ≤ 2 :=
      (measure_mono (subset_univ _)).trans_eq count_univ_bool
    have hsqrt : (2 : ℝ≥0∞) ^ (2 : ℝ)⁻¹ ≤ 2 := by
      rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ENNReal.ofReal_rpow_of_pos two_pos]
      exact ENNReal.ofReal_le_ofReal (by
        rw [← one_div, ← Real.sqrt_eq_rpow]
        exact Real.sqrt_le_iff.2 ⟨zero_le_two, by norm_num⟩)
    calc c * (Measure.count {b : Bool | c < ‖h b‖ₑ}) ^ (2 : ℝ)⁻¹
        ≤ 1 * (2 : ℝ≥0∞) ^ (2 : ℝ)⁻¹ :=
          mul_le_mul' hc1.le (ENNReal.rpow_le_rpow hcount (by positivity))
      _ ≤ 2 := by simpa using hsqrt

/-- **Failure of the triangle inequality for `eLorentzNorm`.** On `Bool` with counting measure, the
two-valued functions `f = (1, 2)` and `g = (2, 1)` satisfy `‖f‖_{2,∞} ≤ 2` and `‖g‖_{2,∞} ≤ 2`,
whereas `f + g = (3, 3)` has `‖f + g‖_{2,∞} = 3 √2 > 4 ≥ ‖f‖_{2,∞} + ‖g‖_{2,∞}`. This
distinguishes the rearrangement gauge from the Banach norm induced by real interpolation of
`(L¹, L^∞)`. -/
theorem exists_lt_eLorentzNorm_add :
    ∃ f g : Bool → ℝ,
      MemLorentz f 2 ∞ Measure.count ∧ MemLorentz g 2 ∞ Measure.count ∧
        eLorentzNorm f 2 ∞ Measure.count + eLorentzNorm g 2 ∞ Measure.count <
          eLorentzNorm (f + g) 2 ∞ Measure.count := by
  set f : Bool → ℝ := fun b ↦ if b then 1 else 2
  set g : Bool → ℝ := fun b ↦ if b then 2 else 1
  have hf2 : eLorentzNorm f 2 ∞ Measure.count ≤ 2 :=
    eLorentzNorm_two_top_bool_le_two (fun b ↦ by cases b <;> simp [f]) (b₀ := true) (by simp [f])
  have hg2 : eLorentzNorm g 2 ∞ Measure.count ≤ 2 :=
    eLorentzNorm_two_top_bool_le_two (fun b ↦ by cases b <;> simp [g]) (b₀ := false) (by simp [g])
  have hsum_eq : f + g = univ.indicator fun _ : Bool ↦ (3 : ℝ) := by
    ext b
    cases b <;> simp [f, g] <;> norm_num
  have hfg : eLorentzNorm (f + g) 2 ∞ Measure.count = ENNReal.ofReal (3 * Real.sqrt 2) := by
    rw [hsum_eq, eLorentzNorm_indicator_const MeasurableSet.univ (3 : ℝ) (by norm_num) (by simp)
      (by simp)]
    have hcount : (Measure.count : Measure Bool) univ = ENNReal.ofReal 2 := by
      rw [count_univ_bool]
      simp
    rw [ENNReal.toReal_top, div_zero, inv_zero, Real.rpow_zero, ENNReal.ofReal_one, one_mul,
      Real.eNorm_of_nonneg (by positivity), ENNReal.toReal_ofNat, hcount,
      ENNReal.ofReal_rpow_of_pos two_pos, ← one_div, ← Real.sqrt_eq_rpow,
      ← ENNReal.ofReal_mul (by positivity)]
  refine ⟨f, g, hf2.trans_lt (by norm_num), hg2.trans_lt (by norm_num), ?_⟩
  calc eLorentzNorm f 2 ∞ Measure.count + eLorentzNorm g 2 ∞ Measure.count
      ≤ 2 + 2 := add_le_add hf2 hg2
    _ = ENNReal.ofReal 4 := by norm_num
    _ < ENNReal.ofReal (3 * Real.sqrt 2) := by
        refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).2 ?_
        rw [show (4 : ℝ) = Real.sqrt 16 by
              rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by positivity)],
          show 3 * Real.sqrt 2 = Real.sqrt 18 by
            rw [show (18 : ℝ) = 3 ^ 2 * 2 by norm_num, Real.sqrt_mul (by positivity),
              Real.sqrt_sq (by positivity)]]
        exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)
    _ = eLorentzNorm (f + g) 2 ∞ Measure.count := hfg.symm

end QuasiTriangle

end TauCeti
