/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality
public import TauCeti.MeasureTheory.Function.DecreasingRearrangement
public import TauCeti.MeasureTheory.Measure.Haar.MultHaar

/-!
# Scalar Lorentz gauges `L^{p,q}`

For a measure `μ` on `α`, exponents `p, q ∈ [0, ∞]`, and `f : α → ε`, the **Lorentz gauge**
`TauCeti.eLorentzNorm f p q μ` is `0` for `p = 0` (when `f` is a.e. strongly measurable), the
`L^q(dt / t)` seminorm of `t ↦ t ^ (1 / p) (‖f‖ₑ)* t` for `p ≠ 0`, and `∞` if `f` is not a.e.
strongly measurable. Here `(‖f‖ₑ)*` is the decreasing rearrangement
`MeasureTheory.Measure.decreasingRearrangement` and `dt / t` is `TauCeti.multHaar`. The predicate
`TauCeti.MemLorentz f p q μ` asserts `eLorentzNorm f p q μ < ∞`, which includes a.e. strong
measurability for all `p, q`.

Note that `eLorentzNorm` is the rearrangement gauge `‖f‖_{p,q}^*`: it is only a quasi-norm in
general (subadditive up to `2 ^ (1 / p) * ENNReal.LpAddConst q`), whereas for `1 < p < ∞` and
`1 ≤ q ≤ ∞` replacing `(‖f‖ₑ)* t` by its maximal average `t⁻¹ ∫₀ᵗ (‖f‖ₑ)*` yields an equivalent
Banach norm via real interpolation of `(L¹, L^∞)`.

## Main declarations

* `TauCeti.eLorentzNorm`, `TauCeti.MemLorentz`: the Lorentz gauge in `[0, ∞]` and the corresponding
  membership predicate.
* `TauCeti.eLorentzNorm_self`, `TauCeti.memLorentz_self_iff`: `L^{p,p} = Lᵖ` isometrically for
  every `p ∈ [0, ∞]`.
* `TauCeti.eLorentzNorm_eq_zero_iff`: for `p ≠ 0` and `q ≠ 0`, `eLorentzNorm f p q μ = 0` iff `f`
  is a.e. strongly measurable and `‖f‖ₑ = 0` almost everywhere.
* `TauCeti.eLorentzNorm_add_le'`, `TauCeti.eLorentzNorm_add_le`, `TauCeti.MemLorentz.add`:
  quasi-triangle inequality and closure under addition.
* `TauCeti.eLorentzNorm_const_smul`, `TauCeti.eLorentzNorm_smul_le_eLpNorm_top_mul_eLorentzNorm`:
  homogeneity and `L^∞` multiplier bound.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §1.3.
* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., GTM 249, Springer, 2014, §1.4.
* T. Fack and H. Kosaki, *Generalized s-numbers of τ-measurable operators*, Pacific J. Math.
  **123** (1986), 269–300.
-/

public noncomputable section

open Filter MeasureTheory Measure Set Topology
open scoped ENNReal NNReal

namespace TauCeti

variable {α ε : Type*} {mα : MeasurableSpace α} {μ : Measure α} {p q : ℝ≥0∞}

/-- The **Lorentz gauge** `‖f‖_{L^{p,q}(μ)}` in `[0, ∞]`: for an a.e. strongly measurable `f`, it
is `0` when `p = 0` and `‖t ↦ t ^ (1 / p) (‖f‖ₑ)* t‖_{L^q(dt / t)}` when `p ≠ 0`; if `f` is not
a.e. strongly measurable, it is `∞`. -/
def eLorentzNorm [TopologicalSpace ε] [ENorm ε] {_ : MeasurableSpace α}
    (f : α → ε) (p q : ℝ≥0∞) (μ : Measure α := by volume_tac) : ℝ≥0∞ :=
  open scoped Classical in
  if AEStronglyMeasurable f μ then
    if p = 0 then 0
    else eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) *
      μ.decreasingRearrangement (‖f ·‖ₑ) t) q multHaar
  else ∞

theorem eLorentzNorm_def [TopologicalSpace ε] [ENorm ε]
    (f : α → ε) (p q : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm f p q μ =
      open scoped Classical in
      if AEStronglyMeasurable f μ then
        if p = 0 then 0
        else eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) *
          μ.decreasingRearrangement (‖f ·‖ₑ) t) q multHaar
      else ∞ :=
  (rfl)

/-- Membership in the Lorentz class `L^{p,q}(μ)`: `f` is a.e. strongly measurable and has finite
Lorentz gauge `eLorentzNorm f p q μ < ∞`. -/
def MemLorentz [TopologicalSpace ε] [ENorm ε] {_ : MeasurableSpace α}
    (f : α → ε) (p q : ℝ≥0∞) (μ : Measure α := by volume_tac) : Prop :=
  eLorentzNorm f p q μ < ∞

theorem memLorentz_iff [TopologicalSpace ε] [ENorm ε] {f : α → ε} :
    MemLorentz f p q μ ↔ eLorentzNorm f p q μ < ∞ :=
  Iff.rfl

/-- For every `r : ℝ` and `h : α → ℝ≥0∞`, `t ↦ ENNReal.ofReal (t ^ r) * h*(t)` is Borel
measurable. -/
theorem measurable_ofReal_rpow_mul_decreasingRearrangement (μ : Measure α) (r : ℝ)
    (h : α → ℝ≥0∞) :
    Measurable fun t : ℝ ↦ ENNReal.ofReal (t ^ r) * μ.decreasingRearrangement h t :=
  ((measurable_id.pow_const r).ennreal_ofReal).mul (μ.measurable_decreasingRearrangement h)

section Basic

variable [TopologicalSpace ε] [ENorm ε] {f g : α → ε}

theorem eLorentzNorm_of_not_aestronglyMeasurable (h : ¬ AEStronglyMeasurable f μ) :
    eLorentzNorm f p q μ = ∞ := by
  simp [eLorentzNorm, h]

theorem aestronglyMeasurable_of_eLorentzNorm_ne_top (h : eLorentzNorm f p q μ ≠ ∞) :
    AEStronglyMeasurable f μ := by
  contrapose h
  exact eLorentzNorm_of_not_aestronglyMeasurable h

theorem MemLorentz.eLorentzNorm_lt_top (h : MemLorentz f p q μ) :
    eLorentzNorm f p q μ < ∞ :=
  h

@[aesop (rule_sets := [finiteness]) unsafe 95% apply]
theorem MemLorentz.eLorentzNorm_ne_top (h : MemLorentz f p q μ) :
    eLorentzNorm f p q μ ≠ ∞ :=
  h.ne

theorem MemLorentz.aestronglyMeasurable (h : MemLorentz f p q μ) :
    AEStronglyMeasurable f μ :=
  aestronglyMeasurable_of_eLorentzNorm_ne_top h.ne

theorem eLorentzNorm_eq_eLpNorm_multHaar (hp : p ≠ 0) (hf : AEStronglyMeasurable f μ) :
    eLorentzNorm f p q μ =
      eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) *
        μ.decreasingRearrangement (‖f ·‖ₑ) t) q multHaar := by
  simp [eLorentzNorm, hf, hp]

@[simp]
theorem eLorentzNorm_exponent_zero_left (hf : AEStronglyMeasurable f μ) :
    eLorentzNorm f 0 q μ = 0 := by
  simp [eLorentzNorm, hf]

@[simp]
theorem eLorentzNorm_exponent_zero_right (hf : AEStronglyMeasurable f μ) :
    eLorentzNorm f p 0 μ = 0 := by
  by_cases hp : p = 0
  · simp [hp, hf]
  · rw [eLorentzNorm_eq_eLpNorm_multHaar hp hf,
      eLpNorm_exponent_zero
        (measurable_ofReal_rpow_mul_decreasingRearrangement μ _ _).aestronglyMeasurable]

@[simp]
theorem memLorentz_zero_left_iff : MemLorentz f 0 q μ ↔ AEStronglyMeasurable f μ :=
  ⟨MemLorentz.aestronglyMeasurable, fun hf ↦ by simp [memLorentz_iff, hf]⟩

@[simp]
theorem memLorentz_zero_right_iff : MemLorentz f p 0 μ ↔ AEStronglyMeasurable f μ :=
  ⟨MemLorentz.aestronglyMeasurable, fun hf ↦ by simp [memLorentz_iff, hf]⟩

@[simp]
theorem eLorentzNorm_measure_zero : eLorentzNorm f p q (0 : Measure α) = 0 := by
  have hf : AEStronglyMeasurable f (0 : Measure α) := aestronglyMeasurable_zero_measure f
  by_cases hp : p = 0
  · simp [hp, hf]
  · rw [eLorentzNorm_eq_eLpNorm_multHaar hp hf]
    have h0 : ∀ t, (0 : Measure α).decreasingRearrangement (‖f ·‖ₑ) t = 0 := fun t ↦
      le_antisymm (((0 : Measure α).decreasingRearrangement_le_iff).2 (by simp)) bot_le
    simp [h0]

@[simp]
theorem memLorentz_measure_zero : MemLorentz f p q (0 : Measure α) := by
  simp [memLorentz_iff]

theorem eLorentzNorm_congr_eNorm_ae {ε' : Type*} [TopologicalSpace ε'] [ENorm ε'] {g : α → ε'}
    (hf : AEStronglyMeasurable f μ) (hg : AEStronglyMeasurable g μ)
    (hfg : (‖f ·‖ₑ) =ᵐ[μ] (‖g ·‖ₑ)) :
    eLorentzNorm f p q μ = eLorentzNorm g p q μ := by
  by_cases hp : p = 0
  · simp [hp, hf, hg]
  · rw [eLorentzNorm_eq_eLpNorm_multHaar hp hf, eLorentzNorm_eq_eLpNorm_multHaar hp hg,
      μ.decreasingRearrangement_congr_ae hfg]

theorem eLorentzNorm_congr_ae (hfg : f =ᵐ[μ] g) :
    eLorentzNorm f p q μ = eLorentzNorm g p q μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · exact eLorentzNorm_congr_eNorm_ae hf (hf.congr hfg) (hfg.mono fun _ h ↦ congrArg (‖·‖ₑ) h)
  · have hg : ¬ AEStronglyMeasurable g μ := fun hg ↦ hf (hg.congr hfg.symm)
    rw [eLorentzNorm_of_not_aestronglyMeasurable hf, eLorentzNorm_of_not_aestronglyMeasurable hg]

theorem memLorentz_congr_ae (hfg : f =ᵐ[μ] g) :
    MemLorentz f p q μ ↔ MemLorentz g p q μ := by
  rw [memLorentz_iff, memLorentz_iff, eLorentzNorm_congr_ae hfg]

theorem MemLorentz.congr_ae (hf : MemLorentz f p q μ) (hfg : f =ᵐ[μ] g) :
    MemLorentz g p q μ :=
  (memLorentz_congr_ae hfg).1 hf

theorem eLorentzNorm_mono_eNorm_ae {ε' : Type*} [TopologicalSpace ε'] [ENorm ε'] {g : α → ε'}
    (hf : AEStronglyMeasurable f μ) (hfg : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    eLorentzNorm f p q μ ≤ eLorentzNorm g p q μ := by
  by_cases hg : AEStronglyMeasurable g μ
  · by_cases hp : p = 0
    · simp [hp, hf, hg]
    · rw [eLorentzNorm_eq_eLpNorm_multHaar hp hf, eLorentzNorm_eq_eLpNorm_multHaar hp hg]
      refine eLpNorm_mono_eNorm_ae
        (measurable_ofReal_rpow_mul_decreasingRearrangement μ _ _).aestronglyMeasurable ?_
      filter_upwards [ae_pos_multHaar] with t _
      simp only [eNorm_eq_self]
      gcongr
      exact μ.decreasingRearrangement_mono_ae hfg t
  · rw [eLorentzNorm_of_not_aestronglyMeasurable hg]
    exact le_top

theorem MemLorentz.mono_eNorm {ε' : Type*} [TopologicalSpace ε'] [ENorm ε'] {g : α → ε'}
    (hg : MemLorentz g p q μ) (hf : AEStronglyMeasurable f μ)
    (hfg : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    MemLorentz f p q μ :=
  (eLorentzNorm_mono_eNorm_ae hf hfg).trans_lt hg

end Basic

section ContinuousENorm

variable [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε}

@[simp]
theorem eLorentzNorm_eNorm (hf : AEStronglyMeasurable f μ) :
    eLorentzNorm (fun x ↦ ‖f x‖ₑ) p q μ = eLorentzNorm f p q μ :=
  eLorentzNorm_congr_eNorm_ae hf.eNorm.aestronglyMeasurable hf (.of_forall fun _ ↦ eNorm_eNorm _)

/-- **Diagonal identity `L^{p,p} = Lᵖ`.** For every `p ∈ [0, ∞]`, the Lorentz gauge `(p, p)`
coincides with the `Lᵖ` seminorm. -/
@[simp]
theorem eLorentzNorm_self (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm f p p μ = eLpNorm f p μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · rcases eq_or_ne p 0 with rfl | hp
    · simp [hf]
    · rw [eLorentzNorm_eq_eLpNorm_multHaar hp hf, eLpNorm_rpow_toReal_inv_mul_multHaar hp,
        μ.eLpNorm_decreasingRearrangement hf.eNorm p, eLpNorm_eNorm f hf]
  · rw [eLorentzNorm_of_not_aestronglyMeasurable hf, eLpNorm_of_not_aestronglyMeasurable hf]

@[simp]
theorem memLorentz_self_iff : MemLorentz f p p μ ↔ MemLp f p μ := by
  rw [memLorentz_iff, memLp_iff, eLorentzNorm_self]

end ContinuousENorm

section ESeminormedAddMonoid

variable [TopologicalSpace ε] [ESeminormedAddMonoid ε] {f g : α → ε}

@[to_fun (attr := simp) eLorentzNorm_fun_zero]
theorem eLorentzNorm_zero : eLorentzNorm (0 : α → ε) p q μ = 0 := by
  by_cases hp : p = 0
  · simp [hp, aestronglyMeasurable_zero]
  · rw [eLorentzNorm_eq_eLpNorm_multHaar hp aestronglyMeasurable_zero]
    simp only [Pi.zero_apply, eNorm_zero]
    have h0 : ∀ t, μ.decreasingRearrangement (fun _ : α ↦ (0 : ℝ≥0∞)) t = 0 := fun t ↦
      le_antisymm (μ.decreasingRearrangement_le_iff.2 (by simp)) bot_le
    simp [h0]

@[simp]
theorem MemLorentz.zero : MemLorentz (0 : α → ε) p q μ := by
  simp [memLorentz_iff]

@[simp]
theorem MemLorentz.zero' : MemLorentz (fun _ : α ↦ (0 : ε)) p q μ :=
  MemLorentz.zero

/-- For `p ≠ 0` and `q ≠ 0`, `eLorentzNorm f p q μ = 0` exactly when `f` is a.e. strongly
measurable and `‖f x‖ₑ = 0` almost everywhere. -/
theorem eLorentzNorm_eq_zero_iff (hp : p ≠ 0) (hq : q ≠ 0) :
    eLorentzNorm f p q μ = 0 ↔ AEStronglyMeasurable f μ ∧ (‖f ·‖ₑ) =ᵐ[μ] 0 := by
  constructor
  · intro h
    have hf : AEStronglyMeasurable f μ :=
      aestronglyMeasurable_of_eLorentzNorm_ne_top (h ▸ ENNReal.zero_ne_top)
    refine ⟨hf, ?_⟩
    rw [eLorentzNorm_eq_eLpNorm_multHaar hp hf, eLpNorm_eq_zero_iff hq,
      Filter.EventuallyEq, ae_multHaar] at h
    have h_ae : μ.decreasingRearrangement (‖f ·‖ₑ) =ᵐ[volume.restrict (Ioi 0)] 0 := by
      filter_upwards [ae_restrict_mem measurableSet_Ioi, h] with t (ht : 0 < t) ht0
      have hpos : ENNReal.ofReal (t ^ p.toReal⁻¹) ≠ 0 :=
        (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos ht _)).ne'
      exact (mul_eq_zero.1 ht0).resolve_left hpos
    have hess : essSup (‖f ·‖ₑ) μ = 0 := by
      rw [← μ.essSup_decreasingRearrangement, essSup_congr_ae h_ae]
      simp
    exact ENNReal.essSup_eq_zero_iff.1 hess
  · rintro ⟨hf, h0⟩
    rw [eLorentzNorm_congr_eNorm_ae (g := (0 : α → ε)) hf aestronglyMeasurable_zero
      (h0.trans (.of_forall fun _ ↦ by simp)), eLorentzNorm_zero]

theorem eLorentzNorm_indicator_le {s : Set α} (hs : NullMeasurableSet s μ) :
    eLorentzNorm (s.indicator f) p q μ ≤ eLorentzNorm f p q μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · refine eLorentzNorm_mono_eNorm_ae (hf.indicator₀ hs) (.of_forall fun x ↦ ?_)
    by_cases hx : x ∈ s <;> simp [hx]
  · rw [eLorentzNorm_of_not_aestronglyMeasurable hf]
    exact le_top

theorem MemLorentz.indicator₀ {s : Set α} (hs : NullMeasurableSet s μ)
    (hf : MemLorentz f p q μ) : MemLorentz (s.indicator f) p q μ :=
  (eLorentzNorm_indicator_le hs).trans_lt hf

theorem MemLorentz.indicator {s : Set α} (hs : MeasurableSet s)
    (hf : MemLorentz f p q μ) : MemLorentz (s.indicator f) p q μ :=
  hf.indicator₀ hs.nullMeasurableSet

/-- Pointwise rearrangement subadditivity with the power weight `t ^ r`: for `t ≥ 0`,
`t ^ r * (‖f + g‖ₑ)* t ≤ 2 ^ r * ((t/2) ^ r * (‖f‖ₑ)* (t/2) + (t/2) ^ r * (‖g‖ₑ)* (t/2))`. -/
private theorem rpow_mul_decreasingRearrangement_add_le (f g : α → ε) (r : ℝ) {t : ℝ}
    (ht : 0 ≤ t) (μ : Measure α) :
    ENNReal.ofReal (t ^ r) * μ.decreasingRearrangement (‖(f + g) ·‖ₑ) t ≤
      ENNReal.ofReal (2 ^ r) *
        (ENNReal.ofReal ((2⁻¹ * t) ^ r) * μ.decreasingRearrangement (‖f ·‖ₑ) (2⁻¹ * t) +
          ENNReal.ofReal ((2⁻¹ * t) ^ r) * μ.decreasingRearrangement (‖g ·‖ₑ) (2⁻¹ * t)) := by
  have ht2 : 0 ≤ (2 : ℝ)⁻¹ * t := by positivity
  have hsplit : t = 2⁻¹ * t + 2⁻¹ * t := by ring
  have hrear : μ.decreasingRearrangement (‖(f + g) ·‖ₑ) t ≤
      μ.decreasingRearrangement (‖f ·‖ₑ) (2⁻¹ * t) +
        μ.decreasingRearrangement (‖g ·‖ₑ) (2⁻¹ * t) := by
    calc μ.decreasingRearrangement (‖(f + g) ·‖ₑ) t
        ≤ μ.decreasingRearrangement ((‖f ·‖ₑ) + (‖g ·‖ₑ)) t :=
          μ.decreasingRearrangement_mono (fun y ↦ eNorm_add_le (f y) (g y)) t
      _ ≤ _ := by
          conv_lhs => rw [hsplit]
          exact μ.decreasingRearrangement_add_le _ _ ht2 ht2
  have hrpow : ENNReal.ofReal (t ^ r) =
      ENNReal.ofReal (2 ^ r) * ENNReal.ofReal ((2⁻¹ * t) ^ r) := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow (by norm_num) ht2]
    congr 2
    ring
  calc ENNReal.ofReal (t ^ r) * μ.decreasingRearrangement (‖(f + g) ·‖ₑ) t
      ≤ (ENNReal.ofReal (2 ^ r) * ENNReal.ofReal ((2⁻¹ * t) ^ r)) *
          (μ.decreasingRearrangement (‖f ·‖ₑ) (2⁻¹ * t) +
            μ.decreasingRearrangement (‖g ·‖ₑ) (2⁻¹ * t)) := by
        rw [← hrpow]
        gcongr
    _ = _ := by ring

section QuasiTriangle

variable [ContinuousAdd ε]

/-- **Quasi-triangle inequality for Lorentz gauges**, valid for all `p, q ∈ [0, ∞]`. -/
theorem eLorentzNorm_add_le' (f g : α → ε) (p q : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm (f + g) p q μ ≤
      ENNReal.ofReal (2 ^ p.toReal⁻¹) * ENNReal.LpAddConst q *
        (eLorentzNorm f p q μ + eLorentzNorm g p q μ) := by
  have hC0 : ENNReal.ofReal (2 ^ p.toReal⁻¹) * ENNReal.LpAddConst q ≠ 0 :=
    mul_ne_zero (ENNReal.ofReal_pos.2 (by positivity)).ne' (ENNReal.LpAddConst_ne_zero q)
  by_cases hf : AEStronglyMeasurable f μ; swap
  · simp [eLorentzNorm_of_not_aestronglyMeasurable hf, ENNReal.mul_top hC0]
  by_cases hg : AEStronglyMeasurable g μ; swap
  · simp [eLorentzNorm_of_not_aestronglyMeasurable hg, ENNReal.mul_top hC0]
  have hfg : AEStronglyMeasurable (f + g) μ := hf.add hg
  rcases eq_or_ne p 0 with rfl | hp
  · simp [hf, hg, hfg]
  rw [eLorentzNorm_eq_eLpNorm_multHaar hp hfg, eLorentzNorm_eq_eLpNorm_multHaar hp hf,
    eLorentzNorm_eq_eLpNorm_multHaar hp hg]
  set r := p.toReal⁻¹
  set Φf : ℝ → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (t ^ r) * μ.decreasingRearrangement (‖f ·‖ₑ) t
  set Φg : ℝ → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (t ^ r) * μ.decreasingRearrangement (‖g ·‖ₑ) t
  have hΦf : Measurable Φf := measurable_ofReal_rpow_mul_decreasingRearrangement μ r _
  have hΦg : Measurable Φg := measurable_ofReal_rpow_mul_decreasingRearrangement μ r _
  have hmp : MeasurePreserving ((2 : ℝ)⁻¹ * ·) multHaar multHaar :=
    ⟨measurable_const_mul _, map_multHaar_mul_left (by norm_num)⟩
  have hdil_f : eLpNorm (fun t ↦ Φf (2⁻¹ * t)) q multHaar = eLpNorm Φf q multHaar :=
    eLpNorm_comp_measurePreserving hΦf.aestronglyMeasurable hmp
  have hdil_g : eLpNorm (fun t ↦ Φg (2⁻¹ * t)) q multHaar = eLpNorm Φg q multHaar :=
    eLpNorm_comp_measurePreserving hΦg.aestronglyMeasurable hmp
  calc eLpNorm (fun t ↦ ENNReal.ofReal (t ^ r) *
          μ.decreasingRearrangement (‖(f + g) ·‖ₑ) t) q multHaar
      ≤ eLpNorm (fun t ↦ ENNReal.ofReal (2 ^ r) * (Φf (2⁻¹ * t) + Φg (2⁻¹ * t))) q multHaar := by
        refine eLpNorm_mono_eNorm_ae
          (measurable_ofReal_rpow_mul_decreasingRearrangement μ r _).aestronglyMeasurable ?_
        filter_upwards [ae_pos_multHaar] with t ht
        simpa only [eNorm_eq_self] using
          rpow_mul_decreasingRearrangement_add_le f g r ht.le μ
    _ = ENNReal.ofReal (2 ^ r) *
          eLpNorm ((fun t ↦ Φf (2⁻¹ * t)) + fun t ↦ Φg (2⁻¹ * t)) q multHaar :=
        eLpNorm_const_mul_ennreal
          (((hΦf.comp (measurable_const_mul _)).add
            (hΦg.comp (measurable_const_mul _))).aestronglyMeasurable)
    _ ≤ ENNReal.ofReal (2 ^ r) *
          (ENNReal.LpAddConst q * (eLpNorm (fun t ↦ Φf (2⁻¹ * t)) q multHaar +
            eLpNorm (fun t ↦ Φg (2⁻¹ * t)) q multHaar)) := by
        gcongr
        exact eLpNorm_add_le' q
    _ = ENNReal.ofReal (2 ^ r) * ENNReal.LpAddConst q *
          (eLpNorm Φf q multHaar + eLpNorm Φg q multHaar) := by
        rw [hdil_f, hdil_g, mul_assoc]

/-- For `1 ≤ q ≤ ∞`, the Lorentz gauge is subadditive with constant `2 ^ (1 / p)`. -/
theorem eLorentzNorm_add_le (hq : 1 ≤ q) (f g : α → ε) (p : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm (f + g) p q μ ≤
      ENNReal.ofReal (2 ^ p.toReal⁻¹) * (eLorentzNorm f p q μ + eLorentzNorm g p q μ) := by
  simpa [ENNReal.LpAddConst_of_one_le hq] using eLorentzNorm_add_le' f g p q μ

theorem MemLorentz.add (hf : MemLorentz f p q μ) (hg : MemLorentz g p q μ) :
    MemLorentz (f + g) p q μ :=
  (eLorentzNorm_add_le' f g p q μ).trans_lt <|
    ENNReal.mul_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.LpAddConst_lt_top q))
      (ENNReal.add_lt_top.2 ⟨hf, hg⟩)

end QuasiTriangle

end ESeminormedAddMonoid

section NormedAddCommGroup

variable {E : Type*} [NormedAddCommGroup E] {f g : α → E}

@[simp]
theorem eLorentzNorm_neg (f : α → E) (p q : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm (-f) p q μ = eLorentzNorm f p q μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · exact eLorentzNorm_congr_eNorm_ae hf.neg hf (.of_forall fun x ↦ by simp)
  · have hnf : ¬ AEStronglyMeasurable (-f) μ := fun h ↦ hf (neg_neg f ▸ h.neg)
    rw [eLorentzNorm_of_not_aestronglyMeasurable hnf, eLorentzNorm_of_not_aestronglyMeasurable hf]

theorem eLorentzNorm_sub_comm (f g : α → E) (p q : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm (f - g) p q μ = eLorentzNorm (g - f) p q μ := by
  rw [← eLorentzNorm_neg (f - g), neg_sub]

theorem MemLorentz.neg (hf : MemLorentz f p q μ) : MemLorentz (-f) p q μ := by
  simpa [memLorentz_iff] using hf

@[simp]
theorem memLorentz_neg_iff : MemLorentz (-f) p q μ ↔ MemLorentz f p q μ :=
  ⟨fun h ↦ neg_neg f ▸ h.neg, MemLorentz.neg⟩

theorem MemLorentz.sub (hf : MemLorentz f p q μ) (hg : MemLorentz g p q μ) :
    MemLorentz (f - g) p q μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg

theorem eLorentzNorm_const_mul_ennreal {h : α → ℝ≥0∞} {c : ℝ≥0∞}
    (hh : AEStronglyMeasurable h μ) :
    eLorentzNorm (fun x ↦ c * h x) p q μ = c * eLorentzNorm h p q μ := by
  have hch : AEStronglyMeasurable (fun x ↦ c * h x) μ :=
    (hh.aemeasurable.const_mul c).aestronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp
  · simp [hh, hch]
  rw [eLorentzNorm_eq_eLpNorm_multHaar hp hch, eLorentzNorm_eq_eLpNorm_multHaar hp hh]
  simp only [eNorm_eq_self, μ.decreasingRearrangement_const_mul]
  have hcomm : (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) *
        (c * μ.decreasingRearrangement h t)) =
      fun t : ℝ ↦ c * (ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement h t) := by
    ext t
    ring
  rw [hcomm, eLpNorm_const_mul_ennreal
    (measurable_ofReal_rpow_mul_decreasingRearrangement μ _ _).aestronglyMeasurable]

section SMul

variable {𝕜 : Type*}

theorem eLorentzNorm_const_smul_le [NormedRing 𝕜] [MulActionWithZero 𝕜 E] [IsBoundedSMul 𝕜 E]
    (c : 𝕜) (f : α → E) (p q : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm (c • f) p q μ ≤ ‖c‖ₑ * eLorentzNorm f p q μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · calc eLorentzNorm (c • f) p q μ
        ≤ eLorentzNorm (fun x ↦ ‖c‖ₑ * ‖f x‖ₑ) p q μ :=
          eLorentzNorm_mono_eNorm_ae (hf.const_smul c) (.of_forall fun x ↦ by
            simp only [Pi.smul_apply, eNorm_eq_self]
            exact eNorm_smul_le)
      _ = ‖c‖ₑ * eLorentzNorm f p q μ := by
          rw [eLorentzNorm_const_mul_ennreal hf.eNorm.aestronglyMeasurable, eLorentzNorm_eNorm hf]
  · rcases eq_or_ne c 0 with rfl | hc
    · simp
    · rw [eLorentzNorm_of_not_aestronglyMeasurable hf, ENNReal.mul_top (by simpa using hc)]
      exact le_top

theorem MemLorentz.const_smul [NormedRing 𝕜] [MulActionWithZero 𝕜 E] [IsBoundedSMul 𝕜 E]
    (hf : MemLorentz f p q μ) (c : 𝕜) : MemLorentz (c • f) p q μ :=
  (eLorentzNorm_const_smul_le c f p q μ).trans_lt (ENNReal.mul_lt_top eNorm_lt_top hf)

theorem eLorentzNorm_const_smul [NormedDivisionRing 𝕜] [Module 𝕜 E] [NormSMulClass 𝕜 E]
    (c : 𝕜) (f : α → E) (p q : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm (c • f) p q μ = ‖c‖ₑ * eLorentzNorm f p q μ := by
  obtain rfl | hc := eq_or_ne c 0
  · simp
  refine le_antisymm (eLorentzNorm_const_smul_le c f p q μ) (ENNReal.mul_le_of_le_div' ?_)
  simpa [eNorm_inv, hc, ENNReal.div_eq_inv_mul] using
    eLorentzNorm_const_smul_le c⁻¹ (c • f) p q μ

/-- **Bounded multiplier law for Lorentz gauges:** multiplying by an `L^∞` scalar function `φ`
multiplies the `(p, q)` Lorentz gauge by at most `‖φ‖_{L^∞}`. -/
theorem eLorentzNorm_smul_le_eLpNorm_top_mul_eLorentzNorm [NormedRing 𝕜]
    [MulActionWithZero 𝕜 E] [IsBoundedSMul 𝕜 E] {φ : α → 𝕜}
    (hφ : AEStronglyMeasurable φ μ) (f : α → E) (p q : ℝ≥0∞) :
    eLorentzNorm (φ • f) p q μ ≤ eLpNorm φ ∞ μ * eLorentzNorm f p q μ := by
  by_cases hf : AEStronglyMeasurable f μ
  · calc eLorentzNorm (φ • f) p q μ
        ≤ eLorentzNorm (fun x ↦ eLpNorm φ ∞ μ * ‖f x‖ₑ) p q μ := by
          refine eLorentzNorm_mono_eNorm_ae (hφ.smul hf) ?_
          filter_upwards [ae_le_eLpNormEssSup (f := φ) (μ := μ)] with x hx
          simp only [eNorm_eq_self]
          refine eNorm_smul_le.trans ?_
          rw [eLpNorm_exponent_top hφ]
          gcongr
      _ = eLpNorm φ ∞ μ * eLorentzNorm f p q μ := by
          rw [eLorentzNorm_const_mul_ennreal hf.eNorm.aestronglyMeasurable, eLorentzNorm_eNorm hf]
  · rcases eq_or_ne (eLpNorm φ ∞ μ) 0 with hφ0 | hφ0
    · have hφ_ae : φ =ᵐ[μ] 0 := (eLpNorm_eq_zero_iff ENNReal.top_ne_zero).1 hφ0
      have hsmul : φ • f =ᵐ[μ] 0 := hφ_ae.mono fun x hx ↦ by simp [hx]
      rw [eLorentzNorm_congr_ae hsmul, eLorentzNorm_zero, hφ0, zero_mul]
    · rw [eLorentzNorm_of_not_aestronglyMeasurable hf, ENNReal.mul_top hφ0]
      exact le_top

theorem MemLorentz.smul_of_memLp_top [NormedRing 𝕜] [MulActionWithZero 𝕜 E] [IsBoundedSMul 𝕜 E]
    {φ : α → 𝕜} (hφ : MemLp φ ∞ μ) (hf : MemLorentz f p q μ) :
    MemLorentz (φ • f) p q μ :=
  (eLorentzNorm_smul_le_eLpNorm_top_mul_eLorentzNorm hφ.aestronglyMeasurable f p q).trans_lt
    (ENNReal.mul_lt_top hφ hf)

end SMul

end NormedAddCommGroup

end TauCeti
