/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import TauCeti.MeasureTheory.Function.DecreasingRearrangement
public import TauCeti.MeasureTheory.Measure.Haar.MultHaar
import Mathlib.MeasureTheory.Function.LpSeminorm.SMul
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-!
# Lorentz gauges and weak `Lᵖ`

For a measure `μ` on `α`, a function `f : α → E` valued in a type with an extended norm `‖·‖ₑ`,
and exponents `p, q ∈ [0, ∞]`, the **Lorentz gauge** is

`‖f‖_{L^{p, q}(μ)} = ‖t ↦ t ^ (1 / p) ‖f‖*(t)‖_{L^q(dt / t)}`

(`TauCeti.eLorentzNorm`), with the convention `‖f‖_{L^{0, q}(μ)} = 0`, where `‖f‖*` is the
decreasing rearrangement `MeasureTheory.Measure.decreasingRearrangement` and `dt / t` is
`TauCeti.multHaar`.

The gauge depends only on the almost-everywhere class of `‖f ·‖ₑ` and needs no measurability
hypothesis on `f`. It is positively homogeneous (`TauCeti.eLorentzNorm_const_smul`), vanishes
exactly for almost-everywhere zero functions when `p ≠ 0` and `q ≠ 0`
(`TauCeti.eLorentzNorm_eq_zero_iff`), and for `1 ≤ q` satisfies the quasi-triangle inequality
with constant `2 ^ (1 / p)` (`TauCeti.eLorentzNorm_add_le`). On the diagonal `q = p`, for an
a.e. strongly measurable function it coincides with the Lebesgue seminorm `eLpNorm f p μ` for
every `p ∈ [0, ∞]` (`TauCeti.eLorentzNorm_self`). At `q = ∞` and `0 < p < ∞` it equals both
`sup_{t > 0} t ^ (1 / p) ‖f‖*(t)` (`TauCeti.eLorentzNorm_exponent_top_right`) and the weak-`Lᵖ`
distribution gauge `sup_c c μ {‖f‖ > c} ^ (1 / p)`
(`TauCeti.eLorentzNorm_exponent_top_right_eq_iSup_measure`).

For indicators, `‖c 1_A‖_{L^{p, q}} = (p / q) ^ (1 / q) ‖c‖ μ(A) ^ (1 / p)` when `0 < p < ∞` and
`0 < q ≤ ∞` (`TauCeti.eLorentzNorm_indicator`). The Lorentz gauges decrease with the secondary
exponent: for `0 < p < ∞` and `0 < q₀ ≤ q₁ ≤ ∞`,

`‖f‖_{L^{p, q₁}} ≤ (q₀ / p) ^ (1 / q₀ - 1 / q₁) ‖f‖_{L^{p, q₀}}`

(`TauCeti.eLorentzNorm_le_mul_eLorentzNorm`), with the sharp constant attained on indicators.
On `(0, ∞)` with Lebesgue measure, `t ↦ t ^ (-1 / p)` has weak-`Lᵖ` gauge `1`
(`TauCeti.eLorentzNorm_rpow_neg_inv_exponent_top`) and infinite `Lᵖ` seminorm
(`TauCeti.eLpNorm_rpow_neg_inv_eq_top`), witnessing the strict inclusion `Lᵖ ⊊ L^{p, ∞}`.

## Main declarations

* `TauCeti.eLorentzNorm`: the Lorentz gauge `‖f‖_{L^{p, q}(μ)}` in `[0, ∞]`.
* `TauCeti.eLorentzNorm_const_smul`, `TauCeti.eLorentzNorm_add_le`,
  `TauCeti.eLorentzNorm_eq_zero_iff`: homogeneity, quasi-triangle inequality, and definiteness.
* `TauCeti.eLorentzNorm_self`: `eLorentzNorm f p p μ = eLpNorm f p μ` for a.e. strongly
  measurable `f` and every `p ∈ [0, ∞]`.
* `TauCeti.eLorentzNorm_exponent_top_right`,
  `TauCeti.eLorentzNorm_exponent_top_right_eq_iSup_measure`: weak-`Lᵖ` characterizations at
  `q = ∞`.
* `TauCeti.eLorentzNorm_indicator`: exact formula on indicator functions.
* `TauCeti.eLorentzNorm_le_mul_eLorentzNorm`: sharp secondary-exponent embedding
  `L^{p, q₀} ↪ L^{p, q₁}` for `0 < q₀ ≤ q₁ ≤ ∞`.
* `TauCeti.eLorentzNorm_rpow_neg_inv_exponent_top`, `TauCeti.eLpNorm_rpow_neg_inv_eq_top`:
  the power-function witness `t ↦ t ^ (-1 / p)` for `Lᵖ ⊊ L^{p, ∞}`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §1.3.
* E. M. Stein and G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*,
  Princeton University Press, 1971, Chapter V, §3.
* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Springer, 2014, §1.4 (Proposition 1.4.10).
-/

public noncomputable section

open Filter MeasureTheory Set Topology
open scoped ENNReal

namespace TauCeti

/-! ### Definition and basic properties of the Lorentz gauge -/

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

section Basic

variable {E : Type*} [ENorm E]

/-- The **Lorentz gauge** `‖f‖_{L^{p, q}(μ)} = ‖t ↦ t ^ (1 / p) ‖f‖*(t)‖_{L^q(dt / t)}` in
`[0, ∞]`, where `‖f‖*` is the decreasing rearrangement of `‖f ·‖ₑ`. By convention it is `0` when
`p = 0`. -/
def eLorentzNorm (f : α → E) (p q : ℝ≥0∞) (μ : Measure α) : ℝ≥0∞ :=
  if p = 0 then 0 else
    eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t)
      q multHaar

theorem eLorentzNorm_def (f : α → E) (p q : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm f p q μ = if p = 0 then 0 else
      eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t)
        q multHaar := (rfl)

/-- The integrand `t ↦ t ^ (1 / p) ‖f‖*(t)` of `eLorentzNorm` is always measurable. -/
private theorem measurable_eLorentzIntegrand (f : α → E) (p : ℝ≥0∞) (μ : Measure α) :
    Measurable (fun t : ℝ ↦
      ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t) :=
  ((by fun_prop : Measurable fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹))).mul
    (μ.measurable_decreasingRearrangement _)

@[simp]
theorem eLorentzNorm_exponent_zero_left (f : α → E) (q : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm f 0 q μ = 0 := by
  simp [eLorentzNorm_def]

@[simp]
theorem eLorentzNorm_exponent_zero_right (f : α → E) (p : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm f p 0 μ = 0 := by
  rw [eLorentzNorm_def]
  split_ifs
  · rfl
  · exact eLpNorm_exponent_zero (measurable_eLorentzIntegrand f p μ).aestronglyMeasurable

@[simp]
theorem eLorentzNorm_eNorm (f : α → E) (p q : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm (fun x ↦ ‖f x‖ₑ) p q μ = eLorentzNorm f p q μ := by
  simp [eLorentzNorm_def]

theorem eLorentzNorm_mono_eNorm_ae {E' : Type*} [ENorm E'] {f : α → E} {g : α → E'}
    {p q : ℝ≥0∞} (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    eLorentzNorm f p q μ ≤ eLorentzNorm g p q μ := by
  rw [eLorentzNorm_def, eLorentzNorm_def]
  split_ifs
  · exact le_rfl
  · refine eLpNorm_mono_eNorm_ae (measurable_eLorentzIntegrand f p μ).aestronglyMeasurable
      (ae_of_all _ fun t ↦ ?_)
    simp only [eNorm_eq_self]
    gcongr
    exact μ.decreasingRearrangement_mono_ae h t

theorem eLorentzNorm_congr_eNorm_ae {E' : Type*} [ENorm E'] {f : α → E} {g : α → E'}
    {p q : ℝ≥0∞} (h : ∀ᵐ x ∂μ, ‖f x‖ₑ = ‖g x‖ₑ) :
    eLorentzNorm f p q μ = eLorentzNorm g p q μ :=
  (eLorentzNorm_mono_eNorm_ae (h.mono fun _ hx ↦ hx.le)).antisymm
    (eLorentzNorm_mono_eNorm_ae (h.mono fun _ hx ↦ hx.ge))

theorem eLorentzNorm_congr_ae {f g : α → E} {p q : ℝ≥0∞} (h : f =ᵐ[μ] g) :
    eLorentzNorm f p q μ = eLorentzNorm g p q μ :=
  eLorentzNorm_congr_eNorm_ae (h.mono fun _ hx ↦ by rw [hx])

/-- The Lorentz gauge is positively homogeneous: `‖c • f‖_{L^{p, q}} = ‖c‖ₑ * ‖f‖_{L^{p, q}}`. -/
theorem eLorentzNorm_const_smul {𝕜 : Type*} [ENorm 𝕜] [SMul 𝕜 E] [ENormSMulClass 𝕜 E]
    (c : 𝕜) (f : α → E) (p q : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm (c • f) p q μ = ‖c‖ₑ * eLorentzNorm f p q μ := by
  rw [eLorentzNorm_def, eLorentzNorm_def]
  split_ifs
  · simp
  · have heq : (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) *
          μ.decreasingRearrangement (fun y ↦ ‖(c • f) y‖ₑ) t) =
        fun t ↦ ‖c‖ₑ * (ENNReal.ofReal (t ^ p.toReal⁻¹) *
          μ.decreasingRearrangement (‖f ·‖ₑ) t) := by
      ext t
      simp only [Pi.smul_apply, eNorm_smul, μ.decreasingRearrangement_const_mul]
      ring
    rw [heq, eLpNorm_const_mul_ennreal (measurable_eLorentzIntegrand f p μ).aestronglyMeasurable]

end Basic

@[simp]
theorem eLorentzNorm_zero {E : Type*} [TopologicalSpace E] [ESeminormedAddMonoid E]
    (p q : ℝ≥0∞) (μ : Measure α) : eLorentzNorm (0 : α → E) p q μ = 0 := by
  rw [eLorentzNorm_def]
  split_ifs
  · rfl
  · have hzero : μ.decreasingRearrangement (fun _ : α ↦ (0 : ℝ≥0∞)) = 0 := by
      ext s
      refine le_antisymm (μ.decreasingRearrangement_le_iff.2 ?_) zero_le
      simp
    simp [hzero]

@[simp]
theorem eLorentzNorm_neg {F : Type*} [SeminormedAddGroup F] (f : α → F) (p q : ℝ≥0∞)
    (μ : Measure α) : eLorentzNorm (-f) p q μ = eLorentzNorm f p q μ :=
  eLorentzNorm_congr_eNorm_ae (ae_of_all _ fun x ↦ by simp)

/-- For `p ≠ 0` and `q ≠ 0`, the Lorentz gauge vanishes exactly for almost-everywhere zero
functions. -/
theorem eLorentzNorm_eq_zero_iff {E : Type*} [TopologicalSpace E] [ENormedAddMonoid E]
    {f : α → E} {p q : ℝ≥0∞} (hp : p ≠ 0) (hq : q ≠ 0) :
    eLorentzNorm f p q μ = 0 ↔ f =ᵐ[μ] 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ (eLorentzNorm_congr_ae h).trans (eLorentzNorm_zero p q μ)⟩
  rw [eLorentzNorm_def] at h
  simp only [hp, ↓reduceIte, eLpNorm_eq_zero_iff hq] at h
  have hzero : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), μ.decreasingRearrangement (‖f ·‖ₑ) t = 0 := by
    rw [← ae_multHaar_eq_ae_volume_Ioi]
    filter_upwards [h, ae_pos_multHaar] with t ht ht0
    have hpow : ENNReal.ofReal (t ^ p.toReal⁻¹) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos ht0 _)).ne'
    simpa [hpow] using ht
  have hess : essSup (‖f ·‖ₑ) μ = 0 := by
    rw [← μ.essSup_decreasingRearrangement]
    exact le_antisymm (essSup_le_of_ae_le 0 (hzero.mono fun _ ht ↦ ht.le)) zero_le
  filter_upwards [ENNReal.ae_le_essSup (μ := μ) (‖f ·‖ₑ)] with x hx
  rw [hess, nonpos_iff_eq_zero, eNorm_eq_zero] at hx
  exact hx

/-- **Quasi-triangle inequality for Lorentz gauges.** For `1 ≤ q ≤ ∞` and every `p ∈ [0, ∞]`,
`‖f + g‖_{L^{p, q}} ≤ 2 ^ (1 / p) (‖f‖_{L^{p, q}} + ‖g‖_{L^{p, q}})`. -/
theorem eLorentzNorm_add_le {E : Type*} [TopologicalSpace E] [ESeminormedAddMonoid E]
    (f g : α → E) {p q : ℝ≥0∞} (hq : 1 ≤ q) (μ : Measure α) :
    eLorentzNorm (f + g) p q μ ≤
      ENNReal.ofReal (2 ^ p.toReal⁻¹) * (eLorentzNorm f p q μ + eLorentzNorm g p q μ) := by
  rw [eLorentzNorm_def, eLorentzNorm_def, eLorentzNorm_def]
  split_ifs
  · simp
  set F : ℝ → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t
  set G : ℝ → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖g ·‖ₑ) t
  have hmp : MeasurePreserving ((2 : ℝ)⁻¹ * ·) multHaar multHaar :=
    ⟨measurable_const_mul _, map_multHaar_mul_left (by positivity)⟩
  have hF : AEStronglyMeasurable F multHaar :=
    (measurable_eLorentzIntegrand f p μ).aestronglyMeasurable
  have hG : AEStronglyMeasurable G multHaar :=
    (measurable_eLorentzIntegrand g p μ).aestronglyMeasurable
  have hFG : AEStronglyMeasurable (fun t ↦ F (2⁻¹ * t) + G (2⁻¹ * t)) multHaar :=
    ((hF.comp_measurePreserving hmp).aemeasurable.add
      (hG.comp_measurePreserving hmp).aemeasurable).aestronglyMeasurable
  calc eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) *
            μ.decreasingRearrangement (‖(f + g) ·‖ₑ) t) q multHaar
      ≤ eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (2 ^ p.toReal⁻¹) * (F (2⁻¹ * t) + G (2⁻¹ * t)))
          q multHaar := by
          refine eLpNorm_mono_eNorm_ae
            (measurable_eLorentzIntegrand (f + g) p μ).aestronglyMeasurable ?_
          filter_upwards [ae_pos_multHaar] with t ht
          simp only [eNorm_eq_self, F, G]
          have hpow : ENNReal.ofReal (t ^ p.toReal⁻¹) =
              ENNReal.ofReal (2 ^ p.toReal⁻¹) * ENNReal.ofReal ((2⁻¹ * t) ^ p.toReal⁻¹) := by
            rw [← ENNReal.ofReal_mul (Real.rpow_nonneg zero_le_two _),
              ← Real.mul_rpow zero_le_two (by positivity), ← mul_assoc,
              mul_inv_cancel₀ two_ne_zero, one_mul]
          have hadd : μ.decreasingRearrangement (‖(f + g) ·‖ₑ) t ≤
              μ.decreasingRearrangement (‖f ·‖ₑ) (2⁻¹ * t) +
                μ.decreasingRearrangement (‖g ·‖ₑ) (2⁻¹ * t) := by
            have hhalf : 2⁻¹ * t + 2⁻¹ * t = t := by ring
            calc μ.decreasingRearrangement (‖(f + g) ·‖ₑ) t
                ≤ μ.decreasingRearrangement ((‖f ·‖ₑ) + (‖g ·‖ₑ)) (2⁻¹ * t + 2⁻¹ * t) := by
                    rw [hhalf]
                    exact μ.decreasingRearrangement_mono (fun y ↦ eNorm_add_le (f y) (g y)) t
              _ ≤ _ := μ.decreasingRearrangement_add_le _ _ (by positivity) (by positivity)
          rw [hpow, mul_assoc, ← mul_add]
          gcongr
    _ = ENNReal.ofReal (2 ^ p.toReal⁻¹) *
          eLpNorm (fun t ↦ F (2⁻¹ * t) + G (2⁻¹ * t)) q multHaar :=
          eLpNorm_const_mul_ennreal hFG
    _ ≤ ENNReal.ofReal (2 ^ p.toReal⁻¹) *
          (eLpNorm (F ∘ ((2 : ℝ)⁻¹ * ·)) q multHaar +
            eLpNorm (G ∘ ((2 : ℝ)⁻¹ * ·)) q multHaar) := by
          gcongr
          exact eLpNorm_add_le hq
    _ = ENNReal.ofReal (2 ^ p.toReal⁻¹) * (eLpNorm F q multHaar + eLpNorm G q multHaar) := by
          rw [eLpNorm_comp_measurePreserving hF hmp, eLpNorm_comp_measurePreserving hG hmp]

/-! ### Diagonal identity `L^{p, p} = Lᵖ` -/

/-- **Diagonal Lorentz identity.** For an a.e. strongly measurable function `f` and every
`p ∈ [0, ∞]`, the Lorentz gauge `‖f‖_{L^{p, p}}` equals the Lebesgue seminorm `‖f‖_{Lᵖ}`. -/
theorem eLorentzNorm_self {E : Type*} [TopologicalSpace E] [ContinuousENorm E] {f : α → E}
    (hf : AEStronglyMeasurable f μ) (p : ℝ≥0∞) :
    eLorentzNorm f p p μ = eLpNorm f p μ := by
  rcases eq_or_ne p 0 with rfl | hp0
  · rw [eLorentzNorm_exponent_zero_left, eLpNorm_exponent_zero hf]
  rw [eLorentzNorm_def]
  simp only [hp0, ↓reduceIte, ← eLpNorm_volume_Ioi_eq_eLpNorm_multHaar hp0,
    μ.eLpNorm_decreasingRearrangement hf.eNorm, eLpNorm_eNorm f hf]

/-! ### Weak `Lᵖ` (`q = ∞`) -/

section WeakLp

variable {E : Type*} [ENorm E]

/-- For `p ≠ 0`, the `q = ∞` Lorentz gauge is the pointwise supremum
`sup_{t > 0} t ^ (1 / p) ‖f‖*(t)`. The essential supremum agrees with the pointwise supremum
because `t ↦ t ^ (1 / p) ‖f‖*(t)` is right continuous on `(0, ∞)`. -/
theorem eLorentzNorm_exponent_top_right (f : α → E) {p : ℝ≥0∞} (hp0 : p ≠ 0) (μ : Measure α) :
    eLorentzNorm f p ∞ μ =
      ⨆ (t : ℝ) (_ : 0 < t),
        ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t := by
  set h : ℝ → ℝ≥0∞ := fun t ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t
  rw [eLorentzNorm_def]
  simp only [hp0, ↓reduceIte,
    eLpNorm_exponent_top (measurable_eLorentzIntegrand f p μ).aestronglyMeasurable,
    eLpNormEssSup_eq_essSup_eNorm, eNorm_eq_self]
  refine le_antisymm ?_ (iSup₂_le fun t₀ ht₀ ↦ ?_)
  · exact essSup_le_of_ae_le _ (ae_pos_multHaar.mono fun t ht ↦ le_iSup₂_of_le t ht le_rfl)
  · refine le_of_forall_lt fun c hc ↦ ?_
    have ha0 : ENNReal.ofReal (t₀ ^ p.toReal⁻¹) ≠ 0 :=
      (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos ht₀ _)).ne'
    have hcont_pow : ContinuousWithinAt (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹))
        (Ici t₀) t₀ :=
      (ENNReal.continuous_ofReal.continuousAt.comp
        (Real.continuousAt_rpow_const t₀ _ (Or.inl ht₀.ne'))).continuousWithinAt
    have hcont : ContinuousWithinAt h (Ici t₀) t₀ :=
      ENNReal.Tendsto.mul hcont_pow (Or.inl ha0)
        (μ.continuousWithinAt_decreasingRearrangement _ t₀) (Or.inr ENNReal.ofReal_ne_top)
    have hev : {t | c < h t} ∈ 𝓝[≥] t₀ := hcont.eventually (lt_mem_nhds hc)
    obtain ⟨δ, hδ, hsub⟩ := Metric.mem_nhdsWithin_iff.1 hev
    have hmeas_pos : multHaar (Ico t₀ (t₀ + δ)) ≠ 0 := by
      rw [multHaar_Ico ht₀ (by linarith)]
      exact (ENNReal.ofReal_pos.2 (sub_pos.2 (Real.log_lt_log ht₀ (by linarith)))).ne'
    by_contra! hlt
    have hnull : multHaar {t | c < h t} = 0 :=
      measure_mono_null (fun t (ht : c < h t) ↦ hlt.trans_lt ht) (meas_essSup_lt (f := h))
    refine hmeas_pos (measure_mono_null (fun t ht ↦ hsub ⟨?_, ht.1⟩) hnull)
    rw [Metric.mem_ball, Real.dist_eq, abs_of_nonneg (sub_nonneg.2 ht.1)]
    linarith [ht.2]

/-- **Weak-`Lᵖ` distribution formula.** For `0 < p < ∞`, the Lorentz gauge `‖f‖_{L^{p, ∞}}` equals
the weak-`Lᵖ` distribution gauge `sup_c c * μ {‖f‖ > c} ^ (1 / p)`. -/
theorem eLorentzNorm_exponent_top_right_eq_iSup_measure (f : α → E) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (μ : Measure α) :
    eLorentzNorm f p ∞ μ = ⨆ c : ℝ≥0∞, c * μ {y | c < ‖f y‖ₑ} ^ p.toReal⁻¹ := by
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hr_pos : 0 < p.toReal⁻¹ := inv_pos.2 hp_pos
  rw [eLorentzNorm_exponent_top_right f hp0 μ]
  refine le_antisymm (iSup₂_le fun t ht ↦ ?_) (iSup_le fun c ↦ le_of_forall_lt fun a ha ↦ ?_)
  · rw [μ.decreasingRearrangement_def, ENNReal.mul_iSup]
    refine iSup_le fun c ↦ ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun hc ↦ ?_
    rw [mul_comm, ← ENNReal.ofReal_rpow_of_pos ht]
    exact le_iSup_of_le c (mul_le_mul_right (ENNReal.rpow_le_rpow hc.le hr_pos.le) c)
  · obtain ⟨a', haa', ha'⟩ := exists_between ha
    have ha0 : a' ≠ 0 := (bot_le.trans_lt haa').ne'
    have hc0 : c ≠ 0 := by
      rintro rfl
      simp at ha'
    have hctop : c ≠ ∞ := by
      rintro rfl
      simp [hr_pos] at ha'
    have hdiv_lt : a' / c < μ {y | c < ‖f y‖ₑ} ^ p.toReal⁻¹ :=
      (ENNReal.div_lt_iff (Or.inl hc0) (Or.inl hctop)).2 (by rwa [mul_comm])
    have hpow_lt : (a' / c) ^ p.toReal < μ {y | c < ‖f y‖ₑ} := by
      calc (a' / c) ^ p.toReal < (μ {y | c < ‖f y‖ₑ} ^ p.toReal⁻¹) ^ p.toReal :=
            ENNReal.rpow_lt_rpow hdiv_lt hp_pos
        _ = μ {y | c < ‖f y‖ₑ} := by
            rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hp_pos.ne', ENNReal.rpow_one]
    have hdiv0 : a' / c ≠ 0 := (ENNReal.div_pos ha0 hctop).ne'
    have hpow0 : (a' / c) ^ p.toReal ≠ 0 := by
      simp [hdiv0, hp_pos.le]
    have hpow_top : (a' / c) ^ p.toReal ≠ ∞ := hpow_lt.ne_top
    set t : ℝ := ((a' / c) ^ p.toReal).toReal
    have ht : 0 < t := ENNReal.toReal_pos hpow0 hpow_top
    have hofReal : ENNReal.ofReal t = (a' / c) ^ p.toReal := ENNReal.ofReal_toReal hpow_top
    have hcf : c < μ.decreasingRearrangement (‖f ·‖ₑ) t :=
      μ.lt_decreasingRearrangement_iff.2 (hofReal.symm ▸ hpow_lt)
    have ha_eq : ENNReal.ofReal (t ^ p.toReal⁻¹) * c = a' := by
      rw [← ENNReal.ofReal_rpow_of_pos ht, hofReal, ← ENNReal.rpow_mul,
        mul_inv_cancel₀ hp_pos.ne', ENNReal.rpow_one, ENNReal.div_mul_cancel hc0 hctop]
    refine haa'.trans_le (le_iSup₂_of_le t ht ?_)
    rw [← ha_eq]
    exact mul_le_mul_right hcf.le _

/-- Distribution tail bound from the weak-`Lᵖ` Lorentz gauge:
`c * μ {‖f‖ > c} ^ (1 / p) ≤ ‖f‖_{L^{p, ∞}}`. -/
theorem mul_measure_setOf_lt_rpow_le_eLorentzNorm (f : α → E) {p : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (c : ℝ≥0∞) (μ : Measure α) :
    c * μ {y | c < ‖f y‖ₑ} ^ p.toReal⁻¹ ≤ eLorentzNorm f p ∞ μ := by
  rw [eLorentzNorm_exponent_top_right_eq_iSup_measure f hp0 hp μ]
  exact le_iSup (fun c ↦ c * μ {y | c < ‖f y‖ₑ} ^ p.toReal⁻¹) c

end WeakLp

/-! ### Indicator functions -/

/-- Exact Lorentz gauge of an indicator function `c 1_A`: for `0 < p < ∞` and `0 < q ≤ ∞`,
`‖c 1_A‖_{L^{p, q}} = (p / q) ^ (1 / q) * ‖c‖ₑ * μ(A) ^ (1 / p)`.
At `q = ∞` the prefactor `(p / q) ^ (1 / q)` simplifies to `1`. -/
theorem eLorentzNorm_indicator {E : Type*} [TopologicalSpace E] [ESeminormedAddMonoid E]
    (A : Set α) (c : E) {p q : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) (hq0 : q ≠ 0) (μ : Measure α) :
    eLorentzNorm (A.indicator fun _ ↦ c) p q μ =
      ENNReal.ofReal ((p.toReal / q.toReal) ^ q.toReal⁻¹) * ‖c‖ₑ * μ A ^ p.toReal⁻¹ := by
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hr_pos : 0 < p.toReal⁻¹ := inv_pos.2 hp_pos
  rcases eq_or_ne ‖c‖ₑ 0 with hc0 | hc0
  · have hzero : ∀ᵐ y ∂μ, ‖A.indicator (fun _ ↦ c) y‖ₑ = ‖(0 : α → E) y‖ₑ :=
      ae_of_all _ fun y ↦ by by_cases hy : y ∈ A <;> simp [hy, hc0]
    rw [eLorentzNorm_congr_eNorm_ae hzero, eLorentzNorm_zero, hc0, mul_zero, zero_mul]
  rcases eq_or_ne q ∞ with rfl | hqtop
  · rw [ENNReal.toReal_top, inv_zero, Real.rpow_zero, ENNReal.ofReal_one, one_mul,
      eLorentzNorm_exponent_top_right_eq_iSup_measure _ hp0 hp μ]
    refine le_antisymm (iSup_le fun b ↦ ?_) ?_
    · by_cases hbc : b < ‖c‖ₑ
      · have hset : {y | b < ‖A.indicator (fun _ ↦ c) y‖ₑ} = A := by
          ext y
          by_cases hy : y ∈ A <;> simp [hy, hbc]
        rw [hset]
        exact mul_le_mul_left hbc.le _
      · have hset : {y | b < ‖A.indicator (fun _ ↦ c) y‖ₑ} = ∅ := by
          ext y
          by_cases hy : y ∈ A <;> simp [hy, hbc]
        rw [hset, measure_empty, ENNReal.zero_rpow_of_pos hr_pos, mul_zero]
        exact zero_le
    · refine le_of_forall_lt fun a ha ↦ ?_
      rcases eq_or_ne (μ A) 0 with hA0 | hA0
      · simp [hA0, hr_pos] at ha
      obtain ⟨b, hbc, hab⟩ : ∃ b < ‖c‖ₑ, a < b * μ A ^ p.toReal⁻¹ := by
        have hpos : 0 < μ A ^ p.toReal⁻¹ := ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.2 hA0)
          hr_pos.le
        rcases eq_or_ne (μ A ^ p.toReal⁻¹) ∞ with htop | hfin
        · rw [htop, ENNReal.mul_top hc0] at ha
          obtain ⟨b, hb0, hbc⟩ := exists_between (pos_iff_ne_zero.2 hc0)
          exact ⟨b, hbc, by rw [htop, ENNReal.mul_top hb0.ne']; exact ha⟩
        · have hlt : a / μ A ^ p.toReal⁻¹ < ‖c‖ₑ :=
            (ENNReal.div_lt_iff (Or.inl hpos.ne') (Or.inl hfin)).2 ha
          obtain ⟨b, h1, h2⟩ := exists_between hlt
          exact ⟨b, h2, (ENNReal.div_lt_iff (Or.inl hpos.ne') (Or.inl hfin)).1 h1⟩
      have hset : {y | b < ‖A.indicator (fun _ ↦ c) y‖ₑ} = A := by
        ext y
        by_cases hy : y ∈ A <;> simp [hy, hbc]
      exact hab.trans_le (le_iSup_of_le b (by rw [hset]))
  have hq_pos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
  have hα_pos : 0 < q.toReal / p.toReal := div_pos hq_pos hp_pos
  have hrearr : μ.decreasingRearrangement (fun y ↦ ‖A.indicator (fun _ ↦ c) y‖ₑ) =
      fun t ↦ if ENNReal.ofReal t < μ A then ‖c‖ₑ else 0 := by
    ext t
    simp_rw [eNorm_indicator_eq_indicator_eNorm]
    exact μ.decreasingRearrangement_indicator A ‖c‖ₑ t
  rw [eLorentzNorm_def]
  simp only [hp0, ↓reduceIte]
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal hq0 hqtop
    (measurable_eLorentzIntegrand _ p μ).aestronglyMeasurable]
  simp only [eNorm_eq_self, hrearr]
  rcases eq_or_ne (μ A) 0 with hA0 | hA0
  · simp [hA0, hq_pos, hr_pos]
  rcases eq_or_ne (μ A) ∞ with hAtop | hAtop
  · have heq : (fun t : ℝ ↦ (ENNReal.ofReal (t ^ p.toReal⁻¹) *
        if ENNReal.ofReal t < ∞ then ‖c‖ₑ else 0) ^ q.toReal) =ᵐ[multHaar]
        fun t ↦ ‖c‖ₑ ^ q.toReal * ENNReal.ofReal (t ^ (q.toReal / p.toReal)) := by
      filter_upwards [ae_pos_multHaar] with t ht
      simp only [ENNReal.ofReal_lt_top, ↓reduceIte]
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq_pos.le, mul_comm,
        ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg ht.le _) hq_pos.le,
        ← Real.rpow_mul ht.le, inv_mul_eq_div]
    rw [hAtop, lintegral_congr_ae heq, lintegral_const_mul'' _ (by fun_prop),
      lintegral_multHaar_rpow_eq_top hα_pos,
      ENNReal.mul_top (by simp [hc0, hq_pos.le]),
      ENNReal.top_rpow_of_pos (by positivity),
      ENNReal.top_rpow_of_pos hr_pos,
      ENNReal.mul_top (ENNReal.mul_pos (ENNReal.ofReal_pos.2 (by positivity)).ne' hc0).ne']
  have hm_pos : 0 < (μ A).toReal := ENNReal.toReal_pos hA0 hAtop
  have heq : (fun t : ℝ ↦ (ENNReal.ofReal (t ^ p.toReal⁻¹) *
      if ENNReal.ofReal t < μ A then ‖c‖ₑ else 0) ^ q.toReal) =ᵐ[multHaar]
      fun t ↦ ‖c‖ₑ ^ q.toReal *
        (Iio (μ A).toReal).indicator (fun t ↦ ENNReal.ofReal (t ^ (q.toReal / p.toReal))) t := by
    filter_upwards [ae_pos_multHaar] with t ht
    have hiff : ENNReal.ofReal t < μ A ↔ t < (μ A).toReal :=
      ENNReal.ofReal_lt_iff_lt_toReal ht.le hAtop
    by_cases hlt : t < (μ A).toReal
    · simp only [hiff.2 hlt, ↓reduceIte, indicator_of_mem (mem_Iio.2 hlt)]
      rw [ENNReal.mul_rpow_of_nonneg _ _ hq_pos.le, mul_comm,
        ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg ht.le _) hq_pos.le,
        ← Real.rpow_mul ht.le, inv_mul_eq_div]
    · simp [mt hiff.1 hlt, hlt, hq_pos]
  rw [lintegral_congr_ae heq, lintegral_const_mul'' _ ((by fun_prop : Measurable fun t : ℝ ↦
      ENNReal.ofReal (t ^ (q.toReal / p.toReal))).indicator measurableSet_Iio).aemeasurable,
    lintegral_indicator measurableSet_Iio, lintegral_Iio_multHaar_rpow hα_pos hm_pos,
    ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    mul_one_div_cancel hq_pos.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), one_div,
    Real.mul_rpow (Real.rpow_nonneg hm_pos.le _) (by positivity),
    ← Real.rpow_mul hm_pos.le,
    show q.toReal / p.toReal * q.toReal⁻¹ = p.toReal⁻¹ by field_simp [hq_pos.ne'], inv_div,
    ENNReal.ofReal_mul (Real.rpow_nonneg hm_pos.le _),
    ← ENNReal.ofReal_rpow_of_pos hm_pos, ENNReal.ofReal_toReal hAtop]
  ring

/-! ### Secondary-exponent embeddings -/

section Embeddings

variable {E : Type*} [ENorm E]

/-- **Lorentz embedding into weak `Lᵖ`.** For `0 < p < ∞` and `0 < q ≤ ∞`,
`‖f‖_{L^{p, ∞}} ≤ (q / p) ^ (1 / q) * ‖f‖_{L^{p, q}}`.
The constant is sharp and attained on indicator functions. -/
theorem eLorentzNorm_top_le_mul_eLorentzNorm (f : α → E) {p q : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (hq0 : q ≠ 0) (μ : Measure α) :
    eLorentzNorm f p ∞ μ ≤
      ENNReal.ofReal ((q.toReal / p.toReal) ^ q.toReal⁻¹) * eLorentzNorm f p q μ := by
  rcases eq_or_ne q ∞ with rfl | hqtop
  · simp
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hq_pos : 0 < q.toReal := ENNReal.toReal_pos hq0 hqtop
  have hα_pos : 0 < q.toReal / p.toReal := div_pos hq_pos hp_pos
  rw [eLorentzNorm_exponent_top_right f hp0 μ, eLorentzNorm_def]
  simp only [hp0, ↓reduceIte,
    eLpNorm_eq_lintegral_rpow_eNorm_toReal hq0 hqtop
      (measurable_eLorentzIntegrand f p μ).aestronglyMeasurable,
    eNorm_eq_self]
  refine iSup₂_le fun t ht ↦ ?_
  -- Use antitonicity of `f*` on `(0, t]` to bound `t ^ (1 / p) f*(t)` by the `L^q` integral.
  have hstep : ENNReal.ofReal (t ^ (q.toReal / p.toReal) * (q.toReal / p.toReal)⁻¹) *
        μ.decreasingRearrangement (‖f ·‖ₑ) t ^ q.toReal ≤
      ∫⁻ s, (ENNReal.ofReal (s ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) s) ^ q.toReal
        ∂multHaar := by
    calc ENNReal.ofReal (t ^ (q.toReal / p.toReal) * (q.toReal / p.toReal)⁻¹) *
            μ.decreasingRearrangement (‖f ·‖ₑ) t ^ q.toReal
        = (∫⁻ s in Iic t, ENNReal.ofReal (s ^ (q.toReal / p.toReal)) ∂multHaar) *
            μ.decreasingRearrangement (‖f ·‖ₑ) t ^ q.toReal := by
            rw [lintegral_Iic_multHaar_rpow hα_pos ht]
      _ = ∫⁻ s in Iic t, ENNReal.ofReal (s ^ (q.toReal / p.toReal)) *
            μ.decreasingRearrangement (‖f ·‖ₑ) t ^ q.toReal ∂multHaar :=
            (lintegral_mul_const _ (by fun_prop)).symm
      _ ≤ ∫⁻ s in Iic t, (ENNReal.ofReal (s ^ p.toReal⁻¹) *
            μ.decreasingRearrangement (‖f ·‖ₑ) s) ^ q.toReal ∂multHaar := by
            refine setLIntegral_mono_ae' measurableSet_Iic ?_
            filter_upwards [ae_pos_multHaar] with s hs hst
            rw [ENNReal.mul_rpow_of_nonneg _ _ hq_pos.le,
              ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hs.le _) hq_pos.le,
              ← Real.rpow_mul hs.le, inv_mul_eq_div]
            gcongr
            exact μ.antitone_decreasingRearrangement _ hst
      _ ≤ _ := setLIntegral_le_lintegral _ _
  have hrpow := ENNReal.rpow_le_rpow hstep (by positivity : (0 : ℝ) ≤ 1 / q.toReal)
  rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
    mul_one_div_cancel hq_pos.ne', ENNReal.rpow_one,
    ENNReal.ofReal_rpow_of_nonneg (by positivity) (by positivity), one_div,
    Real.mul_rpow (Real.rpow_nonneg ht.le _) (by positivity), ← Real.rpow_mul ht.le,
    show q.toReal / p.toReal * q.toReal⁻¹ = p.toReal⁻¹ by field_simp [hq_pos.ne'],
    ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _)] at hrpow
  have hcancel : ENNReal.ofReal ((q.toReal / p.toReal) ^ q.toReal⁻¹) *
      ENNReal.ofReal ((q.toReal / p.toReal)⁻¹ ^ q.toReal⁻¹) = 1 := by
    rw [← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow hα_pos.le (by positivity),
      mul_inv_cancel₀ hα_pos.ne', Real.one_rpow, ENNReal.ofReal_one]
  calc ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t
      = ENNReal.ofReal ((q.toReal / p.toReal) ^ q.toReal⁻¹) *
          (ENNReal.ofReal ((q.toReal / p.toReal)⁻¹ ^ q.toReal⁻¹) *
            (ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t)) := by
          rw [← mul_assoc, hcancel, one_mul]
    _ = ENNReal.ofReal ((q.toReal / p.toReal) ^ q.toReal⁻¹) *
          (ENNReal.ofReal (t ^ p.toReal⁻¹) * ENNReal.ofReal ((q.toReal / p.toReal)⁻¹ ^ q.toReal⁻¹) *
            μ.decreasingRearrangement (‖f ·‖ₑ) t) := by ring
    _ ≤ ENNReal.ofReal ((q.toReal / p.toReal) ^ q.toReal⁻¹) *
          (∫⁻ s, (ENNReal.ofReal (s ^ p.toReal⁻¹) *
            μ.decreasingRearrangement (‖f ·‖ₑ) s) ^ q.toReal ∂multHaar) ^ (1 / q.toReal) := by
          rw [one_div]
          exact mul_le_mul_right hrpow _

/-- **Secondary-exponent embedding for Lorentz gauges.** For `0 < p < ∞` and `0 < q₀ ≤ q₁ ≤ ∞`,
`‖f‖_{L^{p, q₁}} ≤ (q₀ / p) ^ (1 / q₀ - 1 / q₁) * ‖f‖_{L^{p, q₀}}`. -/
theorem eLorentzNorm_le_mul_eLorentzNorm (f : α → E) {p q₀ q₁ : ℝ≥0∞}
    (hp0 : p ≠ 0) (hp : p ≠ ∞) (hq₀ : q₀ ≠ 0) (hq : q₀ ≤ q₁) (μ : Measure α) :
    eLorentzNorm f p q₁ μ ≤
      ENNReal.ofReal ((q₀.toReal / p.toReal) ^ (q₀.toReal⁻¹ - q₁.toReal⁻¹)) *
        eLorentzNorm f p q₀ μ := by
  rcases eq_or_ne q₁ ∞ with rfl | hq₁top
  · simpa using eLorentzNorm_top_le_mul_eLorentzNorm f hp0 hp hq₀ μ
  have hq₀top : q₀ ≠ ∞ := ne_top_of_le_ne_top hq₁top hq
  have hq₁0 : q₁ ≠ 0 := (pos_iff_ne_zero.2 hq₀ |>.trans_le hq).ne'
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hq₀_pos : 0 < q₀.toReal := ENNReal.toReal_pos hq₀ hq₀top
  have hq₁_pos : 0 < q₁.toReal := ENNReal.toReal_pos hq₁0 hq₁top
  have hq_le : q₀.toReal ≤ q₁.toReal := ENNReal.toReal_mono hq₁top hq
  have hdiff_nonneg : 0 ≤ q₁.toReal - q₀.toReal := sub_nonneg.2 hq_le
  set h : ℝ → ℝ≥0∞ := fun t ↦
    ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t
  set M : ℝ≥0∞ := eLorentzNorm f p ∞ μ with hM_def
  have hM_bound : ∀ t : ℝ, 0 < t → h t ≤ M := fun t ht ↦ by
    rw [hM_def, eLorentzNorm_exponent_top_right f hp0 μ]
    exact le_iSup₂_of_le t ht le_rfl
  have hq₁_eq : eLorentzNorm f p q₁ μ = (∫⁻ t, h t ^ q₁.toReal ∂multHaar) ^ (1 / q₁.toReal) := by
    rw [eLorentzNorm_def]
    simp only [hp0, ↓reduceIte,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal hq₁0 hq₁top
        (measurable_eLorentzIntegrand f p μ).aestronglyMeasurable,
      eNorm_eq_self, h]
  have hq₀_eq : eLorentzNorm f p q₀ μ = (∫⁻ t, h t ^ q₀.toReal ∂multHaar) ^ (1 / q₀.toReal) := by
    rw [eLorentzNorm_def]
    simp only [hp0, ↓reduceIte,
      eLpNorm_eq_lintegral_rpow_eNorm_toReal hq₀ hq₀top
        (measurable_eLorentzIntegrand f p μ).aestronglyMeasurable,
      eNorm_eq_self, h]
  have hI_eq : ∫⁻ t, h t ^ q₀.toReal ∂multHaar = eLorentzNorm f p q₀ μ ^ q₀.toReal := by
    rw [hq₀_eq, ← ENNReal.rpow_mul, one_div_mul_cancel hq₀_pos.ne', ENNReal.rpow_one]
  have hint_le : ∫⁻ t, h t ^ q₁.toReal ∂multHaar ≤
      M ^ (q₁.toReal - q₀.toReal) * eLorentzNorm f p q₀ μ ^ q₀.toReal := by
    rw [← hI_eq, ← lintegral_const_mul'' _
      ((measurable_eLorentzIntegrand f p μ).pow_const _).aemeasurable]
    refine lintegral_mono_ae ?_
    filter_upwards [ae_pos_multHaar] with t ht
    calc h t ^ q₁.toReal = h t ^ (q₁.toReal - q₀.toReal) * h t ^ q₀.toReal := by
            rw [← ENNReal.rpow_add_of_nonneg _ _ hdiff_nonneg hq₀_pos.le, sub_add_cancel]
      _ ≤ M ^ (q₁.toReal - q₀.toReal) * h t ^ q₀.toReal := by
            gcongr
            exact hM_bound t ht
  have hsub_nonneg : 0 ≤ 1 - q₀.toReal / q₁.toReal :=
    sub_nonneg.2 ((div_le_one hq₁_pos).2 hq_le)
  have htop_le : M ≤
      ENNReal.ofReal ((q₀.toReal / p.toReal) ^ q₀.toReal⁻¹) * eLorentzNorm f p q₀ μ :=
    eLorentzNorm_top_le_mul_eLorentzNorm f hp0 hp hq₀ μ
  calc eLorentzNorm f p q₁ μ
      = (∫⁻ t, h t ^ q₁.toReal ∂multHaar) ^ (1 / q₁.toReal) := hq₁_eq
    _ ≤ (M ^ (q₁.toReal - q₀.toReal) * eLorentzNorm f p q₀ μ ^ q₀.toReal) ^ (1 / q₁.toReal) :=
          ENNReal.rpow_le_rpow hint_le (by positivity)
    _ = M ^ (1 - q₀.toReal / q₁.toReal) * eLorentzNorm f p q₀ μ ^ (q₀.toReal / q₁.toReal) := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ (by positivity), ← ENNReal.rpow_mul,
            ← ENNReal.rpow_mul, mul_one_div, mul_one_div, sub_div, div_self hq₁_pos.ne']
    _ ≤ (ENNReal.ofReal ((q₀.toReal / p.toReal) ^ q₀.toReal⁻¹) * eLorentzNorm f p q₀ μ) ^
            (1 - q₀.toReal / q₁.toReal) *
          eLorentzNorm f p q₀ μ ^ (q₀.toReal / q₁.toReal) := by
          gcongr
    _ = ENNReal.ofReal ((q₀.toReal / p.toReal) ^ (q₀.toReal⁻¹ - q₁.toReal⁻¹)) *
          eLorentzNorm f p q₀ μ := by
          rw [ENNReal.mul_rpow_of_nonneg _ _ hsub_nonneg, mul_assoc,
            ← ENNReal.rpow_add_of_nonneg _ _ hsub_nonneg (by positivity),
            sub_add_cancel, ENNReal.rpow_one,
            ENNReal.ofReal_rpow_of_nonneg (by positivity) hsub_nonneg,
            ← Real.rpow_mul (by positivity)]
          congr 3
          field_simp [hq₀_pos.ne', hq₁_pos.ne']

end Embeddings

/-! ### Power-function witness for `Lᵖ ⊊ L^{p, ∞}` -/

/-- On `(0, ∞)` with Lebesgue measure, `t ↦ t ^ (-1 / p)` has weak-`Lᵖ` Lorentz gauge `1`. -/
theorem eLorentzNorm_rpow_neg_inv_exponent_top {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    eLorentzNorm (fun t : ℝ ↦ t ^ (-p.toReal⁻¹)) p ∞ (volume.restrict (Ioi 0)) = 1 := by
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hr_pos : 0 < p.toReal⁻¹ := inv_pos.2 hp_pos
  rw [eLorentzNorm_exponent_top_right_eq_iSup_measure _ hp0 hp]
  have hterm : ∀ c : ℝ≥0∞, 0 < c → c < ∞ →
      c * volume.restrict (Ioi (0 : ℝ)) {y | c < ‖y ^ (-p.toReal⁻¹)‖ₑ} ^ p.toReal⁻¹ = 1 := by
    intro c hc0 hctop
    have hc_pos : 0 < c.toReal := ENNReal.toReal_pos hc0.ne' hctop.ne
    have hset : {y : ℝ | c < ‖y ^ (-p.toReal⁻¹)‖ₑ} ∩ Ioi 0 = Ioo 0 (c.toReal ^ (-p.toReal)) := by
      ext y
      simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, mem_Ioo]
      refine ⟨fun ⟨hy, hy0⟩ ↦ ⟨hy0, ?_⟩, fun ⟨hy0, hy⟩ ↦ ⟨?_, hy0⟩⟩
      · rw [Real.eNorm_of_nonneg (Real.rpow_nonneg hy0.le _),
          ← ENNReal.ofReal_toReal hctop.ne,
          ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hy0 _)] at hy
        have hlt := Real.rpow_lt_rpow hc_pos.le hy hp_pos
        rw [← Real.rpow_mul hy0.le, neg_mul, inv_mul_cancel₀ hp_pos.ne', Real.rpow_neg_one] at hlt
        rw [Real.rpow_neg hc_pos.le]
        exact (lt_inv_comm₀ hy0 (Real.rpow_pos_of_pos hc_pos _)).2 hlt
      · rw [Real.eNorm_of_nonneg (Real.rpow_nonneg hy0.le _),
          ← ENNReal.ofReal_toReal hctop.ne,
          ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hy0 _)]
        rw [Real.rpow_neg hc_pos.le] at hy
        have hlt := (lt_inv_comm₀ hy0 (Real.rpow_pos_of_pos hc_pos _)).1 hy
        have hpow := Real.rpow_lt_rpow (Real.rpow_pos_of_pos hc_pos _).le hlt hr_pos
        rwa [← Real.rpow_mul hc_pos.le, mul_inv_cancel₀ hp_pos.ne', Real.rpow_one,
          Real.inv_rpow hy0.le, ← Real.rpow_neg hy0.le] at hpow
    rw [Measure.restrict_apply' measurableSet_Ioi, hset, Real.volume_Ioo, sub_zero,
      ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg hc_pos.le _) hr_pos.le,
      ← Real.rpow_mul hc_pos.le, neg_mul, mul_inv_cancel₀ hp_pos.ne', Real.rpow_neg_one,
      ENNReal.ofReal_inv_of_pos hc_pos, ENNReal.ofReal_toReal hctop.ne,
      ENNReal.mul_inv_cancel hc0.ne' hctop.ne]
  refine le_antisymm (iSup_le fun c ↦ ?_) (le_iSup_of_le 1 (hterm 1 one_pos ENNReal.one_lt_top).ge)
  rcases eq_or_ne c 0 with rfl | hc0
  · simp
  rcases eq_or_ne c ∞ with rfl | hctop
  · simp [hr_pos]
  exact (hterm c (pos_iff_ne_zero.2 hc0) hctop.lt_top).le

/-- On `(0, ∞)` with Lebesgue measure, `t ↦ t ^ (-1 / p)` has infinite `Lᵖ` seminorm. Together
with `TauCeti.eLorentzNorm_rpow_neg_inv_exponent_top` this witnesses `Lᵖ ⊊ L^{p, ∞}`. -/
theorem eLpNorm_rpow_neg_inv_eq_top {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    eLpNorm (fun t : ℝ ↦ t ^ (-p.toReal⁻¹)) p (volume.restrict (Ioi 0)) = ∞ := by
  have hp_pos : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hmeas : AEStronglyMeasurable (fun t : ℝ ↦ t ^ (-p.toReal⁻¹)) (volume.restrict (Ioi 0)) :=
    (continuousOn_id.rpow_const fun _ ht ↦ Or.inl (ne_of_gt ht)).aestronglyMeasurable
      measurableSet_Ioi
  have heq : (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * ‖t ^ (-p.toReal⁻¹)‖ₑ) =ᵐ[multHaar]
      fun _ ↦ (1 : ℝ≥0∞) := by
    filter_upwards [ae_pos_multHaar] with t ht
    rw [Real.eNorm_of_nonneg (Real.rpow_nonneg ht.le _),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← Real.rpow_add ht, add_neg_cancel,
      Real.rpow_zero, ENNReal.ofReal_one]
  have huniv : multHaar (univ : Set ℝ) = ∞ := by
    rw [← map_volume_exp, Measure.map_apply Real.measurable_exp MeasurableSet.univ, preimage_univ,
      Real.volume_univ]
  rw [← eLpNorm_eNorm _ hmeas, eLpNorm_volume_Ioi_eq_eLpNorm_multHaar hp0, eLpNorm_congr_ae heq,
    eLpNorm_const (1 : ℝ≥0∞) hp0 (fun h ↦ by simp [h] at huniv), eNorm_eq_self, one_mul, huniv,
    ENNReal.top_rpow_of_pos (by positivity)]

end TauCeti
