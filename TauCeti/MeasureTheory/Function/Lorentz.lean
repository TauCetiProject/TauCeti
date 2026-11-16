/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Function.DecreasingRearrangement
public import TauCeti.MeasureTheory.Measure.Haar.MultHaar
import TauCeti.Analysis.SpecialFunctions.Pow.Integral

/-!
# Lorentz gauges `‖f‖_{p,q}`

For a function `f : α → ε` on a measure space `(α, μ)` and exponents `p, q ∈ [0, ∞]`, the Lorentz
gauge `TauCeti.eLorentzNorm f p q μ` is the `L^q(dt / t)` seminorm of `t ↦ t ^ (1 / p) ‖f‖*(t)`:

`‖f‖_{p,q} = ‖t ↦ t ^ (1 / p) (‖f‖ₑ)* t‖_{L^q(dt / t)}`,

where `(‖f‖ₑ)*` is the decreasing rearrangement `MeasureTheory.Measure.decreasingRearrangement`
and `dt / t` is the multiplicative Haar measure `TauCeti.multHaar`.

On the diagonal `p = q` the Lorentz gauge recovers the `Lᵖ` seminorm `eLpNorm f p μ` for every
almost everywhere strongly measurable function and every `p ∈ [0, ∞]`
(`TauCeti.eLorentzNorm_self`). At `q = ∞` it is the weak-`Lᵖ` quasi-seminorm
`sup_{t > 0} t ^ (1 / p) ‖f‖*(t) = sup_{c ≥ 0} c μ {‖f‖ > c} ^ (1 / p)`
(`TauCeti.eLorentzNorm_top_eq_iSup`, `TauCeti.eLorentzNorm_top_eq_iSup_measure_lt`).

The Lorentz gauges satisfy absolute homogeneity (`TauCeti.eLorentzNorm_const_smul`),
definiteness for `q ≠ 0` (`TauCeti.eLorentzNorm_eq_zero_iff`), the quasi-triangle inequality with
constant `2 ^ (1 / p)` for `1 ≤ q` (`TauCeti.eLorentzNorm_add_le`), and sharp monotonicity in the
secondary exponent `q`: for `0 < p < ∞` and `0 < q₀ ≤ q₁ ≤ ∞`,

`‖f‖_{p, q₁} ≤ (q₀ / p) ^ (1 / q₀ - 1 / q₁) ‖f‖_{p, q₀}`

(`TauCeti.eLorentzNorm_le_of_le`). The constant is attained on every indicator `c 1_A` of positive
finite measure, whose Lorentz gauge is `(p / q) ^ (1 / q) ‖c‖ (μ A) ^ (1 / p)`
(`TauCeti.eLorentzNorm_indicator`). For `1 < p < ∞` and `q ≠ 0`, finiteness of `‖f‖_{p,q}` implies
local integrability of the decreasing rearrangement (`∫₀ᵗ ‖f‖* < ∞`,
`TauCeti.lintegral_decreasingRearrangement_lt_top_of_eLorentzNorm_lt_top`), placing every function
of finite Lorentz gauge in `L¹ + L^∞`. Finally, on `(0, ∞)` with Lebesgue measure, the power
function `t ↦ t ^ (-1 / p)` has `‖f‖_{p, ∞} = 1` and `‖f‖_{p, q} = ∞` for every finite `q > 0`
(`TauCeti.eLorentzNorm_ofReal_rpow_neg_inv_top`,
`TauCeti.eLorentzNorm_ofReal_rpow_neg_inv_eq_top`), witnessing the strict inclusion
`L^{p, q} ⊊ L^{p, ∞}` (in particular `Lᵖ ⊊ L^{p, ∞}`).

## Main declarations

* `TauCeti.eLorentzNorm`: the Lorentz gauge `‖f‖_{p,q}`.
* `TauCeti.eLorentzNorm_self`: `‖f‖_{p,p} = eLpNorm f p μ` for `AEStronglyMeasurable f μ`.
* `TauCeti.eLorentzNorm_top_eq_iSup` and `TauCeti.eLorentzNorm_top_eq_iSup_measure_lt`: the
  weak-`Lᵖ` characterizations at `q = ∞`.
* `TauCeti.eLorentzNorm_const_smul`, `TauCeti.eLorentzNorm_add_le`,
  `TauCeti.eLorentzNorm_eq_zero_iff`: quasi-seminorm properties.
* `TauCeti.eLorentzNorm_indicator`, `TauCeti.eLorentzNorm_indicator_top`: exact evaluation on
  indicators.
* `TauCeti.eLorentzNorm_top_le_mul_eLorentzNorm`, `TauCeti.eLorentzNorm_le_of_le`: sharp
  monotonicity in the secondary exponent `q`.
* `TauCeti.lintegral_decreasingRearrangement_le_mul_eLorentzNorm_top`,
  `TauCeti.lintegral_decreasingRearrangement_lt_top_of_eLorentzNorm_lt_top`: bounding `∫₀ᵗ ‖f‖*`
  by the Lorentz gauge for `1 < p < ∞`.

## References

* J. Bergh and J. Löfström, *Interpolation Spaces. An Introduction*, Grundlehren 223,
  Springer, 1976, §1.3 and §5.2.
* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Springer, 2014, §1.4.2 (Propositions 1.4.9
  and 1.4.10).
* E. M. Stein and G. Weiss, *Introduction to Fourier Analysis on Euclidean Spaces*, Chapter V,
  §3.
-/

public noncomputable section

open MeasureTheory Set Filter Topology
open scoped ENNReal

namespace TauCeti

variable {α ε ε' : Type*} {mα : MeasurableSpace α} {μ : Measure α}

/-- The **Lorentz gauge** `‖f‖_{p,q} = ‖t ↦ t ^ (1 / p) ‖f‖*(t)‖_{L^q(dt / t)}` of `f : α → ε`
on `(α, μ)`, for exponents `p, q ∈ [0, ∞]`. -/
def eLorentzNorm [ENorm ε] (f : α → ε) (p q : ℝ≥0∞)
    (μ : Measure α := by volume_tac) : ℝ≥0∞ :=
  eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t)
    q multHaar

theorem eLorentzNorm_def [ENorm ε] (f : α → ε) (p q : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm f p q μ =
      eLpNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t)
        q multHaar :=
  (rfl)

/-- The integrand defining `eLorentzNorm` is always measurable, without measurability hypotheses
on `f`. -/
private theorem measurable_eLorentzNorm_integrand [ENorm ε] (f : α → ε) (p : ℝ≥0∞)
    (μ : Measure α) :
    Measurable fun t : ℝ ↦
      ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t := by
  fun_prop

section Basic

variable [ENorm ε] [ENorm ε'] {f g : α → ε} {p q : ℝ≥0∞}

@[simp]
theorem eLorentzNorm_eNorm (f : α → ε) (p q : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm (fun x ↦ ‖f x‖ₑ) p q μ = eLorentzNorm f p q μ := by
  simp only [eLorentzNorm_def, eNorm_eq_self]

@[simp]
theorem eLorentzNorm_exponent_zero (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm f p 0 μ = 0 :=
  eLpNorm_exponent_zero (measurable_eLorentzNorm_integrand f p μ).aestronglyMeasurable

@[simp]
theorem eLorentzNorm_measure_zero (f : α → ε) (p q : ℝ≥0∞) :
    eLorentzNorm f p q (0 : Measure α) = 0 := by
  rw [eLorentzNorm_def]
  have h0 : (0 : Measure α).decreasingRearrangement (‖f ·‖ₑ) = fun _ ↦ 0 := by
    ext s
    exact le_antisymm (((0 : Measure α).decreasingRearrangement_le_iff).2 (by simp)) zero_le
  simp [h0]

/-- Integral formula for `eLorentzNorm` when `0 < q < ∞`. -/
theorem eLorentzNorm_eq_lintegral (f : α → ε) (p : ℝ≥0∞) {q : ℝ≥0∞} (hq0 : q ≠ 0) (hq : q ≠ ∞)
    (μ : Measure α) :
    eLorentzNorm f p q μ =
      (∫⁻ t, (ENNReal.ofReal (t ^ p.toReal⁻¹) *
        μ.decreasingRearrangement (‖f ·‖ₑ) t) ^ q.toReal ∂multHaar) ^ q.toReal⁻¹ := by
  rw [eLorentzNorm_def, eLpNorm_eq_lintegral_rpow_eNorm_toReal hq0 hq
    (measurable_eLorentzNorm_integrand f p μ).aestronglyMeasurable, one_div]
  simp only [eNorm_eq_self]

theorem eLorentzNorm_mono_ae {g : α → ε'} (h : ∀ᵐ x ∂μ, ‖f x‖ₑ ≤ ‖g x‖ₑ) :
    eLorentzNorm f p q μ ≤ eLorentzNorm g p q μ :=
  eLpNorm_mono_eNorm (measurable_eLorentzNorm_integrand f p μ).aestronglyMeasurable fun t ↦ by
    simp only [eNorm_eq_self]
    exact mul_le_mul_of_nonneg_left (μ.decreasingRearrangement_mono_ae h t) zero_le

theorem eLorentzNorm_congr_eNorm_ae {g : α → ε'} (h : ∀ᵐ x ∂μ, ‖f x‖ₑ = ‖g x‖ₑ) :
    eLorentzNorm f p q μ = eLorentzNorm g p q μ :=
  le_antisymm (eLorentzNorm_mono_ae (h.mono fun _ hx ↦ hx.le))
    (eLorentzNorm_mono_ae (h.mono fun _ hx ↦ hx.ge))

theorem eLorentzNorm_congr_ae (h : f =ᵐ[μ] g) :
    eLorentzNorm f p q μ = eLorentzNorm g p q μ :=
  eLorentzNorm_congr_eNorm_ae (h.mono fun _ hx ↦ congrArg eNorm hx)

/-- **Diagonal identity.** On `p = q`, the Lorentz gauge agrees with `eLpNorm` for every almost
everywhere strongly measurable function and every `p ∈ [0, ∞]`. -/
theorem eLorentzNorm_self {ε : Type*} [TopologicalSpace ε] [ContinuousENorm ε] {f : α → ε}
    (hf : AEStronglyMeasurable f μ) (p : ℝ≥0∞) :
    eLorentzNorm f p p μ = eLpNorm f p μ := by
  rw [eLorentzNorm_def, eLpNorm_ofReal_rpow_inv_mul_multHaar,
    μ.eLpNorm_decreasingRearrangement hf.eNorm, eLpNorm_eNorm f hf]

/-- The Lorentz gauge is absolutely homogeneous. -/
theorem eLorentzNorm_const_smul {𝕜 : Type*} [ENorm 𝕜] [SMul 𝕜 ε] [ENormSMulClass 𝕜 ε] (c : 𝕜)
    (f : α → ε) (p q : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm (c • f) p q μ = ‖c‖ₑ * eLorentzNorm f p q μ := by
  rw [eLorentzNorm_def, eLorentzNorm_def,
    ← eLpNorm_const_mul_ennreal (measurable_eLorentzNorm_integrand f p μ).aestronglyMeasurable]
  congr 1
  ext t
  simp only [Pi.smul_apply, eNorm_smul, μ.decreasingRearrangement_const_mul]
  ring

/-- For `q ≠ 0`, `‖f‖_{p,q} = 0` holds exactly when `‖f x‖ₑ = 0` almost everywhere. -/
theorem eLorentzNorm_eq_zero_iff_ae_eNorm_eq_zero (hq : q ≠ 0) :
    eLorentzNorm f p q μ = 0 ↔ ∀ᵐ x ∂μ, ‖f x‖ₑ = 0 := by
  constructor
  · intro h0
    rw [eLorentzNorm_def, eLpNorm_eq_zero_iff hq] at h0
    have hstar : ∀ s > (0 : ℝ), μ.decreasingRearrangement (‖f ·‖ₑ) s = 0 := fun s hs ↦ by
      have hpos : multHaar (Ico (s / 2) s) ≠ 0 := by
        rw [multHaar_Ico (half_pos hs) (half_le_self hs.le)]
        exact (ENNReal.ofReal_pos.2 (sub_pos.2 (Real.log_lt_log (half_pos hs)
          (half_lt_self hs)))).ne'
      have hex : ∃ t ∈ Ico (s / 2) s,
          ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t = 0 := by
        by_contra! hne
        exact hpos <| measure_mono_null (fun t ht ↦ hne t ht) (ae_iff.1 h0)
      obtain ⟨t, ht, htz⟩ := hex
      have hft0 : μ.decreasingRearrangement (‖f ·‖ₑ) t = 0 := by
        simpa [(ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos ((half_pos hs).trans_le ht.1) _)).ne']
          using htz
      exact le_antisymm ((μ.antitone_decreasingRearrangement _ ht.2.le).trans_eq hft0) zero_le
    rw [ae_iff]
    by_contra hne
    have hpos : (0 : ℝ≥0∞) < μ {y | 0 < ‖f y‖ₑ} := by
      simpa only [pos_iff_ne_zero, ne_eq] using hne
    obtain ⟨r, hr0, hrm⟩ := exists_between hpos
    have hlt : ENNReal.ofReal r.toReal < μ {y | 0 < ‖f y‖ₑ} := by
      rwa [ENNReal.ofReal_toReal hrm.ne_top]
    have hlt' := (μ.lt_decreasingRearrangement_iff (f := (‖f ·‖ₑ)) (s := r.toReal) (c := 0)).2 hlt
    rw [hstar r.toReal (ENNReal.toReal_pos hr0.ne' hrm.ne_top)] at hlt'
    exact lt_irrefl _ hlt'
  · intro h
    have hnull : μ {y | 0 < ‖f y‖ₑ} = 0 := by
      simpa only [ae_iff, pos_iff_ne_zero, ne_eq] using h
    have h0 : μ.decreasingRearrangement (‖f ·‖ₑ) = fun _ ↦ 0 := by
      ext s
      refine le_antisymm (μ.decreasingRearrangement_le_iff.2 ?_) zero_le
      rw [hnull]
      exact zero_le
    rw [eLorentzNorm_def]
    simp [h0]

end Basic

section Algebraic

@[simp]
theorem eLorentzNorm_zero {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
    (p q : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm (0 : α → ε) p q μ = 0 := by
  rcases eq_or_ne q 0 with rfl | hq
  · exact eLorentzNorm_exponent_zero _ _ _
  · exact (eLorentzNorm_eq_zero_iff_ae_eNorm_eq_zero hq).2 (ae_of_all _ fun _ ↦ eNorm_zero)

@[simp]
theorem eLorentzNorm_neg {E : Type*} [SeminormedAddGroup E] (f : α → E) (p q : ℝ≥0∞)
    (μ : Measure α) :
    eLorentzNorm (-f) p q μ = eLorentzNorm f p q μ :=
  eLorentzNorm_congr_eNorm_ae (ae_of_all _ fun x ↦ by simp)

/-- For `q ≠ 0` and an `ENormedAddMonoid` codomain, `‖f‖_{p,q} = 0` iff `f = 0` almost
everywhere. -/
theorem eLorentzNorm_eq_zero_iff {ε : Type*} [TopologicalSpace ε] [ENormedAddMonoid ε]
    {f : α → ε} {p q : ℝ≥0∞} (hq : q ≠ 0) :
    eLorentzNorm f p q μ = 0 ↔ f =ᵐ[μ] 0 := by
  rw [eLorentzNorm_eq_zero_iff_ae_eNorm_eq_zero hq]
  exact Filter.eventually_congr (ae_of_all _ fun x ↦ eNorm_eq_zero)

/-- **Quasi-triangle inequality for Lorentz gauges.** For `1 ≤ q ≤ ∞` and every `p ∈ [0, ∞]`,
`‖f + g‖_{p,q} ≤ 2 ^ (1 / p) (‖f‖_{p,q} + ‖g‖_{p,q})`. -/
theorem eLorentzNorm_add_le {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
    (f g : α → ε) (p : ℝ≥0∞) {q : ℝ≥0∞} (hq : 1 ≤ q) (μ : Measure α) :
    eLorentzNorm (f + g) p q μ ≤
      ENNReal.ofReal (2 ^ p.toReal⁻¹) * (eLorentzNorm f p q μ + eLorentzNorm g p q μ) := by
  have hmp : MeasurePreserving ((2 : ℝ)⁻¹ * ·) multHaar multHaar :=
    ⟨measurable_const_mul _, map_multHaar_mul_left (inv_pos.2 two_pos)⟩
  set F : ℝ → ℝ≥0∞ :=
    fun t ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t
  set G : ℝ → ℝ≥0∞ :=
    fun t ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖g ·‖ₑ) t
  have hF : Measurable F := measurable_eLorentzNorm_integrand f p μ
  have hG : Measurable G := measurable_eLorentzNorm_integrand g p μ
  have hpt : ∀ᵐ t ∂multHaar,
      ‖ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖(f + g) ·‖ₑ) t‖ₑ ≤
        ‖ENNReal.ofReal (2 ^ p.toReal⁻¹) * (F (2⁻¹ * t) + G (2⁻¹ * t))‖ₑ := by
    filter_upwards [ae_pos_multHaar] with t ht
    simp only [eNorm_eq_self]
    have hsplit : t = 2⁻¹ * t + 2⁻¹ * t := by ring
    have hrearr : μ.decreasingRearrangement (‖(f + g) ·‖ₑ) t ≤
        μ.decreasingRearrangement (‖f ·‖ₑ) (2⁻¹ * t) +
          μ.decreasingRearrangement (‖g ·‖ₑ) (2⁻¹ * t) := by
      calc μ.decreasingRearrangement (‖(f + g) ·‖ₑ) t
          ≤ μ.decreasingRearrangement ((‖f ·‖ₑ) + (‖g ·‖ₑ)) (2⁻¹ * t + 2⁻¹ * t) := by
            rw [← hsplit]
            exact μ.decreasingRearrangement_mono (fun y ↦ eNorm_add_le (f y) (g y)) t
        _ ≤ _ := μ.decreasingRearrangement_add_le _ _ (by positivity) (by positivity)
    have hpow : ENNReal.ofReal (t ^ p.toReal⁻¹) =
        ENNReal.ofReal (2 ^ p.toReal⁻¹) * ENNReal.ofReal ((2⁻¹ * t) ^ p.toReal⁻¹) := by
      rw [← ENNReal.ofReal_mul (by positivity), ← Real.mul_rpow (by positivity) (by positivity)]
      congr 2
      ring
    calc ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖(f + g) ·‖ₑ) t
        ≤ ENNReal.ofReal (t ^ p.toReal⁻¹) *
            (μ.decreasingRearrangement (‖f ·‖ₑ) (2⁻¹ * t) +
              μ.decreasingRearrangement (‖g ·‖ₑ) (2⁻¹ * t)) :=
          mul_le_mul_of_nonneg_left hrearr zero_le
      _ = ENNReal.ofReal (2 ^ p.toReal⁻¹) * (F (2⁻¹ * t) + G (2⁻¹ * t)) := by
          rw [hpow]
          simp only [F, G]
          ring
  calc eLorentzNorm (f + g) p q μ
      ≤ eLpNorm (fun t ↦ ENNReal.ofReal (2 ^ p.toReal⁻¹) * (F (2⁻¹ * t) + G (2⁻¹ * t)))
          q multHaar :=
        eLpNorm_mono_eNorm_ae (measurable_eLorentzNorm_integrand (f + g) p μ).aestronglyMeasurable
          hpt
    _ = ENNReal.ofReal (2 ^ p.toReal⁻¹) *
          eLpNorm (fun t ↦ F (2⁻¹ * t) + G (2⁻¹ * t)) q multHaar :=
        eLpNorm_const_mul_ennreal ((hF.add hG).comp (measurable_const_mul _)).aestronglyMeasurable
    _ ≤ ENNReal.ofReal (2 ^ p.toReal⁻¹) *
          (eLpNorm (F ∘ (2⁻¹ * ·)) q multHaar + eLpNorm (G ∘ (2⁻¹ * ·)) q multHaar) :=
        mul_le_mul_of_nonneg_left (eLpNorm_add_le hq) zero_le
    _ = ENNReal.ofReal (2 ^ p.toReal⁻¹) * (eLorentzNorm f p q μ + eLorentzNorm g p q μ) := by
        rw [eLpNorm_comp_measurePreserving hF.aestronglyMeasurable hmp,
          eLpNorm_comp_measurePreserving hG.aestronglyMeasurable hmp]
        rfl

end Algebraic

/-! ### The weak-`Lᵖ` characterization at `q = ∞` -/

section WeakLp

variable [ENorm ε] {f : α → ε} {p : ℝ≥0∞}

/-- **Weak-`Lᵖ` supremum formula.** For every `p ∈ [0, ∞]`,
`‖f‖_{p,∞} = sup_{t > 0} t ^ (1 / p) ‖f‖*(t)`. -/
theorem eLorentzNorm_top_eq_iSup (f : α → ε) (p : ℝ≥0∞) (μ : Measure α) :
    eLorentzNorm f p ∞ μ =
      ⨆ t ∈ Ioi (0 : ℝ),
        ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t := by
  set g : ℝ → ℝ≥0∞ :=
    fun t ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t
  rw [eLorentzNorm_def, eLpNorm_exponent_top
    (measurable_eLorentzNorm_integrand f p μ).aestronglyMeasurable, eLpNormEssSup]
  simp only [eNorm_eq_self]
  refine le_antisymm (essSup_le_of_ae_le _ ?_) (iSup₂_le fun t (ht : 0 < t) ↦ ?_)
  · filter_upwards [ae_pos_multHaar] with t ht
    exact le_iSup₂_of_le t ht le_rfl
  · have hcont : ContinuousAt (fun s : ℝ ↦ ENNReal.ofReal (s ^ p.toReal⁻¹)) t :=
      ENNReal.continuous_ofReal.continuousAt.comp
        (Real.continuousAt_rpow_const t _ (Or.inl ht.ne'))
    have htend : Tendsto
        (fun s : ℝ ↦ ENNReal.ofReal (s ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t)
        (𝓝[<] t) (𝓝 (g t)) :=
      ENNReal.Tendsto.mul_const (hcont.tendsto.mono_left nhdsWithin_le_nhds)
        (Or.inl (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos ht _)).ne')
    refine le_of_tendsto htend <| eventually_of_mem (Ioo_mem_nhdsLT ht) fun s ⟨hs0, hst⟩ ↦ ?_
    have hpos : multHaar (Ico s t) ≠ 0 := by
      rw [multHaar_Ico hs0 hst.le]
      exact (ENNReal.ofReal_pos.2 (sub_pos.2 (Real.log_lt_log hs0 hst))).ne'
    have hex : ∃ u ∈ Ico s t, g u ≤ essSup g multHaar := by
      by_contra! hgt
      exact hpos <| measure_mono_null (fun u hu ↦ not_le.2 (hgt u hu))
        (ae_iff.1 (ae_le_essSup (f := g) (μ := multHaar)))
    obtain ⟨u, hu, hle⟩ := hex
    have hpow : ENNReal.ofReal (s ^ p.toReal⁻¹) ≤ ENNReal.ofReal (u ^ p.toReal⁻¹) :=
      ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow hs0.le hu.1 (inv_nonneg.2 ENNReal.toReal_nonneg))
    exact (mul_le_mul' hpow (μ.antitone_decreasingRearrangement _ hu.2.le)).trans hle

theorem eLorentzNorm_top_le_iff {C : ℝ≥0∞} :
    eLorentzNorm f p ∞ μ ≤ C ↔
      ∀ t > (0 : ℝ),
        ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t ≤ C := by
  rw [eLorentzNorm_top_eq_iSup, iSup₂_le_iff]
  rfl

/-- At `p = q = ∞`, the Lorentz gauge is the essential supremum of `‖f‖ₑ`. -/
@[simp]
theorem eLorentzNorm_top_top (f : α → ε) (μ : Measure α) :
    eLorentzNorm f ∞ ∞ μ = essSup (‖f ·‖ₑ) μ := by
  rw [eLorentzNorm_top_eq_iSup]
  simp only [ENNReal.toReal_top, inv_zero, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
  refine le_antisymm (iSup₂_le fun t _ ↦ μ.decreasingRearrangement_le_essSup _ t)
    (le_of_forall_lt fun c hc ↦ ?_)
  have hpos : 0 < μ {y | c < ‖f y‖ₑ} := by
    by_contra h0
    simp only [not_lt, nonpos_iff_eq_zero] at h0
    have hle : essSup (‖f ·‖ₑ) μ ≤ c :=
      essSup_le_of_ae_le c ((measure_eq_zero_iff_ae_notMem.1 h0).mono fun _ hy ↦ not_lt.1 hy)
    exact hle.not_gt hc
  obtain ⟨r, hr0, hrm⟩ := exists_between hpos
  have hlt : ENNReal.ofReal r.toReal < μ {y | c < ‖f y‖ₑ} := by
    rwa [ENNReal.ofReal_toReal hrm.ne_top]
  exact ((μ.lt_decreasingRearrangement_iff (f := (‖f ·‖ₑ)) (s := r.toReal) (c := c)).2 hlt).trans_le
    (le_iSup₂_of_le r.toReal (ENNReal.toReal_pos hr0.ne' hrm.ne_top) le_rfl)

/-- **Distributional form of the weak-`Lᵖ` quasi-seminorm.** For `0 < p < ∞`,
`‖f‖_{p,∞} = sup_{c ≥ 0} c μ {‖f‖ > c} ^ (1 / p)`. -/
theorem eLorentzNorm_top_eq_iSup_measure_lt (f : α → ε) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (μ : Measure α) :
    eLorentzNorm f p ∞ μ = ⨆ c : ℝ≥0∞, c * μ {y | c < ‖f y‖ₑ} ^ p.toReal⁻¹ := by
  have hr : 0 < p.toReal⁻¹ := inv_pos.2 (ENNReal.toReal_pos hp0 hp)
  refine le_antisymm ?_ (iSup_le fun c ↦ ?_)
  · rw [eLorentzNorm_top_le_iff]
    intro t ht
    rw [μ.decreasingRearrangement_def, ENNReal.mul_iSup]
    refine iSup_le fun c ↦ ?_
    rw [ENNReal.mul_iSup]
    refine iSup_le fun hct ↦ ?_
    calc ENNReal.ofReal (t ^ p.toReal⁻¹) * c
        = c * ENNReal.ofReal t ^ p.toReal⁻¹ := by
          rw [mul_comm, ENNReal.ofReal_rpow_of_pos ht]
      _ ≤ c * μ {y | c < ‖f y‖ₑ} ^ p.toReal⁻¹ := by gcongr
      _ ≤ ⨆ c : ℝ≥0∞, c * μ {y | c < ‖f y‖ₑ} ^ p.toReal⁻¹ :=
          le_iSup (fun c : ℝ≥0∞ ↦ c * μ {y | c < ‖f y‖ₑ} ^ p.toReal⁻¹) c
  · rcases eq_or_ne c 0 with rfl | hc0
    · simp
    rcases eq_or_ne (μ {y | c < ‖f y‖ₑ}) 0 with hm0 | hm0
    · simp [hm0, ENNReal.zero_rpow_of_pos hr]
    rcases eq_or_ne (μ {y | c < ‖f y‖ₑ}) ∞ with hm_top | hm_top
    · rw [hm_top, ENNReal.top_rpow_of_pos hr, ENNReal.mul_top hc0]
      have htend : Tendsto (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * c) atTop (𝓝 ∞) := by
        simpa only [Function.comp_def, ENNReal.top_mul hc0] using
          ENNReal.Tendsto.mul_const (b := c)
            (ENNReal.tendsto_ofReal_atTop.comp (tendsto_rpow_atTop hr))
            (Or.inl ENNReal.top_ne_zero)
      refine le_of_tendsto htend ?_
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      have hct : c ≤ μ.decreasingRearrangement (‖f ·‖ₑ) t :=
        ((μ.lt_decreasingRearrangement_iff (f := (‖f ·‖ₑ)) (s := t) (c := c)).2
          (hm_top ▸ ENNReal.ofReal_lt_top)).le
      exact (mul_le_mul_of_nonneg_left hct zero_le).trans (eLorentzNorm_top_le_iff.1 le_rfl t ht)
    · have hmpos : 0 < (μ {y | c < ‖f y‖ₑ}).toReal := ENNReal.toReal_pos hm0 hm_top
      have hcont :
          ContinuousAt (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹)) (μ {y | c < ‖f y‖ₑ}).toReal :=
        ENNReal.continuous_ofReal.continuousAt.comp
          (Real.continuousAt_rpow_const _ _ (Or.inl hmpos.ne'))
      have htend : Tendsto (fun t : ℝ ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * c)
          (𝓝[<] (μ {y | c < ‖f y‖ₑ}).toReal)
          (𝓝 (ENNReal.ofReal ((μ {y | c < ‖f y‖ₑ}).toReal ^ p.toReal⁻¹) * c)) :=
        ENNReal.Tendsto.mul_const (hcont.tendsto.mono_left nhdsWithin_le_nhds)
          (Or.inl (ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos hmpos _)).ne')
      have hbound : ENNReal.ofReal ((μ {y | c < ‖f y‖ₑ}).toReal ^ p.toReal⁻¹) * c ≤
          eLorentzNorm f p ∞ μ :=
        le_of_tendsto htend <| eventually_of_mem (Ioo_mem_nhdsLT hmpos) fun t ht ↦ by
          have hct : c ≤ μ.decreasingRearrangement (‖f ·‖ₑ) t :=
            ((μ.lt_decreasingRearrangement_iff (f := (‖f ·‖ₑ)) (s := t) (c := c)).2
              ((ENNReal.ofReal_lt_iff_lt_toReal ht.1.le hm_top).2 ht.2)).le
          exact (mul_le_mul_of_nonneg_left hct zero_le).trans
            (eLorentzNorm_top_le_iff.1 le_rfl t ht.1)
      rwa [← ENNReal.ofReal_rpow_of_pos hmpos, ENNReal.ofReal_toReal hm_top, mul_comm] at hbound

end WeakLp

/-! ### Indicators and monotonicity in `q` -/

section IndicatorAndMonotonicity

/-- Weak-`Lᵖ` quasi-seminorm of an indicator: `‖c 1_A‖_{p,∞} = ‖c‖ (μ A) ^ (1 / p)` for
`0 < p < ∞`. -/
theorem eLorentzNorm_indicator_top {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
    (A : Set α) (c : ε) {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) (μ : Measure α) :
    eLorentzNorm (A.indicator fun _ ↦ c) p ∞ μ = ‖c‖ₑ * μ A ^ p.toReal⁻¹ := by
  have hpr : 0 < p.toReal⁻¹ := inv_pos.2 (ENNReal.toReal_pos hp0 hp)
  have hset (r : ℝ≥0∞) :
      {y | r < ‖A.indicator (fun _ ↦ c) y‖ₑ} = if r < ‖c‖ₑ then A else ∅ := by
    ext y
    by_cases hy : y ∈ A <;> by_cases hr : r < ‖c‖ₑ <;> simp [hy, hr]
  rw [eLorentzNorm_top_eq_iSup_measure_lt _ hp0 hp]
  simp_rw [hset]
  refine le_antisymm (iSup_le fun r ↦ ?_) ?_
  · split_ifs with hr
    · exact mul_le_mul_of_nonneg_right hr.le zero_le
    · simp [ENNReal.zero_rpow_of_pos hpr]
  · refine le_of_forall_lt fun b hb ↦ ?_
    have hsup : ⨆ r : {r : ℝ≥0∞ // r < ‖c‖ₑ}, (r : ℝ≥0∞) * μ A ^ p.toReal⁻¹ =
        ‖c‖ₑ * μ A ^ p.toReal⁻¹ := by
      rw [← ENNReal.iSup_mul]
      congr 1
      refine le_antisymm (iSup_le fun r ↦ r.2.le) (le_of_forall_lt fun r hr ↦ ?_)
      obtain ⟨r', hr', hr'c⟩ := exists_between hr
      exact hr'.trans_le (le_iSup (fun x : {x : ℝ≥0∞ // x < ‖c‖ₑ} ↦ (x : ℝ≥0∞)) ⟨r', hr'c⟩)
    rw [← hsup, lt_iSup_iff] at hb
    obtain ⟨⟨r, hr⟩, hbr⟩ := hb
    exact hbr.trans_le (le_iSup_of_le r (by simp [hr]))

/-- **Lorentz gauge of an indicator.** For `0 < p < ∞` and `q ≠ 0`,
`‖c 1_A‖_{p,q} = (p / q) ^ (1 / q) ‖c‖ (μ A) ^ (1 / p)` (with the factor equal to `1` when
`q = ∞`). -/
theorem eLorentzNorm_indicator {ε : Type*} [TopologicalSpace ε] [ESeminormedAddMonoid ε]
    (A : Set α) (c : ε) {p q : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) (hq0 : q ≠ 0) (μ : Measure α) :
    eLorentzNorm (A.indicator fun _ ↦ c) p q μ =
      ENNReal.ofReal ((p.toReal / q.toReal) ^ q.toReal⁻¹) * ‖c‖ₑ * μ A ^ p.toReal⁻¹ := by
  rcases eq_or_ne q ∞ with rfl | hq
  · simpa using eLorentzNorm_indicator_top A c hp0 hp μ
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hqr : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  have hqp : 0 < q.toReal / p.toReal := div_pos hqr hpr
  have hind : (fun y ↦ ‖A.indicator (fun _ ↦ c) y‖ₑ) = A.indicator (fun _ ↦ ‖c‖ₑ) := by
    ext y
    by_cases hy : y ∈ A <;> simp [hy]
  rw [eLorentzNorm_eq_lintegral _ _ hq0 hq, hind]
  simp_rw [μ.decreasingRearrangement_indicator]
  have hS : MeasurableSet {t : ℝ | ENNReal.ofReal t < μ A} :=
    measurableSet_lt ENNReal.measurable_ofReal measurable_const
  have hcongr : (fun t : ℝ ↦ (ENNReal.ofReal (t ^ p.toReal⁻¹) *
      if ENNReal.ofReal t < μ A then ‖c‖ₑ else 0) ^ q.toReal) =ᵐ[multHaar]
      fun t : ℝ ↦ ‖c‖ₑ ^ q.toReal *
        {t : ℝ | ENNReal.ofReal t < μ A}.indicator
          (fun t ↦ ENNReal.ofReal (t ^ (q.toReal / p.toReal))) t := by
    filter_upwards [ae_pos_multHaar] with t ht
    by_cases hlt : ENNReal.ofReal t < μ A
    · have htS : t ∈ {t : ℝ | ENNReal.ofReal t < μ A} := hlt
      simp only [hlt, ↓reduceIte, indicator_of_mem htS,
        ENNReal.mul_rpow_of_nonneg _ _ hqr.le,
        ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos ht _),
        ← Real.rpow_mul ht.le, mul_comm (‖c‖ₑ ^ q.toReal), inv_mul_eq_div]
    · simp [hlt, ENNReal.zero_rpow_of_pos hqr]
  have hcancel : q.toReal / p.toReal * q.toReal⁻¹ = p.toReal⁻¹ := by field_simp
  rw [lintegral_congr_ae hcongr, lintegral_const_mul _ (by fun_prop),
    lintegral_indicator hS, setLIntegral_multHaar_ofReal_lt_rpow hqp (μ A),
    inv_div, ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hqr.le),
    ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hqr.le),
    ← ENNReal.rpow_mul, ← ENNReal.rpow_mul, mul_inv_cancel₀ hqr.ne', ENNReal.rpow_one,
    hcancel, ENNReal.ofReal_rpow_of_pos (div_pos hpr hqr), mul_left_comm, mul_assoc]

variable [ENorm ε] {f : α → ε} {p q q₀ q₁ : ℝ≥0∞}

/-- **Weak-`Lᵖ` bound by `L^{p,q}`.** For `0 < p < ∞` and `q ≠ 0`,
`‖f‖_{p,∞} ≤ (q / p) ^ (1 / q) ‖f‖_{p,q}` (with constant `1` for `q = ∞`). The constant is sharp
on every indicator of positive finite measure. -/
theorem eLorentzNorm_top_le_mul_eLorentzNorm (hp0 : p ≠ 0) (hp : p ≠ ∞) (hq0 : q ≠ 0) :
    eLorentzNorm f p ∞ μ ≤
      ENNReal.ofReal ((q.toReal / p.toReal) ^ q.toReal⁻¹) * eLorentzNorm f p q μ := by
  rcases eq_or_ne q ∞ with rfl | hq
  · simp
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hqr : 0 < q.toReal := ENNReal.toReal_pos hq0 hq
  have hqp : 0 < q.toReal / p.toReal := div_pos hqr hpr
  rw [eLorentzNorm_top_le_iff]
  intro t ht
  set c := μ.decreasingRearrangement (‖f ·‖ₑ) t
  have hsub : ∫⁻ s in {s : ℝ | ENNReal.ofReal s < ENNReal.ofReal t},
      (ENNReal.ofReal (s ^ p.toReal⁻¹) * c) ^ q.toReal ∂multHaar ≤
      ∫⁻ s, (ENNReal.ofReal (s ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) s) ^ q.toReal
        ∂multHaar := by
    refine (setLIntegral_mono_ae (by fun_prop) ?_).trans (setLIntegral_le_lintegral _ _)
    filter_upwards [ae_pos_multHaar] with s _ hlt
    gcongr
    exact μ.antitone_decreasingRearrangement _ ((ENNReal.ofReal_lt_ofReal_iff ht).1 hlt).le
  have hlhs : ∫⁻ s in {s : ℝ | ENNReal.ofReal s < ENNReal.ofReal t},
      (ENNReal.ofReal (s ^ p.toReal⁻¹) * c) ^ q.toReal ∂multHaar =
      ENNReal.ofReal (p.toReal / q.toReal) * (ENNReal.ofReal (t ^ p.toReal⁻¹) * c) ^ q.toReal := by
    have hcongr : (fun s : ℝ ↦ (ENNReal.ofReal (s ^ p.toReal⁻¹) * c) ^ q.toReal) =ᵐ[multHaar]
        fun s : ℝ ↦ c ^ q.toReal * ENNReal.ofReal (s ^ (q.toReal / p.toReal)) := by
      filter_upwards [ae_pos_multHaar] with s hs
      rw [ENNReal.mul_rpow_of_nonneg _ _ hqr.le,
        ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos hs _), ← Real.rpow_mul hs.le,
        inv_mul_eq_div, mul_comm]
    rw [lintegral_congr_ae (ae_restrict_of_ae hcongr),
      lintegral_const_mul _ (by fun_prop), setLIntegral_multHaar_ofReal_lt_rpow hqp, inv_div,
      ENNReal.mul_rpow_of_nonneg _ _ hqr.le,
      ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos ht _),
      ← Real.rpow_mul ht.le, inv_mul_eq_div, ENNReal.ofReal_rpow_of_pos ht]
    ring
  rw [hlhs] at hsub
  have hinv : q.toReal / p.toReal * (p.toReal / q.toReal) = 1 := by field_simp
  have hmul : (ENNReal.ofReal (t ^ p.toReal⁻¹) * c) ^ q.toReal ≤
      ENNReal.ofReal (q.toReal / p.toReal) *
        ∫⁻ s, (ENNReal.ofReal (s ^ p.toReal⁻¹) *
          μ.decreasingRearrangement (‖f ·‖ₑ) s) ^ q.toReal ∂multHaar := by
    calc (ENNReal.ofReal (t ^ p.toReal⁻¹) * c) ^ q.toReal
        = ENNReal.ofReal (q.toReal / p.toReal) * (ENNReal.ofReal (p.toReal / q.toReal) *
            (ENNReal.ofReal (t ^ p.toReal⁻¹) * c) ^ q.toReal) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hqp.le, hinv, ENNReal.ofReal_one, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hsub zero_le
  have hrpow := ENNReal.rpow_le_rpow hmul (inv_nonneg.2 hqr.le)
  rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hqr.ne', ENNReal.rpow_one,
    ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hqr.le),
    ENNReal.ofReal_rpow_of_pos hqp, ← eLorentzNorm_eq_lintegral f p hq0 hq μ] at hrpow
  exact hrpow

/-- **Sharp monotonicity of Lorentz gauges in the secondary exponent.** For `0 < p < ∞` and
`0 < q₀ ≤ q₁ ≤ ∞`, `‖f‖_{p, q₁} ≤ (q₀ / p) ^ (1 / q₀ - 1 / q₁) ‖f‖_{p, q₀}`. -/
theorem eLorentzNorm_le_of_le (hp0 : p ≠ 0) (hp : p ≠ ∞) (hq₀ : q₀ ≠ 0) (hq : q₀ ≤ q₁) :
    eLorentzNorm f p q₁ μ ≤
      ENNReal.ofReal ((q₀.toReal / p.toReal) ^ (q₀.toReal⁻¹ - q₁.toReal⁻¹)) *
        eLorentzNorm f p q₀ μ := by
  rcases eq_or_ne q₁ ∞ with rfl | hq₁_top
  · simpa using eLorentzNorm_top_le_mul_eLorentzNorm (f := f) (μ := μ) hp0 hp hq₀
  have hq₀_top : q₀ ≠ ∞ := ne_top_of_le_ne_top hq₁_top hq
  have hq₁ : q₁ ≠ 0 := (pos_iff_ne_zero.2 hq₀).trans_le hq |>.ne'
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  have hr₀ : 0 < q₀.toReal := ENNReal.toReal_pos hq₀ hq₀_top
  have hr₁ : 0 < q₁.toReal := ENNReal.toReal_pos hq₁ hq₁_top
  have hrle : q₀.toReal ≤ q₁.toReal := ENNReal.toReal_mono hq₁_top hq
  have hdiff : 0 ≤ q₁.toReal - q₀.toReal := sub_nonneg.2 hrle
  set g : ℝ → ℝ≥0∞ :=
    fun t ↦ ENNReal.ofReal (t ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) t
  have hpt : ∀ᵐ t ∂multHaar, g t ^ q₁.toReal ≤
      eLorentzNorm f p ∞ μ ^ (q₁.toReal - q₀.toReal) * g t ^ q₀.toReal := by
    filter_upwards [ae_pos_multHaar] with t ht
    have hgt : g t ≤ eLorentzNorm f p ∞ μ := eLorentzNorm_top_le_iff.1 le_rfl t ht
    calc g t ^ q₁.toReal = g t ^ ((q₁.toReal - q₀.toReal) + q₀.toReal) := by rw [sub_add_cancel]
      _ = g t ^ (q₁.toReal - q₀.toReal) * g t ^ q₀.toReal :=
          ENNReal.rpow_add_of_nonneg _ _ hdiff hr₀.le
      _ ≤ eLorentzNorm f p ∞ μ ^ (q₁.toReal - q₀.toReal) * g t ^ q₀.toReal := by gcongr
  have hint : ∫⁻ t, g t ^ q₁.toReal ∂multHaar ≤
      eLorentzNorm f p ∞ μ ^ (q₁.toReal - q₀.toReal) * ∫⁻ t, g t ^ q₀.toReal ∂multHaar :=
    (lintegral_mono_ae hpt).trans_eq <|
      lintegral_const_mul _ ((measurable_eLorentzNorm_integrand f p μ).pow_const _)
  have hq01 : 0 ≤ 1 - q₀.toReal / q₁.toReal := sub_nonneg.2 ((div_le_one hr₁).2 hrle)
  have hexp1 : (q₁.toReal - q₀.toReal) * q₁.toReal⁻¹ = 1 - q₀.toReal / q₁.toReal := by field_simp
  have hexp2 : q₀.toReal⁻¹ * (1 - q₀.toReal / q₁.toReal) = q₀.toReal⁻¹ - q₁.toReal⁻¹ := by
    field_simp
  have hexp3 : q₀.toReal⁻¹ * (q₀.toReal / q₁.toReal) = q₁.toReal⁻¹ := by field_simp
  calc eLorentzNorm f p q₁ μ
      = (∫⁻ t, g t ^ q₁.toReal ∂multHaar) ^ q₁.toReal⁻¹ :=
        eLorentzNorm_eq_lintegral f p hq₁ hq₁_top μ
    _ ≤ (eLorentzNorm f p ∞ μ ^ (q₁.toReal - q₀.toReal) *
          ∫⁻ t, g t ^ q₀.toReal ∂multHaar) ^ q₁.toReal⁻¹ :=
        ENNReal.rpow_le_rpow hint (inv_nonneg.2 hr₁.le)
    _ = eLorentzNorm f p ∞ μ ^ (1 - q₀.toReal / q₁.toReal) *
          eLorentzNorm f p q₀ μ ^ (q₀.toReal / q₁.toReal) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (inv_nonneg.2 hr₁.le), ← ENNReal.rpow_mul, hexp1,
          eLorentzNorm_eq_lintegral f p hq₀ hq₀_top μ, ← ENNReal.rpow_mul, hexp3]
    _ ≤ (ENNReal.ofReal ((q₀.toReal / p.toReal) ^ q₀.toReal⁻¹) * eLorentzNorm f p q₀ μ) ^
            (1 - q₀.toReal / q₁.toReal) *
          eLorentzNorm f p q₀ μ ^ (q₀.toReal / q₁.toReal) := by
        gcongr
        exact eLorentzNorm_top_le_mul_eLorentzNorm hp0 hp hq₀
    _ = ENNReal.ofReal ((q₀.toReal / p.toReal) ^ (q₀.toReal⁻¹ - q₁.toReal⁻¹)) *
          eLorentzNorm f p q₀ μ := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ hq01, mul_assoc,
          ← ENNReal.rpow_add_of_nonneg _ _ hq01 (div_nonneg hr₀.le hr₁.le), sub_add_cancel,
          ENNReal.rpow_one, ENNReal.ofReal_rpow_of_pos (Real.rpow_pos_of_pos (div_pos hr₀ hpr) _),
          ← Real.rpow_mul (div_nonneg hr₀.le hpr.le), hexp2]

end IndicatorAndMonotonicity

/-! ### Local integrability of the decreasing rearrangement -/

section Truncation

variable [ENorm ε] {f : α → ε} {p q : ℝ≥0∞}

/-- For `1 < p < ∞` and `t ≥ 0`, the integral `∫₀ᵗ ‖f‖*` is controlled by the weak-`Lᵖ`
quasi-seminorm: `∫₀ᵗ ‖f‖* ≤ (1 - 1 / p)⁻¹ t ^ (1 - 1 / p) ‖f‖_{p,∞}`. -/
theorem lintegral_decreasingRearrangement_le_mul_eLorentzNorm_top (hp₁ : 1 < p) (hp : p ≠ ∞)
    {t : ℝ} (ht : 0 ≤ t) :
    ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s ≤
      ENNReal.ofReal ((1 - p.toReal⁻¹)⁻¹ * t ^ (1 - p.toReal⁻¹)) * eLorentzNorm f p ∞ μ := by
  have h1p : (1 : ℝ) < p.toReal := by simpa using ENNReal.toReal_strict_mono hp hp₁
  have hneg : -1 < -p.toReal⁻¹ := by linarith [inv_lt_one_of_one_lt₀ h1p]
  have hpt : ∀ s ∈ Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s ≤
      ENNReal.ofReal (s ^ (-p.toReal⁻¹)) * eLorentzNorm f p ∞ μ := fun s hs ↦ by
    have hle := eLorentzNorm_top_le_iff.1 (le_refl (eLorentzNorm f p ∞ μ)) s hs.1
    calc μ.decreasingRearrangement (‖f ·‖ₑ) s
        = ENNReal.ofReal (s ^ (-p.toReal⁻¹)) *
            (ENNReal.ofReal (s ^ p.toReal⁻¹) * μ.decreasingRearrangement (‖f ·‖ₑ) s) := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (Real.rpow_nonneg hs.1.le _),
            ← Real.rpow_add hs.1, neg_add_cancel, Real.rpow_zero, ENNReal.ofReal_one, one_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_left hle zero_le
  calc ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s
      ≤ ∫⁻ s in Ioc 0 t, ENNReal.ofReal (s ^ (-p.toReal⁻¹)) * eLorentzNorm f p ∞ μ :=
        setLIntegral_mono' measurableSet_Ioc hpt
    _ = (∫⁻ s in Ioc 0 t, ENNReal.ofReal (s ^ (-p.toReal⁻¹))) * eLorentzNorm f p ∞ μ :=
        lintegral_mul_const _ (by fun_prop)
    _ = ENNReal.ofReal ((1 - p.toReal⁻¹)⁻¹ * t ^ (1 - p.toReal⁻¹)) * eLorentzNorm f p ∞ μ := by
        rw [Measure.restrict_congr_set Ioo_ae_eq_Ioc.symm, lintegral_ofReal_rpow_Ioo hneg ht,
          neg_add_eq_sub, div_eq_inv_mul]

/-- For `1 < p < ∞` and `q ≠ 0`, any function with finite Lorentz gauge `‖f‖_{p,q} < ∞` has
`∫₀ᵗ ‖f‖* < ∞` for every `t : ℝ`. -/
theorem lintegral_decreasingRearrangement_lt_top_of_eLorentzNorm_lt_top (hp₁ : 1 < p) (hp : p ≠ ∞)
    (hq : q ≠ 0) (t : ℝ) (hf : eLorentzNorm f p q μ < ∞) :
    ∫⁻ s in Ioc 0 t, μ.decreasingRearrangement (‖f ·‖ₑ) s < ∞ := by
  rcases le_total t 0 with ht | ht
  · rw [Ioc_eq_empty_of_le ht, Measure.restrict_empty, lintegral_zero_measure]
    exact ENNReal.zero_lt_top
  have htop : eLorentzNorm f p ∞ μ < ∞ :=
    (eLorentzNorm_top_le_mul_eLorentzNorm (zero_lt_one.trans hp₁).ne' hp hq).trans_lt
      (ENNReal.mul_lt_top ENNReal.ofReal_lt_top hf)
  exact (lintegral_decreasingRearrangement_le_mul_eLorentzNorm_top hp₁ hp ht).trans_lt
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top htop)

end Truncation

/-! ### The power function `t ↦ t ^ (-1 / p)` in weak `Lᵖ` -/

section PowerExample

/-- On `(0, ∞)` with Lebesgue measure, the decreasing rearrangement of `t ↦ t ^ (-1 / p)` is
itself for `0 < p < ∞` and `s > 0`. -/
theorem decreasingRearrangement_ofReal_rpow_neg_inv {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    {s : ℝ} (hs : 0 < s) :
    (volume.restrict (Ioi (0 : ℝ))).decreasingRearrangement
        (fun t : ℝ ↦ ENNReal.ofReal (t ^ (-p.toReal⁻¹))) s =
      ENNReal.ofReal (s ^ (-p.toReal⁻¹)) := by
  have hpr : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
  refine eq_of_forall_lt_iff fun c ↦ ?_
  rw [Measure.lt_decreasingRearrangement_iff]
  rcases eq_or_ne c 0 with rfl | hc0
  · have hsub : {t : ℝ | 0 < ENNReal.ofReal (t ^ (-p.toReal⁻¹))} ∩ Ioi 0 = Ioi 0 := by
      refine inter_eq_right.2 fun t (ht : 0 < t) ↦ ?_
      exact ENNReal.ofReal_pos.2 (Real.rpow_pos_of_pos ht _)
    rw [Measure.restrict_apply (measurableSet_lt measurable_const (by fun_prop)), hsub,
      Real.volume_Ioi]
    simp [Real.rpow_pos_of_pos hs]
  rcases eq_or_ne c ∞ with rfl | hc_top
  · simp
  have hcpos : 0 < c.toReal := ENNReal.toReal_pos hc0 hc_top
  have hiff (t : ℝ) (ht : 0 < t) :
      c.toReal < t ^ (-p.toReal⁻¹) ↔ t < c.toReal ^ (-p.toReal) := by
    constructor
    · intro hlt
      calc t = (t ^ (-p.toReal⁻¹)) ^ (-p.toReal) := by
            rw [← Real.rpow_mul ht.le, neg_mul_neg, inv_mul_cancel₀ hpr.ne', Real.rpow_one]
        _ < c.toReal ^ (-p.toReal) :=
            Real.rpow_lt_rpow_of_neg hcpos hlt (neg_lt_zero.2 hpr)
    · intro hlt
      calc c.toReal = (c.toReal ^ (-p.toReal)) ^ (-p.toReal⁻¹) := by
            rw [← Real.rpow_mul hcpos.le, neg_mul_neg, mul_inv_cancel₀ hpr.ne', Real.rpow_one]
        _ < t ^ (-p.toReal⁻¹) :=
            Real.rpow_lt_rpow_of_neg ht hlt (neg_lt_zero.2 (inv_pos.2 hpr))
  have hset : {t : ℝ | c < ENNReal.ofReal (t ^ (-p.toReal⁻¹))} ∩ Ioi (0 : ℝ) =
      Ioo 0 (c.toReal ^ (-p.toReal)) := by
    ext t
    simp only [mem_inter_iff, mem_ofPred_eq, mem_Ioi, mem_Ioo]
    refine ⟨fun ⟨hlt, ht⟩ ↦ ⟨ht, (hiff t ht).1 ?_⟩, fun ⟨ht, hlt⟩ ↦ ⟨?_, ht⟩⟩
    · rwa [← ENNReal.ofReal_toReal hc_top,
        ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos ht _)] at hlt
    · rw [← ENNReal.ofReal_toReal hc_top,
        ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos ht _)]
      exact (hiff t ht).2 hlt
  rw [Measure.restrict_apply (measurableSet_lt measurable_const (by fun_prop)), hset,
    Real.volume_Ioo, sub_zero, ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hcpos _)]
  conv_rhs =>
    rw [← ENNReal.ofReal_toReal hc_top,
      ENNReal.ofReal_lt_ofReal_iff (Real.rpow_pos_of_pos hs _)]
  exact (hiff s hs).symm

/-- On `(0, ∞)` with Lebesgue measure, `t ↦ t ^ (-1 / p)` has weak-`Lᵖ` quasi-seminorm `1`, for
every `0 < p < ∞`. -/
theorem eLorentzNorm_ofReal_rpow_neg_inv_top {p : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞) :
    eLorentzNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ (-p.toReal⁻¹))) p ∞ (volume.restrict (Ioi 0)) =
      1 := by
  rw [eLorentzNorm_top_eq_iSup]
  have hval : ∀ t ∈ Ioi (0 : ℝ),
      ENNReal.ofReal (t ^ p.toReal⁻¹) *
        (volume.restrict (Ioi (0 : ℝ))).decreasingRearrangement
          (fun t : ℝ ↦ ‖ENNReal.ofReal (t ^ (-p.toReal⁻¹))‖ₑ) t = 1 := fun t ht ↦ by
    simp only [eNorm_eq_self]
    rw [decreasingRearrangement_ofReal_rpow_neg_inv hp0 hp ht,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← Real.rpow_add ht, add_neg_cancel,
      Real.rpow_zero, ENNReal.ofReal_one]
  refine le_antisymm (iSup₂_le fun t ht ↦ (hval t ht).le)
    (le_iSup₂_of_le 1 one_pos (hval 1 one_pos).ge)

/-- On `(0, ∞)` with Lebesgue measure, `t ↦ t ^ (-1 / p)` has infinite `L^{p,q}` gauge for every
finite `q ≠ 0` (and in particular infinite `Lᵖ` norm), witnessing `L^{p,q} ⊊ L^{p,∞}`. -/
theorem eLorentzNorm_ofReal_rpow_neg_inv_eq_top {p q : ℝ≥0∞} (hp0 : p ≠ 0) (hp : p ≠ ∞)
    (hq0 : q ≠ 0) (hq : q ≠ ∞) :
    eLorentzNorm (fun t : ℝ ↦ ENNReal.ofReal (t ^ (-p.toReal⁻¹))) p q (volume.restrict (Ioi 0)) =
      ∞ := by
  rw [eLorentzNorm_eq_lintegral _ _ hq0 hq]
  have hcongr : (fun t : ℝ ↦ (ENNReal.ofReal (t ^ p.toReal⁻¹) *
      (volume.restrict (Ioi (0 : ℝ))).decreasingRearrangement
        (fun t : ℝ ↦ ‖ENNReal.ofReal (t ^ (-p.toReal⁻¹))‖ₑ) t) ^ q.toReal) =ᵐ[multHaar]
      fun _ ↦ (1 : ℝ≥0∞) := by
    filter_upwards [ae_pos_multHaar] with t ht
    simp only [eNorm_eq_self]
    rw [decreasingRearrangement_ofReal_rpow_neg_inv hp0 hp ht,
      ← ENNReal.ofReal_mul (Real.rpow_nonneg ht.le _), ← Real.rpow_add ht, add_neg_cancel,
      Real.rpow_zero, ENNReal.ofReal_one, ENNReal.one_rpow]
  rw [lintegral_congr_ae hcongr, lintegral_one, multHaar_univ,
    ENNReal.top_rpow_of_pos (inv_pos.2 (ENNReal.toReal_pos hq0 hq))]

end PowerExample

end TauCeti
