/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.MeasureTheory.Function.LpSeminorm.Defs
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.MeasureTheory.Measure.WithDensity
import TauCeti.Analysis.SpecialFunctions.Pow.Integral
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.MeasureTheory.Function.LpSeminorm.Lintegral

/-!
# `Lᵖ` bounds from superlevel set integrals

Let `u, v : α → ℝ≥0∞` be almost everywhere measurable functions on a measure space `(α, μ)` such
that every positive strict superlevel set `{ofReal t < u}` has finite measure and satisfies

`ofReal t * μ {ofReal t < u} ≤ A * ∫⁻ x in {ofReal t < u}, v x ∂μ`

for all `t > 0`. Then for every `1 < p < ∞`,

`∫⁻ u ^ p ∂μ ≤ (ofReal (p / (p - 1)) * A) ^ p * ∫⁻ v ^ p ∂μ`,

and in seminorm form `‖u‖_p ≤ (p / (p - 1)) * A * ‖v‖_p`. This is the distributional layer-cake
step behind Doob's `Lᵖ` maximal inequality and Hardy's inequality: unlike Marcinkiewicz
interpolation, the right-hand integral is taken over the superlevel set of `u` itself rather than
a superlevel set of `v`, yielding the sharp constant `p / (p - 1)`.

## Sharpness of the hypotheses

* The exponent range `1 < p` cannot be relaxed to `p = 1`, where `p / (p - 1)` diverges.
* On an infinite measure space, finiteness of the superlevel measures `μ {ofReal t < u}` cannot
  be dropped: for Lebesgue measure on `[1, ∞)` with `u = 1` and `v x = x ^ (-3 / 4)`, both sides
  of `t * μ {t < u} ≤ ∫⁻_{t < u} v` are `∞` for `0 < t < 1` and `0` for `t ≥ 1`, whereas
  `∫⁻ v ^ 2 < ∞` and `∫⁻ u ^ 2 = ∞`. No finiteness or σ-finiteness assumption on `μ` itself is
  needed once the positive superlevel sets of `u` have finite measure.

## Method of proof

Truncate a measurable representative `u₀` of `u` simultaneously from below at `ε > 0` and from
above at `k > ε`, setting `w x = {ofReal ε < u₀}.indicator (fun x ↦ min (u₀ x) k) x`. This
cutoff preserves the superlevel inequality at every height `t > 0` while making `∫⁻ w ^ p ∂μ`
finite. Applying the layer-cake formula to `w ^ p` under `μ` and to `w ^ (p - 1)` under
`μ.withDensity v₀` bounds `∫⁻ w ^ p ∂μ` by `(p / (p - 1)) * A * ∫⁻ v₀ * w ^ (p - 1) ∂μ` without
product measures or Tonelli's theorem. Hölder's inequality with conjugate exponents `p` and
`p / (p - 1)`, cancellation of the finite factor `(∫⁻ w ^ p ∂μ) ^ (1 - 1 / p)`, and monotone
convergence along `ε = 1 / (n + 1)`, `k = n + 1` complete the proof.

## Main statements

* `TauCeti.lintegral_rpow_le_of_mul_meas_ofReal_lt_le_mul_setLIntegral`: the `Lᵖ` lower-integral
  bound with constant `A` from strict superlevel set integrals.
* `TauCeti.lintegral_rpow_le_of_mul_meas_ofReal_lt_le_setLIntegral`: the specialization `A = 1`.
* `TauCeti.lintegral_rpow_le_of_mul_meas_ofReal_le_le_mul_setLIntegral` and
  `TauCeti.lintegral_rpow_le_of_mul_meas_ofReal_le_le_setLIntegral`: closed-superlevel variants.
* `TauCeti.eLpNorm_le_of_mul_meas_ofReal_lt_le_mul_setLIntegral`,
  `TauCeti.eLpNorm_le_of_mul_meas_ofReal_lt_le_setLIntegral`,
  `TauCeti.eLpNorm_le_of_mul_meas_ofReal_le_le_mul_setLIntegral`, and
  `TauCeti.eLpNorm_le_of_mul_meas_ofReal_le_le_setLIntegral`: `eLpNorm` forms for functions
  valued in possibly distinct `ContinuousENorm` spaces, written with `p / (p - 1)` in `ℝ≥0∞` and
  requiring no measurability assumption on the right-hand function `v`.

## References

* W. Rudin, *Real and Complex Analysis*, third edition, McGraw-Hill, 1987, Lemma 8.16.
* D. Revuz, M. Yor, *Continuous Martingales and Brownian Motion*, third edition, Springer, 1999,
  Chapter II, Lemma 1.6.
-/

public section

open Filter MeasureTheory Set Topology
open scoped ENNReal NNReal

namespace TauCeti

variable {α : Type*} [MeasurableSpace α] {μ : Measure α}

/-- Auxiliary case of `lintegral_rpow_le_of_mul_meas_ofReal_lt_le_mul_setLIntegral` for genuinely
measurable `u` and `v`. -/
private theorem lintegral_rpow_le_of_measurable {u v : α → ℝ≥0∞}
    (hu : Measurable u) (hv : Measurable v) {p : ℝ} (hp : 1 < p) {A : ℝ≥0∞}
    (hfin : ∀ t : ℝ, 0 < t → μ {x | ENNReal.ofReal t < u x} ≠ ∞)
    (hle : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * μ {x | ENNReal.ofReal t < u x} ≤
        A * ∫⁻ x in {x | ENNReal.ofReal t < u x}, v x ∂μ) :
    ∫⁻ x, u x ^ p ∂μ ≤ (ENNReal.ofReal (p / (p - 1)) * A) ^ p * ∫⁻ x, v x ^ p ∂μ := by
  have hp0 : 0 < p := zero_lt_one.trans hp
  have hp1 : 0 < p - 1 := sub_pos.2 hp
  -- Two-sided truncations at lower height `1 / (n + 1)` and upper cap `n + 1` have finite `p`-th
  -- moment and preserve the superlevel bound at every positive threshold.
  let ε : ℕ → ℝ := fun n ↦ ((n : ℝ) + 1)⁻¹
  have hεpos (n : ℕ) : 0 < ε n := by positivity
  let E : ℕ → Set α := fun n ↦ {x | ENNReal.ofReal (ε n) < u x}
  have hEm (n : ℕ) : MeasurableSet (E n) := measurableSet_lt measurable_const hu
  let w : ℕ → α → ℝ≥0∞ := fun n ↦ (E n).indicator fun x ↦ min (u x) (n + 1)
  have hwm (n : ℕ) : Measurable (w n) := (hu.min measurable_const).indicator (hEm n)
  have hwfin (n : ℕ) : ∫⁻ x, w n x ^ p ∂μ ≠ ∞ := by
    refine ne_top_of_le_ne_top
      (b := ∫⁻ x, (E n).indicator (fun _ ↦ ((n + 1 : ℕ) : ℝ≥0∞) ^ p) x ∂μ) ?_
      (lintegral_mono fun x ↦ ?_)
    · rw [lintegral_indicator_const (hEm n)]
      exact ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg hp0.le (ENNReal.natCast_ne_top _))
        (hfin (ε n) (hεpos n))
    · by_cases hx : x ∈ E n
      · simp only [w, indicator_of_mem hx, Nat.cast_add, Nat.cast_one]
        exact ENNReal.rpow_le_rpow (min_le_right _ _) hp0.le
      · simp [w, indicator_of_notMem hx, ENNReal.zero_rpow_of_pos hp0]
  -- Check that `w n` inherits the superlevel inequality for all `t > 0`.
  have hw_le (n : ℕ) (t : ℝ) (ht : 0 < t) :
      ENNReal.ofReal t * μ {x | ENNReal.ofReal t < w n x} ≤
        A * (μ.withDensity v) {x | ENNReal.ofReal t < w n x} := by
    rcases le_or_gt ((n : ℝ) + 1) t with hnt | htn
    · have hempty : {x | ENNReal.ofReal t < w n x} = ∅ := by
        ext x
        simp only [mem_ofPred_eq, mem_empty_iff_false, iff_false, not_lt]
        refine (indicator_le_self _ _ x).trans ((min_le_right _ _).trans ?_)
        simpa [ENNReal.ofReal_add] using ENNReal.ofReal_le_ofReal hnt
      simp [hempty]
    have htn' : ENNReal.ofReal t < (n : ℝ≥0∞) + 1 := by
      have hcast : ((n : ℝ≥0∞) + 1) = ENNReal.ofReal ((n : ℝ) + 1) := by
        rw [ENNReal.ofReal_add n.cast_nonneg zero_le_one, ENNReal.ofReal_natCast,
          ENNReal.ofReal_one]
      rw [hcast]
      exact (ENNReal.ofReal_lt_ofReal_iff (ht.trans htn)).2 htn
    rcases le_or_gt t (ε n) with htε | hεt
    · have hset : {x | ENNReal.ofReal t < w n x} = E n := by
        ext x
        by_cases hx : x ∈ E n
        · simp only [mem_ofPred_eq, w, indicator_of_mem hx, lt_min_iff, htn', and_true]
          exact ⟨fun _ ↦ hx, fun hx' ↦ (ENNReal.ofReal_le_ofReal htε).trans_lt hx'⟩
        · simp only [mem_ofPred_eq, w, indicator_of_notMem hx, hx, iff_false, not_lt, zero_le]
      rw [hset, withDensity_apply _ (hEm n)]
      exact (mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal htε) zero_le).trans
        (hle (ε n) (hεpos n))
    · have hset : {x | ENNReal.ofReal t < w n x} = {x | ENNReal.ofReal t < u x} := by
        ext x
        by_cases hx : x ∈ E n
        · simp [w, indicator_of_mem hx, lt_min_iff, htn']
        · have hux : u x ≤ ENNReal.ofReal (ε n) := not_lt.1 hx
          have htu : ¬ ENNReal.ofReal t < u x :=
            not_lt.2 (hux.trans (ENNReal.ofReal_le_ofReal hεt.le))
          simp [w, indicator_of_notMem hx, htu]
      rw [hset, withDensity_apply _ (measurableSet_lt measurable_const hu)]
      exact hle t ht
  -- Bound each truncated integral via two layer-cake identities and Hölder's inequality.
  have hw_bound (n : ℕ) :
      ∫⁻ x, w n x ^ p ∂μ ≤ (ENNReal.ofReal (p / (p - 1)) * A) ^ p * ∫⁻ x, v x ^ p ∂μ := by
    have hlayer1 := lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul μ (hwm n).aemeasurable hp0
    have hlayer2 := lintegral_rpow_eq_lintegral_meas_ofReal_lt_mul (μ.withDensity v)
      (hwm n).aemeasurable hp1
    have hpsplit : ENNReal.ofReal p =
        ENNReal.ofReal (p / (p - 1)) * ENNReal.ofReal (p - 1) := by
      rw [← ENNReal.ofReal_mul (div_nonneg hp0.le hp1.le), div_mul_cancel₀ _ hp1.ne']
    have hstep1 : ∫⁻ x, w n x ^ p ∂μ ≤
        ENNReal.ofReal (p / (p - 1)) * A * ∫⁻ x, v x * w n x ^ (p - 1) ∂μ := by
      have hwd : ∫⁻ x, w n x ^ (p - 1) ∂μ.withDensity v = ∫⁻ x, v x * w n x ^ (p - 1) ∂μ := by
        simpa only [Pi.mul_apply] using
          lintegral_withDensity_eq_lintegral_mul μ hv ((hwm n).pow_const (p - 1))
      rw [hlayer1, hpsplit, ← hwd]
      calc ENNReal.ofReal (p / (p - 1)) * ENNReal.ofReal (p - 1) *
            ∫⁻ t in Ioi (0 : ℝ), μ {x | ENNReal.ofReal t < w n x} * ENNReal.ofReal (t ^ (p - 1))
          ≤ ENNReal.ofReal (p / (p - 1)) * ENNReal.ofReal (p - 1) *
              ∫⁻ t in Ioi (0 : ℝ), A * ((μ.withDensity v) {x | ENNReal.ofReal t < w n x} *
                ENNReal.ofReal (t ^ (p - 1 - 1))) := by
            refine mul_le_mul_of_nonneg_left (setLIntegral_mono' measurableSet_Ioi fun t ht ↦ ?_)
              zero_le
            have ht' : 0 < t := ht
            have hpow : t ^ (p - 1) = t * t ^ (p - 1 - 1) := by
              conv_lhs => rw [show p - 1 = 1 + (p - 1 - 1) by ring]
              rw [Real.rpow_add ht', Real.rpow_one]
            calc μ {x | ENNReal.ofReal t < w n x} * ENNReal.ofReal (t ^ (p - 1))
                = ENNReal.ofReal t * μ {x | ENNReal.ofReal t < w n x} *
                    ENNReal.ofReal (t ^ (p - 1 - 1)) := by
                  rw [hpow, ENNReal.ofReal_mul ht'.le]; ring
              _ ≤ (A * (μ.withDensity v) {x | ENNReal.ofReal t < w n x}) *
                    ENNReal.ofReal (t ^ (p - 1 - 1)) :=
                  mul_le_mul_of_nonneg_right (hw_le n t ht') zero_le
              _ = A * ((μ.withDensity v) {x | ENNReal.ofReal t < w n x} *
                    ENNReal.ofReal (t ^ (p - 1 - 1))) := by ring
        _ = ENNReal.ofReal (p / (p - 1)) * A *
              (ENNReal.ofReal (p - 1) * ∫⁻ t in Ioi (0 : ℝ),
                (μ.withDensity v) {x | ENNReal.ofReal t < w n x} *
                  ENNReal.ofReal (t ^ (p - 1 - 1))) := by
            have hmeas_t : Measurable fun t : ℝ ↦
                (μ.withDensity v) {x | ENNReal.ofReal t < w n x} *
                  ENNReal.ofReal (t ^ (p - 1 - 1)) :=
              (Antitone.measurable fun _ _ h ↦ measure_mono fun _ hx ↦
                (ENNReal.ofReal_le_ofReal h).trans_lt hx).mul
                ((measurable_id.pow measurable_const).ennreal_ofReal)
            rw [lintegral_const_mul _ hmeas_t]
            ring
        _ = ENNReal.ofReal (p / (p - 1)) * A * ∫⁻ x, w n x ^ (p - 1) ∂μ.withDensity v := by
            rw [← hlayer2]
    -- Apply Hölder's inequality with conjugate exponents `p` and `p / (p - 1)`.
    have hconj : p.HolderConjugate (p / (p - 1)) := by
      rw [Real.holderConjugate_iff]
      refine ⟨hp, ?_⟩
      field_simp [hp0.ne', hp1.ne']
      ring
    have hholder : ∫⁻ x, v x * w n x ^ (p - 1) ∂μ ≤
        (∫⁻ x, v x ^ p ∂μ) ^ p⁻¹ * (∫⁻ x, w n x ^ p ∂μ) ^ (1 - p⁻¹) := by
      have hh := ENNReal.lintegral_mul_le_Lp_mul_Lq μ hconj hv.aemeasurable
        ((hwm n).pow_const (p - 1)).aemeasurable
      have hexp1 : 1 / p = p⁻¹ := one_div p
      have hexp2 : 1 / (p / (p - 1)) = 1 - p⁻¹ := by
        field_simp [hp0.ne']
      have hwpow : (fun x ↦ (w n x ^ (p - 1)) ^ (p / (p - 1))) = fun x ↦ w n x ^ p := by
        ext x
        rw [← ENNReal.rpow_mul, mul_div_cancel₀ _ hp1.ne']
      simpa only [Pi.mul_apply, hexp1, hexp2, hwpow] using hh
    have hcomb : ∫⁻ x, w n x ^ p ∂μ ≤
        (ENNReal.ofReal (p / (p - 1)) * A * (∫⁻ x, v x ^ p ∂μ) ^ p⁻¹) *
          (∫⁻ x, w n x ^ p ∂μ) ^ (1 - p⁻¹) :=
      hstep1.trans ((mul_le_mul_of_nonneg_left hholder zero_le).trans_eq (mul_assoc _ _ _).symm)
    have hcancel := ENNReal.rpow_one_sub_le_of_le_mul_rpow
      (show 1 - p⁻¹ < 1 by linarith [inv_pos.2 hp0]) (hwfin n) hcomb
    rw [sub_sub_cancel] at hcancel
    have hrpow := ENNReal.rpow_le_rpow hcancel hp0.le
    rwa [ENNReal.rpow_inv_rpow hp0.ne', ENNReal.mul_rpow_of_nonneg _ _ hp0.le,
      ENNReal.rpow_inv_rpow hp0.ne'] at hrpow
  -- Pass to the supremum over `n`.
  have hwmono : Monotone w := fun m n hmn x ↦ by
    have hEsub : E m ⊆ E n := fun y hy ↦
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal (by
        dsimp [ε]
        gcongr)) hy
    by_cases hx : x ∈ E m
    · simp only [w, indicator_of_mem hx, indicator_of_mem (hEsub hx)]
      exact min_le_min_left _ (by gcongr)
    · simp [w, indicator_of_notMem hx]
  have hwsup (x : α) : u x ^ p = ⨆ n, w n x ^ p := by
    have hux : u x = ⨆ n, w n x := by
      refine le_antisymm (le_of_forall_lt fun c hc ↦ ?_)
        (iSup_le fun n ↦ indicator_le (fun _ _ ↦ min_le_left _ _) x)
      rcases eq_or_ne c 0 with rfl | hc0
      · rcases eq_or_ne (u x) ∞ with htop | htop
        · refine lt_iSup_iff.2 ⟨0, ?_⟩
          have hxE : x ∈ E 0 := by simp [E, ε, htop]
          simp [w, indicator_of_mem hxE, htop]
        · obtain ⟨N, hN⟩ := exists_nat_one_div_lt (ENNReal.toReal_pos hc.ne' htop)
          have hxE : x ∈ E N := by
            dsimp [E, ε]
            simpa [one_div, ENNReal.ofReal_toReal htop] using
              (ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_pos hc.ne' htop)).2 hN
          refine lt_iSup_iff.2 ⟨N, ?_⟩
          simp only [w, indicator_of_mem hxE]
          exact lt_min hc (by positivity)
      · obtain ⟨N₁, hN₁⟩ := ENNReal.exists_nat_gt hc.ne_top
        obtain ⟨N₂, hN₂⟩ := exists_nat_one_div_lt (ENNReal.toReal_pos hc0 hc.ne_top)
        let N := max N₁ N₂
        have hxE : x ∈ E N := by
          dsimp [E, ε]
          have hlt : ((N : ℝ) + 1)⁻¹ < c.toReal :=
            (by gcongr; exact le_max_right N₁ N₂ : ((N : ℝ) + 1)⁻¹ ≤ ((N₂ : ℝ) + 1)⁻¹).trans_lt
              (by simpa [one_div] using hN₂)
          exact ((ENNReal.ofReal_lt_ofReal_iff (ENNReal.toReal_pos hc0 hc.ne_top)).2 hlt).trans
            (by simpa [ENNReal.ofReal_toReal hc.ne_top] using hc)
        refine lt_iSup_iff.2 ⟨N, ?_⟩
        simp only [w, indicator_of_mem hxE]
        exact lt_min hc (hN₁.trans_le (le_add_right (by exact_mod_cast le_max_left N₁ N₂)))
    rw [hux]
    exact Monotone.map_iSup_of_continuousAt ENNReal.continuous_rpow_const.continuousAt
      (ENNReal.monotone_rpow_of_nonneg hp0.le) (ENNReal.zero_rpow_of_pos hp0)
  calc ∫⁻ x, u x ^ p ∂μ = ∫⁻ x, ⨆ n, w n x ^ p ∂μ := by simp_rw [hwsup]
    _ = ⨆ n, ∫⁻ x, w n x ^ p ∂μ :=
        lintegral_iSup (fun n ↦ (hwm n).pow_const p) fun m n hmn x ↦
          ENNReal.rpow_le_rpow (hwmono hmn x) hp0.le
    _ ≤ (ENNReal.ofReal (p / (p - 1)) * A) ^ p * ∫⁻ x, v x ^ p ∂μ := iSup_le hw_bound

/-- **`Lᵖ` lower-integral bound from superlevel set integrals.** If `u, v : α → ℝ≥0∞` are almost
everywhere measurable, every positive strict superlevel set of `u` has finite measure, and
`ofReal t * μ {ofReal t < u} ≤ A * ∫⁻_{ofReal t < u} v ∂μ` for all `t > 0`, then
`∫⁻ u ^ p ∂μ ≤ (ofReal (p / (p - 1)) * A) ^ p * ∫⁻ v ^ p ∂μ` for every `p > 1`. -/
theorem lintegral_rpow_le_of_mul_meas_ofReal_lt_le_mul_setLIntegral
    {u v : α → ℝ≥0∞} (hu : AEMeasurable u μ) (hv : AEMeasurable v μ)
    {p : ℝ} (hp : 1 < p) {A : ℝ≥0∞}
    (hfin : ∀ t : ℝ, 0 < t → μ {x | ENNReal.ofReal t < u x} ≠ ∞)
    (hle : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * μ {x | ENNReal.ofReal t < u x} ≤
        A * ∫⁻ x in {x | ENNReal.ofReal t < u x}, v x ∂μ) :
    ∫⁻ x, u x ^ p ∂μ ≤ (ENNReal.ofReal (p / (p - 1)) * A) ^ p * ∫⁻ x, v x ^ p ∂μ := by
  -- Reduce from `AEMeasurable` functions to their measurable representatives `hu.mk u`, `hv.mk v`.
  have hset (t : ℝ) :
      {x | ENNReal.ofReal t < hu.mk u x} =ᵐ[μ] {x | ENNReal.ofReal t < u x} := by
    filter_upwards [hu.ae_eq_mk] with x hx
    simp [hx]
  have hup : ∫⁻ x, u x ^ p ∂μ = ∫⁻ x, hu.mk u x ^ p ∂μ :=
    lintegral_congr_ae (hu.ae_eq_mk.mono fun _ hx ↦ by simp [hx])
  have hvp : ∫⁻ x, v x ^ p ∂μ = ∫⁻ x, hv.mk v x ^ p ∂μ :=
    lintegral_congr_ae (hv.ae_eq_mk.mono fun _ hx ↦ by simp [hx])
  rw [hup, hvp]
  refine lintegral_rpow_le_of_measurable hu.measurable_mk hv.measurable_mk hp
    (fun t ht ↦ by rw [measure_congr (hset t)]; exact hfin t ht) (fun t ht ↦ ?_)
  rw [measure_congr (hset t)]
  refine (hle t ht).trans (mul_le_mul_of_nonneg_left (le_of_eq ?_) zero_le)
  exact (setLIntegral_congr (hset t).symm).trans
    (lintegral_congr_ae (ae_restrict_of_ae hv.ae_eq_mk))

/-- **`Lᵖ` lower-integral bound from superlevel set integrals (`A = 1`).** If every positive strict
superlevel set of `u` has finite measure and `ofReal t * μ {ofReal t < u} ≤ ∫⁻_{ofReal t < u} v ∂μ`
for all `t > 0`, then `∫⁻ u ^ p ∂μ ≤ ofReal (p / (p - 1)) ^ p * ∫⁻ v ^ p ∂μ` for every `p > 1`. -/
theorem lintegral_rpow_le_of_mul_meas_ofReal_lt_le_setLIntegral
    {u v : α → ℝ≥0∞} (hu : AEMeasurable u μ) (hv : AEMeasurable v μ)
    {p : ℝ} (hp : 1 < p)
    (hfin : ∀ t : ℝ, 0 < t → μ {x | ENNReal.ofReal t < u x} ≠ ∞)
    (hle : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * μ {x | ENNReal.ofReal t < u x} ≤
        ∫⁻ x in {x | ENNReal.ofReal t < u x}, v x ∂μ) :
    ∫⁻ x, u x ^ p ∂μ ≤ ENNReal.ofReal (p / (p - 1)) ^ p * ∫⁻ x, v x ^ p ∂μ := by
  simpa only [mul_one, one_mul] using
    lintegral_rpow_le_of_mul_meas_ofReal_lt_le_mul_setLIntegral hu hv hp hfin
      (A := 1) (fun t ht ↦ by simpa only [one_mul] using hle t ht)

/-- **`Lᵖ` lower-integral bound from closed superlevel set integrals.** Exhausting strict
superlevel sets `{ofReal t < u}` by closed ones `{ofReal (t + 1 / (n + 1)) ≤ u}` reduces closed
threshold bounds to strict ones. -/
theorem lintegral_rpow_le_of_mul_meas_ofReal_le_le_mul_setLIntegral
    {u v : α → ℝ≥0∞} (hu : AEMeasurable u μ) (hv : AEMeasurable v μ)
    {p : ℝ} (hp : 1 < p) {A : ℝ≥0∞}
    (hfin : ∀ t : ℝ, 0 < t → μ {x | ENNReal.ofReal t < u x} ≠ ∞)
    (hle : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * μ {x | ENNReal.ofReal t ≤ u x} ≤
        A * ∫⁻ x in {x | ENNReal.ofReal t ≤ u x}, v x ∂μ) :
    ∫⁻ x, u x ^ p ∂μ ≤ (ENNReal.ofReal (p / (p - 1)) * A) ^ p * ∫⁻ x, v x ^ p ∂μ := by
  refine lintegral_rpow_le_of_mul_meas_ofReal_lt_le_mul_setLIntegral hu hv hp hfin fun t ht ↦ ?_
  let B : ℕ → Set α := fun n ↦ {x | ENNReal.ofReal (t + ((n : ℝ) + 1)⁻¹) ≤ u x}
  have hmono : Monotone B := fun i j hij x hx ↦
    (ENNReal.ofReal_le_ofReal (by gcongr)).trans hx
  have hsub (n : ℕ) : B n ⊆ {x | ENNReal.ofReal t < u x} := fun x hx ↦
    lt_of_lt_of_le ((ENNReal.ofReal_lt_ofReal_iff (by positivity)).2
      (lt_add_of_pos_right t (by positivity))) hx
  have hUnion : (⋃ n, B n) = {x | ENNReal.ofReal t < u x} := by
    refine Subset.antisymm (iUnion_subset hsub) fun x hx ↦ ?_
    simp only [mem_ofPred_eq] at hx
    rcases eq_or_ne (u x) ∞ with htop | htop
    · exact mem_iUnion.2 ⟨0, by simp [B, htop]⟩
    · have hpos : 0 < (u x).toReal := ENNReal.toReal_pos (zero_le.trans_lt hx).ne' htop
      have hux : t < (u x).toReal := by
        rw [← ENNReal.ofReal_toReal htop] at hx
        exact (ENNReal.ofReal_lt_ofReal_iff hpos).1 hx
      obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.2 hux)
      rw [one_div] at hn
      refine mem_iUnion.2 ⟨n, ?_⟩
      simp only [B, mem_ofPred_eq]
      rw [← ENNReal.ofReal_toReal htop]
      exact ENNReal.ofReal_le_ofReal (by linarith)
  rw [← hUnion, hmono.measure_iUnion, ENNReal.mul_iSup]
  refine iSup_le fun n ↦ ?_
  calc ENNReal.ofReal t * μ (B n)
      ≤ ENNReal.ofReal (t + ((n : ℝ) + 1)⁻¹) * μ (B n) :=
        mul_le_mul_of_nonneg_right
          (ENNReal.ofReal_le_ofReal (le_add_of_nonneg_right (by positivity))) zero_le
    _ ≤ A * ∫⁻ x in B n, v x ∂μ := hle _ (by positivity)
    _ ≤ A * ∫⁻ x in ⋃ k, B k, v x ∂μ :=
        mul_le_mul_of_nonneg_left (lintegral_mono_set (subset_iUnion B n)) zero_le

/-- **`Lᵖ` lower-integral bound from closed superlevel set integrals (`A = 1`).** -/
theorem lintegral_rpow_le_of_mul_meas_ofReal_le_le_setLIntegral
    {u v : α → ℝ≥0∞} (hu : AEMeasurable u μ) (hv : AEMeasurable v μ)
    {p : ℝ} (hp : 1 < p)
    (hfin : ∀ t : ℝ, 0 < t → μ {x | ENNReal.ofReal t < u x} ≠ ∞)
    (hle : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * μ {x | ENNReal.ofReal t ≤ u x} ≤
        ∫⁻ x in {x | ENNReal.ofReal t ≤ u x}, v x ∂μ) :
    ∫⁻ x, u x ^ p ∂μ ≤ ENNReal.ofReal (p / (p - 1)) ^ p * ∫⁻ x, v x ^ p ∂μ := by
  simpa only [mul_one, one_mul] using
    lintegral_rpow_le_of_mul_meas_ofReal_le_le_mul_setLIntegral hu hv hp hfin
      (A := 1) (fun t ht ↦ by simpa only [one_mul] using hle t ht)

section ELpNorm

variable {ε₁ ε₂ : Type*} [TopologicalSpace ε₁] [ContinuousENorm ε₁]
  [TopologicalSpace ε₂] [ContinuousENorm ε₂]

/-- **`Lᵖ` seminorm bound from superlevel set integrals.** For `1 < p < ∞`, an almost everywhere
strongly measurable function `u`, and any function `v` valued in a possibly distinct
`ContinuousENorm` space, if every positive strict superlevel set of `‖u‖ₑ` has finite measure and
satisfies `ofReal t * μ {ofReal t < ‖u‖ₑ} ≤ A * ∫⁻_{ofReal t < ‖u‖ₑ} ‖v‖ₑ ∂μ` for all `t > 0`,
then `eLpNorm u p μ ≤ p / (p - 1) * A * eLpNorm v p μ`. Measurability is needed only for `u`
(without it `eLpNorm u p μ = ∞` by convention); when `v` is not `AEStronglyMeasurable` and `A ≠ 0`,
`eLpNorm v p μ = ∞` makes the right-hand side `∞`. -/
theorem eLpNorm_le_of_mul_meas_ofReal_lt_le_mul_setLIntegral
    {u : α → ε₁} {v : α → ε₂} (hu : AEStronglyMeasurable u μ)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) {A : ℝ≥0∞}
    (hfin : ∀ t : ℝ, 0 < t → μ {x | ENNReal.ofReal t < ‖u x‖ₑ} ≠ ∞)
    (hle : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * μ {x | ENNReal.ofReal t < ‖u x‖ₑ} ≤
        A * ∫⁻ x in {x | ENNReal.ofReal t < ‖u x‖ₑ}, ‖v x‖ₑ ∂μ) :
    eLpNorm u p μ ≤ p / (p - 1) * A * eLpNorm v p μ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hpr : 1 < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp
  rcases eq_or_ne A 0 with rfl | hA0
  · have hint := lintegral_rpow_le_of_mul_meas_ofReal_lt_le_mul_setLIntegral
      hu.eNorm (v := 0) (A := 0) measurable_const.aemeasurable hpr hfin fun t ht ↦ by
        simpa using hle t ht
    simp only [mul_zero, zero_mul, ENNReal.zero_rpow_of_pos (zero_lt_one.trans hpr)] at hint
    refine (eLpNorm_le_of_lintegral_rpow_le hp0 hp_top hu ?_).trans zero_le
    rwa [ENNReal.zero_rpow_of_pos (zero_lt_one.trans hpr)]
  by_cases hv : AEStronglyMeasurable v μ
  · have hconst : ENNReal.ofReal (p.toReal / (p.toReal - 1)) = p / (p - 1) := by
      rw [ENNReal.ofReal_div_of_pos (sub_pos.2 hpr), ENNReal.ofReal_sub _ zero_le_one,
        ENNReal.ofReal_toReal hp_top, ENNReal.ofReal_one]
    have hint := lintegral_rpow_le_of_mul_meas_ofReal_lt_le_mul_setLIntegral
      hu.eNorm hv.eNorm hpr hfin hle
    rw [hconst, lintegral_rpow_enorm_eq_eLpNorm_rpow hp0 hp_top hv,
      ← ENNReal.mul_rpow_of_nonneg _ _ (zero_lt_one.trans hpr).le] at hint
    exact eLpNorm_le_of_lintegral_rpow_le hp0 hp_top hu hint
  · rw [eLpNorm_of_not_aestronglyMeasurable hv]
    have hc_ne0 : p / (p - 1) ≠ 0 :=
      ENNReal.div_ne_zero.2 ⟨hp0, ENNReal.sub_ne_top hp_top⟩
    rw [ENNReal.mul_top (mul_ne_zero hc_ne0 hA0)]
    exact le_top

/-- **`Lᵖ` seminorm bound from superlevel set integrals (`A = 1`).** -/
theorem eLpNorm_le_of_mul_meas_ofReal_lt_le_setLIntegral
    {u : α → ε₁} {v : α → ε₂} (hu : AEStronglyMeasurable u μ)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞)
    (hfin : ∀ t : ℝ, 0 < t → μ {x | ENNReal.ofReal t < ‖u x‖ₑ} ≠ ∞)
    (hle : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * μ {x | ENNReal.ofReal t < ‖u x‖ₑ} ≤
        ∫⁻ x in {x | ENNReal.ofReal t < ‖u x‖ₑ}, ‖v x‖ₑ ∂μ) :
    eLpNorm u p μ ≤ p / (p - 1) * eLpNorm v p μ := by
  simpa only [mul_one, one_mul] using
    eLpNorm_le_of_mul_meas_ofReal_lt_le_mul_setLIntegral hu hp hp_top hfin
      (A := 1) (fun t ht ↦ by simpa only [one_mul] using hle t ht)

/-- **`Lᵖ` seminorm bound from closed superlevel set integrals.** -/
theorem eLpNorm_le_of_mul_meas_ofReal_le_le_mul_setLIntegral
    {u : α → ε₁} {v : α → ε₂} (hu : AEStronglyMeasurable u μ)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞) {A : ℝ≥0∞}
    (hfin : ∀ t : ℝ, 0 < t → μ {x | ENNReal.ofReal t < ‖u x‖ₑ} ≠ ∞)
    (hle : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * μ {x | ENNReal.ofReal t ≤ ‖u x‖ₑ} ≤
        A * ∫⁻ x in {x | ENNReal.ofReal t ≤ ‖u x‖ₑ}, ‖v x‖ₑ ∂μ) :
    eLpNorm u p μ ≤ p / (p - 1) * A * eLpNorm v p μ := by
  have hp0 : p ≠ 0 := (zero_lt_one.trans hp).ne'
  have hpr : 1 < p.toReal := by
    rw [← ENNReal.toReal_one]
    exact (ENNReal.toReal_lt_toReal ENNReal.one_ne_top hp_top).2 hp
  rcases eq_or_ne A 0 with rfl | hA0
  · have hint := lintegral_rpow_le_of_mul_meas_ofReal_le_le_mul_setLIntegral
      hu.eNorm (v := 0) (A := 0) measurable_const.aemeasurable hpr hfin fun t ht ↦ by
        simpa using hle t ht
    simp only [mul_zero, zero_mul, ENNReal.zero_rpow_of_pos (zero_lt_one.trans hpr)] at hint
    refine (eLpNorm_le_of_lintegral_rpow_le hp0 hp_top hu ?_).trans zero_le
    rwa [ENNReal.zero_rpow_of_pos (zero_lt_one.trans hpr)]
  by_cases hv : AEStronglyMeasurable v μ
  · have hconst : ENNReal.ofReal (p.toReal / (p.toReal - 1)) = p / (p - 1) := by
      rw [ENNReal.ofReal_div_of_pos (sub_pos.2 hpr), ENNReal.ofReal_sub _ zero_le_one,
        ENNReal.ofReal_toReal hp_top, ENNReal.ofReal_one]
    have hint := lintegral_rpow_le_of_mul_meas_ofReal_le_le_mul_setLIntegral
      hu.eNorm hv.eNorm hpr hfin hle
    rw [hconst, lintegral_rpow_enorm_eq_eLpNorm_rpow hp0 hp_top hv,
      ← ENNReal.mul_rpow_of_nonneg _ _ (zero_lt_one.trans hpr).le] at hint
    exact eLpNorm_le_of_lintegral_rpow_le hp0 hp_top hu hint
  · rw [eLpNorm_of_not_aestronglyMeasurable hv]
    have hc_ne0 : p / (p - 1) ≠ 0 :=
      ENNReal.div_ne_zero.2 ⟨hp0, ENNReal.sub_ne_top hp_top⟩
    rw [ENNReal.mul_top (mul_ne_zero hc_ne0 hA0)]
    exact le_top

/-- **`Lᵖ` seminorm bound from closed superlevel set integrals (`A = 1`).** -/
theorem eLpNorm_le_of_mul_meas_ofReal_le_le_setLIntegral
    {u : α → ε₁} {v : α → ε₂} (hu : AEStronglyMeasurable u μ)
    {p : ℝ≥0∞} (hp : 1 < p) (hp_top : p ≠ ∞)
    (hfin : ∀ t : ℝ, 0 < t → μ {x | ENNReal.ofReal t < ‖u x‖ₑ} ≠ ∞)
    (hle : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal t * μ {x | ENNReal.ofReal t ≤ ‖u x‖ₑ} ≤
        ∫⁻ x in {x | ENNReal.ofReal t ≤ ‖u x‖ₑ}, ‖v x‖ₑ ∂μ) :
    eLpNorm u p μ ≤ p / (p - 1) * eLpNorm v p μ := by
  simpa only [mul_one, one_mul] using
    eLpNorm_le_of_mul_meas_ofReal_le_le_mul_setLIntegral hu hp hp_top hfin
      (A := 1) (fun t ht ↦ by simpa only [one_mul] using hle t ht)

end ELpNorm

end TauCeti
