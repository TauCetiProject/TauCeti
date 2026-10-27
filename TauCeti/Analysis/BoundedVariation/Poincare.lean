/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Translation
public import Mathlib.MeasureTheory.Integral.Average
public import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Group.LIntegral
import TauCeti.MeasureTheory.Integral.Average
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace

/-!
# The Poincaré inequality for functions of bounded variation

Let `Ω` be a convex open set of a finite-dimensional real inner product space `E` of dimension
`n`, with an additive Haar measure `μ`, and let `u` be locally integrable on `Ω`. This file proves
the `L¹` **Poincaré inequality** for `u` in terms of its variational total variation
`|Du|(Ω) = TauCeti.totalVariationOn μ Ω u`: for every `S ⊆ Ω` of finite positive measure,

`∫_Ω |u - ⨍_S u| ≤ (∫_{Ω - Ω} ‖h‖ dh) / μ(S) · |Du|(Ω)`.

For bounded `Ω` the constant is at most `μ(B(0, 1)) (diam Ω) ^ (n + 1) / μ(S)`, and on a ball of
radius `R`, averaging over the ball itself, it is at most `2 ^ (n + 1) R`. These are the constants
of the Poincaré–Wirtinger inequality on `W^{1,p}`,
`TauCeti.W1p.eLpNorm_value_sub_setAverage_le_of_convex`, whose case `p = 1` the present statements
extend to functions of bounded variation: no derivative, no integrability on `Ω` and no
finiteness of `|Du|(Ω)` is assumed, both sides may be infinite, and `S` need not be measurable.
For a `W^{1,1}` function the variation is the `L¹` norm of the weak gradient
(`TauCeti.HasWeakFDerivOn.totalVariationOn_eq_setLIntegral_enorm`).

The proof averages the translation estimate
`TauCeti.setLIntegral_enorm_comp_add_sub_le_mul_totalVariationOn`. Writing `y = x + h`,

`∫_Ω ∫_Ω |u x - u y| dy dx = ∫_{Ω - Ω} ∫_{Ω ∩ (Ω - h)} |u (x + h) - u x| dx dh`,

and by convexity of `Ω` the segment from `x` to `x + h` lies in `Ω` whenever both endpoints do, so
the inner integral is at most `‖h‖ |Du|(Ω)`. Averaging `|u x - u y|` over `y ∈ S` then bounds the
deviation of `u x` from the mean of `u` over `S`.

## Main results

* `TauCeti.setLIntegral_setLIntegral_enorm_sub_le_mul_totalVariationOn`: the double-integral
  estimate `∫_Ω ∫_Ω |u x - u y| ≤ (∫_{Ω - Ω} ‖h‖) |Du|(Ω)` on a convex open set.
* `TauCeti.setLIntegral_enorm_sub_setAverage_le_mul_totalVariationOn`: the Poincaré inequality on
  a convex open set, with constant `(∫_{Ω - Ω} ‖h‖) / μ(S)`.
* `TauCeti.setLIntegral_enorm_sub_setAverage_le_mul_totalVariationOn_of_convex`: the Poincaré
  inequality on a bounded convex open set, with constant `μ(B(0, 1)) (diam Ω) ^ (n + 1) / μ(S)`.
* `TauCeti.setLIntegral_enorm_sub_setAverage_le_mul_totalVariationOn_of_eq_ball`: the Poincaré
  inequality on a ball of radius `R`, with constant `2 ^ (n + 1) R`.

## References

* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.6.2 (Poincaré's inequality for functions of bounded variation).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  equation (7.45), for the constant on convex sets.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Set Metric TopologicalSpace Module
open scoped ENNReal Pointwise

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {u : E → ℝ} {S : Set E}

/-- The double-integral estimate for a measurable function, in the substituted form
`∫_Ω ∫_Ω |u y - u x| dy dx` with `y = x + h`. -/
private theorem setLIntegral_setLIntegral_enorm_sub_le_of_measurable
    (hconv : Convex ℝ (Ω : Set E)) (hu : LocallyIntegrableOn u Ω μ) (hum : Measurable u) :
    ∫⁻ x in Ω, ∫⁻ y in Ω, ‖u y - u x‖ₑ ∂μ ∂μ ≤
      (∫⁻ h in (Ω : Set E) - Ω, ‖h‖ₑ ∂μ) * totalVariationOn μ Ω u := by
  set U : Set E := (Ω : Set E)
  have hU : MeasurableSet U := Ω.isOpen.measurableSet
  set F : E → E → ℝ≥0∞ := fun x h => U.indicator (fun y => ‖u y - u x‖ₑ) (x + h)
  -- The substitution `y = x + h` in the inner integral.
  have hsub : ∀ x, ∫⁻ y in U, ‖u y - u x‖ₑ ∂μ = ∫⁻ h, F x h ∂μ := fun x => by
    rw [← lintegral_indicator hU]
    exact (lintegral_add_left_eq_self _ x).symm
  have hFm : Measurable (Function.uncurry F) := by
    have hset : MeasurableSet {p : E × E | p.1 + p.2 ∈ U} :=
      (measurable_fst.add measurable_snd) hU
    have hg : Measurable fun p : E × E => ‖u (p.1 + p.2) - u p.1‖ₑ :=
      ((hum.comp (measurable_fst.add measurable_snd)).sub (hum.comp measurable_fst)).enorm
    have hF_eq : Function.uncurry F =
        {p : E × E | p.1 + p.2 ∈ U}.indicator fun p => ‖u (p.1 + p.2) - u p.1‖ₑ := by
      ext ⟨x, h⟩
      by_cases hxh : x + h ∈ U <;> simp [F, hxh]
    rw [hF_eq]
    exact hg.indicator hset
  -- For a fixed translation `h`, the inner integral is at most `‖h‖ |Du|(Ω)`, and it vanishes
  -- unless `h ∈ Ω - Ω`.
  have hinner : ∀ h, ∫⁻ x in U, F x h ∂μ ≤
      (U - U).indicator (fun h => ‖h‖ₑ) h * totalVariationOn μ Ω u := fun h => by
    by_cases hh : h ∈ U - U
    · rw [indicator_of_mem hh]
      let V : Opens E := Ω ⊓ Opens.comap (ContinuousMap.addRight h) Ω
      have hV : (V : Set E) = (· + h) ⁻¹' U ∩ U := by
        ext x
        simp [V, U, and_comm]
      calc ∫⁻ x in U, F x h ∂μ
          = ∫⁻ x in U, ((· + h) ⁻¹' U).indicator (fun x => ‖u (x + h) - u x‖ₑ) x ∂μ :=
            lintegral_congr fun x => by by_cases hxh : x + h ∈ U <;> simp [F, hxh]
        _ = ∫⁻ x in V, ‖u (x + h) - u x‖ₑ ∂μ := by
            rw [setLIntegral_indicator (hU.preimage (measurable_add_const h)), hV]
        _ ≤ ‖h‖ₑ * totalVariationOn μ Ω u := by
            refine setLIntegral_enorm_comp_add_sub_le_mul_totalVariationOn hu fun t ht x hx => ?_
            have hx' : x ∈ (V : Set E) := hx
            rw [hV] at hx'
            exact hconv.add_smul_mem hx'.2 hx'.1 ht
    · -- If `x ∈ Ω` and `x + h ∈ Ω`, then `h ∈ Ω - Ω`.
      have hzero : EqOn (fun x => F x h) (fun _ => 0) U := fun x hx =>
        indicator_of_notMem (fun hxh => hh ⟨x + h, hxh, x, hx, add_sub_cancel_left x h⟩) _
      rw [setLIntegral_congr_fun hU hzero, lintegral_zero]
      exact zero_le
  calc ∫⁻ x in U, ∫⁻ y in U, ‖u y - u x‖ₑ ∂μ ∂μ
      = ∫⁻ x in U, ∫⁻ h, F x h ∂μ ∂μ := by simp_rw [hsub]
    _ = ∫⁻ h, ∫⁻ x in U, F x h ∂μ ∂μ :=
        lintegral_lintegral_swap hFm.aemeasurable
    _ ≤ ∫⁻ h, (U - U).indicator (fun h => ‖h‖ₑ) h * totalVariationOn μ Ω u ∂μ :=
        lintegral_mono hinner
    _ = (∫⁻ h in U - U, ‖h‖ₑ ∂μ) * totalVariationOn μ Ω u := by
        have hUU : MeasurableSet (U - U) := (Ω.isOpen.sub_left).measurableSet
        rw [lintegral_mul_const _ (measurable_enorm.indicator hUU), lintegral_indicator hUU]

/-- **The double-integral estimate.** On a convex open set `Ω`, a locally integrable `u`
satisfies `∫_Ω ∫_Ω |u x - u y| ≤ (∫_{Ω - Ω} ‖h‖) |Du|(Ω)`, where `|Du|(Ω)` is the total
variation of `u` on `Ω`. Both sides may be infinite. -/
theorem setLIntegral_setLIntegral_enorm_sub_le_mul_totalVariationOn
    (hconv : Convex ℝ (Ω : Set E)) (hu : LocallyIntegrableOn u Ω μ) :
    ∫⁻ x in Ω, ∫⁻ y in Ω, ‖u x - u y‖ₑ ∂μ ∂μ ≤
      (∫⁻ h in (Ω : Set E) - Ω, ‖h‖ₑ ∂μ) * totalVariationOn μ Ω u := by
  -- Replace `u` by a measurable function equal to it almost everywhere on `Ω`.
  have hm := hu.aestronglyMeasurable
  set v := hm.mk u
  have hv : u =ᵐ[μ.restrict Ω] v := hm.ae_eq_mk
  rw [totalVariationOn_congr_ae hv]
  calc ∫⁻ x in Ω, ∫⁻ y in Ω, ‖u x - u y‖ₑ ∂μ ∂μ = ∫⁻ x in Ω, ∫⁻ y in Ω, ‖v y - v x‖ₑ ∂μ ∂μ := by
        refine lintegral_congr_ae ?_
        filter_upwards [hv] with x hx
        refine lintegral_congr_ae ?_
        filter_upwards [hv] with y hy
        rw [hx, hy, enorm_sub_rev]
    _ ≤ _ := setLIntegral_setLIntegral_enorm_sub_le_of_measurable hconv (hu.congr hv)
        hm.stronglyMeasurable_mk.measurable

/-- **The Poincaré inequality for functions of bounded variation on a convex set.** Let `u` be
locally integrable on a convex open set `Ω` and let `S ⊆ Ω` have finite positive measure. Then
`∫_Ω |u - ⨍_S u| ≤ (∫_{Ω - Ω} ‖h‖) / μ(S) · |Du|(Ω)`. Both sides may be infinite. -/
theorem setLIntegral_enorm_sub_setAverage_le_mul_totalVariationOn
    (hconv : Convex ℝ (Ω : Set E)) (hu : LocallyIntegrableOn u Ω μ) (hS : S ⊆ Ω)
    (hS₀ : μ S ≠ 0) (hS_top : μ S ≠ ⊤) :
    ∫⁻ x in Ω, ‖u x - ⨍ y in S, u y ∂μ‖ₑ ∂μ ≤
      (∫⁻ h in (Ω : Set E) - Ω, ‖h‖ₑ ∂μ) / μ S * totalVariationOn μ Ω u := by
  have hSm : AEStronglyMeasurable u (μ.restrict S) :=
    hu.aestronglyMeasurable.mono_measure (Measure.restrict_mono hS le_rfl)
  calc ∫⁻ x in Ω, ‖u x - ⨍ y in S, u y ∂μ‖ₑ ∂μ
      ≤ ∫⁻ x in Ω, (∫⁻ y in Ω, ‖u x - u y‖ₑ ∂μ) * (μ S)⁻¹ ∂μ := lintegral_mono fun x => by
        rw [enorm_sub_rev, ← div_eq_mul_inv]
        refine (enorm_setAverage_sub_le_setLAverage hSm hS₀ hS_top (u x)).trans ?_
        rw [setLAverage_eq]
        gcongr ?_ / _
        refine (lintegral_mono_set hS).trans_eq' (lintegral_congr fun y => ?_)
        exact enorm_sub_rev _ _
    _ = (∫⁻ x in Ω, ∫⁻ y in Ω, ‖u x - u y‖ₑ ∂μ ∂μ) * (μ S)⁻¹ :=
        lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 hS₀)
    _ ≤ (∫⁻ h in (Ω : Set E) - Ω, ‖h‖ₑ ∂μ) * totalVariationOn μ Ω u * (μ S)⁻¹ := by
        gcongr
        exact setLIntegral_setLIntegral_enorm_sub_le_mul_totalVariationOn hconv hu
    _ = (∫⁻ h in (Ω : Set E) - Ω, ‖h‖ₑ ∂μ) / μ S * totalVariationOn μ Ω u := by
        rw [div_eq_mul_inv, mul_right_comm]

/-- **The Poincaré inequality for functions of bounded variation on a bounded convex set.** Let
`u` be locally integrable on a bounded convex open set `Ω` of dimension `n`, and let `S ⊆ Ω` have
positive measure. Then `u` deviates from its mean over `S` in `L¹(Ω)` by at most
`μ(B(0, 1)) (diam Ω) ^ (n + 1) / μ(S)` times its total variation on `Ω`. -/
theorem setLIntegral_enorm_sub_setAverage_le_mul_totalVariationOn_of_convex
    (hconv : Convex ℝ (Ω : Set E)) (hb : Bornology.IsBounded (Ω : Set E))
    (hu : LocallyIntegrableOn u Ω μ) (hS : S ⊆ Ω) (hS₀ : μ S ≠ 0) :
    ∫⁻ x in Ω, ‖u x - ⨍ y in S, u y ∂μ‖ₑ ∂μ ≤
      ENNReal.ofReal (μ.real (ball 0 1) * diam (Ω : Set E) ^ (finrank ℝ E + 1) / μ.real S) *
        totalVariationOn μ Ω u := by
  set d := diam (Ω : Set E)
  have hd : 0 ≤ d := diam_nonneg
  have hS_top : μ S ≠ ⊤ :=
    ((measure_mono (hS.trans subset_closure)).trans_lt hb.isCompact_closure.measure_lt_top).ne
  refine (setLIntegral_enorm_sub_setAverage_le_mul_totalVariationOn hconv hu hS hS₀ hS_top).trans
    (mul_le_mul_left ?_ _)
  -- Every `h ∈ Ω - Ω` has `‖h‖ ≤ diam Ω`.
  have hnorm : ∀ h ∈ (Ω : Set E) - Ω, ‖h‖ ≤ d := by
    rintro _ ⟨x, hx, y, hy, rfl⟩
    rw [← dist_eq_norm]
    exact dist_le_diam_of_mem hb hx hy
  have hkernel : ∫⁻ h in (Ω : Set E) - Ω, ‖h‖ₑ ∂μ ≤
      ENNReal.ofReal d * (ENNReal.ofReal (d ^ finrank ℝ E) * μ (ball 0 1)) := by
    rw [← Measure.addHaar_closedBall μ 0 hd]
    calc ∫⁻ h in (Ω : Set E) - Ω, ‖h‖ₑ ∂μ ≤ ∫⁻ _ in (Ω : Set E) - Ω, ENNReal.ofReal d ∂μ :=
          setLIntegral_mono' Ω.isOpen.sub_left.measurableSet fun h hh => by
            rw [← ofReal_norm]
            exact ENNReal.ofReal_le_ofReal (hnorm h hh)
      _ ≤ ENNReal.ofReal d * μ (closedBall 0 d) := by
          rw [setLIntegral_const]
          gcongr
          exact fun h hh => mem_closedBall_zero_iff.2 (hnorm h hh)
  have hS_pos : 0 < μ.real S := ENNReal.toReal_pos hS₀ hS_top
  rw [ENNReal.ofReal_div_of_pos hS_pos, ofReal_measureReal hS_top,
    ENNReal.ofReal_mul measureReal_nonneg, ofReal_measureReal measure_ball_lt_top.ne, pow_succ',
    ENNReal.ofReal_mul hd]
  calc (∫⁻ h in (Ω : Set E) - Ω, ‖h‖ₑ ∂μ) / μ S
      ≤ ENNReal.ofReal d * (ENNReal.ofReal (d ^ finrank ℝ E) * μ (ball 0 1)) / μ S := by
        gcongr
    _ = μ (ball 0 1) * (ENNReal.ofReal d * ENNReal.ofReal (d ^ finrank ℝ E)) / μ S := by
        rw [mul_comm (μ (ball 0 1)), mul_assoc]

/-- **The Poincaré inequality for functions of bounded variation on a ball.** A function locally
integrable on a ball of radius `R` in a space of dimension `n` deviates from its mean over the
ball in `L¹` by at most `2 ^ (n + 1) R` times its total variation on the ball. The constant is
proportional to `R`, as the scaling of both sides forces. -/
theorem setLIntegral_enorm_sub_setAverage_le_mul_totalVariationOn_of_eq_ball {c : E} {R : ℝ}
    (hΩ : (Ω : Set E) = ball c R) (hu : LocallyIntegrableOn u (ball c R) μ) :
    ∫⁻ x in ball c R, ‖u x - ⨍ y in ball c R, u y ∂μ‖ₑ ∂μ ≤
      ENNReal.ofReal (2 ^ (finrank ℝ E + 1) * R) * totalVariationOn μ Ω u := by
  rcases le_or_gt R 0 with hR | hR
  · -- An empty ball carries no integral.
    rw [ball_eq_empty.2 hR, Measure.restrict_empty, lintegral_zero_measure]
    exact zero_le
  have h := setLIntegral_enorm_sub_setAverage_le_mul_totalVariationOn_of_convex (Ω := Ω)
    (S := ball c R) (hΩ ▸ convex_ball c R) (hΩ ▸ isBounded_ball) (hΩ ▸ hu) hΩ.symm.subset
    (measure_ball_pos μ c hR).ne'
  rw [hΩ] at h
  refine h.trans ?_
  gcongr
  exact μ.addHaar_real_ball_mul_diam_ball_pow_div_le c hR

end TauCeti
