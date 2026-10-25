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
import TauCeti.Analysis.BoundedVariation.Convolution
import TauCeti.Analysis.Convex.Exhaustion
import TauCeti.Analysis.Sobolev.Poincare.Wirtinger.Basic
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

For bounded `Ω`, `S ⊆ Ω` of positive measure and `u` integrable on `Ω`, the file also proves the
inequality localized to an arbitrary subset `A ⊆ Ω`:

`∫_A |u - ⨍_S u| ≤ μ(B(0, 1)) ^ (1 - 1/n) (diam Ω) ^ n / μ(S) μ(A) ^ (1/n) |Du|(Ω)`.

The factor `μ(A) ^ (1/n)` makes it scale-invariant: it is a weak-type `L^{n/(n-1)}` Poincaré
inequality, implied by the strong `L^{n/(n-1)}` Sobolev–Poincaré inequality through Hölder's
inequality. Its indicator case is the relative isoperimetric inequality
(`TauCeti.min_measure_inter_measure_sdiff_rpow_le_perimeter`). The `C¹` case
(`TauCeti.setLIntegral_enorm_sub_setAverage_le_mul_measure_rpow_mul_of_convex`) integrates the
Riesz potential estimate over `A` and bounds the Riesz kernel on `A` by its value on a ball of the
same measure. It passes to `u` through mollifications on convex open sets with compact closures in
`Ω`, which converge in `L¹` and do not increase the variation
(`TauCeti.exists_seq_contDiff_tendsto_setLIntegral_enorm_sub_totalVariationOn_le`), and through an
exhaustion of `Ω` by such sets
(`TauCeti.exists_seq_isOpen_convex_isCompact_closure_subset_iUnion_eq`).

## Main results

* `TauCeti.setLIntegral_setLIntegral_enorm_sub_le_mul_totalVariationOn`: the double-integral
  estimate `∫_Ω ∫_Ω |u x - u y| ≤ (∫_{Ω - Ω} ‖h‖) |Du|(Ω)` on a convex open set.
* `TauCeti.setLIntegral_enorm_sub_setAverage_le_mul_totalVariationOn`: the Poincaré inequality on
  a convex open set, with constant `(∫_{Ω - Ω} ‖h‖) / μ(S)`.
* `TauCeti.setLIntegral_enorm_sub_setAverage_le_mul_totalVariationOn_of_convex`: the Poincaré
  inequality on a bounded convex open set, with constant `μ(B(0, 1)) (diam Ω) ^ (n + 1) / μ(S)`.
* `TauCeti.setLIntegral_enorm_sub_setAverage_le_mul_totalVariationOn_of_eq_ball`: the Poincaré
  inequality on a ball of radius `R`, with constant `2 ^ (n + 1) R`.
* `TauCeti.setLIntegral_enorm_sub_setAverage_le_mul_measure_rpow_mul_totalVariationOn_of_convex`:
  the inequality localized to a subset `A`, on a bounded convex open set.

## References

* L. Ambrosio, N. Fusco, D. Pallara, *Functions of Bounded Variation and Free Discontinuity
  Problems*, Remark 3.50.
* L. C. Evans, R. F. Gariepy, *Measure Theory and Fine Properties of Functions*, revised edition,
  §5.6.2 (Poincaré's inequality for functions of bounded variation).
* D. Gilbarg, N. S. Trudinger, *Elliptic Partial Differential Equations of Second Order*,
  equation (7.45), for the constant on convex sets, and Lemmas 7.12 and 7.16.
-/

public section

noncomputable section

namespace TauCeti

open MeasureTheory Filter Set Metric TopologicalSpace Module
open scoped ENNReal Pointwise Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {Ω : Opens E}
  {u : E → ℝ} {S A : Set E}

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

/-! ### The localized inequality -/

/-- The inequality on a convex open set `U` whose closure is a compact subset of `Ω`, with the
mean over a measurable `T ⊆ U`, a set `A ⊆ U` and the variation of `u` on `Ω`. -/
private theorem setLIntegral_enorm_sub_setAverage_le_of_closure_subset {U T : Set E}
    (hU : IsOpen U) (hUc : Convex ℝ U) (hUK : IsCompact (closure U)) (hUΩ : closure U ⊆ Ω)
    (hu : LocallyIntegrableOn u Ω μ) (hT : T ⊆ U) (hT₀ : μ T ≠ 0) (hA : A ⊆ U) :
    ∫⁻ x in A, ‖u x - ⨍ y in T, u y ∂μ‖ₑ ∂μ ≤
      ENNReal.ofReal (μ.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) * diam U ^ finrank ℝ E /
        μ.real T) * μ A ^ (finrank ℝ E : ℝ)⁻¹ * totalVariationOn μ Ω u := by
  set C := ENNReal.ofReal (μ.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) *
    diam U ^ finrank ℝ E / μ.real T) * μ A ^ (finrank ℝ E : ℝ)⁻¹
  have hUb : Bornology.IsBounded U := hUK.isBounded.subset subset_closure
  have hUfin : μ U ≠ ∞ := hUb.measure_lt_top.ne
  have huK : IntegrableOn u (closure U) μ := hu.integrableOn_compact_subset hUΩ hUK
  -- Smooth functions `v n` converging to `u` in `L¹(closure U)`, with variation on `U` at most
  -- `|Du|(Ω)`. The `L¹(closure U)` distance from `v n` to `u` is `e n`.
  obtain ⟨v, hv, he, hvar⟩ :=
    exists_seq_contDiff_tendsto_setLIntegral_enorm_sub_totalVariationOn_le hu hUK hUΩ
  set e : ℕ → ℝ≥0∞ := fun n => ∫⁻ x in closure U, ‖v n x - u x‖ₑ ∂μ
  set M : ℝ≥0∞ := μ U / μ T
  have hM : M ≠ ∞ := ENNReal.div_ne_top hUfin hT₀
  -- The inequality holds for `u` up to an error `(1 + M) e n`.
  have hbound (n : ℕ) : ∫⁻ x in A, ‖u x - ⨍ y in T, u y ∂μ‖ₑ ∂μ ≤
      e n + M * e n + C * totalVariationOn μ Ω u := by
    have hv1 : ContDiff ℝ 1 (v n) := (hv n).of_le (by norm_cast)
    -- The smooth inequality for `v n` on `U`, whose variation there is at most `|Du|(Ω)`.
    have hvA : ∫⁻ x in A, ‖v n x - ⨍ y in T, v n y ∂μ‖ₑ ∂μ ≤ C * totalVariationOn μ Ω u := by
      refine (setLIntegral_enorm_sub_setAverage_le_mul_measure_rpow_mul_of_convex hU hUc hUb
        hv1.contDiffOn hT hT₀ hA).trans (mul_le_mul_right ?_ _)
      have hL := (hv1.locallyLipschitz.locallyLipschitzOn (s := U)
        ).totalVariationOn_eq_setLIntegral_enorm_fderiv (μ := μ) (Ω := ⟨U, hU⟩)
      rw [Opens.coe_mk] at hL
      exact hL ▸ hvar ⟨U, hU⟩ subset_closure n
    -- The means over `T` differ by at most `e n / μ(T)`.
    have hab : ‖(⨍ y in T, v n y ∂μ) - ⨍ y in T, u y ∂μ‖ₑ ≤ e n / μ T := by
      have hTK : T ⊆ closure U := hT.trans subset_closure
      rw [← setAverage_fun_sub
        (((hv n).continuous.locallyIntegrable.integrableOn_isCompact hUK).mono_set hTK)
        (huK.mono_set hTK)]
      refine (enorm_setAverage_le_setLAverage μ _ T).trans ?_
      rw [setLAverage_eq]
      gcongr
      exact lintegral_mono_set hTK
    -- The triangle inequality through `v n` and its mean.
    have hdist : AEMeasurable (fun x => ‖v n x - u x‖ₑ) (μ.restrict A) :=
      (((hv n).continuous.aestronglyMeasurable.restrict.sub huK.aestronglyMeasurable).enorm
        ).mono_measure (Measure.restrict_mono (hA.trans subset_closure) le_rfl)
    calc ∫⁻ x in A, ‖u x - ⨍ y in T, u y ∂μ‖ₑ ∂μ
        ≤ ∫⁻ x in A, (‖v n x - u x‖ₑ + ‖v n x - ⨍ y in T, v n y ∂μ‖ₑ +
            ‖(⨍ y in T, v n y ∂μ) - ⨍ y in T, u y ∂μ‖ₑ) ∂μ := by
          refine lintegral_mono fun x => ?_
          rw [← enorm_neg (v n x - u x)]
          refine le_of_eq_of_le ?_
            ((enorm_add_le _ _).trans (add_le_add_left (enorm_add_le _ _) _))
          congr 1
          ring
      _ = ∫⁻ x in A, ‖v n x - u x‖ₑ ∂μ + ∫⁻ x in A, ‖v n x - ⨍ y in T, v n y ∂μ‖ₑ ∂μ +
            ‖(⨍ y in T, v n y ∂μ) - ⨍ y in T, u y ∂μ‖ₑ * μ A := by
          rw [lintegral_add_right _ measurable_const, lintegral_add_left' hdist,
            setLIntegral_const]
      _ ≤ e n + C * totalVariationOn μ Ω u + e n / μ T * μ U := by
          gcongr
          exact lintegral_mono_set (hA.trans subset_closure)
      _ = e n + M * e n + C * totalVariationOn μ Ω u := by
          simp only [M, div_eq_mul_inv]
          ring
  have hlim : Tendsto (fun n => e n + M * e n + C * totalVariationOn μ Ω u) atTop
      (𝓝 (0 + M * 0 + C * totalVariationOn μ Ω u)) :=
    (he.add (ENNReal.Tendsto.const_mul he (Or.inr hM))).add tendsto_const_nhds
  simpa using ge_of_tendsto hlim (.of_forall hbound)

/-- The inequality for a measurable `S`, from the inequality on an exhaustion of `Ω` by convex
open sets with compact closures in `Ω`. -/
private theorem setLIntegral_enorm_sub_setAverage_le_of_measurableSet
    (hΩc : Convex ℝ (Ω : Set E)) (hb : Bornology.IsBounded (Ω : Set E))
    (hu : IntegrableOn u Ω μ) (hSm : MeasurableSet S) (hS : S ⊆ Ω) (hS₀ : μ S ≠ 0)
    (hA : A ⊆ Ω) :
    ∫⁻ x in A, ‖u x - ⨍ y in S, u y ∂μ‖ₑ ∂μ ≤
      ENNReal.ofReal (μ.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) *
        diam (Ω : Set E) ^ finrank ℝ E / μ.real S) * μ A ^ (finrank ℝ E : ℝ)⁻¹ *
        totalVariationOn μ Ω u := by
  obtain ⟨V, hVmono, hVopen, hVconv, hVcompact, hVclosure, hVunion⟩ :=
    exists_seq_isOpen_convex_isCompact_closure_subset_iUnion_eq Ω.isOpen hΩc
  have hVsub (n : ℕ) : V n ⊆ Ω := subset_closure.trans (hVclosure n)
  have hΩfin : μ Ω ≠ ∞ := hb.measure_lt_top.ne
  have hSfin : μ S ≠ ∞ := ne_top_of_le_ne_top hΩfin (measure_mono hS)
  have hSpos : 0 < μ.real S := ENNReal.toReal_pos hS₀ hSfin
  set K : ℝ := μ.real (ball (0 : E) 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) *
    diam (Ω : Set E) ^ finrank ℝ E
  set a := ⨍ y in S, u y ∂μ
  set T := μ A ^ (finrank ℝ E : ℝ)⁻¹ * totalVariationOn μ Ω u
  -- The measures of, and the means over, `S ∩ V n` converge to those over `S`.
  have hSV : S ⊆ ⋃ n, V n := hVunion ▸ hS
  have hmeas : Tendsto (fun n ↦ μ.real (S ∩ V n)) atTop (𝓝 (μ.real S)) :=
    tendsto_measureReal_inter_of_monotone hVmono hSV hSfin
  have havg : Tendsto (fun n ↦ ⨍ y in S ∩ V n, u y ∂μ) atTop (𝓝 a) :=
    tendsto_setAverage_inter_of_monotone hVmono hSV
      (fun n ↦ (hSm.inter (hVopen n).measurableSet).nullMeasurableSet) hSfin (hu.mono_set hS)
  -- On `A ∩ V n`, the deviation from `a` is the deviation from the mean over `S ∩ V n` up to an
  -- error `μ(Ω) |⨍_{S ∩ V n} u - a|`.
  have hpiece : ∀ᶠ n in atTop, ∫⁻ x in A ∩ V n, ‖u x - a‖ₑ ∂μ ≤
      ENNReal.ofReal (K / μ.real (S ∩ V n)) * T + μ Ω * ‖(⨍ y in S ∩ V n, u y ∂μ) - a‖ₑ := by
    filter_upwards [hmeas.eventually (lt_mem_nhds hSpos)] with n hn
    have hn0 : μ (S ∩ V n) ≠ 0 := fun h => by simp [measureReal_def, h] at hn
    calc ∫⁻ x in A ∩ V n, ‖u x - a‖ₑ ∂μ
        ≤ ∫⁻ x in A ∩ V n, (‖u x - ⨍ y in S ∩ V n, u y ∂μ‖ₑ +
            ‖(⨍ y in S ∩ V n, u y ∂μ) - a‖ₑ) ∂μ :=
          lintegral_mono fun x => by
            simpa only [sub_add_sub_cancel] using enorm_add_le (u x - ⨍ y in S ∩ V n, u y ∂μ)
              ((⨍ y in S ∩ V n, u y ∂μ) - a)
      _ = ∫⁻ x in A ∩ V n, ‖u x - ⨍ y in S ∩ V n, u y ∂μ‖ₑ ∂μ +
            ‖(⨍ y in S ∩ V n, u y ∂μ) - a‖ₑ * μ (A ∩ V n) := by
          rw [lintegral_add_right _ measurable_const, setLIntegral_const]
      _ ≤ ENNReal.ofReal (K / μ.real (S ∩ V n)) * T +
            μ Ω * ‖(⨍ y in S ∩ V n, u y ∂μ) - a‖ₑ := by
          rw [mul_comm (‖_‖ₑ), ← mul_assoc]
          gcongr
          · refine (setLIntegral_enorm_sub_setAverage_le_of_closure_subset (hVopen n)
              (hVconv n) (hVcompact n) (hVclosure n) hu.locallyIntegrableOn inter_subset_right
              hn0 inter_subset_right).trans ?_
            gcongr
            · simp only [K]
              gcongr
              exact diam_mono (hVsub n) hb
            · exact inter_subset_left
          · exact inter_subset_right.trans (hVsub n)
  -- The bounds converge to `C μ(A) ^ (1/n) |Du|(Ω)`.
  have hlim : Tendsto (fun n => ENNReal.ofReal (K / μ.real (S ∩ V n)) * T +
      μ Ω * ‖(⨍ y in S ∩ V n, u y ∂μ) - a‖ₑ) atTop
      (𝓝 (ENNReal.ofReal (K / μ.real S) * T + μ Ω * 0)) := by
    refine Tendsto.add ?_ (ENNReal.Tendsto.const_mul ?_ (Or.inr hΩfin))
    · rcases eq_or_ne K 0 with hK | hK
      · simp [hK]
      refine ENNReal.Tendsto.mul_const
        (ENNReal.tendsto_ofReal (tendsto_const_nhds.div hmeas hSpos.ne')) (Or.inl ?_)
      exact (ENNReal.ofReal_pos.2 (div_pos (lt_of_le_of_ne (by positivity) hK.symm) hSpos)).ne'
    · have h0 : Tendsto (fun n ↦ (⨍ y in S ∩ V n, u y ∂μ) - a) atTop (𝓝 0) := by
        simpa using havg.sub_const a
      simpa [Function.comp_def] using (continuous_enorm.tendsto (0 : ℝ)).comp h0
  -- `A` is the increasing union of the sets `A ∩ V n`.
  have hAV : ⋃ n, A ∩ V n = A := by rw [← inter_iUnion, hVunion, inter_eq_left.2 hA]
  have hdir : Directed (· ⊆ ·) fun n => A ∩ V n :=
    Monotone.directed_le fun m n hmn => inter_subset_inter_right A (hVmono hmn)
  have hsup : ∫⁻ x in A, ‖u x - a‖ₑ ∂μ = ⨆ k, ∫⁻ x in A ∩ V k, ‖u x - a‖ₑ ∂μ := by
    rw [← setLIntegral_iUnion_of_directed _ hdir, hAV]
  rw [hsup, mul_assoc]
  refine iSup_le fun k => ge_of_tendsto (by simpa using hlim) ?_
  filter_upwards [hpiece, eventually_ge_atTop k] with n hn hkn
  exact (lintegral_mono_set (inter_subset_inter_right A (hVmono hkn))).trans hn

/-- **The Poincaré–Wirtinger inequality for functions of bounded variation, localized to a
subset.** Let `Ω` be a bounded convex open set in a finite-dimensional real inner product space of
dimension `n`, and let `S ⊆ Ω` have positive measure. For every `u` integrable on `Ω` and every
`A ⊆ Ω`, the integral over `A` of the deviation of `u` from its mean over `S` is at most
`μ(B(0, 1)) ^ (1 - 1/n) * (diam Ω) ^ n / μ(S) * μ(A) ^ (1/n)` times the total variation
`|Du|(Ω)`, finite or infinite. -/
theorem setLIntegral_enorm_sub_setAverage_le_mul_measure_rpow_mul_totalVariationOn_of_convex
    (hΩc : Convex ℝ (Ω : Set E)) (hb : Bornology.IsBounded (Ω : Set E))
    (hu : IntegrableOn u Ω μ) (hS : S ⊆ Ω) (hS₀ : μ S ≠ 0) (hA : A ⊆ Ω) :
    ∫⁻ x in A, ‖u x - ⨍ y in S, u y ∂μ‖ₑ ∂μ ≤
      ENNReal.ofReal (μ.real (ball 0 1) ^ (1 - (finrank ℝ E : ℝ)⁻¹) *
        diam (Ω : Set E) ^ finrank ℝ E / μ.real S) * μ A ^ (finrank ℝ E : ℝ)⁻¹ *
        totalVariationOn μ Ω u := by
  -- Replace `S` by the measurable set `Ω ∩ toMeasurable μ S`, with the same restricted measure.
  have hSfin : μ S ≠ ∞ := ne_top_of_le_ne_top hb.measure_lt_top.ne (measure_mono hS)
  set S' := (Ω : Set E) ∩ toMeasurable μ S
  have hres : μ.restrict S' = μ.restrict S := by
    rw [← Measure.restrict_restrict Ω.isOpen.measurableSet, Measure.restrict_toMeasurable hSfin,
      Measure.restrict_restrict Ω.isOpen.measurableSet, inter_eq_right.2 hS]
  have hμ : μ S' = μ S := by
    rw [← Measure.restrict_apply_univ, hres, Measure.restrict_apply_univ]
  have havg : ⨍ y in S', u y ∂μ = ⨍ y in S, u y ∂μ := by rw [hres]
  have hreal : μ.real S' = μ.real S := by rw [measureReal_def, measureReal_def, hμ]
  rw [← havg, ← hreal]
  exact setLIntegral_enorm_sub_setAverage_le_of_measurableSet hΩc hb hu
    (Ω.isOpen.measurableSet.inter (measurableSet_toMeasurable μ S)) inter_subset_left
    (hμ ▸ hS₀) hA

end TauCeti
