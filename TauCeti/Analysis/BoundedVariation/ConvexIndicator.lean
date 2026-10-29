/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Perimeter
import Mathlib.Analysis.Convex.Measure
import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Analysis.BoundedVariation.Convolution
import TauCeti.MeasureTheory.Function.Lp.ApproximateIdentity

/-!
# Restriction to a convex set does not increase variation

Let `μ` be an additive Haar measure on a finite-dimensional real inner product space `E`. For
an integrable function `u : E → ℝ` and a convex set `C ⊆ E`, cutting `u` off outside `C` does
not increase its total variation on the whole space:

`|D(1_C u)|(E) ≤ |Du|(E)`

(`Convex.totalVariationOn_indicator_le`). For sets this says that intersecting a set of finite
volume with a convex set does not increase its perimeter, `P(s ∩ C) ≤ P(s)`
(`Convex.perimeter_inter_le`). This strengthens `Convex.perimeter_le_of_subset`, which is the
case `C ⊆ s` and is proved by duality in `TauCeti.Analysis.BoundedVariation.Convex`. The finite
volume hypothesis cannot be dropped: the complement of a small ball has small perimeter, but its
intersection with a large concentric ball has larger perimeter.

The proof first treats a closed half-space `{x | ⟪e, x⟫ ≤ c}` and a `C¹` integrable function
`w`. A smooth decreasing profile `g` of `⟪e, x⟫` with values in `[0, 1]` has
`|D(g w)| ≤ g |Dw| + |g'| |w|`, and the fundamental theorem of calculus along the rays
`s ↦ x + s • e` bounds the cut-off term `∫ |g'(⟪e, x⟫)| |w x|` by `∫ (1 - g(⟪e, x⟫)) ‖Dw x‖`:
the mass of `w` near the hyperplane is controlled by the variation of `w` beyond it. Hence
`|D(g w)|(E) ≤ ∫ ‖Dw‖`. Mollifying a general integrable `u`, letting `g` tend to the indicator
of the half-space and using lower semicontinuity gives the half-space case. A closed convex set
is a countable intersection of closed half-spaces, so the general case follows by induction
over finite intersections and lower semicontinuity once more; a convex set agrees almost
everywhere with its closure.

## Main results

* `Convex.totalVariationOn_indicator_le`: `|D(1_C u)|(E) ≤ |Du|(E)` for convex `C` and
  integrable `u`.
* `Convex.perimeter_inter_le`: `P(s ∩ C) ≤ P(s)` for convex `C` and `s` of finite volume.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Part II, where
  `P(E ∩ F) ≤ P(E)` for convex `F` and `|E| < ∞` is a standard property of the perimeter.
-/

public section

noncomputable section

open MeasureTheory Filter Set TopologicalSpace ContinuousLinearMap
open scoped ENNReal Convolution Topology RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [μ.IsAddHaarMeasure] {u : E → ℝ}

namespace TauCeti

/-! ### The smooth half-space estimate -/

omit [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] in
/-- Along the ray from `x` in the direction of a unit vector `e`, a `C¹` function is controlled
by its value at distance `L` and the integral of its derivative over the ray segment. -/
private theorem enorm_le_enorm_add_lintegral_enorm_fderiv {w : E → ℝ} (hw : ContDiff ℝ 1 w)
    {e : E} (he : ‖e‖ = 1) (x : E) {L : ℝ} (hL : 0 ≤ L) :
    ‖w x‖ₑ ≤ ‖w (x + L • e)‖ₑ + ∫⁻ s in Ioc 0 L, ‖fderiv ℝ w (x + s • e)‖ₑ := by
  have hderiv (s : ℝ) (_ : s ∈ uIcc 0 L) :
      HasDerivAt (fun s : ℝ => w (x + s • e)) (fderiv ℝ w (x + s • e) e) s := by
    have hray : HasDerivAt (fun s : ℝ => x + s • e) e s := by
      simpa using ((hasDerivAt_id s).smul_const e).const_add x
    exact (hw.differentiable one_ne_zero (x + s • e)).hasFDerivAt.comp_hasDerivAt s hray
  have hcont : Continuous fun s : ℝ => fderiv ℝ w (x + s • e) e :=
    ((hw.continuous_fderiv one_ne_zero).comp
      (continuous_const.add (continuous_id.smul continuous_const))).clm_apply continuous_const
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hcont.intervalIntegrable 0 L)
  rw [zero_smul, add_zero] at hftc
  calc ‖w x‖ₑ = ‖w (x + L • e) - ∫ s in (0)..L, fderiv ℝ w (x + s • e) e‖ₑ := by
        rw [hftc, sub_sub_cancel]
    _ ≤ ‖w (x + L • e)‖ₑ + ‖∫ s in (0)..L, fderiv ℝ w (x + s • e) e‖ₑ := enorm_sub_le
    _ ≤ _ := by
      gcongr
      rw [intervalIntegral.integral_of_le hL]
      refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun s => ?_)
      simpa [← ofReal_norm, he] using (fderiv ℝ w (x + s • e)).le_opENorm e

/-- For a `C¹` profile `g ≤ 1` with nonpositive derivative, the derivative integrates along a
segment of length `L` ending at `t` to at most `1 - g t`. -/
private theorem lintegral_enorm_deriv_sub_le {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hg1 : ∀ t, g t ≤ 1) (hg' : ∀ t, deriv g t ≤ 0) (t : ℝ) {L : ℝ} (hL : 0 ≤ L) :
    ∫⁻ s in Ioc 0 L, ‖deriv g (t - s)‖ₑ ≤ ENNReal.ofReal (1 - g t) := by
  have hdc : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hcont : Continuous fun s => -deriv g (t - s) := (hdc.comp (continuous_const.sub
    continuous_id)).neg
  have hnorm (s : ℝ) : ‖deriv g (t - s)‖ₑ = ENNReal.ofReal (-deriv g (t - s)) := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonpos (hg' _)]
  simp_rw [hnorm]
  rw [← ofReal_integral_eq_lintegral_ofReal (hcont.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (.of_forall fun s => neg_nonneg.2 (hg' _)), ← intervalIntegral.integral_of_le hL,
    intervalIntegral.integral_comp_sub_left (fun s => -deriv g s), intervalIntegral.integral_neg,
    intervalIntegral.integral_deriv_eq_sub (fun s _ => hg.differentiable one_ne_zero s)
      (hdc.intervalIntegrable _ _), sub_zero]
  exact ENNReal.ofReal_le_ofReal (by linarith [hg1 (t - L)])

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- Translating the weight `|g'(⟪e, x⟫)|` of compact support to `+∞` makes its integral against
an integrable `|w|` tend to zero. -/
private theorem tendsto_lintegral_enorm_deriv_sub_mul {w : E → ℝ} (hw : Continuous w)
    (hwi : Integrable w μ) {e : E} {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hgs : HasCompactSupport (deriv g)) :
    Tendsto (fun L : ℕ => ∫⁻ x, ‖deriv g (⟪e, x⟫ - L)‖ₑ * ‖w x‖ₑ ∂μ) atTop (𝓝 0) := by
  have hdc : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hinner : Continuous fun x : E => ⟪e, x⟫ := continuous_const.inner continuous_id
  obtain ⟨M, hM⟩ := hdc.bounded_above_of_compact_support hgs
  have hlim : Tendsto (deriv g) atBot (𝓝 0) :=
    hgs.is_zero_at_infty.mono_left atBot_le_cocompact
  rw [← lintegral_zero (μ := μ)]
  refine tendsto_lintegral_of_dominated_convergence (fun x => ENNReal.ofReal M * ‖w x‖ₑ)
    (fun L => (hdc.comp (hinner.sub continuous_const)).enorm.measurable.mul
      hw.enorm.measurable) (fun L => .of_forall fun x => ?_) ?_ (.of_forall fun x => ?_)
  · dsimp only
    gcongr
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hM _)
  · rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hwi.2.ne
  · have ht : Tendsto (fun L : ℕ => ⟪e, x⟫ - L) atTop atBot :=
      tendsto_atTop_atBot.2 fun b => ⟨⌈⟪e, x⟫ - b⌉₊, fun L hL => by
        have := Nat.ceil_le.1 hL
        linarith⟩
    simpa using ENNReal.Tendsto.mul_const ((hlim.comp ht).enorm) (.inr enorm_ne_top)

/-- **A one-sided trace estimate.** For a `C¹` integrable function `w`, a unit vector `e` and a
`C¹` profile `g ≤ 1` whose derivative is nonpositive and compactly supported, the mass of `w`
weighted by `|g'(⟪e, x⟫)|` is at most the integral of `(1 - g(⟪e, x⟫)) ‖Dw x‖`. -/
private theorem lintegral_enorm_mul_enorm_deriv_le {w : E → ℝ} (hw : ContDiff ℝ 1 w)
    (hwi : Integrable w μ) {e : E} (he : ‖e‖ = 1) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hg1 : ∀ t, g t ≤ 1) (hg' : ∀ t, deriv g t ≤ 0) (hgs : HasCompactSupport (deriv g)) :
    ∫⁻ x, ‖w x‖ₑ * ‖deriv g ⟪e, x⟫‖ₑ ∂μ ≤
      ∫⁻ x, ENNReal.ofReal (1 - g ⟪e, x⟫) * ‖fderiv ℝ w x‖ₑ ∂μ := by
  have hdc : Continuous (deriv g) := hg.continuous_deriv le_rfl
  have hDw : Continuous (fderiv ℝ w) := hw.continuous_fderiv one_ne_zero
  have hinner : Continuous fun x : E => ⟪e, x⟫ := continuous_const.inner continuous_id
  -- The error term coming from the far end of each ray segment of length `L`.
  set δ : ℕ → ℝ≥0∞ := fun L => ∫⁻ x, ‖deriv g (⟪e, x⟫ - L)‖ₑ * ‖w x‖ₑ ∂μ
  have hδ : Tendsto δ atTop (𝓝 0) := tendsto_lintegral_enorm_deriv_sub_mul hw.continuous hwi hg hgs
  -- For every `L`, the weighted mass is at most the right side plus `δ L`.
  have hle (L : ℕ) : ∫⁻ x, ‖w x‖ₑ * ‖deriv g ⟪e, x⟫‖ₑ ∂μ ≤
      ∫⁻ x, ENNReal.ofReal (1 - g ⟪e, x⟫) * ‖fderiv ℝ w x‖ₑ ∂μ + δ L := by
    have hL : (0 : ℝ) ≤ L := L.cast_nonneg
    have hmeas : Measurable (Function.uncurry fun (x : E) (s : ℝ) =>
        ‖deriv g ⟪e, x⟫‖ₑ * ‖fderiv ℝ w (x + s • e)‖ₑ) :=
      (hdc.comp (hinner.comp continuous_fst)).enorm.measurable.mul
        (hDw.comp (continuous_fst.add (continuous_snd.smul continuous_const))).enorm.measurable
    have hmeas' : Measurable (Function.uncurry fun (y : E) (s : ℝ) =>
        ‖deriv g (⟪e, y⟫ - s)‖ₑ * ‖fderiv ℝ w y‖ₑ) :=
      (hdc.comp ((hinner.comp continuous_fst).sub continuous_snd)).enorm.measurable.mul
        (hDw.comp continuous_fst).enorm.measurable
    calc ∫⁻ x, ‖w x‖ₑ * ‖deriv g ⟪e, x⟫‖ₑ ∂μ
        ≤ ∫⁻ x, (‖deriv g ⟪e, x⟫‖ₑ * ‖w (x + (L : ℝ) • e)‖ₑ +
            ∫⁻ s in Ioc 0 (L : ℝ), ‖deriv g ⟪e, x⟫‖ₑ * ‖fderiv ℝ w (x + s • e)‖ₑ) ∂μ := by
          refine lintegral_mono fun x => ?_
          rw [lintegral_const_mul' _ _ enorm_ne_top, ← mul_add, mul_comm]
          gcongr
          exact enorm_le_enorm_add_lintegral_enorm_fderiv hw he x hL
      _ = δ L + ∫⁻ s in Ioc 0 (L : ℝ), ∫⁻ y, ‖deriv g (⟪e, y⟫ - s)‖ₑ * ‖fderiv ℝ w y‖ₑ ∂μ := by
          have hm : Measurable fun x => ‖deriv g ⟪e, x⟫‖ₑ * ‖w (x + (L : ℝ) • e)‖ₑ :=
            (hdc.comp hinner).enorm.measurable.mul
              (hw.continuous.comp (continuous_id.add continuous_const)).enorm.measurable
          rw [lintegral_add_left hm,
            lintegral_lintegral_swap hmeas.aemeasurable]
          congr 1
          · refine Eq.trans (lintegral_congr fun x => ?_)
              (lintegral_add_right_eq_self (μ := μ) _ ((L : ℝ) • e))
            simp [inner_add_right, inner_smul_right, he]
          · refine lintegral_congr fun s => Eq.trans (lintegral_congr fun x => ?_)
              (lintegral_add_right_eq_self (μ := μ)
                (fun y => ‖deriv g (⟪e, y⟫ - s)‖ₑ * ‖fderiv ℝ w y‖ₑ) (s • e))
            simp [inner_add_right, inner_smul_right, he]
      _ = δ L + ∫⁻ y, (∫⁻ s in Ioc 0 (L : ℝ), ‖deriv g (⟪e, y⟫ - s)‖ₑ) * ‖fderiv ℝ w y‖ₑ ∂μ := by
          rw [← lintegral_lintegral_swap hmeas'.aemeasurable]
          simp_rw [lintegral_mul_const' _ _ enorm_ne_top]
      _ ≤ δ L + ∫⁻ y, ENNReal.ofReal (1 - g ⟪e, y⟫) * ‖fderiv ℝ w y‖ₑ ∂μ := by
          gcongr with y
          exact lintegral_enorm_deriv_sub_le hg hg1 hg' _ hL
      _ = _ := add_comm _ _
  have hlim : Tendsto (fun L => ∫⁻ x, ENNReal.ofReal (1 - g ⟪e, x⟫) * ‖fderiv ℝ w x‖ₑ ∂μ + δ L)
      atTop (𝓝 (∫⁻ x, ENNReal.ofReal (1 - g ⟪e, x⟫) * ‖fderiv ℝ w x‖ₑ ∂μ)) := by
    simpa using tendsto_const_nhds.add hδ
  exact le_of_tendsto_of_tendsto' tendsto_const_nhds hlim hle

/-- **The smooth half-space estimate.** Multiplying a `C¹` integrable function `w` by a `C¹`
decreasing profile `g(⟪e, x⟫)` with values in `[0, 1]` and compactly supported derivative gives
total variation at most `∫ ‖Dw‖`. -/
private theorem totalVariationOn_comp_inner_mul_le {w : E → ℝ} (hw : ContDiff ℝ 1 w)
    (hwi : Integrable w μ) {e : E} (he : ‖e‖ = 1) {g : ℝ → ℝ} (hg : ContDiff ℝ 1 g)
    (hg0 : ∀ t, 0 ≤ g t) (hg1 : ∀ t, g t ≤ 1) (hg' : ∀ t, deriv g t ≤ 0)
    (hgs : HasCompactSupport (deriv g)) :
    totalVariationOn μ ⊤ (fun x => g ⟪e, x⟫ * w x) ≤ ∫⁻ x, ‖fderiv ℝ w x‖ₑ ∂μ := by
  have hinner : ContDiff ℝ 1 fun x : E => ⟪e, x⟫ := contDiff_const.inner ℝ contDiff_id
  have hv : ContDiff ℝ 1 fun x => g ⟪e, x⟫ * w x := (hg.comp hinner).mul hw
  rw [hv.locallyLipschitz.locallyLipschitzOn.totalVariationOn_eq_setLIntegral_enorm_fderiv,
    Opens.coe_top, Measure.restrict_univ]
  -- The product rule bounds the derivative by `g ‖Dw‖ + |w| |g'|`.
  have hpt (x : E) : ‖fderiv ℝ (fun x => g ⟪e, x⟫ * w x) x‖ₑ ≤
      ENNReal.ofReal (g ⟪e, x⟫) * ‖fderiv ℝ w x‖ₑ + ‖w x‖ₑ * ‖deriv g ⟪e, x⟫‖ₑ := by
    have hgx : HasFDerivAt (fun x => g ⟪e, x⟫) (deriv g ⟪e, x⟫ • innerSL ℝ e) x :=
      (hg.differentiable one_ne_zero _).hasDerivAt.comp_hasFDerivAt x (innerSL ℝ e).hasFDerivAt
    rw [(hgx.fun_mul (hw.differentiable one_ne_zero x).hasFDerivAt).fderiv]
    refine (enorm_add_le (g ⟪e, x⟫ • fderiv ℝ w x)
      (w x • deriv g ⟪e, x⟫ • innerSL ℝ e)).trans (add_le_add ?_ ?_)
    · rw [enorm_smul, Real.enorm_of_nonneg (hg0 _)]
    · rw [enorm_smul, enorm_smul, ← ofReal_norm (innerSL ℝ e), innerSL_apply_norm, he,
        ENNReal.ofReal_one, mul_one]
  have hDw : Measurable fun x => ‖fderiv ℝ w x‖ₑ :=
    (hw.continuous_fderiv one_ne_zero).enorm.measurable
  have hm : Measurable fun x => ENNReal.ofReal (g ⟪e, x⟫) * ‖fderiv ℝ w x‖ₑ :=
    (hg.continuous.comp hinner.continuous).measurable.ennreal_ofReal.mul hDw
  calc ∫⁻ x, ‖fderiv ℝ (fun x => g ⟪e, x⟫ * w x) x‖ₑ ∂μ
      ≤ ∫⁻ x, (ENNReal.ofReal (g ⟪e, x⟫) * ‖fderiv ℝ w x‖ₑ + ‖w x‖ₑ * ‖deriv g ⟪e, x⟫‖ₑ) ∂μ :=
        lintegral_mono hpt
    _ ≤ ∫⁻ x, ENNReal.ofReal (g ⟪e, x⟫) * ‖fderiv ℝ w x‖ₑ ∂μ +
          ∫⁻ x, ENNReal.ofReal (1 - g ⟪e, x⟫) * ‖fderiv ℝ w x‖ₑ ∂μ := by
        rw [lintegral_add_left hm]
        exact add_le_add_right (lintegral_enorm_mul_enorm_deriv_le hw hwi he hg hg1 hg' hgs) _
    _ = ∫⁻ x, ‖fderiv ℝ w x‖ₑ ∂μ := by
        rw [← lintegral_add_left hm]
        refine lintegral_congr fun x => ?_
        rw [← add_mul, ← ENNReal.ofReal_add (hg0 _) (sub_nonneg.2 (hg1 _)), add_sub_cancel,
          ENNReal.ofReal_one, one_mul]

/-! ### Smooth cut-off profiles -/

/-- Smooth decreasing profiles, equal to one on `(-∞, c]` and to zero on `[c + 1 / (k + 1), ∞)`,
converging pointwise to the indicator of `(-∞, c]`. -/
private def cutoff (c : ℝ) (k : ℕ) (t : ℝ) : ℝ := Real.smoothTransition ((k + 1) * (c - t) + 1)

private theorem contDiff_cutoff (c : ℝ) (k : ℕ) : ContDiff ℝ 1 (cutoff c k) :=
  Real.smoothTransition.contDiff.comp
    ((contDiff_const.mul (contDiff_const.sub contDiff_id)).add contDiff_const)

private theorem enorm_cutoff_le_one (c t : ℝ) (k : ℕ) : ‖cutoff c k t‖ₑ ≤ 1 := by
  rw [cutoff, Real.enorm_of_nonneg (Real.smoothTransition.nonneg _), ENNReal.ofReal_le_one]
  exact Real.smoothTransition.le_one _

private theorem cutoff_eq_one {c t : ℝ} (k : ℕ) (ht : t ≤ c) : cutoff c k t = 1 :=
  Real.smoothTransition.one_of_one_le (by nlinarith)

private theorem antitone_cutoff (c : ℝ) (k : ℕ) : Antitone (cutoff c k) := fun s t hst =>
  Real.smoothTransition.monotone (by nlinarith)

private theorem hasCompactSupport_deriv_cutoff (c : ℝ) (k : ℕ) :
    HasCompactSupport (deriv (cutoff c k)) := by
  refine HasCompactSupport.intro (isCompact_Icc (a := c) (b := c + 1)) fun t ht => ?_
  rcases not_and_or.1 ht with ht | ht
  · -- Left of `c` the profile is constantly one.
    have : cutoff c k =ᶠ[𝓝 t] fun _ => 1 := eventually_of_mem (Iio_mem_nhds (not_le.1 ht))
      fun s hs => cutoff_eq_one k (le_of_lt hs)
    rw [this.deriv_eq, deriv_const]
  · -- Right of `c + 1` the profile is constantly zero.
    have : cutoff c k =ᶠ[𝓝 t] fun _ => 0 := eventually_of_mem (Ioi_mem_nhds (not_le.1 ht))
      fun s hs => Real.smoothTransition.zero_of_nonpos (by
        have : (0 : ℝ) ≤ k := k.cast_nonneg
        nlinarith [show c - s < -1 from by linarith [mem_Ioi.1 hs]])
    rw [this.deriv_eq, deriv_const]

private theorem tendsto_cutoff (c t : ℝ) :
    Tendsto (fun k => cutoff c k t) atTop (𝓝 ({s | s ≤ c}.indicator 1 t)) := by
  by_cases ht : t ≤ c
  · simp [ht, cutoff_eq_one _ ht]
  · simp only [mem_ofPred_eq, ht, not_false_eq_true, indicator_of_notMem]
    obtain ⟨N, hN⟩ := exists_nat_ge (1 / (t - c))
    have htc : 0 < t - c := by linarith [not_le.1 ht]
    refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨N, fun k hk => ?_⟩)
    refine (Real.smoothTransition.zero_of_nonpos ?_).symm
    have hk : 1 / (t - c) ≤ k + 1 := hN.trans (by exact_mod_cast hk.trans (Nat.le_succ k))
    rw [div_le_iff₀ htc] at hk
    nlinarith

/-! ### Half-spaces and convex sets -/

omit [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure] in
/-- Cutting off an integrable `u` by the smooth profiles `cutoff c n ⟪e, x⟫` approximates its
restriction to the closed half-space `{x | ⟪e, x⟫ ≤ c}` in `L¹(K)`. -/
private theorem tendsto_setLIntegral_enorm_cutoff_mul_sub_indicator (hu : Integrable u μ) (e : E)
    (c : ℝ) (K : Set E) :
    Tendsto (fun n => ∫⁻ x in K, ‖cutoff c n ⟪e, x⟫ * u x - {x | ⟪e, x⟫ ≤ c}.indicator u x‖ₑ ∂μ)
      atTop (𝓝 0) := by
  set H : Set E := {x | ⟪e, x⟫ ≤ c}
  have hinner : Continuous fun x : E => ⟪e, x⟫ := continuous_const.inner continuous_id
  have hH : MeasurableSet H := (isClosed_le hinner continuous_const).measurableSet
  rw [← lintegral_zero (μ := μ.restrict K)]
  refine tendsto_lintegral_of_dominated_convergence' (fun x => ‖u x‖ₑ)
    (fun n => ((((contDiff_cutoff c n).continuous.comp hinner).aestronglyMeasurable.mul
      hu.1).sub (hu.1.indicator hH)).enorm.restrict) (fun n => .of_forall fun x => ?_)
    (ne_top_of_le_ne_top hu.2.ne (setLIntegral_le_lintegral _ _)) (.of_forall fun x => ?_)
  · by_cases hx : x ∈ H
    · simp [indicator_of_mem hx, cutoff_eq_one n hx]
    · dsimp only
      rw [indicator_of_notMem hx, sub_zero, enorm_mul]
      exact mul_le_of_le_one_left zero_le (enorm_cutoff_le_one _ _ _)
  · have hlim := ((tendsto_cutoff c ⟪e, x⟫).mul_const (u x)).sub_const (H.indicator u x)
    have hHx : {s : ℝ | s ≤ c}.indicator 1 ⟪e, x⟫ * u x - H.indicator u x = 0 := by
      by_cases hx : x ∈ H
      · have hx' : ⟪e, x⟫ ≤ c := hx
        simp [indicator_of_mem hx, hx']
      · have hx' : ¬ ⟪e, x⟫ ≤ c := hx
        simp [indicator_of_notMem hx, hx']
    rw [hHx] at hlim
    simpa using hlim.enorm

/-- **Cutting off by a closed half-space.** For an integrable `u` and a unit vector `e`, the
function equal to `u` on `{x | ⟪e, x⟫ ≤ c}` and to zero elsewhere has total variation at most
`|Du|(E)`. -/
private theorem totalVariationOn_indicator_inner_le (hu : Integrable u μ) {e : E} (he : ‖e‖ = 1)
    (c : ℝ) : totalVariationOn μ ⊤ ({x | ⟪e, x⟫ ≤ c}.indicator u) ≤ totalVariationOn μ ⊤ u := by
  set H : Set E := {x | ⟪e, x⟫ ≤ c}
  have hinner : Continuous fun x : E => ⟪e, x⟫ := continuous_const.inner continuous_id
  have hH : MeasurableSet H := (isClosed_le hinner continuous_const).measurableSet
  -- Mollify `u`, and multiply the mollifications by smooth profiles of `⟪e, x⟫` tending to the
  -- indicator of `H`.
  let φ : ℕ → ContDiffBump (0 : E) := fun n =>
    ⟨1 / (n + 2), 1 / (n + 1), by positivity, by gcongr; norm_num⟩
  have hφ : Tendsto (fun n => (φ n).rOut) atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  set w : ℕ → E → ℝ := fun n => (φ n).normed μ ⋆[lsmul ℝ ℝ, μ] u
  have hw (n : ℕ) : ContDiff ℝ 1 (w n) :=
    (φ n).hasCompactSupport_normed.contDiff_convolution_left _ (φ n).contDiff_normed
      hu.locallyIntegrable
  set v : ℕ → E → ℝ := fun n x => cutoff c n ⟪e, x⟫ * w n x
  have hv (n : ℕ) : totalVariationOn μ ⊤ (v n) ≤ totalVariationOn μ ⊤ u := by
    refine (totalVariationOn_comp_inner_mul_le (hw n)
      ((φ n).integrable_normed.integrable_convolution _ hu) he (contDiff_cutoff c n)
      (fun _ => Real.smoothTransition.nonneg _) (fun _ => Real.smoothTransition.le_one _)
      (fun _ => (antitone_cutoff c n).deriv_nonpos) (hasCompactSupport_deriv_cutoff c n)).trans ?_
    have := (φ n).totalVariationOn_normed_convolution_le (Ω := ⊤) (Ω' := ⊤)
      (hu.locallyIntegrable.locallyIntegrableOn _) fun _ _ => subset_univ _
    rwa [(hw n).locallyLipschitz.locallyLipschitzOn.totalVariationOn_eq_setLIntegral_enorm_fderiv,
      Opens.coe_top, Measure.restrict_univ] at this
  refine (totalVariationOn_le_liminf (l := atTop) (u := v)
    (.of_forall fun n => (((contDiff_cutoff c n).continuous.comp hinner).mul
      (hw n).continuous).locallyIntegrable.locallyIntegrableOn _)
    ((hu.indicator hH).locallyIntegrable.locallyIntegrableOn _) fun K hK _ => ?_).trans
    (liminf_le_of_frequently_le' (.of_forall hv))
  -- Convergence in `L¹(K)`: split off the mollification error and the cut-off error.
  have hsplit (n : ℕ) (x : E) : ‖v n x - H.indicator u x‖ₑ ≤
      ‖w n x - u x‖ₑ + ‖cutoff c n ⟪e, x⟫ * u x - H.indicator u x‖ₑ := by
    calc ‖v n x - H.indicator u x‖ₑ
        = ‖cutoff c n ⟪e, x⟫ * (w n x - u x) + (cutoff c n ⟪e, x⟫ * u x - H.indicator u x)‖ₑ := by
          congr 1
          simp only [v]
          ring
      _ ≤ ‖cutoff c n ⟪e, x⟫‖ₑ * ‖w n x - u x‖ₑ +
            ‖cutoff c n ⟪e, x⟫ * u x - H.indicator u x‖ₑ := by
          rw [← enorm_mul]; exact enorm_add_le _ _
      _ ≤ _ := by gcongr; exact mul_le_of_le_one_left zero_le (enorm_cutoff_le_one _ _ _)
  have hcutoff := tendsto_setLIntegral_enorm_cutoff_mul_sub_indicator (μ := μ) hu e c K
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
    (by simpa using (tendsto_setLIntegral_enorm_normed_convolution_sub hφ hu.locallyIntegrable
      hK).add hcutoff) (fun _ => zero_le) fun n => ?_
  calc ∫⁻ x in K, ‖v n x - H.indicator u x‖ₑ ∂μ
      ≤ ∫⁻ x in K, (‖w n x - u x‖ₑ + ‖cutoff c n ⟪e, x⟫ * u x - H.indicator u x‖ₑ) ∂μ :=
        lintegral_mono (hsplit n)
    _ = _ :=
        lintegral_add_left' ((hw n).continuous.aestronglyMeasurable.sub hu.1).enorm.restrict _

/-- Cutting off by any closed half-space `{x | l x ≤ c}` does not increase the total variation
of an integrable function. -/
private theorem totalVariationOn_indicator_halfSpace_le (hu : Integrable u μ) (l : E →L[ℝ] ℝ)
    (c : ℝ) : totalVariationOn μ ⊤ ({x | l x ≤ c}.indicator u) ≤ totalVariationOn μ ⊤ u := by
  rcases eq_or_ne l 0 with rfl | hl
  · by_cases hc : 0 ≤ c
    · simp [hc]
    · simp [hc]
  -- Write `l = ‖l‖ ⟪e, ·⟫` for a unit vector `e`.
  have hl' : 0 < ‖l‖ := norm_pos_iff.2 hl
  set e : E := ‖l‖⁻¹ • (InnerProductSpace.toDual ℝ E).symm l
  have he : ‖e‖ = 1 := by
    rw [norm_smul, LinearIsometryEquiv.norm_map, norm_inv, norm_norm, inv_mul_cancel₀ hl'.ne']
  have hset : {x | l x ≤ c} = {x | ⟪e, x⟫ ≤ c / ‖l‖} := by
    ext x
    simp only [mem_ofPred_eq, e, inner_smul_left, InnerProductSpace.toDual_symm_apply,
      RCLike.conj_to_real, le_div_iff₀ hl']
    rw [inv_mul_eq_div, div_mul_cancel₀ _ hl'.ne']
  rw [hset]
  exact totalVariationOn_indicator_inner_le hu he _

end TauCeti

/-- **Restriction to a convex set does not increase variation.** For a convex set `C` and an
integrable function `u`, the function equal to `u` on `C` and to zero elsewhere has total
variation on the whole space at most that of `u`. -/
theorem Convex.totalVariationOn_indicator_le {C : Set E} (hC : Convex ℝ C)
    (hu : Integrable u μ) :
    TauCeti.totalVariationOn μ ⊤ (C.indicator u) ≤ TauCeti.totalVariationOn μ ⊤ u := by
  -- A convex set agrees almost everywhere with its closure.
  have hae : C.indicator u =ᵐ[μ.restrict (⊤ : Opens E)] (closure C).indicator u := by
    refine ae_restrict_of_ae (indicator_ae_eq_of_ae_eq_set (ae_eq_set.2 ⟨?_, ?_⟩))
    · simp [sdiff_eq_empty.2 subset_closure]
    · -- `closure C \ C` lies in the frontier `closure C \ interior C`, which is null.
      exact measure_mono_null (sdiff_subset_sdiff_right interior_subset) (hC.addHaar_frontier μ)
  rw [TauCeti.totalVariationOn_congr_ae hae]
  -- The closure is a countable intersection of closed half-spaces.
  obtain ⟨l, c, hlc⟩ := RCLike.iInter_countable_halfSpaces_eq (𝕜 := ℝ) hC.closure
    isClosed_closure
  simp only [RCLike.re_to_real] at hlc
  have hmeas (n : ℕ) : MeasurableSet {x | l n x ≤ c n} :=
    measurableSet_le (l n).continuous.measurable measurable_const
  set D : ℕ → Set E := fun N => ⋂ n ∈ Finset.range N, {x | l n x ≤ c n}
  have hD (N : ℕ) : MeasurableSet (D N) := Finset.measurableSet_biInter _ fun n _ => hmeas n
  have hcD (N : ℕ) : closure C ⊆ D N := fun x hx => by
    rw [← hlc] at hx
    exact mem_iInter₂.2 fun n _ => mem_iInter.1 hx n
  -- Each finite intersection of these half-spaces does not increase the variation.
  have hTV (N : ℕ) : TauCeti.totalVariationOn μ ⊤ ((D N).indicator u) ≤
      TauCeti.totalVariationOn μ ⊤ u := by
    induction N with
    | zero => simp [D]
    | succ N ih =>
      have hDN : D (N + 1) = {x | l N x ≤ c N} ∩ D N := by
        simp only [D, Finset.range_add_one, Finset.set_biInter_insert]
      rw [hDN, ← indicator_indicator]
      exact (TauCeti.totalVariationOn_indicator_halfSpace_le (hu.indicator (hD N)) _ _).trans ih
  refine (TauCeti.totalVariationOn_le_liminf (l := atTop) (u := fun N => (D N).indicator u)
    (.of_forall fun N => (hu.indicator (hD N)).locallyIntegrable.locallyIntegrableOn _)
    ((hu.indicator measurableSet_closure).locallyIntegrable.locallyIntegrableOn _)
    fun K hK _ => ?_).trans (liminf_le_of_frequently_le' (.of_forall hTV))
  -- The finite intersections decrease to the closure, so the indicators converge in `L¹`.
  rw [← lintegral_zero (μ := μ.restrict K)]
  refine tendsto_lintegral_of_dominated_convergence' (fun x => ‖u x‖ₑ)
    (fun N => ((hu.1.indicator (hD N)).sub (hu.1.indicator measurableSet_closure)).enorm.restrict)
    (fun N => .of_forall fun x => ?_)
    (ne_top_of_le_ne_top hu.2.ne (setLIntegral_le_lintegral _ _)) (.of_forall fun x => ?_)
  · by_cases hx : x ∈ closure C
    · simp [indicator_of_mem hx, indicator_of_mem (hcD N hx)]
    · by_cases hxD : x ∈ D N
      · simp [indicator_of_notMem hx, indicator_of_mem hxD]
      · simp [indicator_of_notMem hx, indicator_of_notMem hxD]
  · by_cases hx : x ∈ closure C
    · simp [indicator_of_mem hx, indicator_of_mem (hcD _ hx)]
    · -- A point outside the closure leaves one of the half-spaces, hence all later `D N`.
      have hx' := hx
      rw [← hlc, mem_iInter, not_forall] at hx'
      obtain ⟨n, hn⟩ := hx'
      refine tendsto_const_nhds.congr' (eventually_atTop.2 ⟨n + 1, fun N hN => ?_⟩)
      have hxD : x ∉ D N := fun h => hn (mem_iInter₂.1 h n (Finset.mem_range.2 (by omega)))
      simp [indicator_of_notMem hxD, indicator_of_notMem hx]

/-- **Intersecting with a convex set does not increase perimeter.** For a convex set `C` and a
set `s` of finite measure, `P(s ∩ C) ≤ P(s)` in the whole space. -/
theorem Convex.perimeter_inter_le {C s : Set E} (hC : Convex ℝ C) (hs : NullMeasurableSet s μ)
    (hμs : μ s ≠ ∞) : TauCeti.perimeter μ ⊤ (s ∩ C) ≤ TauCeti.perimeter μ ⊤ s := by
  have hi : Integrable (s.indicator (1 : E → ℝ)) μ :=
    (integrable_indicator_iff₀ hs).2 (integrableOn_const hμs)
  simpa [TauCeti.perimeter_def, indicator_indicator, inter_comm] using
    hC.totalVariationOn_indicator_le hi
