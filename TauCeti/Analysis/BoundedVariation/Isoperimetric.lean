/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.BoundedVariation.Perimeter
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.SpecialFunctions.Sqrt
import TauCeti.Analysis.BoundedVariation.SmoothApproximation
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.MeasureTheory.Measure.Haar.NormedSpace
import TauCeti.MeasureTheory.Measure.Lebesgue.BrunnMinkowski.Isoperimetric

/-!
# The sharp isoperimetric inequality for sets of finite volume

Let `E` be a finite-dimensional real inner product space of dimension `n ≥ 1` with its volume,
and write `ω_n = volume (ball 0 1)` and `P(s)` for the perimeter of `s` in the whole space. Every
null-measurable set `s` of finite positive volume satisfies the sharp isoperimetric inequality

`P(s)^n ≥ n^n ω_n |s|^(n-1)`

(`MeasureTheory.NullMeasurableSet.finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow`),
with no boundedness, connectedness or regularity hypothesis on `s`, and with `P(s)` finite or
infinite. Equivalently `n ω_n^(1/n) |s|^(1 - 1/n) ≤ P(s)`, which is stated in real numbers when the
perimeter is finite
(`MeasureTheory.NullMeasurableSet.mul_volume_real_rpow_mul_le_perimeter_toReal`).
Balls attain equality (`TauCeti.perimeter_ball_pow`), so the constant is sharp. Finite volume
cannot be dropped: the complement of a ball has finite perimeter.

## Strategy

Every set of finite volume is a limit, in measure and in perimeter, of regular superlevel sets
`{u > t}` of compactly supported smooth functions
(`MeasureTheory.NullMeasurableSet.exists_smooth_perimeter_approximation`), so it suffices to treat
such sets. For these, `w = (u - t) / √(‖∇u‖² + (u - t)²)` is a smooth defining function of
`F = {u > t}` whose gradient has norm one on the boundary `{u = t}`. Near the boundary
`‖∇w‖` lies within `ε` of one, and for small `η > 0`:

* the `η / (1 + ε)`-neighbourhood of `G = {w ≥ η}` lies in `F`, so the Brunn–Minkowski inequality
  bounds the volume of the shell `S = {0 < w < η} = F \ G` from below by
  `n |G|^(1 - 1/n) ω_n^(1/n) η / (1 + ε)`;
* for a test vector field `ψ` equal to `-∇w / ‖∇w‖` near the boundary, integration by parts against
  the clamped function `max 0 (min w η)` gives the calibration estimate
  `(1 - ε) |S| ≤ ∫_S ‖∇w‖ ≤ η (∫_F div ψ + ∫_S |div ψ|)`.

Dividing by `η`, letting `η → 0` and then `ε → 0` gives `n ω_n^(1/n) |F|^(1 - 1/n) ≤ ∫_F div ψ`,
and the right-hand side is at most `P(F)` by the definition of the perimeter. No identification of
the perimeter with surface measure or Minkowski content is used.

## Main results

* `MeasureTheory.NullMeasurableSet.finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow`:
  the sharp isoperimetric inequality `n^n ω_n |s|^(n-1) ≤ P(s)^n` in `ℝ≥0∞`.
* `MeasureTheory.NullMeasurableSet.mul_volume_real_rpow_mul_le_perimeter_toReal`: its real form
  `n ω_n^(1/n) |s|^(1 - 1/n) ≤ P(s)` for sets of finite perimeter.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge University
  Press, 2012, Chapters 13 and 14, for the approximation by smooth sets and the isoperimetric
  inequality.
* R. J. Gardner, *The Brunn–Minkowski inequality*, Bull. Amer. Math. Soc. **39** (2002), 355–405,
  Section 5.
-/

public section

noncomputable section

open MeasureTheory Metric Module Set Filter TopologicalSpace TestFunction InnerProductSpace
open scoped ENNReal Topology ContDiff Distributions Gradient Pointwise symmDiff

namespace TauCeti

section NormedSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- If the derivative of `w` has norm at most `L` wherever `a ≤ w ≤ b`, then `w` stays above `a`
at distance less than `(b - a) / L` from every point where `w ≥ b`. -/
private theorem lt_apply_add_of_norm_fderiv_le {w : E → ℝ} (hw : Differentiable ℝ w)
    {a b L : ℝ} (hL : 0 ≤ L) (hbound : ∀ x, a ≤ w x → w x ≤ b → ‖fderiv ℝ w x‖ ≤ L) {x z : E}
    (hx : b ≤ w x) (hz : L * ‖z‖ < b - a) : a < w (x + z) := by
  by_contra! h
  -- Along the segment from `x` to `x + z`, let `s₁` be the first time with `w ≤ a` and `s₀` the
  -- last earlier time with `w ≥ b`. Strictly between them `a < w < b`, so the derivative bound
  -- applies there, and the mean value theorem gives a contradiction.
  let f : ℝ → ℝ := fun s => w (x + s • z)
  have hfd (s : ℝ) : HasDerivAt f (fderiv ℝ w (x + s • z) z) s := by
    have hline : HasDerivAt (fun s : ℝ => x + s • z) z s := by
      simpa using ((hasDerivAt_id s).smul_const z).const_add x
    exact (hw (x + s • z)).hasFDerivAt.comp_hasDerivAt s hline
  have hfc : Continuous f := continuous_iff_continuousAt.2 fun s => (hfd s).continuousAt
  have hab : a < b := by nlinarith [norm_nonneg z]
  obtain ⟨s₁, ⟨⟨hs₁I, hs₁a⟩, hs₁⟩⟩ :=
    (isCompact_Icc.inter_right (isClosed_Iic.preimage hfc)).exists_isLeast
      (⟨1, right_mem_Icc.2 zero_le_one, by simpa [f] using h⟩ :
        (Icc (0 : ℝ) 1 ∩ f ⁻¹' Iic a).Nonempty)
  obtain ⟨s₀, ⟨⟨hs₀I, hs₀b⟩, hs₀⟩⟩ :=
    (isCompact_Icc.inter_right (isClosed_Ici.preimage hfc)).exists_isGreatest
      (⟨0, left_mem_Icc.2 hs₁I.1, by simpa [f] using hx⟩ : (Icc 0 s₁ ∩ f ⁻¹' Ici b).Nonempty)
  simp only [mem_preimage, mem_Iic, mem_Ici] at hs₁a hs₀b
  have hlt : s₀ < s₁ :=
    lt_of_le_of_ne hs₀I.2 fun he => by rw [he] at hs₀b; linarith
  obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope f (fun s => fderiv ℝ w (x + s • z) z) hlt
    hfc.continuousOn fun s _ => hfd s
  have hcI : c ∈ Icc (0 : ℝ) 1 := ⟨hs₀I.1.trans hc.1.le, hc.2.le.trans hs₁I.2⟩
  have hca : a < f c := by
    by_contra! hca
    exact (hs₁ ⟨hcI, hca⟩).not_gt hc.2
  have hcb : f c < b := by
    by_contra! hcb
    exact (hs₀ ⟨⟨hcI.1, hc.2.le⟩, hcb⟩).not_gt hc.1
  have hd : -(L * ‖z‖) ≤ fderiv ℝ w (x + c • z) z := by
    have := ((fderiv ℝ w (x + c • z)).le_opNorm z).trans
      (mul_le_mul_of_nonneg_right (hbound _ hca.le hcb.le) (norm_nonneg z))
    rw [Real.norm_eq_abs] at this
    linarith [neg_abs_le (fderiv ℝ w (x + c • z) z)]
  have hpos : 0 < s₁ - s₀ := sub_pos.2 hlt
  have hslope : f s₁ - f s₀ = fderiv ℝ w (x + c • z) z * (s₁ - s₀) := by
    rw [hcd, div_mul_cancel₀ _ hpos.ne']
  have : -(L * ‖z‖) ≤ f s₁ - f s₀ := by
    rw [hslope]
    nlinarith [mul_nonneg hL (norm_nonneg z), hs₀I.1, hs₁I.2]
  linarith

/-- The derivative of the clamped function `max 0 (min w η)` is the derivative of `w` on
`{0 < w < η}` and vanishes elsewhere, including at both levels `0` and `η`. -/
private theorem fderiv_max_min_eq_indicator {w : E → ℝ} (hw : Continuous w) {η : ℝ} (hη : 0 < η)
    (x : E) :
    fderiv ℝ (fun y => max 0 (min (w y) η)) x = (w ⁻¹' Ioo 0 η).indicator (fderiv ℝ w) x := by
  rcases lt_trichotomy (w x) 0 with h | h | h
  · rw [indicator_of_notMem (s := w ⁻¹' Ioo 0 η) fun hx => (h.trans hx.1).false]
    refine (Filter.EventuallyEq.fderiv_eq (f := fun _ => (0 : ℝ)) ?_).trans (fderiv_const_apply _)
    filter_upwards [hw.continuousAt.eventually (gt_mem_nhds h)] with y hy
    exact max_eq_left ((min_le_left _ _).trans hy.le)
  · rw [indicator_of_notMem (s := w ⁻¹' Ioo 0 η) fun hx => (h ▸ hx.1).false]
    refine IsLocalMin.fderiv_eq_zero (Filter.Eventually.of_forall fun y => ?_)
    simp only [h, min_eq_left hη.le, max_self]
    exact le_max_left _ _
  rcases lt_trichotomy (w x) η with h' | h' | h'
  · rw [indicator_of_mem (s := w ⁻¹' Ioo 0 η) ⟨h, h'⟩]
    refine Filter.EventuallyEq.fderiv_eq ?_
    filter_upwards [hw.continuousAt.eventually (lt_mem_nhds h),
      hw.continuousAt.eventually (gt_mem_nhds h')] with y hy hy'
    rw [min_eq_left hy'.le, max_eq_right hy.le]
  · rw [indicator_of_notMem (s := w ⁻¹' Ioo 0 η) fun hx => (h' ▸ hx.2).false]
    refine IsLocalMax.fderiv_eq_zero (Filter.Eventually.of_forall fun y => ?_)
    simp only [h', min_self, max_eq_right hη.le]
    exact max_le hη.le (min_le_right _ _)
  · rw [indicator_of_notMem (s := w ⁻¹' Ioo 0 η) fun hx => (hx.2.trans h').false]
    refine (Filter.EventuallyEq.fderiv_eq (f := fun _ => η) ?_).trans (fderiv_const_apply _)
    filter_upwards [hw.continuousAt.eventually (lt_mem_nhds h')] with y hy
    rw [min_eq_right hy.le, max_eq_right hη.le]

end NormedSpace

/-- If `{w ≥ -δ}` is compact, then a closed set avoiding the zero level of a continuous `w` also
avoids `{|w| ≤ η}` for some `0 < η ≤ δ`. -/
private theorem exists_forall_abs_le_notMem {X : Type*} [TopologicalSpace X] {w : X → ℝ}
    (hw : Continuous w) {δ : ℝ} (hδ : 0 < δ) (hK : IsCompact {x | -δ ≤ w x}) {C : Set X}
    (hC : IsClosed C)
    (hCw : ∀ x ∈ C, w x ≠ 0) : ∃ η, 0 < η ∧ η ≤ δ ∧ ∀ x, |w x| ≤ η → x ∉ C := by
  rcases ({x | -δ ≤ w x} ∩ C).eq_empty_or_nonempty with hA | hA
  · exact ⟨δ, hδ, le_rfl, fun x hx hxC =>
      hA.subset ⟨neg_le_of_abs_le hx, hxC⟩⟩
  obtain ⟨x₀, hx₀, hmin⟩ := (hK.inter_right hC).exists_isMinOn hA hw.abs.continuousOn
  have hm : 0 < |w x₀| := abs_pos.2 (hCw x₀ hx₀.2)
  refine ⟨min δ (|w x₀| / 2), lt_min hδ (half_pos hm), min_le_left _ _, fun x hx hxC => ?_⟩
  have := isMinOn_iff.1 hmin x ⟨neg_le_of_abs_le (hx.trans (min_le_left _ _)), hxC⟩
  linarith [min_le_right δ (|w x₀| / 2)]

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

omit [MeasurableSpace E] [BorelSpace E] in
/-- A smooth function `w` whose derivative does not vanish on its zero level, with `{w ≥ -δ}`
compact, admits an admissible test vector field equal to `-∇w / ‖∇w‖` near the zero level. Its
derivative pairing with `w` there is `-‖Dw‖`. -/
private theorem exists_testFunction_fderiv_apply_eq_neg_norm {w : E → ℝ} (hw : ContDiff ℝ ∞ w)
    {δ : ℝ} (hδ : 0 < δ) (hK : IsCompact {x | -δ ≤ w x})
    (hreg : ∀ x, w x = 0 → fderiv ℝ w x ≠ 0) :
    ∃ η > 0, ∃ ψ : 𝓓(⊤, E), (∀ x, ‖ψ x‖ ≤ 1) ∧
      ∀ x, |w x| ≤ η → fderiv ℝ w x (ψ x) = -‖fderiv ℝ w x‖ := by
  obtain ⟨η, hη, hηδ, hηC⟩ := exists_forall_abs_le_notMem hw.continuous hδ hK
    (isClosed_eq (hw.continuous_fderiv (by simp)) continuous_const) fun x hx h0 => hreg x h0 hx
  -- `G` is the gradient of `w`, and `ρ ∘ w` cuts off to `{|w| < η}`.
  let G : E → E := ∇ w
  have hG : ContDiff ℝ ∞ G := hw.gradient_right le_rfl
  have hGnorm (x : E) : ‖G x‖ = ‖fderiv ℝ w x‖ := norm_gradient_eq_norm_fderiv w x
  have hGapp (x : E) : fderiv ℝ w x (G x) = ‖G x‖ ^ 2 := by
    rw [← toDual_gradient, toDual_apply_apply, real_inner_self_eq_norm_sq]
  have hG0 {x : E} (hx : |w x| ≤ η) : G x ≠ 0 := by
    rw [← norm_ne_zero_iff, hGnorm, norm_ne_zero_iff]
    exact hηC x hx
  let ρ : ContDiffBump (0 : ℝ) := ⟨η / 2, η, half_pos hη, half_lt_self hη⟩
  have hρ0 {x : E} (hx : η ≤ |w x|) : ρ (w x) = 0 := by
    rw [← Function.notMem_support, ρ.support_eq, mem_ball_zero_iff, Real.norm_eq_abs]
    exact hx.not_gt
  have hρ1 {x : E} (hx : |w x| ≤ η / 2) : ρ (w x) = 1 :=
    ρ.one_of_mem_closedBall (by rwa [mem_closedBall_zero_iff, Real.norm_eq_abs])
  let ψ : E → E := fun x => -((ρ (w x) * ‖G x‖⁻¹) • G x)
  have hψs : ContDiff ℝ ∞ ψ := by
    refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hGx : G x = 0
    · -- Where the gradient vanishes, `|w| > η`, so `ψ` vanishes nearby.
      have hx : η < |w x| := lt_of_not_ge fun h => hG0 h hGx
      refine contDiffAt_const (c := (0 : E)).congr_of_eventuallyEq ?_
      filter_upwards [(hw.continuous.abs.isOpen_preimage _ isOpen_Ioi).mem_nhds hx] with y hy
      simp [ψ, hρ0 (le_of_lt hy)]
    · exact (((ρ.contDiff.comp hw).contDiffAt.mul
        ((hG.contDiffAt.norm ℝ hGx).inv (norm_ne_zero_iff.2 hGx))).smul hG.contDiffAt).neg
  have hψc : HasCompactSupport ψ := HasCompactSupport.intro hK fun x hx => by
    have hx : w x < -δ := not_le.1 hx
    have : η ≤ |w x| := hηδ.trans (le_abs.2 (Or.inr (by linarith)))
    simp [ψ, hρ0 this]
  refine ⟨η / 2, half_pos hη, ⟨ψ, hψs, hψc, by simp⟩, fun x => ?_, fun x hx => ?_⟩
  · simp only [coe_mk, ψ]
    by_cases hGx : G x = 0
    · simp [hGx]
    rw [norm_neg, norm_smul,
      Real.norm_of_nonneg (mul_nonneg ρ.nonneg (inv_nonneg.2 (norm_nonneg _))), mul_assoc,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 hGx), mul_one]
    exact ρ.le_one
  · have hGx := hG0 (hx.trans (half_le_self hη.le))
    simp only [coe_mk, ψ, map_neg, map_smul, smul_eq_mul, hGapp, hρ1 hx, one_mul, ← hGnorm]
    field_simp [norm_ne_zero_iff.2 hGx]

/-- The clamped function `max 0 (min w η)` differs from `η` times the indicator of `{w > 0}`
by at most `η`, and only on the shell `{0 < w < η}`. -/
private theorem abs_mul_indicator_sub_max_min_le {X : Type*} {w : X → ℝ} {η : ℝ} (hη : 0 ≤ η)
    (x : X) :
    |η * {x | 0 < w x}.indicator 1 x - max 0 (min (w x) η)| ≤
      (w ⁻¹' Ioo 0 η).indicator (fun _ => η) x := by
  by_cases hxS : x ∈ w ⁻¹' Ioo 0 η
  · have h1 : 0 < w x := hxS.1
    have h2 : w x < η := hxS.2
    rw [indicator_of_mem hxS, indicator_of_mem (s := {x | 0 < w x}) h1, Pi.one_apply, mul_one,
      min_eq_left h2.le, max_eq_right h1.le, abs_le]
    constructor <;> linarith
  · rw [indicator_of_notMem hxS]
    rcases le_or_gt (w x) 0 with h | h
    · rw [indicator_of_notMem (s := {x | 0 < w x}) h.not_gt, mul_zero,
        max_eq_left ((min_le_left _ _).trans h), sub_zero, abs_zero]
    · have hηx : η ≤ w x := le_of_not_gt fun h' => hxS ⟨h, h'⟩
      rw [indicator_of_mem (s := {x | 0 < w x}) h, Pi.one_apply, mul_one, min_eq_right hηx,
        max_eq_right hη, sub_self, abs_zero]

/-- **The calibration estimate.** If a test vector field `ψ` satisfies `Dw (ψ) = -‖Dw‖` on the
shell `S = {0 < w < η}`, as `-∇w / ‖∇w‖` does, then
`∫_S ‖Dw‖ ≤ η (∫_{w > 0} div ψ + ∫_S |div ψ|)`. -/
private theorem setIntegral_norm_fderiv_le {w : E → ℝ} (hw : ContDiff ℝ 1 w) {η : ℝ} (hη : 0 < η)
    (ψ : 𝓓(⊤, E)) (hψ : ∀ x, w x ∈ Ioo 0 η → fderiv ℝ w x (ψ x) = -‖fderiv ℝ w x‖) :
    ∫ x in w ⁻¹' Ioo 0 η, ‖fderiv ℝ w x‖ ≤
      η * ((∫ x, divergenceCLM ψ x * {x | 0 < w x}.indicator 1 x) +
        ∫ x in w ⁻¹' Ioo 0 η, |divergenceCLM ψ x|) := by
  set S := w ⁻¹' Ioo 0 η
  set F := {x | 0 < w x}
  let v : E → ℝ := fun y => max 0 (min (w y) η)
  let D : E → ℝ := divergenceCLM ψ
  have hS : MeasurableSet S := hw.continuous.measurable measurableSet_Ioo
  have hF : MeasurableSet F := measurableSet_lt measurable_const hw.continuous.measurable
  have hD : Integrable D :=
    (divergenceCLM ψ).continuous.integrable_of_hasCompactSupport (divergenceCLM ψ).hasCompactSupport
  have hv : LocallyLipschitz v := (hw.locallyLipschitz.min_const η).const_max 0
  -- Integration by parts against the clamped function `v` gives `∫ D v = ∫_S ‖Dw‖`.
  have hibp : ∫ x, D x * v x = ∫ x in S, ‖fderiv ℝ w x‖ := by
    have := (hv.locallyLipschitzOn (s := ((⊤ : Opens E) : Set E))).hasWeakFDerivOn_fderiv
      (μ := volume) |>.integral_divergenceCLM_smul_eq_neg_integral ψ
    simp only [smul_eq_mul] at this
    rw [this, ← integral_indicator hS, ← integral_neg]
    refine integral_congr_ae (.of_forall fun x => ?_)
    simp only [v]
    rw [fderiv_max_min_eq_indicator hw.continuous hη x]
    by_cases hx : x ∈ S
    · rw [indicator_of_mem (s := w ⁻¹' Ioo 0 η) hx, indicator_of_mem hx, hψ x hx, neg_neg]
    · rw [indicator_of_notMem (s := w ⁻¹' Ioo 0 η) hx, indicator_of_notMem hx]
      simp
  -- The clamped function agrees with `η 1_F` off `S`, and differs from it by at most `η` on `S`.
  have hpt (x : E) : ‖D x * (η * F.indicator 1 x - v x)‖ ≤ η * S.indicator (fun x => |D x|) x := by
    have hcl := abs_mul_indicator_sub_max_min_le (w := w) hη.le x
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
    by_cases hxS : x ∈ S
    · rw [indicator_of_mem (s := w ⁻¹' Ioo 0 η) hxS] at hcl
      rw [indicator_of_mem hxS, mul_comm η (|D x|)]
      exact mul_le_mul_of_nonneg_left hcl (abs_nonneg _)
    · rw [indicator_of_notMem (s := w ⁻¹' Ioo 0 η) hxS] at hcl
      rw [indicator_of_notMem hxS, mul_zero]
      exact (mul_nonpos_of_nonneg_of_nonpos (abs_nonneg _) hcl)
  have hbdd (f : E → ℝ) (hf : Measurable f) (c : ℝ) (hfc : ∀ x, ‖f x‖ ≤ c) :
      Integrable fun x => D x * f x :=
    hD.mul_bdd hf.aestronglyMeasurable (.of_forall hfc)
  have hFm : Measurable (F.indicator (1 : E → ℝ)) := measurable_const.indicator hF
  have hvm : Measurable v := hv.continuous.measurable
  have hFb (x : E) : ‖F.indicator (1 : E → ℝ) x‖ ≤ 1 := by
    by_cases hx : x ∈ F <;> simp [hx]
  have hvb (x : E) : ‖v x‖ ≤ η := by
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [le_max_left 0 (min (w x) η)], max_le hη.le (min_le_right _ _)⟩
  have hdiff : ∫ x, D x * (η * F.indicator 1 x - v x) =
      η * (∫ x, D x * F.indicator 1 x) - ∫ x, D x * v x := by
    rw [← integral_const_mul, ← integral_sub ((hbdd _ hFm 1 hFb).const_mul η) (hbdd _ hvm η hvb)]
    refine integral_congr_ae (.of_forall fun x => ?_)
    ring
  have hrem : ‖∫ x, D x * (η * F.indicator 1 x - v x)‖ ≤ η * ∫ x in S, |D x| := by
    rw [← integral_indicator hS, ← integral_const_mul]
    exact norm_integral_le_of_norm_le (((hD.abs.indicator hS)).const_mul η) (.of_forall hpt)
  rw [Real.norm_eq_abs] at hrem
  rw [← hibp, mul_add]
  linarith [neg_abs_le (∫ x, D x * (η * F.indicator 1 x - v x))]

/-- **Brunn–Minkowski for a shell.** If the `r`-neighbourhood `G + ball 0 r` of a nonempty
measurable set `G` lies in a set `F` of finite volume, then in dimension `n ≥ 1`
`volume F - volume G ≥ n (volume G ^ (1 / n)) ^ (n - 1) r ω_n ^ (1 / n)`. -/
private theorem finrank_mul_rpow_pow_mul_le_volume_real_sub (hn : finrank ℝ E ≠ 0) {G F : Set E}
    (hG : MeasurableSet G) (hG0 : G.Nonempty) (hF : volume F ≠ ⊤) {r : ℝ} (hr : 0 < r)
    (hsub : G + ball (0 : E) r ⊆ F) :
    finrank ℝ E * (volume.real G ^ (finrank ℝ E : ℝ)⁻¹) ^ (finrank ℝ E - 1) *
        (r * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹) ≤
      volume.real F - volume.real G := by
  set n := finrank ℝ E
  set a := volume.real G ^ (n : ℝ)⁻¹
  set b := r * volume.real (ball (0 : E) 1) ^ (n : ℝ)⁻¹
  have hball : volume.real (ball (0 : E) r) ^ (n : ℝ)⁻¹ = b := by
    rw [volume.addHaar_real_ball_of_pos 0 hr, Real.mul_rpow (by positivity) measureReal_nonneg,
      Real.pow_rpow_inv_natCast hr.le hn]
  have hBM := volume_real_rpow_add_volume_real_rpow_le hn hG0 hG.nullMeasurableSet
    (nonempty_ball.2 hr) measurableSet_ball.nullMeasurableSet
    (ne_top_of_le_ne_top hF (measure_mono hsub))
  rw [hball] at hBM
  have hab : a + b ≤ volume.real F ^ (n : ℝ)⁻¹ := hBM.trans
    (Real.rpow_le_rpow measureReal_nonneg (measureReal_mono hsub hF) (by positivity))
  have ha : 0 ≤ a := by positivity
  have hb : 0 ≤ b := by positivity
  have hpow := pow_le_pow_left₀ (by positivity) hab n
  rw [Real.rpow_inv_natCast_pow measureReal_nonneg hn] at hpow
  have hbin := (Commute.all a b).pow_add_mul_le_add_pow_of_sq_nonneg ha (sq_nonneg b)
    (sq_nonneg _) (by positivity) n
  have han : a ^ n = volume.real G := Real.rpow_inv_natCast_pow measureReal_nonneg hn
  linarith

/-- **One step of the smooth isoperimetric argument.** Suppose that `‖Dw‖` lies within `ε < 1`
of `1` on `{0 ≤ w ≤ η}` and that a test vector field `ψ` satisfies `Dw (ψ) = -‖Dw‖` on
`S = {0 < w < η}`. Then, with `F = {w > 0}` of finite volume and `G = {w ≥ η}` nonempty,
`(1 - ε) / (1 + ε) n ω_n ^ (1 / n) (volume G ^ (1 / n)) ^ (n - 1) ≤ ∫_F div ψ + ∫_S |div ψ|`. -/
private theorem div_mul_le_integral_add_setIntegral {w : E → ℝ} (hw : ContDiff ℝ 1 w)
    (hn : finrank ℝ E ≠ 0) {η ε : ℝ} (hη : 0 < η) (hε : 0 < ε) (hε1 : ε < 1)
    (hF : volume {x | 0 < w x} ≠ ⊤) (hG : {x | η ≤ w x}.Nonempty)
    (hgrad : ∀ x, 0 ≤ w x → w x ≤ η → |‖fderiv ℝ w x‖ - 1| < ε)
    (hint : IntegrableOn (fun x => ‖fderiv ℝ w x‖) (w ⁻¹' Ioo 0 η)) (ψ : 𝓓(⊤, E))
    (hψ : ∀ x, w x ∈ Ioo 0 η → fderiv ℝ w x (ψ x) = -‖fderiv ℝ w x‖) :
    (1 - ε) / (1 + ε) * (finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
        (volume.real {x | η ≤ w x} ^ (finrank ℝ E : ℝ)⁻¹) ^ (finrank ℝ E - 1)) ≤
      (∫ x, divergenceCLM ψ x * {x | 0 < w x}.indicator 1 x) +
        ∫ x in w ⁻¹' Ioo 0 η, |divergenceCLM ψ x| := by
  set n := finrank ℝ E
  set F := {x | 0 < w x}
  set G := {x | η ≤ w x}
  set S := w ⁻¹' Ioo 0 η
  have hGm : MeasurableSet G := measurableSet_le measurable_const hw.continuous.measurable
  have hGF : G ⊆ F := fun x hx => hη.trans_le hx
  have hSFG : S = F \ G := by
    ext x
    simp [S, F, G, not_le]
  have hSm : MeasurableSet S := hw.continuous.measurable measurableSet_Ioo
  have hSfin : volume S ≠ ⊤ := ne_top_of_le_ne_top hF (measure_mono (hSFG ▸ sdiff_subset))
  -- The `η / (1 + ε)`-neighbourhood of `G` stays in `F`, so Brunn–Minkowski bounds `|S|` below.
  have hsub : G + ball (0 : E) (η / (1 + ε)) ⊆ F := by
    rintro _ ⟨x, hx, z, hz, rfl⟩
    refine lt_apply_add_of_norm_fderiv_le (hw.differentiable one_ne_zero) (L := 1 + ε) (by linarith)
      (fun y hy1 hy2 => ?_) hx ?_
    · linarith [(abs_lt.1 (hgrad y hy1 hy2)).2]
    · rw [mem_ball_zero_iff, lt_div_iff₀ (by linarith)] at hz
      linarith
  have hshell := finrank_mul_rpow_pow_mul_le_volume_real_sub hn hGm hG hF
    (div_pos hη (by linarith)) hsub
  rw [← measureReal_sdiff hGF hGm hF, ← hSFG] at hshell
  -- On `S` the gradient has norm at least `1 - ε`, and the calibration bounds its integral.
  have hlow : (1 - ε) * volume.real S ≤ ∫ x in S, ‖fderiv ℝ w x‖ :=
    setIntegral_ge_of_const_le_real hSm hSfin
      (fun x hx => by linarith [(abs_lt.1 (hgrad x hx.1.le hx.2.le)).1]) hint
  have hcal := setIntegral_norm_fderiv_le hw hη ψ hψ
  refine le_of_mul_le_mul_left ?_ hη
  calc η * ((1 - ε) / (1 + ε) * (n * volume.real (ball (0 : E) 1) ^ (n : ℝ)⁻¹ *
          (volume.real G ^ (n : ℝ)⁻¹) ^ (n - 1)))
      = (1 - ε) * (n * (volume.real G ^ (n : ℝ)⁻¹) ^ (n - 1) *
          (η / (1 + ε) * volume.real (ball (0 : E) 1) ^ (n : ℝ)⁻¹)) := by
        field_simp
    _ ≤ (1 - ε) * volume.real S := mul_le_mul_of_nonneg_left hshell (by linarith)
    _ ≤ _ := hlow.trans hcal

/-- **The limit over shrinking shells.** Let `w` be smooth with `{w ≥ -δ}` compact and
`‖Dw‖ = 1` on its zero level, let `F = {w > 0}` have positive volume, and let the test vector
field `ψ` satisfy `Dw (ψ) = -‖Dw‖` on `{|w| ≤ η₀}`. Then for every `0 < ε < 1`,
`(1 - ε) / (1 + ε) n ω_n ^ (1 / n) (|F| ^ (1 / n)) ^ (n - 1) ≤ ∫_F div ψ`. -/
private theorem div_mul_le_integral_mul_indicator {w : E → ℝ} (hw : ContDiff ℝ ∞ w) {δ : ℝ}
    (hδ : 0 < δ) (hK : IsCompact {x | -δ ≤ w x}) (hnorm : ∀ x, w x = 0 → ‖fderiv ℝ w x‖ = 1)
    (hn : finrank ℝ E ≠ 0) (hV : volume {x | 0 < w x} ≠ 0) (ψ : 𝓓(⊤, E)) {η₀ : ℝ}
    (hη₀ : 0 < η₀) (hψ : ∀ x, |w x| ≤ η₀ → fderiv ℝ w x (ψ x) = -‖fderiv ℝ w x‖) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) :
    (1 - ε) / (1 + ε) * (finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
        (volume.real {x | 0 < w x} ^ (finrank ℝ E : ℝ)⁻¹) ^ (finrank ℝ E - 1)) ≤
      ∫ x, divergenceCLM ψ x * {x | 0 < w x}.indicator 1 x := by
  set n := finrank ℝ E
  set F := {x | 0 < w x}
  have hF : volume F ≠ ⊤ := ne_top_of_le_ne_top hK.measure_lt_top.ne
    (measure_mono fun x hx => ((neg_lt_zero.2 hδ).trans hx).le)
  have hfd : Continuous fun x => ‖fderiv ℝ w x‖ := (hw.continuous_fderiv (by simp)).norm
  -- Near the zero level, `‖Dw‖` lies within `ε` of `1`.
  obtain ⟨η₁, hη₁, -, hη₁C⟩ := exists_forall_abs_le_notMem hw.continuous hδ hK
    (C := {x | ε ≤ |‖fderiv ℝ w x‖ - 1|})
    (isClosed_le continuous_const (hfd.sub continuous_const).abs) fun x hx h0 => by
      have hx : ε ≤ |‖fderiv ℝ w x‖ - 1| := hx
      rw [hnorm x h0, sub_self, abs_zero] at hx
      linarith
  -- Along `η k = min η₀ η₁ / (k + 1)`, apply the one-step estimate and let `k → ∞`.
  set m := min η₀ η₁
  have hm : 0 < m := lt_min hη₀ hη₁
  let η : ℕ → ℝ := fun k => m / (k + 1)
  have hηpos (k : ℕ) : 0 < η k := by positivity
  have hηm (k : ℕ) : η k ≤ m := div_le_self hm.le (by linarith [k.cast_nonneg (α := ℝ)])
  have hηanti : Antitone η := fun i j hij =>
    div_le_div_of_nonneg_left hm.le (by positivity) (by gcongr)
  have hηlim : Tendsto η atTop (𝓝 0) := by
    have := (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul m
    rw [mul_zero] at this
    exact this.congr fun k => by simp only [η]; ring
  let G : ℕ → Set E := fun k => {x | η k ≤ w x}
  let S : ℕ → Set E := fun k => w ⁻¹' Ioo 0 (η k)
  -- The superlevel sets `G k` exhaust `F`, and the shells `S k` shrink to the empty set.
  have hGlim : Tendsto (fun k => volume (G k)) atTop (𝓝 (volume F)) := by
    have hU : (⋃ k, G k) = F := by
      ext x
      simp only [mem_iUnion]
      refine ⟨fun ⟨k, hk⟩ => (hηpos k).trans_le hk, fun hx => ?_⟩
      exact ((hηlim.eventually (gt_mem_nhds hx)).exists).imp fun k hk => hk.le
    have hmono : Monotone G := fun i j hij x (hx : η i ≤ w x) => (hηanti hij).trans hx
    have := tendsto_measure_iUnion_atTop (μ := volume) hmono
    rwa [hU] at this
  have hSlim : Tendsto (fun k => ∫ x in S k, |divergenceCLM ψ x|) atTop (𝓝 0) := by
    have hI : (⋂ k, S k) = ∅ := by
      refine eq_empty_of_forall_notMem fun x hx => ?_
      simp only [mem_iInter] at hx
      obtain ⟨k, hk⟩ := (hηlim.eventually (gt_mem_nhds (hx 0).1)).exists
      exact (hx k).2.not_gt hk
    have hanti : Antitone S := fun i j hij x (hx : w x ∈ Ioo 0 (η j)) =>
      ⟨hx.1, hx.2.trans_le (hηanti hij)⟩
    have hDint : Integrable fun x => |divergenceCLM ψ x| :=
      ((divergenceCLM ψ).continuous.integrable_of_hasCompactSupport
        (divergenceCLM ψ).hasCompactSupport).abs
    have := tendsto_setIntegral_of_antitone (μ := volume)
      (fun k => hw.continuous.measurable measurableSet_Ioo) hanti ⟨0, hDint.integrableOn⟩
    rwa [hI, setIntegral_empty] at this
  have hlhs : Tendsto (fun k => (1 - ε) / (1 + ε) * (n * volume.real (ball (0 : E) 1) ^ (n : ℝ)⁻¹ *
      (volume.real (G k) ^ (n : ℝ)⁻¹) ^ (n - 1))) atTop
      (𝓝 ((1 - ε) / (1 + ε) * (n * volume.real (ball (0 : E) 1) ^ (n : ℝ)⁻¹ *
        (volume.real F ^ (n : ℝ)⁻¹) ^ (n - 1)))) := by
    have hreal := (ENNReal.tendsto_toReal hF).comp hGlim
    exact (((Real.continuous_rpow_const (by positivity)).tendsto _).comp hreal).pow _
      |>.const_mul _ |>.const_mul _
  refine le_of_tendsto_of_tendsto hlhs
    (by simpa only [add_zero] using hSlim.const_add (∫ x, divergenceCLM ψ x * F.indicator 1 x)) ?_
  filter_upwards [hGlim.eventually_ne hV] with k hk
  refine div_mul_le_integral_add_setIntegral (hw.of_le (by simp)) hn (hηpos k) hε hε1 hF
    (nonempty_of_measure_ne_zero hk) (fun x hx0 hxη => ?_)
    ((hfd.continuousOn.integrableOn_compact hK).mono_set fun x hx => ?_) ψ fun x hx => ?_
  · exact lt_of_not_ge (hη₁C x (abs_le.2 ⟨by linarith [hηpos k], hxη.trans
      ((hηm k).trans (min_le_right _ _))⟩))
  · exact ((neg_lt_zero.2 hδ).trans (hx : w x ∈ Ioo 0 (η k)).1).le
  · exact hψ x (abs_le.2 ⟨by linarith [hx.1], hx.2.le.trans ((hηm k).trans (min_le_left _ _))⟩)

/-- **The sharp isoperimetric inequality for a normalized smooth defining function.** Let `w` be
smooth with `{w ≥ -δ}` compact for some `δ > 0` and `‖Dw‖ = 1` on its zero level. In dimension
`n ≥ 1`, if `F = {w > 0}` has positive volume, then `n ω_n ^ (1 / n) |F| ^ (1 - 1 / n) ≤ P(F)`. -/
private theorem ofReal_le_perimeter_setOf_pos {w : E → ℝ} (hw : ContDiff ℝ ∞ w) {δ : ℝ}
    (hδ : 0 < δ) (hK : IsCompact {x | -δ ≤ w x}) (hnorm : ∀ x, w x = 0 → ‖fderiv ℝ w x‖ = 1)
    (hn : finrank ℝ E ≠ 0) (hV : volume {x | 0 < w x} ≠ 0) :
    ENNReal.ofReal (finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
        volume.real {x | 0 < w x} ^ (1 - (finrank ℝ E : ℝ)⁻¹)) ≤
      perimeter volume ⊤ {x | 0 < w x} := by
  set n := finrank ℝ E
  obtain ⟨η₀, hη₀, ψ, hψ1, hψ⟩ := exists_testFunction_fderiv_apply_eq_neg_norm hw hδ hK
    fun x hx h0 => by
      have := hnorm x hx
      rw [h0, norm_zero] at this
      exact zero_ne_one this
  -- It suffices to bound `∫_F div ψ`, which is at most the perimeter of `F`.
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    ((ofReal_integral_le_totalVariationOn ψ hψ1).trans_eq perimeter_def.symm)
  have hpow : volume.real {x | 0 < w x} ^ (1 - (n : ℝ)⁻¹) =
      (volume.real {x | 0 < w x} ^ (n : ℝ)⁻¹) ^ (n - 1) := by
    rw [← Real.rpow_mul_natCast measureReal_nonneg, Nat.cast_pred (Nat.pos_of_ne_zero hn),
      mul_sub, mul_one, inv_mul_cancel₀ (Nat.cast_ne_zero.2 hn)]
  rw [hpow]
  -- Let the gradient tolerance `ε` tend to zero.
  have hlim : Tendsto (fun ε : ℝ => (1 - ε) / (1 + ε) * (n * volume.real (ball (0 : E) 1) ^
      (n : ℝ)⁻¹ * (volume.real {x | 0 < w x} ^ (n : ℝ)⁻¹) ^ (n - 1))) (𝓝[>] 0)
      (𝓝 (n * volume.real (ball (0 : E) 1) ^ (n : ℝ)⁻¹ *
        (volume.real {x | 0 < w x} ^ (n : ℝ)⁻¹) ^ (n - 1))) := by
    have : ContinuousAt (fun ε : ℝ => (1 - ε) / (1 + ε) * (n * volume.real (ball (0 : E) 1) ^
        (n : ℝ)⁻¹ * (volume.real {x | 0 < w x} ^ (n : ℝ)⁻¹) ^ (n - 1))) 0 := by
      fun_prop (disch := norm_num)
    simpa using this.tendsto.mono_left nhdsWithin_le_nhds
  exact le_of_tendsto hlim (by
    filter_upwards [Ioo_mem_nhdsGT one_pos] with ε hε using
      div_mul_le_integral_mul_indicator hw hδ hK hnorm hn hV ψ hη₀ hψ hε.1 hε.2)

omit [MeasurableSpace E] [BorelSpace E] in
/-- **A normalized defining function for a regular superlevel set.** Let `u` be smooth and
compactly supported, and let `t > 0` be a regular value of `u`. Then
`w = (u - t) / √(‖∇u‖² + (u - t)²)` is smooth, positive exactly on `{u > t}`, equal to `-1` off
the support of `u`, and its derivative has norm one on its zero level `{u = t}`. -/
private theorem exists_contDiff_setOf_pos_eq_setOf_lt {u : E → ℝ} (hu : ContDiff ℝ ∞ u)
    (huc : HasCompactSupport u) {t : ℝ} (ht : 0 < t) (hreg : ∀ x, u x = t → fderiv ℝ u x ≠ 0) :
    ∃ w : E → ℝ, ContDiff ℝ ∞ w ∧ IsCompact {x | -(1 / 2 : ℝ) ≤ w x} ∧
      (∀ x, w x = 0 → ‖fderiv ℝ w x‖ = 1) ∧ {x | 0 < w x} = {x | t < u x} := by
  -- `G` is the gradient of `u` and `g = √(‖∇u‖² + (u - t)²)` is a smooth positive normalizer.
  let G : E → E := ∇ u
  have hG : ContDiff ℝ ∞ G := hu.gradient_right le_rfl
  have hGnorm (x : E) : ‖G x‖ = ‖fderiv ℝ u x‖ := norm_gradient_eq_norm_fderiv u x
  let q : E → ℝ := fun x => ‖G x‖ ^ 2 + (u x - t) ^ 2
  have hq (x : E) : 0 < q x := by
    by_cases hx : u x = t
    · have hGx : 0 < ‖G x‖ := by rw [hGnorm, norm_pos_iff]; exact hreg x hx
      simp only [q, hx, sub_self]
      positivity
    · have := sq_pos_of_ne_zero (sub_ne_zero.2 hx)
      positivity
  let g : E → ℝ := fun x => √(q x)
  have hg : ContDiff ℝ ∞ g :=
    (((contDiff_norm_sq ℝ).comp hG).add ((hu.sub contDiff_const).pow 2)).sqrt fun x => (hq x).ne'
  have hgpos (x : E) : 0 < g x := Real.sqrt_pos.2 (hq x)
  let w : E → ℝ := fun x => (u x - t) / g x
  have hw : ContDiff ℝ ∞ w := (hu.sub contDiff_const).div hg fun x => (hgpos x).ne'
  have hset : {x | 0 < w x} = {x | t < u x} := by
    ext x
    exact (div_pos_iff_of_pos_right (hgpos x)).trans sub_pos
  -- Off the support of `u`, `w = -1`, so `{w ≥ -1/2}` is compact.
  have hK : IsCompact {x | -(1 / 2 : ℝ) ≤ w x} := by
    refine huc.isCompact.of_isClosed_subset (isClosed_le continuous_const hw.continuous)
      fun x hx => ?_
    by_contra hxs
    have hu0 : u x = 0 := image_eq_zero_of_notMem_tsupport hxs
    have hgx : g x = t := by
      simp [g, q, G, gradient_of_notMem_tsupport hxs, hu0, Real.sqrt_sq ht.le]
    have hx : -(1 / 2 : ℝ) ≤ (u x - t) / g x := hx
    rw [hgx, hu0, zero_sub, neg_div, div_self ht.ne'] at hx
    linarith
  -- On the level `{u = t}` the derivative of `w` is `Du / ‖Du‖`.
  have hnorm (x : E) (hx : w x = 0) : ‖fderiv ℝ w x‖ = 1 := by
    have hux : u x = t := sub_eq_zero.1 ((div_eq_zero_iff.1 hx).resolve_right (hgpos x).ne')
    have h1 : HasFDerivAt (fun y => u y - t) (fderiv ℝ u x) x :=
      ((hu.differentiable (by simp)) x).hasFDerivAt.sub_const t
    have h2 := (((hg.differentiable (by simp)) x).inv (hgpos x).ne').hasFDerivAt
    have hd : HasFDerivAt w ((g x)⁻¹ • fderiv ℝ u x) x := by
      have := h1.mul h2
      simp only [hux, sub_self, zero_smul, zero_add] at this
      exact this.congr_of_eventuallyEq (.of_forall fun y => div_eq_mul_inv _ _)
    have hgx : g x = ‖fderiv ℝ u x‖ := by
      simp only [g, q, hux, sub_self, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        add_zero, Real.sqrt_sq (norm_nonneg _), hGnorm]
    rw [hd.fderiv, norm_smul, norm_inv, Real.norm_of_nonneg (hgpos x).le, hgx,
      inv_mul_cancel₀ (norm_ne_zero_iff.2 (hreg x hux))]
  exact ⟨w, hw, hK, hnorm, hset⟩

/-- **The sharp isoperimetric inequality for regular superlevel sets.** Let `u` be smooth and
compactly supported, and let `t > 0` be a regular value of `u`. In dimension `n ≥ 1`, if
`F = {u > t}` has positive volume, then `n ω_n ^ (1 / n) |F| ^ (1 - 1 / n) ≤ P(F)`. -/
private theorem ofReal_le_perimeter_setOf_lt {u : E → ℝ} (hu : ContDiff ℝ ∞ u)
    (huc : HasCompactSupport u) {t : ℝ} (ht : 0 < t) (hreg : ∀ x, u x = t → fderiv ℝ u x ≠ 0)
    (hn : finrank ℝ E ≠ 0) (hV : volume {x | t < u x} ≠ 0) :
    ENNReal.ofReal (finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
        volume.real {x | t < u x} ^ (1 - (finrank ℝ E : ℝ)⁻¹)) ≤
      perimeter volume ⊤ {x | t < u x} := by
  obtain ⟨w, hw, hK, hnorm, hset⟩ := exists_contDiff_setOf_pos_eq_setOf_lt hu huc ht hreg
  rw [← hset] at hV ⊢
  exact ofReal_le_perimeter_setOf_pos hw (by norm_num) hK hnorm hn hV

/-- The sharp isoperimetric inequality in the form `n ω_n ^ (1 / n) |s| ^ (1 - 1 / n) ≤ P(s)` for
a null-measurable set of finite positive volume, obtained from the smooth case by approximation
in measure and in perimeter. -/
private theorem ofReal_le_perimeter {s : Set E} (hs : NullMeasurableSet s volume)
    (hμs : volume s ≠ ⊤) (hn : finrank ℝ E ≠ 0) (hs0 : volume s ≠ 0) :
    ENNReal.ofReal (finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
        volume.real s ^ (1 - (finrank ℝ E : ℝ)⁻¹)) ≤ perimeter volume ⊤ s := by
  obtain ⟨u, t, hprop, hsymm, hP⟩ := hs.exists_smooth_perimeter_approximation hμs
  set F : ℕ → Set E := fun k => {x | t k < u k x}
  have hFm (k : ℕ) : NullMeasurableSet (F k) volume :=
    (measurableSet_lt measurable_const (hprop k).1.continuous.measurable).nullMeasurableSet
  have hFfin (k : ℕ) : volume (F k) ≠ ⊤ :=
    ne_top_of_le_ne_top (hprop k).2.2.2.2.1.measure_lt_top.ne (measure_mono subset_closure)
  -- The volumes of the approximations converge to the volume of `s`.
  have hV : Tendsto (fun k => volume.real (F k)) atTop (𝓝 (volume.real s)) := by
    have h0 : Tendsto (fun k => volume.real (F k ∆ s)) atTop (𝓝 0) := by
      have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hsymm
      rwa [ENNReal.toReal_zero] at this
    refine tendsto_iff_dist_tendsto_zero.2 (squeeze_zero (fun _ => dist_nonneg) (fun k => ?_) h0)
    rw [Real.dist_eq]
    exact abs_measureReal_sub_le_measureReal_symmDiff' (hFm k) hs (hFfin k) hμs
  have hpos : 0 < volume.real s := ENNReal.toReal_pos hs0 hμs
  refine le_of_tendsto_of_tendsto (ENNReal.tendsto_ofReal ((((Real.continuous_rpow_const
    (sub_nonneg.2 (inv_le_one_of_one_le₀ (Nat.one_le_cast.2 (Nat.pos_of_ne_zero hn))))).tendsto
      _).comp hV).const_mul _)) hP ?_
  filter_upwards [hV.eventually (lt_mem_nhds hpos)] with k hk
  obtain ⟨hu, huc, htk, hreg, -⟩ := hprop k
  refine ofReal_le_perimeter_setOf_lt hu huc htk.1 (fun x hx h0 => ?_) hn ?_
  · obtain ⟨v, hv⟩ := hreg x hx 1
    simp [h0] at hv
  · intro h
    rw [measureReal_def, (h : volume (F k) = 0), ENNReal.toReal_zero] at hk
    exact hk.false

end TauCeti

namespace MeasureTheory.NullMeasurableSet

open TauCeti

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- **The sharp isoperimetric inequality, real-valued form.** In a Euclidean space of dimension
`n ≥ 1`, every null-measurable set `s` of finite positive volume and finite perimeter satisfies
`n ω_n ^ (1 / n) |s| ^ (1 - 1 / n) ≤ P(s)`, where `ω_n = volume (ball 0 1)` and `P(s)` is the
perimeter of `s` in the whole space. No boundedness or regularity is assumed. -/
theorem mul_volume_real_rpow_mul_le_perimeter_toReal
    {s : Set E} (hs : NullMeasurableSet s volume) (hμs : volume s ≠ ⊤) (hn : finrank ℝ E ≠ 0)
    (hs0 : volume s ≠ 0) (hP : perimeter volume ⊤ s ≠ ⊤) :
    finrank ℝ E * volume.real (ball (0 : E) 1) ^ (finrank ℝ E : ℝ)⁻¹ *
        volume.real s ^ (1 - (finrank ℝ E : ℝ)⁻¹) ≤ (perimeter volume ⊤ s).toReal :=
  (ENNReal.ofReal_le_iff_le_toReal hP).1 (ofReal_le_perimeter hs hμs hn hs0)

/-- **The sharp isoperimetric inequality.** In a Euclidean space of dimension `n ≥ 1`, every
null-measurable set `s` of finite positive volume satisfies `P(s)^n ≥ n^n ω_n |s|^(n-1)`, where
`ω_n = volume (ball 0 1)` and `P(s)` is the perimeter of `s` in the whole space, finite or
infinite. No boundedness or regularity is assumed. Balls attain equality
(`TauCeti.perimeter_ball_pow`). -/
theorem finrank_pow_mul_volume_ball_mul_volume_pow_le_perimeter_pow
    {s : Set E} (hs : NullMeasurableSet s volume) (hμs : volume s ≠ ⊤) (hn : finrank ℝ E ≠ 0)
    (hs0 : volume s ≠ 0) :
    (finrank ℝ E : ℝ≥0∞) ^ finrank ℝ E * volume (ball (0 : E) 1) * volume s ^ (finrank ℝ E - 1) ≤
      perimeter volume ⊤ s ^ finrank ℝ E := by
  rw [finrank_pow_mul_volume_ball_mul_volume_pow_eq_ofReal hμs hn,
    ENNReal.ofReal_pow (by positivity)]
  exact pow_le_pow_left₀ zero_le (ofReal_le_perimeter hs hμs hn hs0) _

end MeasureTheory.NullMeasurableSet
