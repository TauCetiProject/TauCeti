/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import TauCeti.Analysis.Sobolev.WeakDeriv.Divergence
import Mathlib.Analysis.Calculus.BumpFunction.InnerProduct
import Mathlib.Analysis.InnerProductSpace.Calculus
import TauCeti.Analysis.Calculus.FDeriv.Clamp
import TauCeti.Analysis.Calculus.Gradient
import TauCeti.Analysis.Sobolev.WeakDeriv.Lipschitz
import TauCeti.Topology.Order.Sublevel

/-!
# Calibrating the shells of a smooth defining function

Let `w` be a smooth real function on a finite-dimensional real inner product space whose
derivative does not vanish on its zero level, so that `F = {w > 0}` is a set with smooth boundary
`{w = 0}`. The unit normal field `-∇w / ‖∇w‖` calibrates `w` near that boundary: if `{w ≥ -δ}` is
compact, a cutoff of this field is an admissible test vector field `ψ`, with `‖ψ‖ ≤ 1`
everywhere and `Dw (ψ) = -‖Dw‖` on a band `{|w| ≤ η}`
(`ContDiff.exists_testFunction_fderiv_apply_eq_neg_norm`).

Integrating by parts against the clamped function `max 0 (min w η)` then controls the gradient
of `w` on the shell `S = {0 < w < η}` by the divergence of `ψ`:

`∫_S ‖Dw‖ ≤ η (∫_F div ψ + ∫_S |div ψ|)`

(`ContDiff.setIntegral_norm_fderiv_le`). Since `∫_F div ψ` is at most the perimeter of `F`, this
bounds the volume of thin shells next to a smooth boundary by the perimeter. It drives the sharp
isoperimetric inequality for smooth sets and the comparison of the outer Minkowski content of a
smooth set with its perimeter.

## References

* F. Maggi, *Sets of Finite Perimeter and Geometric Variational Problems*, Cambridge University
  Press, 2012, Chapter 13.
-/

public section

noncomputable section

open MeasureTheory Set Filter TopologicalSpace TestFunction InnerProductSpace TauCeti
open scoped ENNReal Topology ContDiff Distributions Gradient

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- A smooth function `w` whose derivative does not vanish on its zero level, with `{w ≥ -δ}`
compact, admits an admissible test vector field equal to `-∇w / ‖∇w‖` near the zero level. Its
derivative pairing with `w` there is `-‖Dw‖`. -/
theorem ContDiff.exists_testFunction_fderiv_apply_eq_neg_norm {w : E → ℝ} (hw : ContDiff ℝ ∞ w)
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

variable [MeasurableSpace E] [BorelSpace E]

/-- **The calibration estimate.** If a test vector field `ψ` satisfies `Dw (ψ) = -‖Dw‖` on the
shell `S = {0 < w < η}`, as `-∇w / ‖∇w‖` does, then
`∫_S ‖Dw‖ ≤ η (∫_{w > 0} div ψ + ∫_S |div ψ|)`. -/
theorem ContDiff.setIntegral_norm_fderiv_le {w : E → ℝ} (hw : ContDiff ℝ 1 w) {η : ℝ} (hη : 0 < η)
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
