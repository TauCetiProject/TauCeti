/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.LinearAlgebra.AffineSpace.Slope
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
public import Mathlib.Topology.EMetricSpace.BoundedVariation
public import Mathlib.Topology.Order.LeftRightLim
import Mathlib.Analysis.BoundedVariation
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.Basic.Real.Sign
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Order.Monotone.Odd
import TauCeti.MeasureTheory.Integral.Exp.Decay
import TauCeti.Topology.EMetricSpace.BoundedVariation

/-!
# Admissible test functions for Weil's explicit formula

Mestre's form of Weil's explicit formula pairs the zeros and poles of an `L`-function with the
values of the bilateral transform `Φ_F(s) = ∫ F(x) exp((s - 1/2) x) dx` of a test function
`F : ℝ → ℝ`. This file defines the class of test functions for which the formula is proved, with
the exponential weight imposed on both tails, and the transform.

For `c : ℝ`, `TauCeti.WeilTestFunction c F` states that

* for some `ε > 0`, the weighted function `x ↦ F x * exp ((1/2 + c + ε) * |x|)` is Lebesgue
  integrable and has bounded variation on `ℝ`;
* `F` is the mean of its left and right limits at every point;
* the difference quotient `slope F 0`, equal to `(F x - F 0) / x` for `x ≠ 0` and to `0` at `0`,
  has bounded variation on `ℝ`.

Imposing the weight on both tails strengthens Mestre's one-signed condition; it covers `F` and its
reflection `x ↦ F (-x)` at once, as the contour proof of the explicit formula needs. The difference
quotient may have distinct one-sided limits at `0`: no differentiability at `0` is required, and
`x ↦ exp (-|x|)` is admissible for `c = 0`. The explicit formula uses the condition for `c ≥ 0`;
it is meaningful for every real `c`, and nothing below assumes `c ≥ 0`.

## Main definitions

* `TauCeti.WeilTestFunction c F`: `F` is an admissible test function for `c`.
* `TauCeti.weilTestFunctionSubmodule c`: the admissible test functions for `c`, as a real vector
  subspace of `ℝ → ℝ`.
* `TauCeti.weilTransform F s`: the bilateral transform `∫ F(x) exp((s - 1/2) x) dx`, a totalized
  integral, whose value says nothing about convergence.

## Main results

* `TauCeti.WeilTestFunction.integrable_mul_cexp`: for an admissible `F`, the integrand of the
  transform is integrable on the closed strip `-c ≤ Re s ≤ 1 + c`.
* `TauCeti.WeilTestFunction.comp_neg`: the reflection `x ↦ F (-x)` of an admissible function is
  admissible for the same `c`; `TauCeti.weilTransform_comp_neg` reflects the transform in `1/2`.
* `TauCeti.WeilTestFunction.add`, `TauCeti.WeilTestFunction.const_smul`: real linear combinations
  of admissible functions are admissible.
* `TauCeti.WeilTestFunction.mono`: an admissible function for `c` is admissible for every
  `c' ≤ c`.
* `TauCeti.WeilTestFunction.tendsto_leftLim`, `TauCeti.WeilTestFunction.tendsto_rightLim`: an
  admissible function has one-sided limits everywhere, and by definition it is their mean.
* `TauCeti.WeilTestFunction.exists_abs_sub_le`: `|F x - F 0| ≤ C |x|` for a constant `C ≥ 0`, so
  `F` is continuous at `0` (`TauCeti.WeilTestFunction.continuousAt_zero`).

## References

* J.-F. Mestre, *Formules explicites et minorations de conducteurs de variétés algébriques*,
  Compositio Math. 58 (1986), 209–232, §I.2.
-/

public section

open MeasureTheory Set Filter Topology Function

namespace TauCeti

/-- **Admissible test functions for Weil's explicit formula.** A function `F : ℝ → ℝ` is admissible
for `c` if, for some `ε > 0`, the weighted function `x ↦ F x * exp ((1 / 2 + c + ε) * |x|)` is
Lebesgue integrable and has bounded variation on `ℝ`, if `F` is the mean of its left and right
limits at every point, and if the difference quotient `slope F 0`, equal to `(F x - F 0) / x` for
`x ≠ 0` and to `0` at `0`, has bounded variation on `ℝ`. -/
structure WeilTestFunction (c : ℝ) (F : ℝ → ℝ) : Prop where
  /-- For some `ε > 0`, the weighted function is integrable and has bounded variation. -/
  exists_integrable_boundedVariationOn : ∃ ε > 0,
    Integrable (fun x ↦ F x * Real.exp ((1 / 2 + c + ε) * |x|)) ∧
      BoundedVariationOn (fun x ↦ F x * Real.exp ((1 / 2 + c + ε) * |x|)) univ
  /-- The function is the mean of its left and right limits at every point. -/
  eq_leftLim_add_rightLim_div_two (x : ℝ) : F x = (leftLim F x + rightLim F x) / 2
  /-- The difference quotient at `0` has bounded variation. -/
  boundedVariationOn_slope : BoundedVariationOn (slope F 0) univ

/-- The bilateral transform `Φ_F(s) = ∫ F(x) exp((s - 1/2) x) dx` of Weil's explicit formula. It is
a totalized Bochner integral: its value is `0` wherever the integrand is not integrable. -/
noncomputable def weilTransform (F : ℝ → ℝ) (s : ℂ) : ℂ :=
  ∫ x : ℝ, (F x : ℂ) * Complex.exp ((s - 1 / 2) * x)

/-- Reflecting the test function reflects its transform in the point `1 / 2`. -/
theorem weilTransform_comp_neg (F : ℝ → ℝ) (s : ℂ) :
    weilTransform (fun x ↦ F (-x)) s = weilTransform F (1 - s) := by
  rw [weilTransform, weilTransform,
    ← integral_neg_eq_self (fun x : ℝ ↦ (F x : ℂ) * Complex.exp ((1 - s - 1 / 2) * x))]
  congr 1 with x
  push_cast
  ring_nf

/-- `x ↦ exp (-(δ |x|))` has bounded variation on `ℝ` for `δ ≥ 0`: it increases on `(-∞, 0]` and
decreases on `[0, ∞)`, with values in `(0, 1]`. -/
private theorem boundedVariationOn_exp_neg_mul_abs {δ : ℝ} (hδ : 0 ≤ δ) :
    BoundedVariationOn (fun x : ℝ ↦ Real.exp (-(δ * |x|))) univ := by
  set g : ℝ → ℝ := fun x ↦ Real.exp (-(δ * |x|))
  have hbound (x : ℝ) : |g x| ≤ 1 := by
    rw [abs_of_pos (Real.exp_pos _)]
    exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg hδ (abs_nonneg x)))
  have hleft : BoundedVariationOn g (Iic 0) := by
    refine MonotoneOn.boundedVariationOn (fun x hx y hy hxy ↦ ?_) fun x _ ↦ hbound x
    simp only [g, Real.exp_le_exp, neg_le_neg_iff]
    rw [abs_of_nonpos hx, abs_of_nonpos hy]
    nlinarith
  have hright : BoundedVariationOn (-g) (Ici 0) := by
    refine MonotoneOn.boundedVariationOn (fun x hx y hy hxy ↦ ?_) fun x _ ↦ by
      simpa using hbound x
    simp only [g, Pi.neg_apply, neg_le_neg_iff, Real.exp_le_exp]
    rw [abs_of_nonneg hx, abs_of_nonneg hy]
    nlinarith
  have h := eVariationOn.union g (isGreatest_Iic (a := (0 : ℝ))) isLeast_Ici
  rw [Iic_union_Ici] at h
  rw [BoundedVariationOn, h]
  exact ENNReal.add_ne_top.2 ⟨hleft, by simpa [BoundedVariationOn] using hright⟩

/-- Lowering the exponential weight preserves integrability and bounded variation. -/
private theorem integrable_boundedVariationOn_of_le {F : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (h : Integrable (fun x : ℝ ↦ F x * Real.exp (b * |x|)) ∧
      BoundedVariationOn (fun x ↦ F x * Real.exp (b * |x|)) univ) :
    Integrable (fun x : ℝ ↦ F x * Real.exp (a * |x|)) ∧
      BoundedVariationOn (fun x ↦ F x * Real.exp (a * |x|)) univ := by
  have heq : (fun x ↦ F x * Real.exp (a * |x|)) =
      fun x ↦ F x * Real.exp (b * |x|) * Real.exp (-((b - a) * |x|)) := by
    ext x
    rw [mul_assoc, ← Real.exp_add]
    ring_nf
  rw [heq]
  refine ⟨h.1.mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun x ↦ ?_),
    h.2.fun_mul (boundedVariationOn_exp_neg_mul_abs (sub_nonneg.2 hab))⟩
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_one_iff.2 (neg_nonpos.2 (mul_nonneg (sub_nonneg.2 hab) (abs_nonneg x)))

namespace WeilTestFunction

variable {c c' : ℝ} {F G : ℝ → ℝ}

/-- An admissible function tends to its left limit from the left. -/
theorem tendsto_leftLim (hF : WeilTestFunction c F) (x : ℝ) :
    Tendsto F (𝓝[<] x) (𝓝 (leftLim F x)) := by
  obtain ⟨ε, -, -, hbv⟩ := hF.exists_integrable_boundedVariationOn
  have hc : Continuous fun y : ℝ ↦ Real.exp (-((1 / 2 + c + ε) * |y|)) := by fun_prop
  refine tendsto_leftLim_of_tendsto ⟨_, ((hbv.tendsto_leftLim x).mul
    ((hc.tendsto x).mono_left nhdsWithin_le_nhds)).congr fun y ↦ ?_⟩
  rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- An admissible function tends to its right limit from the right. -/
theorem tendsto_rightLim (hF : WeilTestFunction c F) (x : ℝ) :
    Tendsto F (𝓝[>] x) (𝓝 (rightLim F x)) := by
  obtain ⟨ε, -, -, hbv⟩ := hF.exists_integrable_boundedVariationOn
  have hc : Continuous fun y : ℝ ↦ Real.exp (-((1 / 2 + c + ε) * |y|)) := by fun_prop
  refine tendsto_rightLim_of_tendsto ⟨_, ((hbv.tendsto_rightLim x).mul
    ((hc.tendsto x).mono_left nhdsWithin_le_nhds)).congr fun y ↦ ?_⟩
  rw [mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, mul_one]

/-- An admissible function for `c` is admissible for every smaller `c'`, with the same weight
`1 / 2 + c + ε = 1 / 2 + c' + (ε + (c - c'))`. -/
theorem mono (hF : WeilTestFunction c F) (hc : c' ≤ c) : WeilTestFunction c' F := by
  obtain ⟨ε, hε, h⟩ := hF.exists_integrable_boundedVariationOn
  have hweight : 1 / 2 + c' + (ε + (c - c')) = 1 / 2 + c + ε := by ring
  exact ⟨⟨ε + (c - c'), by linarith, by rwa [hweight]⟩, hF.eq_leftLim_add_rightLim_div_two,
    hF.boundedVariationOn_slope⟩

/-- The reflection `x ↦ F (-x)` of an admissible function is admissible for the same `c`. -/
theorem comp_neg (hF : WeilTestFunction c F) : WeilTestFunction c fun x ↦ F (-x) := by
  obtain ⟨ε, hε, hint, hbv⟩ := hF.exists_integrable_boundedVariationOn
  have hneg : AntitoneOn (fun x : ℝ ↦ -x) univ := fun _ _ _ _ h ↦ neg_le_neg h
  have himage : (fun x : ℝ ↦ -x) '' univ = univ := by rw [image_neg_eq_neg, neg_univ]
  refine ⟨⟨ε, hε, by simpa only [abs_neg] using hint.comp_neg, ?_⟩, fun x ↦ ?_, ?_⟩
  · have h := eVariationOn.comp_eq_of_antitoneOn
      (fun x ↦ F x * Real.exp ((1 / 2 + c + ε) * |x|)) _ hneg
    rw [himage] at h
    simp only [comp_def, abs_neg] at h
    rw [BoundedVariationOn, h]
    exact hbv
  · have hl : Tendsto (fun y ↦ F (-y)) (𝓝[<] x) (𝓝 (rightLim F (-x))) :=
      (hF.tendsto_rightLim (-x)).comp tendsto_neg_nhdsLT
    have hr : Tendsto (fun y ↦ F (-y)) (𝓝[>] x) (𝓝 (leftLim F (-x))) :=
      (hF.tendsto_leftLim (-x)).comp tendsto_neg_nhdsGT
    rw [leftLim_eq_of_tendsto hl, rightLim_eq_of_tendsto hr,
      hF.eq_leftLim_add_rightLim_div_two (-x), add_comm]
  · have h : slope (fun x ↦ F (-x)) 0 = -(slope F 0 ∘ fun x ↦ -x) := by
      ext x
      simp [slope_def_field, div_neg]
    rw [h, BoundedVariationOn, eVariationOn.neg, eVariationOn.comp_eq_of_antitoneOn _ _ hneg,
      himage]
    exact hF.boundedVariationOn_slope

/-- The zero function is admissible. -/
protected theorem zero (c : ℝ) : WeilTestFunction c 0 where
  exists_integrable_boundedVariationOn := ⟨1, one_pos, by simp,
    by simp [BoundedVariationOn, eVariationOn.constant_on]⟩
  eq_leftLim_add_rightLim_div_two x := by
    rw [leftLim_eq_of_tendsto (f := 0) (y := 0) tendsto_const_nhds,
      rightLim_eq_of_tendsto (f := 0) (y := 0) tendsto_const_nhds]
    simp
  boundedVariationOn_slope := by
    simp [slope_fun_def_field, BoundedVariationOn, eVariationOn.constant_on]

/-- The sum of two admissible functions is admissible. -/
protected theorem add (hF : WeilTestFunction c F) (hG : WeilTestFunction c G) :
    WeilTestFunction c (F + G) := by
  obtain ⟨ε₁, hε₁, hF₁⟩ := hF.exists_integrable_boundedVariationOn
  obtain ⟨ε₂, hε₂, hG₂⟩ := hG.exists_integrable_boundedVariationOn
  have hF' := integrable_boundedVariationOn_of_le
    (by linarith [min_le_left ε₁ ε₂] : 1 / 2 + c + min ε₁ ε₂ ≤ 1 / 2 + c + ε₁) hF₁
  have hG' := integrable_boundedVariationOn_of_le
    (by linarith [min_le_right ε₁ ε₂] : 1 / 2 + c + min ε₁ ε₂ ≤ 1 / 2 + c + ε₂) hG₂
  have hsum : (fun x ↦ (F + G) x * Real.exp ((1 / 2 + c + min ε₁ ε₂) * |x|)) =
      (fun x ↦ F x * Real.exp ((1 / 2 + c + min ε₁ ε₂) * |x|)) +
        fun x ↦ G x * Real.exp ((1 / 2 + c + min ε₁ ε₂) * |x|) := by
    ext x
    simp only [Pi.add_apply]
    ring
  refine ⟨⟨min ε₁ ε₂, lt_min hε₁ hε₂, ?_, ?_⟩, fun x ↦ ?_, ?_⟩
  · rw [hsum]
    exact hF'.1.add hG'.1
  · rw [hsum]
    exact hF'.2.add hG'.2
  · rw [leftLim_eq_of_tendsto (f := F + G) ((hF.tendsto_leftLim x).add (hG.tendsto_leftLim x)),
      rightLim_eq_of_tendsto (f := F + G)
        ((hF.tendsto_rightLim x).add (hG.tendsto_rightLim x)),
      Pi.add_apply, hF.eq_leftLim_add_rightLim_div_two x, hG.eq_leftLim_add_rightLim_div_two x]
    ring
  · have h : slope (F + G) 0 = slope F 0 + slope G 0 := by
      ext x
      simp only [slope_def_field, Pi.add_apply]
      ring
    rw [h]
    exact hF.boundedVariationOn_slope.add hG.boundedVariationOn_slope

/-- A real multiple of an admissible function is admissible. -/
protected theorem const_smul (hF : WeilTestFunction c F) (r : ℝ) : WeilTestFunction c (r • F) := by
  obtain ⟨ε, hε, hint, hbv⟩ := hF.exists_integrable_boundedVariationOn
  refine ⟨⟨ε, hε, ?_, ?_⟩, fun x ↦ ?_, ?_⟩
  · simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc] using hint.const_mul r
  · simpa only [Pi.smul_apply, smul_eq_mul, mul_assoc, comp_def] using
      (lipschitzWith_smul r).comp_boundedVariationOn hbv
  · rw [leftLim_eq_of_tendsto (f := r • F) ((hF.tendsto_leftLim x).const_smul r),
      rightLim_eq_of_tendsto (f := r • F) ((hF.tendsto_rightLim x).const_smul r), Pi.smul_apply,
      hF.eq_leftLim_add_rightLim_div_two x]
    simp only [smul_eq_mul]
    ring
  · have h : slope (r • F) 0 = (fun y ↦ r • y) ∘ slope F 0 := by
      ext x
      simp only [slope_def_field, Pi.smul_apply, smul_eq_mul, comp_apply]
      ring
    rw [h]
    exact (lipschitzWith_smul r).comp_boundedVariationOn hF.boundedVariationOn_slope

/-- The negation of an admissible function is admissible. -/
protected theorem neg (hF : WeilTestFunction c F) : WeilTestFunction c (-F) := by
  simpa using hF.const_smul (-1)

/-- The difference of two admissible functions is admissible. -/
protected theorem sub (hF : WeilTestFunction c F) (hG : WeilTestFunction c G) :
    WeilTestFunction c (F - G) := by
  simpa [sub_eq_add_neg] using hF.add hG.neg

/-- For an admissible `F`, the integrand `x ↦ F x * exp ((s - 1 / 2) x)` of the transform
`weilTransform F s` is integrable on the closed strip `-c ≤ Re s ≤ 1 + c`. -/
theorem integrable_mul_cexp (hF : WeilTestFunction c F) {s : ℂ} (hs₀ : -c ≤ s.re)
    (hs₁ : s.re ≤ 1 + c) :
    Integrable (fun x : ℝ ↦ (F x : ℂ) * Complex.exp ((s - 1 / 2) * x)) := by
  obtain ⟨ε, hε, hint, -⟩ := hF.exists_integrable_boundedVariationOn
  set a := 1 / 2 + c + ε with ha
  have heq : (fun x : ℝ ↦ (F x : ℂ) * Complex.exp ((s - 1 / 2) * x)) =
      fun x : ℝ ↦ ((F x * Real.exp (a * |x|) : ℝ) : ℂ) *
        Complex.exp ((s - 1 / 2) * x - a * |x|) := by
    ext x
    push_cast
    rw [mul_assoc, ← Complex.exp_add]
    ring_nf
  rw [heq]
  refine hint.ofReal.mul_bdd (c := 1) (by fun_prop) (Eventually.of_forall fun x ↦ ?_)
  have h₁ : |s.re - 1 / 2| ≤ 1 / 2 + c := abs_le.2 ⟨by linarith, by linarith⟩
  have h₂ : (s.re - 1 / 2) * x ≤ |s.re - 1 / 2| * |x| := by
    rw [← abs_mul]
    exact le_abs_self _
  have h₃ := mul_le_mul_of_nonneg_right h₁ (abs_nonneg x)
  rw [Complex.norm_exp, Real.exp_le_one_iff]
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
    sub_zero, Complex.one_re, Complex.div_ofNat_re, Complex.sub_im, Complex.one_im,
    Complex.div_ofNat_im, zero_div]
  nlinarith [mul_nonneg hε.le (abs_nonneg x)]

/-- An admissible function satisfies `|F x - F 0| ≤ C |x|` for some constant `C ≥ 0`. -/
theorem exists_abs_sub_le (hF : WeilTestFunction c F) :
    ∃ C, 0 ≤ C ∧ ∀ x, |F x - F 0| ≤ C * |x| := by
  refine ⟨(eVariationOn (slope F 0) univ).toReal, ENNReal.toReal_nonneg, fun x ↦ ?_⟩
  have h := hF.boundedVariationOn_slope.dist_le (mem_univ x) (mem_univ 0)
  rw [slope_same, Real.dist_eq, sub_zero] at h
  have hx : F x - F 0 = x * slope F 0 x := by simpa using (sub_smul_slope F 0 x).symm
  rw [hx, abs_mul, mul_comm]
  exact mul_le_mul_of_nonneg_right h (abs_nonneg x)

/-- An admissible function is continuous at `0`, although its one-sided derivatives there need not
agree. -/
theorem continuousAt_zero (hF : WeilTestFunction c F) : ContinuousAt F 0 := by
  obtain ⟨C, -, hC⟩ := hF.exists_abs_sub_le
  exact continuousAt_of_locally_lipschitz one_pos C fun y _ ↦ by
    simpa [Real.dist_eq] using hC y

end WeilTestFunction

/-- The admissible test functions for `c` form a real vector subspace of `ℝ → ℝ`. -/
def weilTestFunctionSubmodule (c : ℝ) : Submodule ℝ (ℝ → ℝ) where
  carrier := {F | WeilTestFunction c F}
  add_mem' := WeilTestFunction.add
  zero_mem' := WeilTestFunction.zero c
  smul_mem' r _ hF := hF.const_smul r

/-- Membership in `weilTestFunctionSubmodule c` is admissibility for `c`. -/
@[simp]
theorem mem_weilTestFunctionSubmodule {c : ℝ} {F : ℝ → ℝ} :
    F ∈ weilTestFunctionSubmodule c ↔ WeilTestFunction c F :=
  Iff.rfl

/-! ### Checks -/

example (s : ℂ) : weilTransform 0 s = 0 := by
  simp [weilTransform]

/-- The difference quotient at `0` of `x ↦ exp (-|x|)` jumps from `1` to `-1` across `0`. Adding
`Real.sign` removes the jump and leaves an odd monotone function with values in `[-1, 1]`. -/
private theorem monotone_slope_exp_neg_abs_add_sign :
    Monotone (fun x ↦ slope (fun x : ℝ ↦ Real.exp (-|x|)) 0 x + Real.sign x) ∧
      ∀ x, |slope (fun x : ℝ ↦ Real.exp (-|x|)) 0 x + Real.sign x| ≤ 1 := by
  set h : ℝ → ℝ := fun x ↦ slope (fun x : ℝ ↦ Real.exp (-|x|)) 0 x + Real.sign x
  have hodd (x : ℝ) : h (-x) = -h x := by
    simp only [h, slope_def_field, abs_neg, Real.sign_neg, sub_zero, div_neg]
    ring
  have hpos {y : ℝ} (hy : 0 < y) : h y = (Real.exp (-y) - 1) / y + 1 := by
    simp [h, slope_def_field, abs_of_pos hy, Real.sign_of_pos hy]
  have hmem {y : ℝ} (hy : 0 < y) : 0 ≤ h y ∧ h y ≤ 1 := by
    have h₁ : -1 ≤ (Real.exp (-y) - 1) / y := by
      rw [le_div_iff₀ hy]
      linarith [Real.add_one_le_exp (-y)]
    have h₂ : (Real.exp (-y) - 1) / y ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by simp [Real.exp_le_one_iff, hy.le]) hy.le
    rw [hpos hy]
    constructor <;> linarith
  have hmono : MonotoneOn h (Ici 0) := by
    intro x hx y hy hxy
    rcases (mem_Ici.1 hx).eq_or_lt with rfl | hx'
    · rcases (mem_Ici.1 hy).eq_or_lt with rfl | hy'
      · exact le_rfl
      · simpa [h] using (hmem hy').1
    · have := convexOn_exp.secant_mono (mem_univ 0) (mem_univ (-y)) (mem_univ (-x))
        (by linarith) (by linarith) (by linarith)
      simp only [Real.exp_zero, sub_zero, div_neg] at this
      rw [hpos hx', hpos (hx'.trans_le hxy)]
      linarith
  refine ⟨monotone_of_odd_of_monotoneOn_nonneg hodd hmono, fun x ↦ ?_⟩
  rcases lt_trichotomy x 0 with hx | rfl | hx
  · have := hmem (neg_pos.2 hx)
    rw [hodd] at this
    exact abs_le.2 ⟨by linarith, by linarith⟩
  · simp
  · exact abs_le.2 ⟨by linarith [(hmem hx).1], (hmem hx).2⟩

/-- `x ↦ exp (-|x|)` is admissible for `c = 0`, although its difference quotient at `0` has the
distinct one-sided limits `1` and `-1`. -/
example : WeilTestFunction 0 fun x ↦ Real.exp (-|x|) := by
  have hweight : (fun x : ℝ ↦ Real.exp (-|x|) * Real.exp ((1 / 2 + 0 + 1 / 4) * |x|)) =
      fun x ↦ Real.exp (-(1 / 4 * |x|)) := by
    ext x
    rw [← Real.exp_add]
    ring_nf
  have hcont : Continuous fun x : ℝ ↦ Real.exp (-|x|) := by fun_prop
  have hsign : BoundedVariationOn Real.sign univ := by
    refine MonotoneOn.boundedVariationOn (C := 1) (fun x _ y _ hxy ↦ ?_) fun x _ ↦ ?_
    · rcases lt_trichotomy x 0 with hx | rfl | hx <;>
        rcases lt_trichotomy y 0 with hy | rfl | hy <;>
        simp [Real.sign_of_neg, Real.sign_of_pos, *] <;> linarith
    · rcases Real.sign_apply_eq x with h | h | h <;> simp [h]
  obtain ⟨hmono, hbound⟩ := monotone_slope_exp_neg_abs_add_sign
  refine ⟨⟨1 / 4, by norm_num, ?_, ?_⟩, fun x ↦ ?_, ?_⟩
  · rw [hweight]
    exact integrable_exp_neg_mul_abs (by norm_num)
  · rw [hweight]
    exact boundedVariationOn_exp_neg_mul_abs (by norm_num)
  · rw [hcont.continuousWithinAt.leftLim_eq, hcont.continuousWithinAt.rightLim_eq]
    ring
  · simpa [Pi.sub_def] using
      ((hmono.monotoneOn univ).boundedVariationOn fun x _ ↦ hbound x).sub hsign

/-- Mestre's one-signed weight condition is weaker than admissibility: this function decays
against `exp ((1 / 2 + ε) x)` on both tails, but its left tail grows against the two-sided weight
`exp ((1 / 2 + ε) |x|)`, so it is not admissible for `c = 0`. -/
example : ¬WeilTestFunction 0 fun x ↦ if x < 0 then Real.exp (x / 4) else Real.exp (-2 * x) := by
  rintro ⟨⟨ε, hε, hint, -⟩, -, -⟩
  have hsub : Iio (0 : ℝ) ⊆ {x | 1 ≤ ‖(if x < 0 then Real.exp (x / 4) else Real.exp (-2 * x)) *
      Real.exp ((1 / 2 + 0 + ε) * |x|)‖} := by
    intro x hx
    rw [mem_Iio] at hx
    rw [mem_ofPred_eq, ite_eq_left hx, abs_of_neg hx, ← Real.exp_add, Real.norm_eq_abs,
      Real.abs_exp, Real.one_le_exp_iff]
    nlinarith
  have h := (measure_mono hsub).trans_lt (hint.measure_norm_ge_lt_top one_pos)
  simp [Real.volume_Iio] at h

/-- A one-tailed exponential is not admissible for any `c`: its difference quotient at `0` is
unbounded, so `|F x - F 0| ≤ C |x|` fails. -/
example (c : ℝ) : ¬WeilTestFunction c fun x ↦ Real.exp (-2 * x) := by
  intro hF
  obtain ⟨C, hC₀, hC⟩ := hF.exists_abs_sub_le
  have h := hC (-(C + 1))
  have hexp := Real.quadratic_le_exp_of_nonneg (x := 2 * (C + 1)) (by linarith)
  have h₁ : Real.exp (-2 * -(C + 1)) = Real.exp (2 * (C + 1)) := by ring_nf
  rw [h₁, mul_zero, Real.exp_zero, abs_neg, abs_of_nonneg (by linarith : (0 : ℝ) ≤ C + 1),
    abs_of_nonneg (by nlinarith [sq_nonneg (C + 1)])] at h
  nlinarith

/-- The Gaussian: its transform at `1 / 2` is `∫ exp (-x ^ 2) dx = √π`. -/
example : weilTransform (fun x ↦ Real.exp (-x ^ 2)) (1 / 2) = Real.sqrt Real.pi := by
  have h := integral_gaussian 1
  simp only [neg_mul, one_mul, div_one] at h
  simp only [weilTransform, sub_self, zero_mul, Complex.exp_zero, mul_one]
  rw [integral_complex_ofReal, h]

end TauCeti
