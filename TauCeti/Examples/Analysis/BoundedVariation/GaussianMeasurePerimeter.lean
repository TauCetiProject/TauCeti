/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.BoundedVariation.Weighted.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import TauCeti.Probability.Distributions.Gaussian.Moments

/-!
# Check: the perimeter against the Gaussian measure is the wrong definition

The plausible wrong definition of the Gaussian perimeter, the supremum of `∫_U div X dγ` over test
vector fields with `‖X‖ ≤ 1` and without the term `−⟨x, X⟩` of the Gaussian divergence, is Tau
Ceti's `TauCeti.perimeter γ Ω U` with the measure `γ` in place of `volume`. On the line it assigns
to the whole space `ℝ` the value `√(2/π) = 0.797885` instead of `0`:
Gaussian integration by parts turns `∫ X' dγ` into `∫ t X(t) dγ`, which is at most `∫ |t| dγ`,
and test fields approximating the sign function attain it. As the empty set has perimeter `0`
for every measure, this perimeter is not complement invariant, unlike the Gaussian perimeter
(`TauCeti.gaussianPerimeter_univ`).
-/

open Filter MeasureTheory ProbabilityTheory Set TestFunction TopologicalSpace
open scoped Topology ENNReal Distributions

public noncomputable section

namespace TauCeti.Examples.GaussianMeasurePerimeter

/-- The standard normal density is `e^{−W}` for the Gaussian weight `W` of `ℝ`. -/
private theorem gaussianPDFReal_eq_exp_neg_gaussianWeight (x : ℝ) :
    gaussianPDFReal 0 1 x = Real.exp (-gaussianWeight ℝ x) := by
  have h2π : (0 : ℝ) < 2 * Real.pi := by positivity
  rw [gaussianPDFReal_def, gaussianWeight_def, Module.finrank_self, Real.sqrt_eq_rpow,
    Real.rpow_def_of_pos (by simpa using h2π), neg_add, Real.exp_add, ← Real.exp_neg,
    Real.norm_eq_abs, sq_abs]
  simp only [NNReal.coe_one, mul_one, sub_zero, Nat.cast_one]
  rw [mul_comm]
  congr 2 <;> ring

/-- The derivative of the Gaussian weight of `ℝ` is multiplication by the point. -/
private theorem fderiv_gaussianWeight_apply (x v : ℝ) :
    fderiv ℝ (gaussianWeight ℝ) x v = x * v := by
  have hW : gaussianWeight ℝ =
      fun y => y ^ 2 / 2 + (Module.finrank ℝ ℝ : ℝ) / 2 * Real.log (2 * Real.pi) := by
    funext y
    rw [gaussianWeight_def, Real.norm_eq_abs, sq_abs]
  have hd : HasDerivAt (gaussianWeight ℝ) x x := by
    rw [hW]
    exact (((hasDerivAt_pow 2 x).div_const 2).add_const _).congr_deriv (by ring)
  rw [hd.hasFDerivAt.fderiv]
  simp [mul_comm]

/-- **Gaussian integration by parts** for a test vector field on `ℝ`:
`∫ X' dγ = ∫ t X(t) dγ`. -/
private theorem integral_divergenceCLM_gaussianReal (X : 𝓓((⊤ : Opens ℝ), ℝ)) :
    ∫ x, divergenceCLM X x ∂gaussianReal 0 1 = ∫ x, x * X x ∂gaussianReal 0 1 := by
  have hW : ContDiff ℝ 1 (gaussianWeight ℝ) := contDiff_gaussianWeight
  have h0 := integral_divergenceCLM_sub_fderiv_mul_exp_neg_eq_zero hW X
  have hexp : Continuous fun x : ℝ => Real.exp (-gaussianWeight ℝ x) :=
    hW.continuous.neg.rexp
  have hdiv : Integrable fun x => divergenceCLM X x * Real.exp (-gaussianWeight ℝ x) :=
    ((divergenceCLM X).continuous.mul hexp).integrable_of_hasCompactSupport
      (divergenceCLM X).hasCompactSupport.mul_right
  have hX : Integrable fun x => x * X x * Real.exp (-gaussianWeight ℝ x) :=
    ((continuous_id.mul X.continuous).mul hexp).integrable_of_hasCompactSupport
      (X.hasCompactSupport.mul_left.mul_right)
  simp_rw [fderiv_gaussianWeight_apply, sub_mul] at h0
  rw [integral_sub hdiv hX, sub_eq_zero] at h0
  rw [integral_gaussianReal_eq_integral_smul one_ne_zero,
    integral_gaussianReal_eq_integral_smul one_ne_zero]
  simp_rw [smul_eq_mul, gaussianPDFReal_eq_exp_neg_gaussianWeight]
  convert h0 using 2 <;> funext x <;> ring

/-- The perimeter of `ℝ` against `γ` is the supremum of `∫ t X(t) dγ` over test fields. -/
private theorem perimeter_gaussianReal_univ_eq_iSup :
    perimeter (gaussianReal 0 1) ⊤ univ = ⨆ (X : 𝓓((⊤ : Opens ℝ), ℝ)) (_ : ∀ x, ‖X x‖ ≤ 1),
      ENNReal.ofReal (∫ x, x * X x ∂gaussianReal 0 1) := by
  rw [perimeter_eq_iSup nullMeasurableSet_univ]
  simp_rw [setIntegral_univ, integral_divergenceCLM_gaussianReal]

/-- The smoothed sign function `ψ(c t) ψ(c + 1 − t) − ψ(−c t) ψ(c + 1 + t)`, with
`ψ = Real.smoothTransition`. -/
private def smoothSign (c t : ℝ) : ℝ :=
  Real.smoothTransition (c * t) * Real.smoothTransition (c + 1 - t) -
    Real.smoothTransition (-(c * t)) * Real.smoothTransition (c + 1 + t)

private theorem smoothSign_of_nonneg {c t : ℝ} (hc : 0 ≤ c) (ht : 0 ≤ t) :
    smoothSign c t = Real.smoothTransition (c * t) * Real.smoothTransition (c + 1 - t) := by
  rw [smoothSign, Real.smoothTransition.zero_of_nonpos (x := -(c * t)) (by nlinarith), zero_mul,
    sub_zero]

private theorem smoothSign_of_nonpos {c t : ℝ} (hc : 0 ≤ c) (ht : t ≤ 0) :
    smoothSign c t = -(Real.smoothTransition (-(c * t)) * Real.smoothTransition (c + 1 + t)) := by
  rw [smoothSign, Real.smoothTransition.zero_of_nonpos (x := c * t) (by nlinarith), zero_mul,
    zero_sub]

private theorem abs_smoothSign_le {c : ℝ} (hc : 0 ≤ c) (t : ℝ) : |smoothSign c t| ≤ 1 := by
  have hp (a b : ℝ) : |Real.smoothTransition a * Real.smoothTransition b| ≤ 1 := by
    rw [abs_of_nonneg (mul_nonneg (Real.smoothTransition.nonneg _)
      (Real.smoothTransition.nonneg _))]
    exact (mul_le_of_le_one_left (Real.smoothTransition.nonneg _)
      (Real.smoothTransition.le_one _)).trans (Real.smoothTransition.le_one _)
  rcases le_total 0 t with ht | ht
  · rw [smoothSign_of_nonneg hc ht]
    exact hp _ _
  · rw [smoothSign_of_nonpos hc ht, abs_neg]
    exact hp _ _

private theorem smoothSign_eq_zero {c t : ℝ} (hc : 0 ≤ c) (ht : t ∉ Icc (-(c + 1)) (c + 1)) :
    smoothSign c t = 0 := by
  rw [mem_Icc, not_and_or, not_le, not_le] at ht
  rcases ht with ht | ht
  · rw [smoothSign_of_nonpos hc (by linarith),
      Real.smoothTransition.zero_of_nonpos (x := c + 1 + t) (by linarith), mul_zero, neg_zero]
  · rw [smoothSign_of_nonneg hc (by linarith),
      Real.smoothTransition.zero_of_nonpos (x := c + 1 - t) (by linarith), mul_zero]

/-- The smoothed sign function as a test vector field on `ℝ`. -/
private def smoothSignField (c : ℝ) (hc : 0 ≤ c) : 𝓓((⊤ : Opens ℝ), ℝ) where
  toFun := smoothSign c
  contDiff' := by
    have h := Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))
    have hc : ContDiff ℝ (⊤ : ℕ∞) fun _ : ℝ => c := contDiff_const
    have hc1 : ContDiff ℝ (⊤ : ℕ∞) fun _ : ℝ => c + 1 := contDiff_const
    have hid : ContDiff ℝ (⊤ : ℕ∞) fun t : ℝ => t := contDiff_id
    exact ((h.comp (hc.mul hid)).mul (h.comp (hc1.sub hid))).sub
      ((h.comp (hc.mul hid).neg).mul (h.comp (hc1.add hid)))
  hasCompactSupport' := HasCompactSupport.intro isCompact_Icc fun _ ht => smoothSign_eq_zero hc ht
  tsupport_subset' := by simp

private theorem smoothSignField_apply (c : ℝ) (hc : 0 ≤ c) (t : ℝ) :
    smoothSignField c hc t = smoothSign c t :=
  rfl

/-- Along `c → ∞`, `t · sign_c(t) → |t|`. -/
private theorem tendsto_mul_smoothSign (t : ℝ) :
    Tendsto (fun n : ℕ => t * smoothSign n t) atTop (𝓝 |t|) := by
  refine tendsto_const_nhds.congr' ?_
  obtain ⟨N, hN⟩ := exists_nat_gt (max |t| |t|⁻¹)
  filter_upwards [eventually_ge_atTop N] with n hn
  have hn' : max |t| |t|⁻¹ < n := hN.trans_le (by exact_mod_cast hn)
  have hA : |t| < n := (le_max_left _ _).trans_lt hn'
  rcases eq_or_ne t 0 with rfl | ht0
  · simp
  have hB : 1 ≤ n * |t| :=
    calc (1 : ℝ) = |t|⁻¹ * |t| := (inv_mul_cancel₀ (abs_ne_zero.2 ht0)).symm
      _ ≤ n * |t| := mul_le_mul_of_nonneg_right ((le_max_right _ _).trans hn'.le) (abs_nonneg t)
  rcases ht0.lt_or_gt with ht | ht
  · rw [abs_of_neg ht] at hA hB ⊢
    rw [smoothSign_of_nonpos (Nat.cast_nonneg n) ht.le,
      Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le (by linarith)]
    ring
  · rw [abs_of_pos ht] at hA hB ⊢
    rw [smoothSign_of_nonneg (Nat.cast_nonneg n) ht.le,
      Real.smoothTransition.one_of_one_le (by linarith),
      Real.smoothTransition.one_of_one_le (by linarith)]
    ring

/-- **Check (§2.1, the wrong definition).** Against the measure `γ` in place of `volume`, the
whole line has perimeter `√(2/π) = 0.797885`, while its Gaussian perimeter is `0`. -/
theorem perimeter_gaussianReal_univ :
    perimeter (gaussianReal 0 1) ⊤ (univ : Set ℝ) = ENNReal.ofReal √(2 / Real.pi) := by
  have habs : Integrable (fun x : ℝ => |x|) (gaussianReal 0 1) :=
    ((memLp_id_gaussianReal 1).integrable le_rfl).abs
  have hmean : ∫ x, |x| ∂gaussianReal 0 1 = √(2 / Real.pi) := by
    simpa using TauCeti.Probability.integral_abs_gaussianReal 1
  have hint (X : 𝓓((⊤ : Opens ℝ), ℝ)) (hX : ∀ x, ‖X x‖ ≤ 1) :
      Integrable (fun x => x * X x) (gaussianReal 0 1) :=
    habs.mono' (continuous_id.mul X.continuous).aestronglyMeasurable
      (Eventually.of_forall fun x => by
        rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_of_le_one_right (abs_nonneg x) (hX x))
  rw [perimeter_gaussianReal_univ_eq_iSup, ← hmean]
  refine le_antisymm (iSup₂_le fun X hX => ENNReal.ofReal_le_ofReal ?_) ?_
  · refine integral_mono (hint X hX) habs fun x => ?_
    calc x * X x ≤ |x * X x| := le_abs_self _
      _ ≤ |x| := by
        rw [abs_mul]
        exact mul_le_of_le_one_right (abs_nonneg x) (by simpa using hX x)
  · have hlim : Tendsto (fun n : ℕ => ∫ x, x * smoothSign n x ∂gaussianReal 0 1) atTop
        (𝓝 (∫ x, |x| ∂gaussianReal 0 1)) :=
      tendsto_integral_of_dominated_convergence (fun x => |x|)
        (fun n => (continuous_id.mul (smoothSignField n (Nat.cast_nonneg n)).continuous
          ).aestronglyMeasurable) habs
        (fun n => Eventually.of_forall fun x => by
          rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
          exact mul_le_of_le_one_right (abs_nonneg x) (abs_smoothSign_le (Nat.cast_nonneg n) x))
        (Eventually.of_forall tendsto_mul_smoothSign)
    refine le_of_tendsto' (ENNReal.tendsto_ofReal hlim) fun n => ?_
    exact le_iSup₂_of_le (f := fun (X : 𝓓((⊤ : Opens ℝ), ℝ)) (_ : ∀ x, ‖X x‖ ≤ 1) =>
      ENNReal.ofReal (∫ x, x * X x ∂gaussianReal 0 1)) (smoothSignField n (Nat.cast_nonneg n))
      (fun x => by
        rw [smoothSignField_apply, Real.norm_eq_abs]
        exact abs_smoothSign_le (Nat.cast_nonneg n) x) le_rfl

/-- Against `γ`, the empty set has perimeter `0` while its complement `ℝ` has positive perimeter:
this perimeter is not complement invariant. -/
example : perimeter (gaussianReal 0 1) ⊤ (∅ : Set ℝ) = 0 :=
  perimeter_empty

/-- The Gaussian perimeter of the whole line is `0`. -/
example : gaussianPerimeter (univ : Set ℝ) = 0 :=
  gaussianPerimeter_univ

end TauCeti.Examples.GaussianMeasurePerimeter

end
