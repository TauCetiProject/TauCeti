/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Group.Convolution
public import Mathlib.Probability.Moments.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul
import Mathlib.Analysis.Convex.Integral
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.MeasureTheory.Integral.Prod
import TauCeti.Analysis.SpecialFunctions.Exp.QuadraticBound

/-!
# Basic facts about moment-generating functions

This file supplements Mathlib's basic moment-generating-function API.

## Main results

* `TauCeti.isProbabilityMeasure_of_mgf_zero_eq_one`: a measure is a probability measure if the
  moment-generating function of any real-valued statistic equals `1` at zero.
* `TauCeti.isFiniteMeasure_of_zero_mem_integrableExpSet`: a measure with an exponential moment at
  `0` is finite.
* `TauCeti.mgf_lt_one_of_nonneg_of_neg`: under a probability measure, the moment-generating
  function of a nonnegative random variable that is not almost surely zero is strictly less than
  `1` at every negative argument.
* `TauCeti.mgf_id_conv`: the moment-generating function of a convolution of two s-finite measures
  on `ℝ` is the product of their moment-generating functions.  This is the transform side of
  `MeasureTheory.Measure.conv`, the companion of `MeasureTheory.charFun_conv`.
* `TauCeti.ae_sum_eq_zero_of_sum_integral_sq_eq_zero`: a finite sum of square-integrable random
  variables whose second moments sum to zero vanishes almost surely.
* `ProbabilityTheory.iIndepFun.mgf_sum_of_aemeasurable`: the moment-generating function of a finite
  sum of independent variables is the product of the factors, needing a.e. measurability only on
  the summation set.
* `ProbabilityTheory.iIndepFun.integrable_exp_mul_sum_of_aemeasurable`: the exponential of a finite
  sum of independent a.e. measurable variables is integrable when each factor is.
* `ProbabilityTheory.iIndepFun.mgf_sum_le_exp_sum`: exponential MGF bound for a finite sum of
  independent variables from coordinatewise exponential bounds.
* `TauCeti.ofReal_mgf_sub_integral_le_lintegral`: symmetrization by Jensen's inequality, the
  moment-generating function of `f - 𝔼 f` is at most `∫∫ exp (t (f x - f y)) dμ(x) dμ(y)`.
* `TauCeti.mgf_add_le_of_mgf_two_mul_le`, `TauCeti.mgf_add_le_exp_half_add`: AM-GM and
  geometric-mean bounds for `mgf (X + Y)` without independence.
* `TauCeti.mgf_sub_integral_le_of_nonneg_exp_le_two`,
  `TauCeti.measureReal_gt_le_exp_min_of_mgf_le`,
  `TauCeti.measureReal_abs_gt_le_two_mul_exp_min_of_mgf_le`: sub-exponential MGF & Chernoff bounds.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ}

/-- A measure is a probability measure if the moment-generating function of any real-valued
statistic equals `1` at zero. -/
theorem isProbabilityMeasure_of_mgf_zero_eq_one (hmgf : mgf X μ 0 = 1) :
    IsProbabilityMeasure μ := by
  rw [mgf_zero'] at hmgf
  exact ⟨(ENNReal.toReal_eq_one_iff _).1 hmgf⟩

/-- A measure admitting an exponential moment at rate `0` is finite: at rate `0` the integrand is
the constant `1`, whose integrability is finiteness of the measure. -/
theorem isFiniteMeasure_of_zero_mem_integrableExpSet (h : (0 : ℝ) ∈ integrableExpSet X μ) :
    IsFiniteMeasure μ :=
  (integrable_const_iff_isFiniteMeasure one_ne_zero).mp <| by
    simpa using integrable_of_mem_integrableExpSet h

/-- Under a probability measure, the moment-generating function of an almost surely nonnegative
random variable that is positive with positive probability is strictly less than `1` at every
negative argument. -/
theorem mgf_lt_one_of_nonneg_of_neg [IsProbabilityMeasure μ] (hX : AEMeasurable X μ)
    (hX0 : 0 ≤ᵐ[μ] X) (hpos : μ {ω | 0 < X ω} ≠ 0) {t : ℝ} (ht : t < 0) : mgf X μ t < 1 := by
  have hle : ∀ᵐ ω ∂μ, Real.exp (t * X ω) ≤ 1 := by
    filter_upwards [hX0] with ω hω
    exact Real.exp_le_one_iff.2 (mul_nonpos_of_nonpos_of_nonneg ht.le hω)
  have hint : Integrable (fun ω ↦ Real.exp (t * X ω)) μ :=
    Integrable.of_bound (by fun_prop) 1 <| hle.mono fun ω hω ↦ by
      rwa [Real.norm_of_nonneg (Real.exp_pos _).le]
  -- `1 - exp (t * X)` is nonnegative and vanishes exactly where `X` does.
  have hdiff : 0 < ∫ ω, (1 - Real.exp (t * X ω)) ∂μ := by
    rw [integral_pos_iff_support_of_nonneg_ae (hle.mono fun ω hω ↦ sub_nonneg.2 hω)
      ((integrable_const 1).sub hint)]
    refine pos_iff_ne_zero.2 fun h0 ↦ hpos <| measure_mono_null (fun ω hω ↦ ?_) h0
    have : t * X ω < 0 := mul_neg_of_neg_of_pos ht hω
    simp [Function.mem_support, sub_eq_zero, (Real.exp_lt_one_iff.2 this).ne']
  rw [integral_sub (integrable_const 1) hint, integral_const, probReal_univ, one_smul] at hdiff
  rw [mgf]
  linarith

/-- **The moment-generating function of a convolution is the product of the two
moment-generating functions.** This is the transform companion of `MeasureTheory.charFun_conv`.
No integrability hypothesis is needed, even though Mathlib totalizes a divergent `mgf` to `0`. -/
@[simp]
theorem mgf_id_conv {μ ν : Measure ℝ} [SFinite μ] [SFinite ν] :
    mgf id (μ ∗ ν) = mgf id μ * mgf id ν := by
  ext t
  rw [Measure.conv, mgf_id_map (by fun_prop), mgf]
  simp only [mul_add, Real.exp_add]
  exact integral_prod_mul (L := ℝ) (fun x ↦ Real.exp (t * x)) fun y ↦ Real.exp (t * y)

/-- If square-integrable random variables have vanishing total second moment, their sum vanishes
almost surely. -/
theorem ae_sum_eq_zero_of_sum_integral_sq_eq_zero {ι : Type*} {X : ι → Ω → ℝ}
    {s : Finset ι} (hX : ∀ i ∈ s, MemLp (X i) 2 μ) (hv : ∑ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ = 0) :
    ∀ᵐ ω ∂μ, ∑ i ∈ s, X i ω = 0 := by
  have hsq : ∀ i ∈ s, ∫ ω, X i ω ^ 2 ∂μ = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ integral_nonneg fun ω ↦ sq_nonneg _).1 hv
  have hae : ∀ i ∈ s, ∀ᵐ ω ∂μ, X i ω = 0 := fun i hi ↦ by
    have h := (integral_eq_zero_iff_of_nonneg_ae (ae_of_all _ fun ω ↦ sq_nonneg (X i ω))
      (hX i hi).integrable_sq).1 (hsq i hi)
    filter_upwards [h] with ω hω
    simpa using hω
  filter_upwards [(Filter.eventually_all_finset s).2 hae] with ω hω
  exact Finset.sum_eq_zero hω

section Symmetrization

open Real

variable {f : Ω → ℝ}

/-- **Symmetrization by Jensen's inequality.** For a probability measure `μ`, the moment
generating function of `f - 𝔼 f` at `t` is at most `∫∫ exp (t (f x - f y)) dμ(x) dμ(y)`. -/
theorem ofReal_mgf_sub_integral_le_lintegral [IsProbabilityMeasure μ]
    (hfi : Integrable f μ) {t : ℝ} (hint : Integrable (fun x ↦ exp (t * (f x - ∫ y, f y ∂μ))) μ)
    (hneg : Integrable (fun x ↦ exp (-t * f x)) μ) :
    ENNReal.ofReal (mgf (fun x ↦ f x - ∫ y, f y ∂μ) μ t) ≤
      ∫⁻ p, .ofReal (exp (t * (f p.1 - f p.2))) ∂μ.prod μ := by
  set m := ∫ y, f y ∂μ
  have hexp (x y : Ω) : exp (t * (f x - f y)) = exp (t * f x) * exp (-t * f y) := by
    rw [← exp_add]
    congr 1
    ring
  have hexpi (x : Ω) : Integrable (fun y ↦ exp (t * (f x - f y))) μ := by
    simp_rw [hexp]
    exact hneg.const_mul _
  -- Jensen's inequality in `y`, for each fixed `x`.
  have hjensen (x : Ω) : exp (t * (f x - m)) ≤ ∫ y, exp (t * (f x - f y)) ∂μ := by
    have hmean : ∫ y, t * (f x - f y) ∂μ = t * (f x - m) := by
      rw [integral_const_mul, integral_sub (integrable_const _) hfi]
      simp [m]
    rw [← hmean]
    exact convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ (by simp)
      (((integrable_const _).sub hfi).const_mul t) (hexpi x)
  have hF : AEMeasurable (fun p : Ω × Ω ↦ ENNReal.ofReal (exp (t * (f p.1 - f p.2)))) (μ.prod μ) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (by fun_prop)
  rw [mgf]
  calc ENNReal.ofReal (∫ x, exp (t * (f x - m)) ∂μ)
      = ∫⁻ x, .ofReal (exp (t * (f x - m))) ∂μ :=
        ofReal_integral_eq_lintegral_ofReal hint (.of_forall fun _ ↦ (exp_pos _).le)
    _ ≤ ∫⁻ x, .ofReal (∫ y, exp (t * (f x - f y)) ∂μ) ∂μ :=
        lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (hjensen x)
    _ = ∫⁻ p, .ofReal (exp (t * (f p.1 - f p.2))) ∂μ.prod μ := by
        rw [lintegral_prod _ hF]
        refine lintegral_congr fun x ↦ ?_
        rw [ofReal_integral_eq_lintegral_ofReal (hexpi x) (.of_forall fun _ ↦ (exp_pos _).le)]

end Symmetrization

section SubExponential

open Real

/-- **AM-GM bound for the moment-generating function of a sum** without independence. -/
theorem mgf_add_le_of_mgf_two_mul_le {Y : Ω → ℝ} {θ M₁ M₂ : ℝ}
    (hX_int : Integrable (fun ω ↦ exp (2 * θ * X ω)) μ)
    (hY_int : Integrable (fun ω ↦ exp (2 * θ * Y ω)) μ)
    (hX_le : mgf X μ (2 * θ) ≤ M₁) (hY_le : mgf Y μ (2 * θ) ≤ M₂) :
    Integrable (fun ω ↦ exp (θ * (X ω + Y ω))) μ ∧
      mgf (fun ω ↦ X ω + Y ω) μ θ ≤ (M₁ + M₂) / 2 := by
  have hsqrt : (fun ω ↦ exp (θ * (X ω + Y ω))) =
      fun ω ↦ Real.sqrt (exp (2 * θ * X ω) * exp (2 * θ * Y ω)) := funext fun ω ↦ by
    have hmul_sq : exp (2 * θ * X ω) * exp (2 * θ * Y ω) = exp (θ * (X ω + Y ω)) ^ 2 := by
      rw [sq, ← exp_add, ← exp_add]; ring_nf
    rw [hmul_sq, Real.sqrt_sq (exp_pos _).le]
  have hpt (ω : Ω) : exp (θ * (X ω + Y ω)) ≤ (exp (2 * θ * X ω) + exp (2 * θ * Y ω)) / 2 := by
    have hsq (z : ℝ) : exp (2 * θ * z) = exp (θ * z) ^ 2 := by rw [sq, ← exp_add]; ring_nf
    rw [mul_add, exp_add, hsq (X ω), hsq (Y ω)]
    linarith [two_mul_le_add_sq (exp (θ * X ω)) (exp (θ * Y ω))]
  have hdom : Integrable (fun ω ↦ (exp (2 * θ * X ω) + exp (2 * θ * Y ω)) / 2) μ :=
    (hX_int.add hY_int).div_const 2
  have hint : Integrable (fun ω ↦ exp (θ * (X ω + Y ω))) μ :=
    hdom.mono' (hsqrt ▸ continuous_sqrt.comp_aestronglyMeasurable (hX_int.1.mul hY_int.1))
      (.of_forall fun ω ↦ by rw [Real.norm_of_nonneg (exp_pos _).le]; exact hpt ω)
  refine ⟨hint, ?_⟩; rw [mgf]; refine (integral_mono hint hdom hpt).trans ?_
  rw [integral_div, integral_add hX_int hY_int, ← mgf, ← mgf]; linarith

/-- **Geometric-mean bound for the moment-generating function of a sum** without independence. -/
theorem mgf_add_le_exp_half_add {Y : Ω → ℝ} {θ a b : ℝ}
    (hX_int : Integrable (fun ω ↦ exp (2 * θ * X ω)) μ)
    (hY_int : Integrable (fun ω ↦ exp (2 * θ * Y ω)) μ)
    (hX_le : mgf X μ (2 * θ) ≤ exp a) (hY_le : mgf Y μ (2 * θ) ≤ exp b) :
    Integrable (fun ω ↦ exp (θ * (X ω + Y ω))) μ ∧
      mgf (fun ω ↦ X ω + Y ω) μ θ ≤ exp ((a + b) / 2) := by
  have hint := (mgf_add_le_of_mgf_two_mul_le hX_int hY_int hX_le hY_le).1
  have hpt (ω : Ω) : exp (θ * (X ω + Y ω)) ≤ exp ((a + b) / 2) / 2 *
      (exp (-a) * exp (2 * θ * X ω) + exp (-b) * exp (2 * θ * Y ω)) := by
    have hsq (z c : ℝ) : exp (-c) * exp (2 * θ * z) = exp (θ * z - c / 2) ^ 2 := by
      rw [sq, ← exp_add, ← exp_add]; ring_nf
    have hsplit : exp (θ * (X ω + Y ω)) =
        exp ((a + b) / 2) * (exp (θ * X ω - a / 2) * exp (θ * Y ω - b / 2)) := by
      rw [← exp_add, ← exp_add]; ring_nf
    rw [hsplit, hsq (X ω) a, hsq (Y ω) b]
    nlinarith [two_mul_le_add_sq (exp (θ * X ω - a / 2)) (exp (θ * Y ω - b / 2)),
      exp_pos ((a + b) / 2)]
  have hdom : Integrable (fun ω ↦ exp ((a + b) / 2) / 2 *
      (exp (-a) * exp (2 * θ * X ω) + exp (-b) * exp (2 * θ * Y ω))) μ :=
    ((hX_int.const_mul (exp (-a))).add (hY_int.const_mul (exp (-b)))).const_mul _
  have h1 {Z : Ω → ℝ} {c : ℝ} (hZ : mgf Z μ (2 * θ) ≤ exp c) : exp (-c) * mgf Z μ (2 * θ) ≤ 1 :=
    (mul_le_mul_of_nonneg_left hZ (exp_pos _).le).trans_eq (by rw [← exp_add]; simp)
  refine ⟨hint, ?_⟩; rw [mgf]; refine (integral_mono hint hdom hpt).trans ?_
  rw [integral_const_mul, integral_add (hX_int.const_mul _) (hY_int.const_mul _),
    integral_const_mul, integral_const_mul, ← mgf, ← mgf]
  nlinarith [h1 hX_le, h1 hY_le, exp_pos ((a + b) / 2)]

/-- **Sub-exponential MGF bound for a centered nonnegative variable** with `∫ exp (Y / B) ≤ 2`. -/
theorem mgf_sub_integral_le_of_nonneg_exp_le_two [IsProbabilityMeasure μ] {Y : Ω → ℝ}
    (hY_meas : AEMeasurable Y μ) (hY_nonneg : 0 ≤ᵐ[μ] Y) {B : ℝ} (hB : 0 < B)
    (hY_int_exp : Integrable (fun ω ↦ exp (Y ω / B)) μ) (hY_exp : ∫ ω, exp (Y ω / B) ∂μ ≤ 2)
    {θ : ℝ} (hθ : B * |θ| ≤ 1 / 2) :
    Integrable (fun ω ↦ exp (θ * (Y ω - μ[Y]))) μ ∧
      mgf (fun ω ↦ Y ω - μ[Y]) μ θ ≤ exp (24 * B ^ 2 * θ ^ 2) := by
  have hY_int : Integrable Y μ := (hY_int_exp.const_mul B).mono' hY_meas.aestronglyMeasurable <| by
    filter_upwards [hY_nonneg] with ω hω
    have h2 := mul_le_mul_of_nonneg_left
      (by linarith [add_one_le_exp (Y ω / B)] : Y ω / B ≤ exp (Y ω / B)) hB.le
    rw [Real.norm_of_nonneg hω]; rwa [mul_div_cancel₀ _ hB.ne'] at h2
  let m : ℝ := μ[Y]; have hm_nonneg : 0 ≤ m := integral_nonneg_of_ae hY_nonneg
  have hm_le : m ≤ B := by
    have hf : Integrable (fun ω ↦ 1 + Y ω / B) μ := (integrable_const 1).add (hY_int.div_const B)
    have h1 := integral_mono hf hY_int_exp fun ω ↦ by linarith [add_one_le_exp (Y ω / B)]
    rw [integral_add (integrable_const 1) (hY_int.div_const B), integral_const, probReal_univ,
      one_smul, integral_div] at h1
    exact (div_le_one hB).mp (by linarith)
  let Z : Ω → ℝ := fun ω ↦ Y ω - m; have hZ_int : Integrable Z μ := hY_int.sub (integrable_const m)
  have hZ_mean : ∫ ω, Z ω ∂μ = 0 := by
    rw [integral_sub hY_int (integrable_const m), integral_const, probReal_univ, one_smul, sub_self]
  have hexp_half_le : exp (1 / 2 : ℝ) ≤ 3 := by
    have h := mul_le_mul_of_nonneg_right
      (exp_neg (1 / 2 : ℝ) ▸ add_one_le_exp (-(1 / 2 : ℝ))) (exp_pos (1 / 2 : ℝ)).le
    rw [inv_mul_cancel₀ (exp_pos _).ne'] at h; linarith
  have hpt : ∀ᵐ ω ∂μ, exp (θ * Z ω) ≤ 1 + θ * Z ω + 12 * B ^ 2 * θ ^ 2 * exp (Y ω / B) := by
    filter_upwards [hY_nonneg] with ω hω
    let u : ℝ := Y ω / B; have hu0 : 0 ≤ u := div_nonneg hω hB.le
    have hY_eq : Y ω = B * u := (mul_div_cancel₀ _ hB.ne').symm
    have hZ_abs : |Z ω| ≤ B * (u + 1) := abs_le.2 ⟨by dsimp [Z]; nlinarith, by dsimp [Z]; nlinarith⟩
    have hθZ : |θ * Z ω| ≤ u / 2 + 1 / 2 := (abs_mul θ (Z ω)) ▸
      (mul_le_mul_of_nonneg_left hZ_abs (abs_nonneg θ)).trans
        (by linarith [mul_le_mul_of_nonneg_right hθ (by positivity : 0 ≤ u + 1)])
    have hu_quad : (u + 1) ^ 2 ≤ 8 * exp (u / 2) := by
      have hpoly : (u + 1) ^ 2 ≤ 8 * (1 + u / 2 + (u / 2) ^ 2 / 2) := by nlinarith
      linarith [hpoly, Real.quadratic_le_exp_of_nonneg (by positivity : 0 ≤ u / 2)]
    have hu_exp : (u + 1) ^ 2 * exp (u / 2 + 1 / 2) ≤ 24 * exp u := by
      have hmul := mul_le_mul hu_quad (mul_le_mul_of_nonneg_left hexp_half_le (exp_pos (u / 2)).le)
        (by positivity) (by positivity)
      have hexp_sq : exp (u / 2) * exp (u / 2) = exp u := by rw [← exp_add]; ring_nf
      rw [exp_add]; linarith [hexp_sq]
    have h1 : (θ * Z ω) ^ 2 / 2 * exp |θ * Z ω| ≤
        (B ^ 2 * θ ^ 2 / 2) * ((u + 1) ^ 2 * exp (u / 2 + 1 / 2)) := by
      have hZ_sq : (θ * Z ω) ^ 2 ≤ B ^ 2 * θ ^ 2 * (u + 1) ^ 2 := by
        have habs_sq : (θ * Z ω) ^ 2 = θ ^ 2 * |Z ω| ^ 2 := by rw [sq_abs]; ring
        rw [habs_sq]; nlinarith [pow_le_pow_left₀ (abs_nonneg _) hZ_abs 2, sq_nonneg θ]
      have hreassoc : (B ^ 2 * θ ^ 2 / 2) * ((u + 1) ^ 2 * exp (u / 2 + 1 / 2)) =
          (B ^ 2 * θ ^ 2 * (u + 1) ^ 2 / 2) * exp (u / 2 + 1 / 2) := by ring
      rw [hreassoc]
      exact mul_le_mul (by linarith) (exp_le_exp.2 hθZ) (exp_pos _).le (by positivity)
    exact (Real.exp_le_one_add_add_sq_div_two_mul_exp_abs (θ * Z ω)).trans
      (by linarith [mul_le_mul_of_nonneg_left hu_exp (by positivity : 0 ≤ B ^ 2 * θ ^ 2 / 2)])
  have hf1 : Integrable (fun ω ↦ 1 + θ * Z ω) μ := (integrable_const 1).add (hZ_int.const_mul θ)
  have hdom : Integrable (fun ω ↦ 1 + θ * Z ω + 12 * B ^ 2 * θ ^ 2 * exp (Y ω / B)) μ :=
    hf1.add (hY_int_exp.const_mul (12 * B ^ 2 * θ ^ 2))
  have hint : Integrable (fun ω ↦ exp (θ * Z ω)) μ :=
    hdom.mono' (Real.measurable_exp.comp_aemeasurable
      ((hY_meas.sub_const m).const_mul θ)).aestronglyMeasurable
      (hpt.mono fun _ hω ↦ by rwa [Real.norm_of_nonneg (exp_pos _).le])
  refine ⟨hint, ?_⟩; rw [mgf]; refine (integral_mono_ae hint hdom hpt).trans ?_
  rw [integral_add hf1 (hY_int_exp.const_mul _),
    integral_add (integrable_const 1) (hZ_int.const_mul θ), integral_const, probReal_univ, one_smul,
    integral_const_mul, integral_const_mul, hZ_mean, mul_zero, add_zero]
  have hlin : 1 + 12 * B ^ 2 * θ ^ 2 * ∫ ω, exp (Y ω / B) ∂μ ≤ 1 + 24 * B ^ 2 * θ ^ 2 := by
    nlinarith [sq_nonneg (B * θ)]
  exact hlin.trans (by linarith [add_one_le_exp (24 * B ^ 2 * θ ^ 2)])

/-- **One-sided sub-exponential Chernoff bound.** -/
theorem measureReal_gt_le_exp_min_of_mgf_le {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ} {C₁ C₂ F op : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hF : 0 ≤ F) (hop : 0 ≤ op)
    (hmgf : ∀ θ : ℝ, C₂ * op * |θ| ≤ 1 →
      Integrable (fun ω ↦ exp (θ * Y ω)) P ∧ mgf Y P θ ≤ exp (C₁ * F * θ ^ 2))
    {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < Y ω} ≤
      exp (-min (1 / (4 * C₁)) (1 / (2 * C₂)) * min (t ^ 2 / F) (t / op)) := by
  let c : ℝ := min (1 / (4 * C₁)) (1 / (2 * C₂))
  rcases hF.eq_or_lt with rfl | hF_pos
  · have hmin0 : min (t ^ 2 / (0 : ℝ)) (t / op) = 0 := by simp [div_nonneg ht hop]
    rw [hmin0, mul_zero, exp_zero]
    exact (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
  rcases hop.eq_or_lt with rfl | hop_pos
  · have hmin0 : min (t ^ 2 / F) (t / (0 : ℝ)) = 0 := by simp [div_nonneg (sq_nonneg t) hF_pos.le]
    rw [hmin0, mul_zero, exp_zero]
    exact (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ
  let θ : ℝ := min (t / (2 * C₁ * F)) (1 / (C₂ * op))
  have hθ0 : 0 ≤ θ := le_min (by positivity) (by positivity)
  have hpos : 0 < C₂ * op := mul_pos hC₂ hop_pos
  obtain ⟨hint, hle⟩ := hmgf θ (by
    rw [abs_of_nonneg hθ0]
    exact (mul_le_mul_of_nonneg_left (min_le_right _ _) hpos.le).trans_eq
      (mul_one_div_cancel hpos.ne'))
  have hCF : 0 < 2 * C₁ * F := by positivity
  have hquad : C₁ * F * θ ^ 2 ≤ θ * t / 2 := by
    nlinarith [(mul_le_mul_of_nonneg_left (min_le_left _ _ : θ ≤ _) hCF.le).trans_eq
      (mul_div_cancel₀ t hCF.ne')]
  have hrate : c * min (t ^ 2 / F) (t / op) ≤ θ * t / 2 := by
    rcases le_total (t / (2 * C₁ * F)) (1 / (C₂ * op)) with hcase | hcase
    · have hθ_eq : θ = t / (2 * C₁ * F) := min_eq_left hcase
      rw [hθ_eq]
      exact (mul_le_mul (min_le_left _ _) (min_le_left _ _)
        (le_min (by positivity) (by positivity)) (by positivity)).trans_eq (by field_simp; ring)
    · have hθ_eq : θ = 1 / (C₂ * op) := min_eq_right hcase
      rw [hθ_eq]
      exact (mul_le_mul (min_le_right _ _) (min_le_right _ _)
        (le_min (by positivity) (by positivity)) (by positivity)).trans_eq (by field_simp)
  have hsub : {ω | t < Y ω} ⊆ {ω | t ≤ Y ω} := fun _ (hω : t < _) ↦ hω.le
  exact ((measureReal_mono hsub).trans (measure_ge_le_exp_mul_mgf t hθ0 hint)).trans
    ((mul_le_mul_of_nonneg_left hle (exp_pos _).le).trans
      ((exp_add _ _).symm.trans_le (exp_le_exp.2 (by linarith))))

/-- **Two-sided sub-exponential Chernoff bound.** -/
theorem measureReal_abs_gt_le_two_mul_exp_min_of_mgf_le {P : Measure Ω} [IsProbabilityMeasure P]
    {Y : Ω → ℝ} {C₁ C₂ F op : ℝ} (hC₁ : 0 < C₁) (hC₂ : 0 < C₂) (hF : 0 ≤ F) (hop : 0 ≤ op)
    (hmgf : ∀ θ : ℝ, C₂ * op * |θ| ≤ 1 →
      Integrable (fun ω ↦ exp (θ * Y ω)) P ∧ mgf Y P θ ≤ exp (C₁ * F * θ ^ 2))
    {t : ℝ} (ht : 0 ≤ t) :
    P.real {ω | t < |Y ω|} ≤
      2 * exp (-min (1 / (4 * C₁)) (1 / (2 * C₂)) * min (t ^ 2 / F) (t / op)) := by
  have hmgf_neg (θ : ℝ) (hθ : C₂ * op * |θ| ≤ 1) :
      Integrable (fun ω ↦ exp (θ * (-Y) ω)) P ∧ mgf (-Y) P θ ≤ exp (C₁ * F * θ ^ 2) := by
    obtain ⟨hint, hle⟩ := hmgf (-θ) (by simpa only [abs_neg] using hθ)
    exact ⟨hint.congr (.of_forall fun _ ↦ by simp [Pi.neg_apply, mul_neg, neg_mul]),
      by rw [mgf_neg]; exact hle.trans_eq (by ring_nf)⟩
  have hsub : {ω | t < |Y ω|} ⊆ {ω | t < Y ω} ∪ {ω | t < (-Y) ω} := fun _ hω ↦ by
    simpa only [Set.mem_ofPred_eq, Set.mem_union, Pi.neg_apply, lt_abs] using hω
  have hpos := measureReal_gt_le_exp_min_of_mgf_le hC₁ hC₂ hF hop hmgf ht
  have hneg := measureReal_gt_le_exp_min_of_mgf_le hC₁ hC₂ hF hop hmgf_neg ht
  exact (measureReal_mono hsub).trans <| (measureReal_union_le _ _).trans (by linarith)

end SubExponential

end TauCeti

namespace ProbabilityTheory.iIndepFun

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ι : Type*} {X : ι → Ω → ℝ} {t : ℝ}

omit [IsProbabilityMeasure μ] in
/-- The moment-generating function of a finite sum of independent variables is the product of
their moment-generating functions, where only the members indexed by the sum need be a.e.
measurable. This weakens the measurability hypothesis of `ProbabilityTheory.iIndepFun.mgf_sum₀`. -/
theorem mgf_sum_of_aemeasurable (h_indep : iIndepFun X μ) {s : Finset ι}
    (h_meas : ∀ i ∈ s, AEMeasurable (X i) μ) :
    mgf (fun ω => ∑ i ∈ s, X i ω) μ t = ∏ i ∈ s, mgf (X i) μ t := by
  have h := (h_indep.precomp Subtype.val_injective).mgf_sum₀ (t := t)
    (fun i : s => h_meas i i.2) Finset.univ
  rw [Finset.prod_coe_sort s (fun i => mgf (X i) μ t)] at h
  rw [← h]
  congr 1
  ext ω
  simp only [Finset.sum_apply]
  exact (Finset.sum_coe_sort s (fun i => X i ω)).symm

/-- A finite sum of independent, almost-everywhere measurable variables with integrable
exponentials has an integrable exponential. This weakens the measurability hypothesis of
`ProbabilityTheory.iIndepFun.integrable_exp_mul_sum`. -/
theorem integrable_exp_mul_sum_of_aemeasurable (h_indep : iIndepFun X μ)
    {s : Finset ι} (h_meas : ∀ i ∈ s, AEMeasurable (X i) μ)
    (h_int : ∀ i ∈ s, Integrable (fun ω => Real.exp (t * X i ω)) μ) :
    Integrable (fun ω => Real.exp (t * (∑ i ∈ s, X i ω))) μ := by
  rw [← mgf_pos_iff]
  rw [h_indep.mgf_sum_of_aemeasurable h_meas (t := t)]
  exact Finset.prod_pos fun i hi => mgf_pos (h_int i hi)

omit [IsProbabilityMeasure μ] in
/-- Exponential MGF bound for a finite sum of independent random variables from coordinatewise
exponential MGF bounds. -/
theorem mgf_sum_le_exp_sum (h_indep : iIndepFun X μ) {s : Finset ι}
    (h_meas : ∀ i ∈ s, AEMeasurable (X i) μ) {b : ι → ℝ}
    (hb : ∀ i ∈ s, mgf (X i) μ t ≤ Real.exp (b i)) :
    mgf (fun ω ↦ ∑ i ∈ s, X i ω) μ t ≤ Real.exp (∑ i ∈ s, b i) := by
  rw [h_indep.mgf_sum_of_aemeasurable h_meas, Real.exp_sum]
  exact Finset.prod_le_prod₀ (fun _ _ ↦ mgf_nonneg) hb

end ProbabilityTheory.iIndepFun
