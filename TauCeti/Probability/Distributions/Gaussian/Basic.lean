/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.PoissonSummation

/-!
# Closed forms for the real Gaussian density

Mathlib's `ProbabilityTheory.gaussianPDFReal μ v` is stated for a general mean `μ` and variance `v`.
This file records the specialization at the standard parameters `μ = 0`, `v = 1`, where the shift
and the variance both disappear and the density collapses to `(√(2π))⁻¹ · e^{-x²/2}`.

That closed form is what any calculation against the standard Gaussian weight rewrites by, and it
is a statement about the Gaussian distribution alone: it mentions no orthogonal family, so it
belongs here rather than in any of the families that consume it (the Hermite orthogonality
relation and the Gaussian Hermite basis both do).

The file also extends the density to extended real points, by its limit `0` at `±∞`, and
differentiates it in the mean, for formulas over intervals whose bounds may be infinite. It also
differentiates the density in its real argument and turns integrability against `gaussianReal μ v`
into Lebesgue integrability of the density-weighted function, the inputs to Gaussian integration
by parts. Finally, it records the integral form of the Gaussian moment-generating function, which
needs nothing beyond the definition of `gaussianReal`.

## Main statements

* `TauCeti.Probability.gaussianPDFReal_zero_one` — `gaussianPDFReal 0 1 x = (√(2π))⁻¹ · e^{-x²/2}`.
* `TauCeti.Probability.gaussianPDFReal_eq_gaussianPDFReal_zero_one` — standardization:
  `gaussianPDFReal m v x = φ ((x - m) / √v) / √v` with `φ = gaussianPDFReal 0 1`.
* `TauCeti.Probability.gaussianPDFReal_neg` and `TauCeti.Probability.gaussianPDFReal_zero_neg` —
  reflection `gaussianPDFReal m v (-x) = gaussianPDFReal (-m) v x` and evenness at zero mean.
* `TauCeti.Probability.antitoneOn_gaussianPDFReal` — the density decreases to the right of the
  mean.
* `TauCeti.Probability.gaussianPDFReal_self`, `TauCeti.Probability.gaussianPDFReal_le_self`,
  `TauCeti.Probability.gaussianPDFReal_le`, and `TauCeti.Probability.gaussianPDF_le` — the density
  attains its global maximum `(√(2 * π * v))⁻¹` at the mean (with both sides vanishing when
  `v = 0`).
* `TauCeti.Probability.tendsto_rpow_abs_sub_mul_gaussianPDFReal_cocompact` — every Gaussian
  density `g` with mean `μ` satisfies `|x - μ| ^ s g(x) → 0` as `|x| → ∞`, for every real `s`; it
  translates Mathlib's `tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact` by the mean.
* `TauCeti.Probability.tendsto_gaussianPDFReal_cocompact` and
  `TauCeti.Probability.tendsto_mul_gaussianPDFReal_cocompact` — its consequences `g(x) → 0` and
  `x g(x) → 0` as `|x| → ∞`.
* `TauCeti.Probability.hasDerivAt_gaussianPDFReal` — the derivative of the Gaussian density in
  its real argument is `-(x - μ) / v` times the density, for every variance.
* `TauCeti.Probability.integrable_gaussianReal_iff_integrable_gaussianPDFReal_smul` — at positive
  variance, integrability against `gaussianReal μ v` is equivalent to Lebesgue integrability of
  the function weighted by the density.
* `TauCeti.Probability.integral_exp_mul_gaussianReal` — the exponential moment
  `∫ exp (t x) ∂N(μ, v) = exp (μ t + v t² / 2)`, and
  `TauCeti.Probability.integral_exp_mul_sub_gaussianReal`, its normalized form.
* `TauCeti.Probability.hasDerivAt_gaussianPDFRealEReal` — as a function of the mean `μ`, the
  density at an extended point `e` has derivative `(e - μ) / v` times the density.

## Main definitions

* `TauCeti.Probability.gaussianPDFRealEReal` — the Gaussian density at an extended real point,
  set to `0`, its limit, at `±∞`. Formulas for intervals with extended bounds, such as the
  moments of a truncated normal law, evaluate the density at the bounds through it.
-/

public section

namespace TauCeti.Probability

open Filter ProbabilityTheory Real
open scoped Topology NNReal

/-- The probability-density form of the standard Gaussian weight:
`gaussianPDFReal 0 1 x = (√(2π))⁻¹ · e^{-x²/2}`. -/
theorem gaussianPDFReal_zero_one (x : ℝ) :
    gaussianPDFReal 0 1 x = (Real.sqrt (2 * π))⁻¹ * Real.exp (-(x ^ 2 / 2)) := by
  simp [gaussianPDFReal, neg_div]

/-- Standardization of the Gaussian density: the density of `N(m, v)` at `x` is
`φ ((x - m) / √v) / √v`, where `φ = gaussianPDFReal 0 1` is the standard Gaussian density. At zero
variance both sides vanish. -/
theorem gaussianPDFReal_eq_gaussianPDFReal_zero_one (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal m v x = gaussianPDFReal 0 1 ((x - m) / √(v : ℝ)) / √(v : ℝ) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [gaussianPDFReal_zero_var]
  have hv' : (0 : ℝ) < v := NNReal.coe_pos.2 (pos_iff_ne_zero.2 hv)
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, div_pow, Real.sq_sqrt hv'.le,
    Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 2 * π)]
  field_simp

/-- Negating the argument of `gaussianPDFReal` negates the mean parameter. -/
theorem gaussianPDFReal_neg (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal m v (-x) = gaussianPDFReal (-m) v x := by
  simp only [gaussianPDFReal, show -(-x - m) ^ 2 = -(x - -m) ^ 2 by ring]

/-- Any centered Gaussian density is an even function. -/
theorem gaussianPDFReal_zero_neg (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal 0 v (-x) = gaussianPDFReal 0 v x := by
  rw [gaussianPDFReal_neg, neg_zero]

/-- The Gaussian density of `N(m, v)` decreases to the right of its mean. -/
theorem antitoneOn_gaussianPDFReal (m : ℝ) (v : ℝ≥0) :
    AntitoneOn (gaussianPDFReal m v) (Set.Ici m) := fun x hx y _ hxy => by
  have hx : 0 ≤ x - m := sub_nonneg.2 hx
  simp only [gaussianPDFReal]
  gcongr

/-- At its mean `μ`, the Gaussian density equals `(√(2 * π * v))⁻¹` (and `0` when `v = 0`). -/
@[simp]
theorem gaussianPDFReal_self (μ : ℝ) (v : ℝ≥0) :
    gaussianPDFReal μ v μ = (√(2 * π * (v : ℝ)))⁻¹ := by
  simp [gaussianPDFReal]

/-- The Gaussian density of `N(μ, v)` attains its global maximum at the mean `μ`. -/
theorem gaussianPDFReal_le_self (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal μ v x ≤ gaussianPDFReal μ v μ := by
  rw [gaussianPDFReal_self, gaussianPDFReal]
  refine mul_le_of_le_one_right (by positivity) (Real.exp_le_one_iff.2 ?_)
  exact div_nonpos_of_nonpos_of_nonneg (neg_nonpos.2 (sq_nonneg _)) (by positivity)

/-- Uniform upper bound on the Gaussian density: `gaussianPDFReal μ v x ≤ (√(2 * π * v))⁻¹` for
every variance `v`, including `v = 0` where both sides vanish. -/
theorem gaussianPDFReal_le (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFReal μ v x ≤ (√(2 * π * (v : ℝ)))⁻¹ :=
  gaussianPDFReal_self μ v ▸ gaussianPDFReal_le_self μ v x

/-- Uniform upper bound on the `ℝ≥0∞`-valued Gaussian density `gaussianPDF`, valid at every
variance `v` (including `v = 0`, where both sides vanish). -/
theorem gaussianPDF_le (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDF μ v x ≤ ENNReal.ofReal (√(2 * π * (v : ℝ)))⁻¹ :=
  ENNReal.ofReal_le_ofReal (gaussianPDFReal_le μ v x)

/-- Every Gaussian density decays faster than any power of the distance to its mean:
`|x - μ| ^ s * gaussianPDFReal μ v x → 0` as `|x| → ∞`, for every real exponent `s` (at zero
variance the density vanishes identically).

This is Mathlib's `tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact`, the decay of
`|x| ^ s * exp (-a * x ^ 2)`, at `a = (2 * v)⁻¹`, translated by the mean. -/
theorem tendsto_rpow_abs_sub_mul_gaussianPDFReal_cocompact (μ : ℝ) (v : ℝ≥0) (s : ℝ) :
    Tendsto (fun x => |x - μ| ^ s * gaussianPDFReal μ v x) (cocompact ℝ) (𝓝 0) := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [gaussianPDFReal_zero_var]
  have h := ((tendsto_rpow_abs_mul_exp_neg_mul_sq_cocompact (a := (2 * (v : ℝ))⁻¹)
    (by positivity) s).comp (Homeomorph.subRight μ).isClosedEmbedding.tendsto_cocompact).const_mul
    (√(2 * π * (v : ℝ)))⁻¹
  rw [mul_zero] at h
  refine h.congr fun x => ?_
  simp only [Function.comp_apply, Homeomorph.coe_subRight, gaussianPDFReal]
  ring_nf

/-- Every Gaussian density tends to `0` as `|x| → ∞` (at zero variance it vanishes
identically). The exponent `0` case of `tendsto_rpow_abs_sub_mul_gaussianPDFReal_cocompact`. -/
theorem tendsto_gaussianPDFReal_cocompact (μ : ℝ) (v : ℝ≥0) :
    Tendsto (gaussianPDFReal μ v) (cocompact ℝ) (𝓝 0) := by
  simpa using tendsto_rpow_abs_sub_mul_gaussianPDFReal_cocompact μ v 0

/-- Every Gaussian density decays faster than `1 / |x|`: `x * gaussianPDFReal μ v x → 0` as
`|x| → ∞`. The centered weight `(x - μ) * gaussianPDFReal μ v x` is the exponent `1` case of
`tendsto_rpow_abs_sub_mul_gaussianPDFReal_cocompact`. -/
theorem tendsto_mul_gaussianPDFReal_cocompact (μ : ℝ) (v : ℝ≥0) :
    Tendsto (fun x => x * gaussianPDFReal μ v x) (cocompact ℝ) (𝓝 0) := by
  have h₁ : Tendsto (fun x => (x - μ) * gaussianPDFReal μ v x) (cocompact ℝ) (𝓝 0) :=
    tendsto_zero_iff_norm_tendsto_zero.2 <|
      (tendsto_rpow_abs_sub_mul_gaussianPDFReal_cocompact μ v 1).congr fun x => by
        rw [rpow_one, norm_mul, norm_eq_abs, norm_eq_abs,
          abs_of_nonneg (gaussianPDFReal_nonneg μ v x)]
  have h := h₁.add ((tendsto_gaussianPDFReal_cocompact μ v).const_mul μ)
  rw [mul_zero, add_zero] at h
  exact h.congr fun x => by ring

/-- The derivative of the Gaussian density in its real argument is `-(x - μ) / v` times the
density. At zero variance both sides vanish. -/
theorem hasDerivAt_gaussianPDFReal (μ : ℝ) (v : ℝ≥0) (x : ℝ) :
    HasDerivAt (gaussianPDFReal μ v) (-(x - μ) / (v : ℝ) * gaussianPDFReal μ v x) x := by
  rcases eq_or_ne v 0 with rfl | hv
  · simp [gaussianPDFReal_zero_var]
  rw [gaussianPDFReal_def]
  -- the derivative of the exponent `-(x - μ) ^ 2 / (2 * v)`
  have hq := (((hasDerivAt_id' x).sub_const μ).fun_pow 2).fun_neg.div_const (2 * (v : ℝ))
  convert hq.exp.const_mul (√(2 * π * (v : ℝ)))⁻¹ using 1
  field_simp
  ring

/-- At positive variance, a function is integrable against `gaussianReal μ v` if and only if its
product with the Gaussian density is Lebesgue integrable. -/
theorem integrable_gaussianReal_iff_integrable_gaussianPDFReal_smul {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : ℝ} {v : ℝ≥0} (hv : v ≠ 0) {g : ℝ → E} :
    MeasureTheory.Integrable g (gaussianReal μ v) ↔
      MeasureTheory.Integrable (fun x => gaussianPDFReal μ v x • g x) := by
  rw [gaussianReal_of_var_ne_zero μ hv,
    MeasureTheory.integrable_withDensity_iff_integrable_smul' (measurable_gaussianPDF μ v)
      (MeasureTheory.ae_of_all _ fun _ => gaussianPDF_lt_top)]
  simp only [toReal_gaussianPDF]

/-! ### Exponential moments -/

/-- The exponential moment of a real Gaussian law: the integral form of
`ProbabilityTheory.mgf_fun_id_gaussianReal`. -/
theorem integral_exp_mul_gaussianReal (μ : ℝ) (v : ℝ≥0) (t : ℝ) :
    ∫ x, Real.exp (t * x) ∂gaussianReal μ v = Real.exp (μ * t + v * t ^ 2 / 2) := by
  simpa only [mgf] using congrFun (mgf_fun_id_gaussianReal (μ := μ) (v := v)) t

/-- A Gaussian exponential normalized by its cumulant-generating function has mean one. -/
theorem integral_exp_mul_sub_gaussianReal (μ b : ℝ) (v : ℝ≥0) :
    ∫ y, Real.exp (b * y - (μ * b + (v : ℝ) * b ^ 2 / 2)) ∂gaussianReal μ v = 1 := by
  simp_rw [Real.exp_sub, MeasureTheory.integral_div]
  rw [integral_exp_mul_gaussianReal, div_self (Real.exp_pos _).ne']

/-! ### The Gaussian density at an extended point -/

/-- The Gaussian density of `N(m, v)` at an extended real point: `gaussianPDFReal m v x` at a
real point `x`, and `0`, the limit of the density, at `⊥` and `⊤`. -/
noncomputable def gaussianPDFRealEReal (m : ℝ) (v : ℝ≥0) : EReal → ℝ :=
  EReal.rec 0 (gaussianPDFReal m v) 0

/-- At a real point, `gaussianPDFRealEReal` is the Gaussian density. -/
@[simp]
theorem gaussianPDFRealEReal_coe (m : ℝ) (v : ℝ≥0) (x : ℝ) :
    gaussianPDFRealEReal m v x = gaussianPDFReal m v x := (rfl)

/-- At `⊥`, `gaussianPDFRealEReal` vanishes. -/
@[simp]
theorem gaussianPDFRealEReal_bot (m : ℝ) (v : ℝ≥0) : gaussianPDFRealEReal m v ⊥ = 0 := (rfl)

/-- At `⊤`, `gaussianPDFRealEReal` vanishes. -/
@[simp]
theorem gaussianPDFRealEReal_top (m : ℝ) (v : ℝ≥0) : gaussianPDFRealEReal m v ⊤ = 0 := (rfl)

/-- The Gaussian density at an extended real point is nonnegative. -/
theorem gaussianPDFRealEReal_nonneg (m : ℝ) (v : ℝ≥0) (e : EReal) :
    0 ≤ gaussianPDFRealEReal m v e := by
  induction e <;> simp [gaussianPDFReal_nonneg]

/-- The Gaussian density at an extended point `e`, as a function of the mean `μ`, has derivative
`(e - μ) / v` times the density; both vanish at an infinite point and at zero variance. -/
theorem hasDerivAt_gaussianPDFRealEReal (v : ℝ≥0) (e : EReal) (μ : ℝ) :
    HasDerivAt (fun μ => gaussianPDFRealEReal μ v e)
      ((e.toReal - μ) * gaussianPDFRealEReal μ v e / v) μ := by
  rcases eq_or_ne v 0 with rfl | hv
  · induction e <;> simpa [gaussianPDFReal_zero_var] using hasDerivAt_const μ (0 : ℝ)
  induction e with
  | bot => simpa using hasDerivAt_const μ (0 : ℝ)
  | top => simpa using hasDerivAt_const μ (0 : ℝ)
  | coe x =>
    simp only [gaussianPDFRealEReal_coe, EReal.toReal_coe]
    have hshift (m : ℝ) : gaussianPDFReal m v x = gaussianPDFReal 0 v (x - m) := by
      simpa only [zero_add] using (gaussianPDFReal_sub (μ := 0) (v := v) x m).symm
    rw [hshift μ, funext hshift]
    convert (hasDerivAt_gaussianPDFReal 0 v (x - μ)).comp μ
      ((hasDerivAt_id μ).const_sub x) using 1
    · simp only [Function.comp_def]
    · field_simp
      ring

end TauCeti.Probability
