/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.MeasureTheory.Function.L2Space
import TauCeti.Analysis.Real.Sqrt

/-!
# The Cauchy–Schwarz inequality for real integrals

For square-integrable real functions `f` and `g`,

`(∫ f g)² ≤ (∫ f²) (∫ g²)`

(`TauCeti.sq_integral_mul_le_integral_sq_mul_integral_sq`). Mathlib states Hölder's inequality
for real integrals with real exponents and roots
(`MeasureTheory.integral_mul_le_Lp_mul_Lq_of_nonneg`); this is the squared form for `p = q = 2`,
without roots or sign conditions, as it is used in energy estimates.

Against the constant function `1` it gives the set-integral form
`(∫ x in S, f x ∂μ)² ≤ μ(S) ∫ x in S, f x² ∂μ` on a set of finite measure
(`TauCeti.sq_setIntegral_le_measureReal_mul_setIntegral_sq`), which needs only `f²`
to be integrable on `S`. For a measure of total mass at most `1`, such as a probability measure or
its restriction to an event, this becomes the first-moment bound `|∫ g dμ| ≤ √(∫ g² dμ)` for `g`
with `g²` integrable (`MeasureTheory.Integrable.abs_integral_le_sqrt_integral_sq`). Its
consequence for absolute moments is `∫ ‖f‖ᵏ dμ ≤ √(∫ ‖f‖²ᵏ dμ)` for `f` with `‖f‖²ᵏ` integrable
(`MeasureTheory.Integrable.integral_norm_pow_le_sqrt_integral_norm_pow_two_mul`).

A weighted variant for nonnegative `a`, `d` and positive `g` gives
`(∫ a √d)² ≤ (∫ a (d / g)) (∫ a g)` (`TauCeti.sq_integral_mul_sqrt_le_integral_mul_div_mul`).
For `f ∈ L²` and nonnegative integrable `g`,
`|∫ f √g dμ| ≤ √((∫ f² dμ) (∫ g dμ))`
(`TauCeti.abs_integral_mul_sqrt_le_sqrt_integral_sq_mul_integral`), which yields the `L¹`-stability
bound `|∫ a √d dμ - ∫ a₀ √d₀ dμ| ≤ √C ∫ |a - a₀| dμ + √((∫ a₀² dμ) ∫ |d - d₀| dμ)`
(`TauCeti.abs_integral_mul_sqrt_sub_integral_mul_sqrt_le`).
-/

public section

namespace TauCeti

open MeasureTheory

/-- **The Cauchy–Schwarz inequality** `(∫ f g)² ≤ (∫ f²) (∫ g²)` for square-integrable real
functions. -/
theorem sq_integral_mul_le_integral_sq_mul_integral_sq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    (∫ x, f x * g x ∂μ) ^ 2 ≤ (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
  have h := integral_mul_le_Lp_mul_Lq_of_nonneg Real.HolderConjugate.two_two
    (Filter.Eventually.of_forall fun x ↦ abs_nonneg (f x))
    (Filter.Eventually.of_forall fun x ↦ abs_nonneg (g x))
    (by simpa [Real.norm_eq_abs] using hf.norm) (by simpa [Real.norm_eq_abs] using hg.norm)
  have hF : 0 ≤ ∫ x, f x ^ 2 ∂μ := integral_nonneg fun x ↦ sq_nonneg _
  have hG : 0 ≤ ∫ x, g x ^ 2 ∂μ := integral_nonneg fun x ↦ sq_nonneg _
  simp only [Real.rpow_two, sq_abs, ← Real.sqrt_eq_rpow] at h
  calc (∫ x, f x * g x ∂μ) ^ 2 = |∫ x, f x * g x ∂μ| ^ 2 := (sq_abs _).symm
    _ ≤ (∫ x, |f x| * |g x| ∂μ) ^ 2 := by
        gcongr
        calc |∫ x, f x * g x ∂μ| ≤ ∫ x, |f x * g x| ∂μ := abs_integral_le_integral_abs
          _ = ∫ x, |f x| * |g x| ∂μ := by simp_rw [abs_mul]
    _ ≤ (√(∫ x, f x ^ 2 ∂μ) * √(∫ x, g x ^ 2 ∂μ)) ^ 2 :=
        pow_le_pow_left₀ (integral_nonneg fun x ↦ by positivity) h 2
    _ = (∫ x, f x ^ 2 ∂μ) * ∫ x, g x ^ 2 ∂μ := by
        rw [mul_pow, Real.sq_sqrt hF, Real.sq_sqrt hG]

/-- Cauchy--Schwarz for a real-valued set integral over a set of finite measure, in squared form.
Only `f²` needs to be integrable on `S`. -/
theorem sq_setIntegral_le_measureReal_mul_setIntegral_sq {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} (f : Ω → ℝ) (S : Set Ω) (hS_top : μ S ≠ ⊤)
    (hf_sq : IntegrableOn (fun x => f x ^ 2) S μ) :
    (∫ x in S, f x ∂μ) ^ 2 ≤ μ.real S * ∫ x in S, f x ^ 2 ∂μ := by
  by_cases hf : AEStronglyMeasurable f (μ.restrict S)
  · have : IsFiniteMeasure (μ.restrict S) := isFiniteMeasure_restrict.2 hS_top
    have h := sq_integral_mul_le_integral_sq_mul_integral_sq
      ((memLp_two_iff_integrable_sq hf).2 hf_sq) (memLp_const (1 : ℝ))
    simpa [mul_comm] using h
  · rw [integral_non_aestronglyMeasurable hf]
    simpa using mul_nonneg measureReal_nonneg (integral_nonneg fun x => sq_nonneg (f x))

/-- **Weighted Cauchy–Schwarz inequality** `(∫ a √d)² ≤ (∫ a (d / g)) (∫ a g)` for almost
everywhere nonnegative weights `a` and `d` and almost everywhere positive `g`. -/
theorem sq_integral_mul_sqrt_le_integral_mul_div_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {a d g : α → ℝ} (ha : ∀ᵐ x ∂μ, 0 ≤ a x) (hd : ∀ᵐ x ∂μ, 0 ≤ d x)
    (hg : ∀ᵐ x ∂μ, 0 < g x) (hadg : Integrable (fun x ↦ a x * (d x / g x)) μ)
    (hag : Integrable (fun x ↦ a x * g x) μ) :
    (∫ x, a x * √(d x) ∂μ) ^ 2 ≤ (∫ x, a x * (d x / g x) ∂μ) * ∫ x, a x * g x ∂μ := by
  have hmem1 : MemLp (fun x ↦ √(a x * (d x / g x))) 2 μ :=
    (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hadg.aestronglyMeasurable)).2 <|
      hadg.congr <| by
        filter_upwards [ha, hd, hg] with x hxa hxd hxg
        exact (Real.sq_sqrt (mul_nonneg hxa (div_nonneg hxd hxg.le))).symm
  have hmem2 : MemLp (fun x ↦ √(a x * g x)) 2 μ :=
    (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hag.aestronglyMeasurable)).2 <|
      hag.congr <| by
        filter_upwards [ha, hg] with x hxa hxg
        exact (Real.sq_sqrt (mul_nonneg hxa hxg.le)).symm
  have hcs := sq_integral_mul_le_integral_sq_mul_integral_sq hmem1 hmem2
  have hprod : (fun x ↦ √(a x * (d x / g x)) * √(a x * g x)) =ᵐ[μ] fun x ↦ a x * √(d x) := by
    filter_upwards [ha, hd, hg] with x hxa hxd hxg
    have hmul : a x * (d x / g x) * (a x * g x) = a x ^ 2 * d x := by
      calc a x * (d x / g x) * (a x * g x) = a x ^ 2 * d x * (g x / g x) := by ring
        _ = a x ^ 2 * d x := by rw [div_self hxg.ne', mul_one]
    rw [← Real.sqrt_mul (mul_nonneg hxa (div_nonneg hxd hxg.le)), hmul,
      Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hxa]
  have hsq1 : (fun x ↦ √(a x * (d x / g x)) ^ 2) =ᵐ[μ] fun x ↦ a x * (d x / g x) := by
    filter_upwards [ha, hd, hg] with x hxa hxd hxg
    exact Real.sq_sqrt (mul_nonneg hxa (div_nonneg hxd hxg.le))
  have hsq2 : (fun x ↦ √(a x * g x) ^ 2) =ᵐ[μ] fun x ↦ a x * g x := by
    filter_upwards [ha, hg] with x hxa hxg
    exact Real.sq_sqrt (mul_nonneg hxa hxg.le)
  rwa [integral_congr_ae hprod, integral_congr_ae hsq1, integral_congr_ae hsq2] at hcs

/-- Cauchy–Schwarz for a product `f * √g` with `f ∈ L²` and `g ≥ 0` integrable:
`|∫ f √g ∂μ| ≤ √((∫ f² ∂μ) (∫ g ∂μ))`. -/
theorem abs_integral_mul_sqrt_le_sqrt_integral_sq_mul_integral {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f g : α → ℝ} (hf : MemLp f 2 μ) (hg : ∀ᵐ x ∂μ, 0 ≤ g x)
    (hg_int : Integrable g μ) :
    |∫ x, f x * √(g x) ∂μ| ≤ √((∫ x, f x ^ 2 ∂μ) * ∫ x, g x ∂μ) := by
  have hg_sqrt : MemLp (fun x ↦ √(g x)) 2 μ :=
    (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hg_int.aestronglyMeasurable)).2 <|
      hg_int.congr <| hg.mono fun x hx ↦ (Real.sq_sqrt hx).symm
  have hcs := sq_integral_mul_le_integral_sq_mul_integral_sq hf hg_sqrt
  have hsq : ∫ x, √(g x) ^ 2 ∂μ = ∫ x, g x ∂μ :=
    integral_congr_ae <| hg.mono fun x hx ↦ Real.sq_sqrt hx
  rw [hsq] at hcs
  exact Real.abs_le_sqrt hcs

/-- `L¹`-stability of the pairing `∫ a √d ∂μ` when `d ≤ C` a.e. and `a₀ ∈ L²`:
`|∫ a √d ∂μ - ∫ a₀ √d₀ ∂μ| ≤ √C ∫ |a - a₀| ∂μ + √((∫ a₀² ∂μ) ∫ |d - d₀| ∂μ)`. -/
theorem abs_integral_mul_sqrt_sub_integral_mul_sqrt_le {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {a a₀ d d₀ : α → ℝ} {C : ℝ} (ha : Integrable a μ)
    (ha₀ : Integrable a₀ μ) (ha₀_L2 : MemLp a₀ 2 μ) (hd : Integrable d μ)
    (hd₀ : Integrable d₀ μ) (hd_le : ∀ᵐ x ∂μ, d x ≤ C) :
    |∫ x, a x * √(d x) ∂μ - ∫ x, a₀ x * √(d₀ x) ∂μ| ≤
      √C * ∫ x, |a x - a₀ x| ∂μ +
        √((∫ x, a₀ x ^ 2 ∂μ) * ∫ x, |d x - d₀ x| ∂μ) := by
  have had : Integrable (fun x ↦ a x * √(d x)) μ :=
    ha.mul_bdd (c := √C)
      (Real.continuous_sqrt.comp_aestronglyMeasurable hd.aestronglyMeasurable)
      (hd_le.mono fun x hx ↦ by
        rw [Real.norm_of_nonneg (Real.sqrt_nonneg _)]
        exact Real.sqrt_le_sqrt hx)
  have hd₀_sqrt : MemLp (fun x ↦ √(d₀ x)) 2 μ :=
    (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hd₀.aestronglyMeasurable)).2 <|
      hd₀.abs.mono' ((Real.continuous_sqrt.comp_aestronglyMeasurable
        hd₀.aestronglyMeasurable).pow 2) (.of_forall fun x ↦ by
          rw [Real.norm_of_nonneg (sq_nonneg _), Real.sq_sqrt']
          exact max_le (le_abs_self _) (abs_nonneg _))
  have ha₀d₀ : Integrable (fun x ↦ a₀ x * √(d₀ x)) μ := ha₀_L2.integrable_mul hd₀_sqrt
  have hdiff_int : Integrable (fun x ↦ |d x - d₀ x|) μ := (hd.sub hd₀).abs
  have hsqrt_diff : MemLp (fun x ↦ √|d x - d₀ x|) 2 μ :=
    (memLp_two_iff_integrable_sq
      (Real.continuous_sqrt.comp_aestronglyMeasurable hdiff_int.aestronglyMeasurable)).2 <|
      hdiff_int.congr (.of_forall fun _ ↦ (Real.sq_sqrt (abs_nonneg _)).symm)
  have ha₀_abs_L2 : MemLp (fun x ↦ |a₀ x|) 2 μ := by
    simpa only [Real.norm_eq_abs] using ha₀_L2.norm
  have hterm1 : Integrable (fun x ↦ √C * |a x - a₀ x|) μ := (ha.sub ha₀).abs.const_mul √C
  have hterm2 : Integrable (fun x ↦ |a₀ x| * √|d x - d₀ x|) μ :=
    ha₀_abs_L2.integrable_mul hsqrt_diff
  have hcs : ∫ x, |a₀ x| * √|d x - d₀ x| ∂μ ≤
      √((∫ x, a₀ x ^ 2 ∂μ) * ∫ x, |d x - d₀ x| ∂μ) := by
    have hnonneg : 0 ≤ ∫ x, |a₀ x| * √|d x - d₀ x| ∂μ :=
      integral_nonneg fun x ↦ mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
    have hle := abs_integral_mul_sqrt_le_sqrt_integral_sq_mul_integral ha₀_abs_L2
      (.of_forall fun _ ↦ abs_nonneg _) hdiff_int
    simpa only [abs_of_nonneg hnonneg, sq_abs] using hle
  have hdiff_eq (x : α) : a x * √(d x) - a₀ x * √(d₀ x) =
      (a x - a₀ x) * √(d x) + a₀ x * (√(d x) - √(d₀ x)) := by ring
  rw [← integral_sub had ha₀d₀]
  calc |∫ x, (a x * √(d x) - a₀ x * √(d₀ x)) ∂μ|
      ≤ ∫ x, |a x * √(d x) - a₀ x * √(d₀ x)| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ x, (√C * |a x - a₀ x| + |a₀ x| * √|d x - d₀ x|) ∂μ := by
        refine integral_mono_ae (had.sub ha₀d₀).abs (hterm1.add hterm2) ?_
        filter_upwards [hd_le] with x hx
        rw [hdiff_eq x]
        refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
        · rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _), mul_comm]
          exact mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hx) (abs_nonneg _)
        · rw [abs_mul]
          exact mul_le_mul_of_nonneg_left (Real.abs_sqrt_sub_sqrt_le _ _) (abs_nonneg _)
    _ = √C * ∫ x, |a x - a₀ x| ∂μ + ∫ x, |a₀ x| * √|d x - d₀ x| ∂μ := by
        rw [integral_add hterm1 hterm2, integral_const_mul]
    _ ≤ _ := add_le_add le_rfl hcs

end TauCeti

namespace MeasureTheory.Integrable

/-- For a measure of total mass at most `1`, the absolute value of the mean of a real function with
integrable square is at most the square root of its second moment. -/
theorem abs_integral_le_sqrt_integral_sq {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {g : Ω → ℝ} (hg : Integrable (fun x => g x ^ 2) μ) (hμ : μ Set.univ ≤ 1) :
    |∫ x, g x ∂μ| ≤ √(∫ x, g x ^ 2 ∂μ) := by
  apply Real.abs_le_sqrt
  have h := TauCeti.sq_setIntegral_le_measureReal_mul_setIntegral_sq g Set.univ
    (hμ.trans_lt ENNReal.one_lt_top).ne hg.integrableOn
  rw [Measure.restrict_univ] at h
  exact h.trans (mul_le_of_le_one_left (integral_nonneg fun x => sq_nonneg _)
    (ENNReal.toReal_le_of_le_ofReal zero_le_one (by rwa [ENNReal.ofReal_one])))

/-- For a measure of total mass at most `1`, the `k`-th absolute moment of a function is at most
the square root of its `2k`-th absolute moment, provided `‖f‖ ^ (2 * k)` is integrable. -/
theorem integral_norm_pow_le_sqrt_integral_norm_pow_two_mul {Ω E : Type*} [MeasurableSpace Ω]
    [Norm E] {μ : Measure Ω} {f : Ω → E} {k : ℕ}
    (hf : Integrable (fun x => ‖f x‖ ^ (2 * k)) μ) (hμ : μ Set.univ ≤ 1) :
    ∫ x, ‖f x‖ ^ k ∂μ ≤ √(∫ x, ‖f x‖ ^ (2 * k) ∂μ) := by
  simp only [pow_mul'] at hf ⊢
  exact le_of_abs_le (hf.abs_integral_le_sqrt_integral_sq hμ)

end MeasureTheory.Integrable
