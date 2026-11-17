/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Polylogarithm.Basic
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Polylogarithm.RadialIntegrand

/-!
# Holomorphy and Euler differential recursion of principal polylogarithms

In every integer weight `n : ℤ`, `TauCeti.Polylog.polylog n` is complex analytic on the cut plane
`{z : ℂ | 1 - z ∈ Complex.slitPlane} = ℂ \ [1, ∞)` (`analyticOnNhd_polylog`, `analyticAt_polylog`)
and satisfies Euler's recursion `z * deriv (polylog (n + 1)) z = polylog n z`
(`mul_deriv_polylog_add_one`, `hasDerivAt_polylog_add_one`), via parametric differentiation and
integration by parts of the radial integral (`hasDerivAt_polylog_nat_add_two`), together with
weight-one regularity and cut discontinuity (`hasDerivAt_polylog_one`, `analyticAt_polylog_one`,
`not_continuousAt_polylog_one_of_one_lt`).

## References

* J. Oesterlé, *Polylogarithmes*, Astérisque 216 (1993), §1.1; A. B. Goncharov, ICM 1994, §1.0.
-/

public section

open Filter MeasureTheory Metric Set Topology

namespace TauCeti.Polylog

/-- The principal polylogarithm domain `{z : ℂ | 1 - z ∈ Complex.slitPlane}` is open. -/
theorem isOpen_one_sub_mem_slitPlane : IsOpen {z : ℂ | 1 - z ∈ Complex.slitPlane} :=
  Complex.isOpen_slitPlane.preimage (by fun_prop)

/-- Complex derivative of `polylog 1` (`-Log(1 - z)`) on `ℂ \ [1, ∞)`. -/
theorem hasDerivAt_polylog_one {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    HasDerivAt (polylog 1) (1 - z)⁻¹ z := by
  rw [funext polylog_one]; convert (((hasDerivAt_id z).const_sub (1 : ℂ)).clog hz).neg using 1
  · ext w; rfl
  · dsimp; ring

/-- Complex analyticity of `polylog 1` (`-Log(1 - z)`) at every point of `ℂ \ [1, ∞)`. -/
theorem analyticAt_polylog_one {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    AnalyticAt ℂ (polylog 1) z := by
  rw [funext polylog_one]; exact ((analyticAt_const.sub analyticAt_id).clog hz).neg

/-- `polylog 1` is not continuous at any real `x > 1`, where `-Log(1 - z)` jumps across `(1, ∞)`. -/
theorem not_continuousAt_polylog_one_of_one_lt {x : ℝ} (hx : 1 < x) :
    ¬ ContinuousAt (polylog 1) x := fun hcont => by
  let φ : ℝ → ℂ := fun y => (x : ℂ) - (y : ℂ) * Complex.I
  have hφ0 : φ 0 = x := by simp [φ]
  have hcont_im : ContinuousAt (fun y : ℝ => (-polylog 1 (φ y)).im) 0 :=
    Complex.continuous_im.continuousAt.comp (((hφ0.symm ▸ hcont).comp (by fun_prop)).neg)
  have htend : Tendsto (fun y : ℝ => (-polylog 1 (φ y)).im) (𝓝[<] 0) (𝓝 ((-polylog 1 x).im)) := by
    simpa [hφ0] using hcont_im.tendsto.mono_left nhdsWithin_le_nhds
  have hle : ∀ᶠ y : ℝ in 𝓝[<] 0, (-polylog 1 (φ y)).im ≤ 0 :=
    eventually_nhdsWithin_of_forall fun y (hy : y < 0) => by
      rw [polylog_one, neg_neg, Complex.log_im]
      exact (Complex.arg_neg_iff.2 (by simpa [φ] using hy)).le
  have hcast : (1 : ℂ) - (x : ℂ) = ((1 - x : ℝ) : ℂ) := by push_cast; ring
  have him_pi : (-polylog 1 x).im = Real.pi := by
    rw [polylog_one, neg_neg, hcast, Complex.log_im, Complex.arg_ofReal_of_neg (sub_neg.mpr hx)]
  linarith [le_of_tendsto htend hle, Real.pi_pos]

private theorem hasDerivAt_integral_radialIntegrand (k : ℕ) {z₀ : ℂ}
    (hz₀ : 1 - z₀ ∈ Complex.slitPlane) :
    IntervalIntegrable (fun t : ℝ => ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z₀)) volume 0 1 ∧
      HasDerivAt (fun z => ∫ t : ℝ in 0..1,
          ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * z)) / (t : ℂ))
        (∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z₀)) z₀ := by
  obtain ⟨r, hr, hrsub⟩ :=
    nhds_basis_closedBall.mem_iff.mp (isOpen_one_sub_mem_slitPlane.mem_nhds hz₀)
  obtain ⟨δ, hδ, hδle⟩ := exists_le_norm_one_sub_ofReal_mul (isCompact_closedBall z₀ r) hrsub
  refine intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z t => ((-Real.log t : ℝ) : ℂ) ^ k * (-Complex.log (1 - (t : ℂ) * z)) / (t : ℂ))
    (F' := fun z t => ((-Real.log t : ℝ) : ℂ) ^ k / (1 - (t : ℂ) * z))
    (s := closedBall z₀ r) (bound := fun t => δ⁻¹ * ‖Real.log t ^ k‖) (closedBall_mem_nhds z₀ hr)
    (.of_forall fun _ => (by fun_prop : Measurable _).aestronglyMeasurable)
    (intervalIntegrable_radialIntegrand k z₀) (by fun_prop : Measurable _).aestronglyMeasurable
    (.of_forall fun t ht z hz => ?_) (((intervalIntegrable_log_pow k).norm).const_mul δ⁻¹)
    (.of_forall fun t ht z hz => ?_)
  · rw [uIoc_of_le zero_le_one] at ht; rw [norm_div, norm_pow, Complex.norm_real, Real.norm_eq_abs,
      abs_neg, Real.norm_eq_abs, abs_pow, inv_mul_eq_div]
    exact div_le_div_of_nonneg_left (pow_nonneg (abs_nonneg _) k) hδ
      (hδle z hz t (Ioc_subset_Icc_self ht))
  · rw [uIoc_of_le zero_le_one] at ht
    have hmem : 1 - (t : ℂ) * z ∈ Complex.slitPlane :=
      mul_comm z (t : ℂ) ▸ Complex.one_sub_mul_ofReal_mem_slitPlane (hrsub hz)
        (Ioc_subset_Icc_self ht)
    have hlog : HasDerivAt (fun w : ℂ => -Complex.log (1 - (t : ℂ) * w))
        ((t : ℂ) / (1 - (t : ℂ) * z)) z := by
      convert ((((hasDerivAt_id z).const_mul (t : ℂ)).const_sub (1 : ℂ)).clog hmem).neg using 1
      · ext w; rfl
      · dsimp; ring
    convert (hlog.const_mul (((-Real.log t : ℝ) : ℂ) ^ k)).div_const (t : ℂ) using 1
    field_simp [Complex.ofReal_ne_zero.mpr ht.1.ne']

/-- Parametric derivative of the radial integral defining `polylog (k + 2)` on `ℂ \ [1, ∞)`. -/
theorem hasDerivAt_polylog_nat_add_two (k : ℕ) {z₀ : ℂ} (hz₀ : 1 - z₀ ∈ Complex.slitPlane) :
    HasDerivAt (polylog (k + 2 : ℕ))
      ((k.factorial : ℂ)⁻¹ * ∫ t : ℝ in 0..1, ((-Real.log t : ℝ) : ℂ) ^ k / (1 - t * z₀)) z₀ := by
  rw [funext (polylog_nat_add_two k)]
  exact (hasDerivAt_integral_radialIntegrand k hz₀).2.const_mul (k.factorial : ℂ)⁻¹

/-- **Holomorphy of principal polylogarithms** on `{z : ℂ | 1 - z ∈ Complex.slitPlane}`. -/
theorem analyticOnNhd_polylog (n : ℤ) :
    AnalyticOnNhd ℂ (polylog n) {z : ℂ | 1 - z ∈ Complex.slitPlane} := by
  have hne : ∀ {z : ℂ}, 1 - z ∈ Complex.slitPlane → z ≠ 1 := fun hz h1 =>
    Complex.slitPlane_ne_zero hz (by simp [h1])
  cases n with
  | negSucc r => exact fun _ hz => (rfl : Int.negSucc r = -((r + 1 : ℕ) : ℤ)) ▸
      analyticAt_polylog_neg_nat (r + 1) (hne hz)
  | ofNat m =>
    rcases m with _ | _ | k
    · exact fun _ hz => by simpa using analyticAt_polylog_neg_nat 0 (hne hz)
    · exact fun _ hz => analyticAt_polylog_one hz
    · exact DifferentiableOn.analyticOnNhd
        (fun _ hz => (hasDerivAt_polylog_nat_add_two k hz).differentiableAt.differentiableWithinAt)
        isOpen_one_sub_mem_slitPlane

/-- Pointwise complex analyticity of `polylog n` at `z ∈ ℂ \ [1, ∞)`. -/
theorem analyticAt_polylog (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    AnalyticAt ℂ (polylog n) z := analyticOnNhd_polylog n z hz

private theorem mul_deriv_polylog_nat_add_three (m : ℕ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    z * deriv (polylog (m + 3 : ℕ)) z = polylog (m + 2 : ℕ) z := by
  let H : ℝ → ℂ := fun t => ((-Real.log t : ℝ) : ℂ) ^ (m + 1) * (-Complex.log (1 - (t : ℂ) * z))
  let H'1 : ℝ → ℂ := fun t =>
    -((m + 1 : ℂ) * (((-Real.log t : ℝ) : ℂ) ^ m * (-Complex.log (1 - (t : ℂ) * z)) / (t : ℂ)))
  let H'2 : ℝ → ℂ := fun t => z * (((-Real.log t : ℝ) : ℂ) ^ (m + 1) / (1 - (t : ℂ) * z))
  have hderiv : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt H (H'1 t + H'2 t) t := fun t ht => by
    have hlog : HasDerivAt (fun s : ℝ => ((-Real.log s : ℝ) : ℂ)) (-(t : ℂ)⁻¹) t := by
      simpa using ((Real.hasDerivAt_log ht.1.ne').neg).ofReal_comp
    have hmem : 1 - (t : ℂ) * z ∈ Complex.slitPlane :=
      mul_comm z (t : ℂ) ▸ Complex.one_sub_mul_ofReal_mem_slitPlane hz (Ioo_subset_Icc_self ht)
    have hclog := ((((hasDerivAt_id (t : ℂ)).mul_const z).const_sub 1).clog hmem).neg.comp_ofReal
    convert (hlog.pow (m + 1)).mul hclog using 1
    · ext s; rfl
    · simp only [H'1, H'2, Pi.pow_apply, Pi.neg_apply, id_eq, Nat.add_sub_cancel]; push_cast; ring
  have hint1 : IntervalIntegrable H'1 volume 0 1 :=
    ((intervalIntegrable_radialIntegrand m z).const_mul (m + 1 : ℂ)).neg
  have hint2 : IntervalIntegrable H'2 volume 0 1 :=
    (hasDerivAt_integral_radialIntegrand (m + 1) hz).1.const_mul z
  have hlim0 : Tendsto H (𝓝[>] 0) (𝓝 0) := by
    have hlog_o : (fun t : ℝ => ((-Real.log t : ℝ) : ℂ) ^ (m + 1)) =o[𝓝[>] 0] fun t => t⁻¹ :=
      Asymptotics.isLittleO_norm_left.mp <| by
        simpa only [norm_pow, Complex.norm_real, Real.norm_eq_abs, abs_neg, Real.rpow_natCast,
          Real.rpow_neg_one] using
          isLittleO_abs_log_rpow_rpow_nhdsGT_zero (s := -1) ((m + 1 : ℕ) : ℝ) (by norm_num)
    have hclog_O : (fun t : ℝ => -Complex.log (1 - (t : ℂ) * z)) =O[𝓝[>] 0] fun t => t := by
      have hd0 :=
        ((((hasDerivAt_id (0 : ℂ)).mul_const z).const_sub 1).clog (by simp)).neg.comp_ofReal
      simpa using hd0.isBigO_sub.mono nhdsWithin_le_nhds
    exact (Asymptotics.isLittleO_one_iff ℝ).mp <| (hlog_o.mul_isBigO hclog_O).congr' .rfl <|
      eventually_mem_nhdsWithin.mono fun t ht => inv_mul_cancel₀ ht.out.ne'
  have hcont : ContinuousAt H 1 :=
    ((Complex.continuous_ofReal.continuousAt.comp (Real.continuousAt_log one_ne_zero).neg).pow
      (m + 1)).mul ((((hasDerivAt_id (1 : ℂ)).mul_const z).const_sub 1).clog
        (by simpa using hz)).neg.comp_ofReal.continuousAt
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto zero_lt_one hderiv
    (hint1.add hint2) hlim0 (by simpa [H] using hcont.tendsto.mono_left nhdsWithin_le_nhds)
  rw [intervalIntegral.integral_add hint1 hint2, intervalIntegral.integral_neg,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul, sub_zero,
    neg_add_eq_zero] at hftc
  rw [(hasDerivAt_polylog_nat_add_two (m + 1) hz).deriv, polylog_nat_add_two, mul_left_comm, ← hftc,
    Nat.factorial_succ, Nat.cast_mul, mul_inv_rev, ← mul_assoc]
  have hm1 : (m + 1 : ℂ) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  simp [Nat.cast_add, Nat.cast_one, hm1]

/-- **Euler's differential recursion** on `ℂ \ [1, ∞)` in every integer weight `n : ℤ`:
`z * deriv (polylog (n + 1)) z = polylog n z`, including `z = 0`. -/
theorem mul_deriv_polylog_add_one (n : ℤ) {z : ℂ} (hz : 1 - z ∈ Complex.slitPlane) :
    z * deriv (polylog (n + 1)) z = polylog n z := by
  cases n with
  | negSucc r =>
    have heq1 : Int.negSucc r + 1 = -(r : ℤ) := by omega
    have hr : Int.negSucc r = -((r + 1 : ℕ) : ℤ) := rfl; rw [heq1, hr, polylog_neg_nat_succ]
  | ofNat m =>
    rcases m with _ | _ | m
    · rw [Int.ofNat_eq_natCast, Nat.cast_zero, zero_add, (hasDerivAt_polylog_one hz).deriv,
        polylog_zero_weight, div_eq_mul_inv]
    · have h12 : ((1 : ℕ) : ℤ) + 1 = ((0 + 2 : ℕ) : ℤ) := rfl
      rw [Int.ofNat_eq_natCast, h12, (hasDerivAt_polylog_nat_add_two 0 hz).deriv]
      simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_mul, pow_zero, one_div]
      rw [← intervalIntegral.integral_const_mul]
      have hderiv : ∀ t ∈ uIcc (0 : ℝ) 1,
          HasDerivAt (fun s : ℝ => -Complex.log (1 - (s : ℂ) * z)) (z * (1 - (t : ℂ) * z)⁻¹) t :=
        fun t ht => by
          rw [uIcc_of_le zero_le_one] at ht
          have hmem : 1 - (t : ℂ) * z ∈ Complex.slitPlane :=
            mul_comm z (t : ℂ) ▸ Complex.one_sub_mul_ofReal_mem_slitPlane hz ht
          convert ((((hasDerivAt_id (t : ℂ)).mul_const z).const_sub 1).clog
            hmem).neg.comp_ofReal using 1
          · ext s; rfl
          · simp [div_eq_mul_inv]
      have hint := (hasDerivAt_integral_radialIntegrand 0 hz).1.const_mul z
      simp only [pow_zero, one_div] at hint
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]; simp [polylog_one]
    · exact mul_deriv_polylog_nat_add_three m hz

/-- Away from `0` on `ℂ \ [1, ∞)`, the derivative of `polylog (n + 1)` is `polylog n z / z`. -/
theorem hasDerivAt_polylog_add_one (n : ℤ) {z : ℂ} (hz0 : z ≠ 0) (hz : 1 - z ∈ Complex.slitPlane) :
    HasDerivAt (polylog (n + 1)) (polylog n z / z) z := by
  have hd := (analyticAt_polylog (n + 1) hz).differentiableAt.hasDerivAt
  rwa [← mul_deriv_polylog_add_one n hz, mul_div_cancel_left₀ _ hz0]

end TauCeti.Polylog
