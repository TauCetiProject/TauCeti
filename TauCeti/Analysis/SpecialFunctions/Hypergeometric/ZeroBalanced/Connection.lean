/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.ZeroBalanced.Basic
public import TauCeti.Analysis.SpecialFunctions.OrdinaryHypergeometric
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.Analysis.Analytic.OfScalars
import TauCeti.Analysis.Complex.Basic
import TauCeti.Analysis.Complex.RealIdentity
import TauCeti.Analysis.SpecialFunctions.Beta.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.GaussSeries
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.EulerIntegral.Basic
import TauCeti.Analysis.SpecialFunctions.Log.Limits
import TauCeti.RingTheory.Binomial

/-!
# The zero-balanced hypergeometric connection formula

When `2a ∉ -ℕ`, `₂F₁(a, a; 2a; 1 - x)` agrees on the lens `‖x‖ < 1`, `‖1 - x‖ < 1` with
`TauCeti.zeroBalancedSeries`, identifying that series as the analytic continuation across
`Metric.ball 0 1 ∩ Complex.slitPlane`. For `a, x ∈ (0, 1)`, Euler's integral and
`-log x · u₁(a, x) + v(a, x)` both solve `(x (1 - x)^(2a) y')' = a² (1 - x)^(2a - 1) y` with `0⁺`
asymptotic `-log x + 2(ψ(1) - ψ(a)) + o(1)`; Wronskian constancy against `u₁` equates them on
`(0, 1)`, and analytic continuation yields
`TauCeti.ordinaryHypergeometric_one_sub_eq_zeroBalancedSeries` and
`TauCeti.zero_balanced_connection`.

## References

* F. Calegari, V. Dimitrov and Y. Tang (CDT), *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. 38 (2025), Lemma 5.1.20 (p. 672).
* [NIST DLMF, 15.8.10](https://dlmf.nist.gov/15.8.E10), [15.6.1](https://dlmf.nist.gov/15.6.E1),
  [15.2.2](https://dlmf.nist.gov/15.2.E2).
-/

public section

open Complex Filter MeasureTheory Metric Set
open scoped Nat Real Topology

namespace TauCeti

/-! ### Sturm-Liouville differential equation on `(0, 1)` -/

private theorem rpow_sub_one_mul {y p : ℝ} (hy : 0 < y) : y ^ (p - 1) * y = y ^ p := by
  rw [← Real.rpow_add_one hy.ne', sub_add_cancel]

private noncomputable def eulerZeroBalanced (a x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, t ^ (a - 1) * (1 - t) ^ (a - 1) * (1 - (1 - x) * t) ^ (-a)

private theorem ordinaryHypergeometric_eq_mul_eulerZeroBalanced {a x : ℝ}
    (ha : 0 < a) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ₂F₁ a a (2 * a) (1 - x) =
      Real.Gamma (2 * a) / Real.Gamma a ^ 2 * eulerZeroBalanced a x := by
  simpa only [eulerZeroBalanced, (by ring : 2 * a - a = a), ← sq] using
    ordinaryHypergeometric_eq_integral (a := a) (b := a) (c := 2 * a) (z := 1 - x)
      ha (by linarith) (abs_lt.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩)

private theorem hasDerivAt_mul_one_sub_rpow (a : ℝ) {x : ℝ} (hx : x < 1) :
    HasDerivAt (fun y : ℝ ↦ y * (1 - y) ^ (2 * a))
      ((1 - x) ^ (2 * a) - 2 * a * x * (1 - x) ^ (2 * a - 1)) x :=
  ((hasDerivAt_id x).mul ((Real.hasDerivAt_rpow_const (p := 2 * a)
    (Or.inl (sub_pos.mpr hx).ne')).comp x ((hasDerivAt_id x).const_sub 1))).congr_deriv
    (by simp only [Function.comp_apply, id_eq]; ring)

private theorem hasFPowerSeriesOnBall_ordinaryHypergeometric_real (a b c : ℝ) :
    HasFPowerSeriesOnBall (₂F₁ a b c : ℝ → ℝ)
      (FormalMultilinearSeries.ofScalars ℝ (ordinaryHypergeometricCoefficient a b c)) 0 1 :=
  ((ordinaryHypergeometricSeries ℝ a b c).hasFPowerSeriesOnBall
    (zero_lt_one.trans_le (one_le_radius_ordinaryHypergeometricSeries ℝ a b c))).mono
      zero_lt_one (one_le_radius_ordinaryHypergeometricSeries ℝ a b c)

private theorem differentiableAt_and_sturmLiouville_eulerZeroBalanced {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (eulerZeroBalanced a) x ∧
    HasDerivAt (fun y ↦ y * (1 - y) ^ (2 * a) * deriv (eulerZeroBalanced a) y)
      (a ^ 2 * (1 - x) ^ (2 * a - 1) * eulerZeroBalanced a x) x := by
  let γ := Real.Gamma a ^ 2 / Real.Gamma (2 * a)
  have hf := hasFPowerSeriesOnBall_ordinaryHypergeometric_real a a (2 * a)
  have hE_eq {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
      eulerZeroBalanced a y = γ * ₂F₁ a a (2 * a) (1 - y) := by
    have h := ordinaryHypergeometric_eq_mul_eulerZeroBalanced ha.1 hy
    dsimp [γ]
    field_simp [(Real.Gamma_pos_of_pos ha.1).ne',
      (Real.Gamma_pos_of_pos (by linarith [ha.1] : 0 < 2 * a)).ne'] at h ⊢
    linarith
  have hmem {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : 1 - y ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one, Real.norm_eq_abs,
      abs_lt]
    exact ⟨by linarith [hy.2], by linarith [hy.1]⟩
  have hd_at {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (eulerZeroBalanced a) (-γ * deriv (₂F₁ a a (2 * a)) (1 - y)) y :=
    ((((hf.analyticAt_of_mem (hmem hy)).differentiableAt.hasDerivAt.comp y
        ((hasDerivAt_id y).const_sub 1)).const_mul γ).congr_of_eventuallyEq
      (by filter_upwards [Ioo_mem_nhds hy.1 hy.2] with u hu using hE_eq hu)).congr_deriv
        (by ring)
  refine ⟨(hd_at hx).differentiableAt, ?_⟩
  have hd2 : HasDerivAt (fun y : ℝ ↦ deriv (₂F₁ a a (2 * a)) (1 - y))
      (-deriv (deriv (₂F₁ a a (2 * a))) (1 - x)) x :=
    ((hf.deriv_ofScalars.analyticAt_of_mem (hmem hx)).differentiableAt.hasDerivAt.comp x
      ((hasDerivAt_id x).const_sub 1)).congr_deriv (by ring)
  refine (((hasDerivAt_mul_one_sub_rpow a hx.2).mul (hd2.const_mul (-γ))).congr_of_eventuallyEq
    ?_).congr_deriv ?_
  · filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy; simp [(hd_at hy).deriv]
  · have hode := ordinaryHypergeometric_gaussEquation_of_norm_lt_one (𝕂 := ℝ) a a (2 * a)
      (fun k hk ↦ by linarith [ha.1, show (0 : ℝ) ≤ k by positivity])
      (Real.norm_eq_abs (1 - x) ▸ abs_lt.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩)
    rw [hE_eq hx, ← rpow_sub_one_mul (sub_pos.mpr hx.2)]
    linear_combination γ * (1 - x) ^ (2 * a - 1) * hode

private noncomputable def realDigammaDiff (a : ℝ) (k : ℕ) : ℝ :=
  2 * (Real.digamma (k + 1) - Real.digamma (k + a))

private noncomputable def realDigammaCoeff (a : ℝ) (k : ℕ) : ℝ :=
  ordinaryHypergeometricCoefficient a a 1 k * realDigammaDiff a k

private noncomputable def realV (a : ℝ) : ℝ → ℝ :=
  FormalMultilinearSeries.ofScalarsSum (realDigammaCoeff a)

private noncomputable def realU2 (a x : ℝ) : ℝ :=
  -Real.log x * ₂F₁ a a 1 x + realV a x

private theorem ordinaryHypergeometricCoefficient_one_eq (a : ℝ) (k : ℕ) :
    ordinaryHypergeometricCoefficient a a 1 k = ((ascPochhammer ℝ k).eval a / k !) ^ 2 := by
  simp [ordinaryHypergeometricCoefficient, ascPochhammer_eval_one]
  ring

private theorem realCoeff_bounds {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (k : ℕ) :
    0 ≤ ordinaryHypergeometricCoefficient a a 1 k ∧
      |ordinaryHypergeometricCoefficient a a 1 k| ≤ 1 := by
  rw [ordinaryHypergeometricCoefficient_one_eq]
  have hle : |(ascPochhammer ℝ k).eval a / k !| ≤ 1 := by
    have hmc : (ascPochhammer ℝ k).eval a / k ! = Ring.multichoose a k := by
      rw [Ring.multichoose_eq_inv_factorial_mul_eval_ascPochhammer, div_eq_inv_mul]
    rw [hmc, ← Real.norm_eq_abs]
    refine (norm_multichoose_le_of_norm_le (w := a) (r := 1) ?_ k).trans_eq
      (Ring.multichoose_one k)
    rw [Real.norm_eq_abs, abs_of_pos ha.1]
    exact ha.2.le
  refine ⟨sq_nonneg _, ?_⟩
  rw [abs_of_nonneg (sq_nonneg _), ← sq_abs]
  exact pow_le_one₀ (abs_nonneg _) hle

private theorem realDigammaCoeff_recurrence {a : ℝ} (ha : 0 < a) (k : ℕ) :
    ((k : ℝ) + 1) * ((k : ℝ) + 1) * realDigammaCoeff a (k + 1) -
      ((k : ℝ) + a) ^ 2 * realDigammaCoeff a k =
    2 * ((k : ℝ) + 1) * ordinaryHypergeometricCoefficient a a 1 (k + 1) -
      2 * ((k : ℝ) + a) * ordinaryHypergeometricCoefficient a a 1 k := by
  have hd : realDigammaDiff a (k + 1) =
      realDigammaDiff a k + 2 / ((k : ℝ) + 1) - 2 / ((k : ℝ) + a) := by
    dsimp [realDigammaDiff]
    rw [Nat.cast_add, Nat.cast_one,
      Real.digamma_apply_add_one (x := (k : ℝ) + 1) (fun m ↦ by
        linarith [show (0 : ℝ) ≤ m by positivity, show (0 : ℝ) ≤ k by positivity]),
      add_right_comm (k : ℝ) 1 a,
      Real.digamma_apply_add_one (x := (k : ℝ) + a) (fun m ↦ by
        linarith [ha, show (0 : ℝ) ≤ m by positivity, show (0 : ℝ) ≤ k by positivity])]
    ring
  have hrec : ((k : ℝ) + 1) * ((k : ℝ) + 1) * ordinaryHypergeometricCoefficient a a 1 (k + 1) =
      ((k : ℝ) + a) ^ 2 * ordinaryHypergeometricCoefficient a a 1 k := by
    rw [ordinaryHypergeometricCoefficient_add_one a a 1 k, (by ring : (1 : ℝ) + k = (k : ℝ) + 1)]
    field_simp
    ring
  dsimp [realDigammaCoeff]
  rw [hd]
  linear_combination (realDigammaDiff a k - 2 / ((k : ℝ) + a)) * hrec +
    ((k : ℝ) + 1) * ordinaryHypergeometricCoefficient a a 1 (k + 1) *
      mul_div_cancel₀ 2 (by positivity : (k : ℝ) + 1 ≠ 0) -
    ((k : ℝ) + a) * ordinaryHypergeometricCoefficient a a 1 k *
      mul_div_cancel₀ 2 (by positivity : (k : ℝ) + a ≠ 0)

private theorem realDigammaCoeff_bound {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, |realDigammaCoeff a k| ≤ B * ((k : ℝ) + 1) ^ 0 := by
  have hd_nn (k : ℕ) : 0 ≤ realDigammaDiff a k := mul_nonneg zero_le_two <| sub_nonneg.mpr <|
    Real.monotoneOn_digamma (mem_Ioi.mpr (by linarith [show (0 : ℝ) ≤ k by positivity, ha.1]))
      (mem_Ioi.mpr (by positivity)) (by linarith [ha.2])
  refine ⟨realDigammaDiff a 0, hd_nn 0, fun k ↦ ?_⟩
  have hle : realDigammaDiff a k ≤ realDigammaDiff a 0 := by
    simpa [realDigammaDiff] using mul_le_mul_of_nonneg_left
      (Real.antitoneOn_digamma_add_sub_digamma_add ha.2.le (mem_Ioi.mpr (by linarith [ha.1]))
        (mem_Ioi.mpr (by linarith [ha.1, show (0 : ℝ) ≤ k by positivity])) (Nat.cast_nonneg k))
      zero_le_two
  rw [realDigammaCoeff, pow_zero, mul_one, abs_mul, abs_of_nonneg (hd_nn k)]
  exact (mul_le_mul (realCoeff_bounds ha k).2 hle (hd_nn k) zero_le_one).trans_eq (one_mul _)

private theorem hasFPowerSeriesOnBall_realV {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    HasFPowerSeriesOnBall (realV a) (FormalMultilinearSeries.ofScalars ℝ (realDigammaCoeff a)) 0
      1 := by
  obtain ⟨B, _, hB⟩ := realDigammaCoeff_bound ha
  have h1 : 1 ≤ (FormalMultilinearSeries.ofScalars ℝ (realDigammaCoeff a)).radius :=
    FormalMultilinearSeries.one_le_radius_ofScalars_of_eventually_norm_le_mul_pow
      (C := B) (m := 0) (Eventually.of_forall fun k ↦ by rw [Real.norm_eq_abs]; exact hB k)
  exact ((FormalMultilinearSeries.ofScalars ℝ (realDigammaCoeff a)).hasFPowerSeriesOnBall
    (zero_lt_one.trans_le h1)).mono zero_lt_one h1

private theorem hasDerivAt_sturmLiouville_realU1 {a x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y ↦ y * (1 - y) ^ (2 * a) * deriv (₂F₁ a a 1) y)
      (a ^ 2 * (1 - x) ^ (2 * a - 1) * ₂F₁ a a 1 x) x := by
  have hx_e : x ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one, Real.norm_eq_abs,
      abs_lt]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hf := hasFPowerSeriesOnBall_ordinaryHypergeometric_real a a 1
  have hd2 := (hf.deriv_ofScalars.analyticAt_of_mem hx_e).differentiableAt.hasDerivAt
  refine ((hasDerivAt_mul_one_sub_rpow a hx.2).mul hd2).congr_deriv ?_
  have hode := ordinaryHypergeometric_gaussEquation_of_norm_lt_one (𝕂 := ℝ) a a 1
    (fun k hk ↦ by linarith [show (0 : ℝ) ≤ k by positivity])
    (Real.norm_eq_abs _ ▸ abs_lt.mpr ⟨by linarith [hx.1], hx.2⟩)
  rw [← rpow_sub_one_mul (sub_pos.mpr hx.2)]
  linear_combination (1 - x) ^ (2 * a - 1) * hode

private theorem realV_ode {a x : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hxa : |x| < 1) :
    x * (1 - x) * deriv (deriv (realV a)) x + (1 - (2 * a + 1) * x) * deriv (realV a) x -
      a ^ 2 * realV a x =
    2 * (1 - x) * deriv (₂F₁ a a 1) x - 2 * a * ₂F₁ a a 1 x := by
  have hxe : ‖x‖ₑ < 1 := by
    rwa [← ofReal_norm, ENNReal.ofReal_lt_one, Real.norm_eq_abs]
  have hxb : x ∈ Metric.eball (0 : ℝ) 1 := mem_eball_zero_iff.mpr hxe
  have hv := hasFPowerSeriesOnBall_realV ha
  have hu := hasFPowerSeriesOnBall_ordinaryHypergeometric_real a a 1
  set D := realDigammaCoeff a
  set C := ordinaryHypergeometricCoefficient a a 1
  have hv0 : HasSum (fun n : ℕ ↦ D n * x ^ n) (realV a x) := by
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hv.hasSum hxb
  have hv1 : HasSum (fun n : ℕ ↦ (n + 1) * D (n + 1) * x ^ n) (deriv (realV a) x) := by
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hv.deriv_ofScalars.hasSum hxb
  have hv2 := hv.hasSum_mul_deriv_ofScalars hxe
  have hv3 := hv.deriv_ofScalars.hasSum_mul_deriv_ofScalars hxe
  have hv4 := hv.hasSum_mul_sq_deriv_deriv_ofScalars hxe
  have hLHS := (hv3.add hv1).sub ((hv4.add (hv2.mul_left (2 * a + 1))).add (hv0.mul_left (a ^ 2)))
  have hu0 : HasSum (fun n : ℕ ↦ C n * x ^ n) (₂F₁ a a 1 x) := by
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hu.hasSum hxb
  have hu1 : HasSum (fun n : ℕ ↦ (n + 1) * C (n + 1) * x ^ n) (deriv (₂F₁ a a 1) x) := by
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hu.deriv_ofScalars.hasSum hxb
  have hu2 := hu.hasSum_mul_deriv_ofScalars hxe
  have hRHS := ((hu1.mul_left 2).sub (hu2.mul_left 2)).sub (hu0.mul_left (2 * a))
  have hcongr :
      (fun n : ℕ ↦ n * ((n + 1) * D (n + 1)) * x ^ n + (n + 1) * D (n + 1) * x ^ n -
        ((n : ℝ) * ((n : ℝ) - 1) * D n * x ^ n + (2 * a + 1) * (n * D n * x ^ n) +
          a ^ 2 * (D n * x ^ n))) =
      fun n : ℕ ↦ 2 * ((n + 1) * C (n + 1) * x ^ n) - 2 * (n * C n * x ^ n) -
        2 * a * (C n * x ^ n) := by
    funext n
    linear_combination x ^ n * realDigammaCoeff_recurrence ha.1 n
  rw [hcongr] at hLHS
  linear_combination hLHS.unique hRHS

private theorem hasDerivAt_sturmLiouville_realU2 {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y ↦ y * (1 - y) ^ (2 * a) * deriv (realU2 a) y)
      (a ^ 2 * (1 - x) ^ (2 * a - 1) * realU2 a x) x := by
  have hmem {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : y ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one, Real.norm_eq_abs,
      abs_lt]
    exact ⟨by linarith [hy.1], hy.2⟩
  have hu := hasFPowerSeriesOnBall_ordinaryHypergeometric_real a a 1
  have hv := hasFPowerSeriesOnBall_realV ha
  let u2' := fun y : ℝ ↦
    -y⁻¹ * ₂F₁ a a 1 y - Real.log y * deriv (₂F₁ a a 1) y + deriv (realV a) y
  have hdu2' : HasDerivAt u2'
      ((x⁻¹) ^ 2 * ₂F₁ a a 1 x - 2 * x⁻¹ * deriv (₂F₁ a a 1) x -
        Real.log x * deriv (deriv (₂F₁ a a 1)) x + deriv (deriv (realV a)) x) x :=
    (((((hasDerivAt_inv hx.1.ne').neg.mul
        ((hu.analyticAt_of_mem (hmem hx)).differentiableAt.hasDerivAt)).sub
      ((Real.hasDerivAt_log hx.1.ne').mul
        ((hu.deriv_ofScalars.analyticAt_of_mem (hmem hx)).differentiableAt.hasDerivAt))).add
      ((hv.deriv_ofScalars.analyticAt_of_mem
        (hmem hx)).differentiableAt.hasDerivAt)).congr_of_eventuallyEq
        (Eventually.of_forall fun _ ↦ rfl)).congr_deriv
        (by simp only [Pi.neg_apply, ← inv_pow]; ring)
  refine (((hasDerivAt_mul_one_sub_rpow a hx.2).mul hdu2').congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    have hdy : deriv (realU2 a) y = u2' y :=
      (((((Real.hasDerivAt_log hy.1.ne').neg.mul
        ((hu.analyticAt_of_mem (hmem hy)).differentiableAt.hasDerivAt)).add
        ((hv.analyticAt_of_mem (hmem hy)).differentiableAt.hasDerivAt)).congr_of_eventuallyEq
        (Eventually.of_forall fun _ ↦ rfl)).congr_deriv (by dsimp [u2']; ring)).deriv
    simp [hdy]
  · have hode := ordinaryHypergeometric_gaussEquation_of_norm_lt_one (𝕂 := ℝ) a a 1
      (fun k hk ↦ by linarith [show (0 : ℝ) ≤ k by positivity])
      (Real.norm_eq_abs _ ▸ abs_lt.mpr ⟨by linarith [hx.1], hx.2⟩)
    have hV_eq := realV_ode ha (abs_lt.mpr ⟨by linarith [hx.1], hx.2⟩)
    rw [← rpow_sub_one_mul (sub_pos.mpr hx.2)]
    dsimp only [u2', realU2]
    linear_combination (1 - x) ^ (2 * a - 1) * (-Real.log x * hode + hV_eq +
      ((2 * a + x⁻¹ - x * x⁻¹) * ₂F₁ a a 1 x - 2 * (1 - x) * deriv (₂F₁ a a 1) x) *
        mul_inv_cancel₀ hx.1.ne')

/-! ### Logarithmic asymptotic at `0⁺`, Wronskian uniqueness, and complex continuation -/

private theorem integral_singular_euler_sub {a x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1) :
    (1 - x) ^ a * (∫ s in (0 : ℝ)..1, s ^ (a - 1) * (x + (1 - x) * s) ^ (-a)) =
      ∫ w in (0 : ℝ)..(1 - x), w ^ (a - 1) / (1 - w) := by
  let u : ℝ → ℝ := fun s ↦ (1 - x) * s / (x + (1 - x) * s)
  let u' : ℝ → ℝ := fun s ↦ x * (1 - x) / (x + (1 - x) * s) ^ 2
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := u) (f' := u') (a := (0 : ℝ)) (b := 1)
    (ContinuousOn.div (by fun_prop) (by fun_prop) fun s hs ↦
      (by rw [uIcc_of_le zero_le_one] at hs; nlinarith [hx.1, hx.2, hs.1, hs.2] :
        0 < x + (1 - x) * s).ne')
    (fun s hs ↦ by
      rw [min_eq_left zero_le_one, max_eq_right zero_le_one] at hs
      exact (((hasDerivAt_id s).const_mul (1 - x)).div
        (((hasDerivAt_id s).const_mul (1 - x)).const_add x)
        (by nlinarith [hx.1, hx.2, hs.1, hs.2] : 0 < x + (1 - x) * s).ne').congr_deriv
        (by dsimp [u']; ring))
    (fun _ _ ↦ div_nonneg (mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le)) (sq_nonneg _))
    (g := fun w : ℝ ↦ w ^ (a - 1) / (1 - w))
  rw [(by simp [u] : u 0 = 0),
    (by dsimp [u]; rw [mul_one, add_sub_cancel, div_one] : u 1 = 1 - x)] at hsub
  rw [← hsub, ← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun s hs ↦ ?_)
  rw [uIoc_of_le zero_le_one] at hs
  have h1x := sub_pos.mpr hx.2
  have hD : 0 < x + (1 - x) * s := by nlinarith [hx.1, h1x, hs.1]
  have h1u : 1 - (1 - x) * s / (x + (1 - x) * s) = x / (x + (1 - x) * s) := by
    field_simp [hD.ne']; ring
  dsimp [u, u']
  rw [Real.div_rpow (mul_nonneg h1x.le hs.1.le) hD.le, Real.mul_rpow h1x.le hs.1.le, h1u,
    ← rpow_sub_one_mul h1x, Real.rpow_neg hD.le, ← rpow_sub_one_mul hD]
  field_simp [hx.1.ne', hD.ne', (Real.rpow_pos_of_pos hD (a - 1)).ne']

private theorem integral_singular_euler_piece {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    (1 - x) ^ a * (∫ s in (0 : ℝ)..1, s ^ (a - 1) * (x + (1 - x) * s) ^ (-a)) =
      (∫ w in (0 : ℝ)..(1 - x), (w ^ (a - 1) - 1) / (1 - w)) - Real.log x := by
  have hint1 : IntervalIntegrable (fun w ↦ (w ^ (a - 1) - 1) / (1 - w)) volume 0 (1 - x) :=
    (Real.intervalIntegrable_rpow_sub_one_div_one_sub ha.1).mono_set <| by
      rw [uIcc_of_le (sub_nonneg.mpr hx.2.le), uIcc_of_le zero_le_one]
      exact Icc_subset_Icc_right (by linarith [hx.1])
  have hint2 : IntervalIntegrable (fun w : ℝ ↦ (1 - w)⁻¹) volume 0 (1 - x) :=
    (ContinuousOn.inv₀ (by fun_prop) fun w hw ↦ by
      rw [uIcc_of_le (sub_nonneg.mpr hx.2.le)] at hw; linarith [hw.2, hx.1]).intervalIntegrable
  have hlog : ∫ w in (0 : ℝ)..(1 - x), (1 - w)⁻¹ = -Real.log x := by
    have h := intervalIntegral.integral_comp_sub_left (fun u : ℝ ↦ u⁻¹) 1 (a := 0) (b := 1 - x)
    simp only [sub_sub_cancel, sub_zero] at h
    rw [h, integral_inv_of_pos hx.1 zero_lt_one, one_div, Real.log_inv]
  rw [integral_singular_euler_sub hx,
    intervalIntegral.integral_congr (fun _ _ ↦ by ring :
      ∀ w ∈ uIcc 0 (1 - x), w ^ (a - 1) / (1 - w) = (w ^ (a - 1) - 1) / (1 - w) + (1 - w)⁻¹),
    intervalIntegral.integral_add hint1 hint2, hlog, ← sub_eq_add_neg]

private theorem intervalIntegrable_swappedEuler {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable
      (fun s ↦ (1 - s) ^ (a - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a)) volume 0 1 ∧
    IntervalIntegrable (fun s ↦ s ^ (a - 1) * (x + (1 - x) * s) ^ (-a)) volume 0 1 := by
  have hcont : ContinuousOn (fun s : ℝ ↦ (x + (1 - x) * s) ^ (-a)) (uIcc 0 1) :=
    ContinuousOn.rpow_const (by fun_prop) fun s hs ↦ Or.inl <| by
      rw [uIcc_of_le zero_le_one] at hs; nlinarith [hx.1, hx.2, hs.1, hs.2]
  exact ⟨((intervalIntegrable_rpow_mul_one_sub_rpow ha.1 ha.1 ⟨le_rfl, zero_le_one⟩
      ⟨zero_le_one, le_rfl⟩).congr fun s _ ↦ by ring).mul_continuousOn hcont,
    (intervalIntegral.intervalIntegrable_rpow' (by linarith [ha.1])).mul_continuousOn hcont⟩

private theorem eulerZeroBalanced_eq_split {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    eulerZeroBalanced a x =
      (∫ s in (0 : ℝ)..1, ((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a)) +
        (1 - x) ^ (-a) * ((∫ w in (0 : ℝ)..(1 - x), (w ^ (a - 1) - 1) / (1 - w)) - Real.log x) := by
  have hswap : eulerZeroBalanced a x =
      ∫ s in (0 : ℝ)..1, (1 - s) ^ (a - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a) := by
    have h := intervalIntegral.integral_comp_sub_left
      (fun t ↦ t ^ (a - 1) * (1 - t) ^ (a - 1) * (1 - (1 - x) * t) ^ (-a)) 1 (a := 0) (b := 1)
    simp only [sub_self, sub_zero] at h; rw [eulerZeroBalanced, ← h]
    exact intervalIntegral.integral_congr fun s _ ↦ by
      rw [sub_sub_cancel, (by ring : 1 - (1 - x) * (1 - s) = x + (1 - x) * s)]
  obtain ⟨htot, hsing⟩ := intervalIntegrable_swappedEuler ha hx
  have hdiff : ∫ s in (0 : ℝ)..1,
      ((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a) =
      eulerZeroBalanced a x - ∫ s in (0 : ℝ)..1, s ^ (a - 1) * (x + (1 - x) * s) ^ (-a) := by
    rw [hswap, ← intervalIntegral.integral_sub htot hsing]
    exact intervalIntegral.integral_congr fun _ _ ↦ by ring
  have hsing_val : ∫ s in (0 : ℝ)..1, s ^ (a - 1) * (x + (1 - x) * s) ^ (-a) =
      (1 - x) ^ (-a) * ((∫ w in (0 : ℝ)..(1 - x), (w ^ (a - 1) - 1) / (1 - w)) - Real.log x) := by
    rw [← integral_singular_euler_piece ha hx, ← mul_assoc, ← Real.rpow_add (sub_pos.mpr hx.2),
      neg_add_cancel, Real.rpow_zero, one_mul]
  linarith

private theorem smooth_euler_integrand_le {a x s : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) (hs : s ∈ Ioo (0 : ℝ) 1) :
    ‖((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a)‖ ≤
      2 ^ a * (1 - s) ^ (a - 1) := by
  have h1s_pos : 0 < 1 - s := sub_pos.mpr hs.2
  have h1s_nn : 0 ≤ (1 - s) ^ (a - 1) - 1 := sub_nonneg.mpr <| by
    simpa using Real.rpow_le_rpow_of_exponent_ge h1s_pos (by linarith [hs.1])
      (by linarith [ha.2] : a - 1 ≤ 0)
  have hdiv_le : ((1 - s) ^ (a - 1) - 1) / s ≤ (1 - s) ^ (a - 1) := by
    rw [div_le_iff₀ hs.1]
    have hpow : (1 - s) ^ (a - 1) - (1 - s) ^ (a - 1) * s = (1 - s) ^ a := by
      rw [← mul_one_sub, rpow_sub_one_mul h1s_pos]
    linarith [Real.rpow_le_one h1s_pos.le (by linarith [hs.1]) ha.1.le]
  have hD_rpow : (x + (1 - x) * s) ^ (-a) ≤ 2 ^ a * s ^ (-a) :=
    (Real.rpow_le_rpow_of_nonpos (half_pos hs.1) (by nlinarith [hx.1, hx.2, hs.1])
      (by linarith [ha.1])).trans_eq <| by
        rw [div_eq_mul_inv, Real.mul_rpow hs.1.le (by norm_num),
          Real.inv_rpow zero_le_two, ← Real.rpow_neg zero_le_two, neg_neg, mul_comm]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg h1s_nn
    (Real.rpow_nonneg hs.1.le _)) (Real.rpow_nonneg (by nlinarith [hx.1, hx.2, hs.1]) _))]
  have hs_comb : s ^ (a - 1) * s ^ (-a) = s⁻¹ := by
    rw [← Real.rpow_add hs.1, (by ring : a - 1 + -a = -1), Real.rpow_neg_one]
  exact ((mul_le_mul_of_nonneg_left hD_rpow
      (mul_nonneg h1s_nn (Real.rpow_nonneg hs.1.le _))).trans_eq
    (by rw [div_eq_mul_inv, ← hs_comb]; ring :
      _ = 2 ^ a * (((1 - s) ^ (a - 1) - 1) / s))).trans
    (mul_le_mul_of_nonneg_left hdiv_le (by positivity))

private theorem tendsto_smooth_euler_piece {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x ↦ ∫ s in (0 : ℝ)..1,
      ((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a))
      (𝓝[>] 0) (𝓝 (Real.digamma 1 - Real.digamma a)) := by
  have hb_int : IntervalIntegrable (fun s : ℝ ↦ 2 ^ a * (1 - s) ^ (a - 1)) volume 0 1 :=
    ((intervalIntegrable_rpow_mul_one_sub_rpow (a := 1) (b := a) zero_lt_one ha.1
      ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩).const_mul (2 ^ a)).congr fun _ _ ↦ by simp
  have hdct := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0 : ℝ))
    (F := fun x s ↦ ((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a))
    (f := fun s ↦ ((1 - s) ^ (a - 1) - 1) / s) (fun s ↦ 2 ^ a * (1 - s) ^ (a - 1)) ?_ ?_ hb_int ?_
  · have h := intervalIntegral.integral_comp_sub_left
      (fun w ↦ (w ^ (a - 1) - 1) / (1 - w)) 1 (a := 0) (b := 1)
    simp only [sub_self, sub_zero, sub_sub_cancel] at h
    rwa [h.trans (Real.integral_rpow_sub_one_div_one_sub ha.1)] at hdct
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
    obtain ⟨h1, h2⟩ := intervalIntegrable_swappedEuler ha ⟨hx.1, by linarith [hx.2]⟩
    exact (intervalIntegrable_iff.mp ((h1.sub h2).congr fun _ _ ↦ by ring)).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
    filter_upwards [Measure.ae_ne volume (1 : ℝ)] with s hs1 hs
    rw [uIoc_of_le zero_le_one] at hs
    exact smooth_euler_integrand_le ha hx ⟨hs.1, lt_of_le_of_ne hs.2 hs1⟩
  · refine Eventually.of_forall fun s hs ↦ ?_
    rw [uIoc_of_le zero_le_one] at hs
    have hlim : Tendsto
        (fun x : ℝ ↦ ((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a))
        (𝓝[>] 0) (𝓝 (((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (0 + (1 - 0) * s) ^ (-a))) :=
      ((continuousAt_const.mul (ContinuousAt.rpow_const (by fun_prop)
        (Or.inl (by simp [hs.1.ne'])))).continuousWithinAt (s := Ioi (0 : ℝ))).tendsto
    rwa [(by rw [zero_add, sub_zero, one_mul, mul_assoc, ← Real.rpow_add hs.1,
        (by ring : a - 1 + -a = -1), Real.rpow_neg_one, div_eq_mul_inv] :
      ((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (0 + (1 - 0) * s) ^ (-a) =
        ((1 - s) ^ (a - 1) - 1) / s)] at hlim

private theorem tendsto_eulerZeroBalanced_add_log {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x ↦ eulerZeroBalanced a x + Real.log x) (𝓝[>] 0)
      (𝓝 (2 * (Real.digamma 1 - Real.digamma a))) := by
  have h1x_lim : Tendsto (fun x : ℝ ↦ (1 - x) ^ (-a)) (𝓝[>] 0) (𝓝 1) := by
    simpa using ((ContinuousAt.rpow_const (by fun_prop)
      (Or.inl (by norm_num : (1 : ℝ) - 0 ≠ 0))).continuousWithinAt (s := Ioi (0 : ℝ))).tendsto
  have hprim : Tendsto (fun x : ℝ ↦ ∫ w in (0 : ℝ)..(1 - x), (w ^ (a - 1) - 1) / (1 - w))
      (𝓝[>] 0) (𝓝 (Real.digamma 1 - Real.digamma a)) := by
    have hc := intervalIntegral.continuousOn_primitive_interval'
      (Real.intervalIntegrable_rpow_sub_one_div_one_sub ha.1)
      (left_mem_uIcc (a := (0 : ℝ)) (b := 1))
    rw [uIcc_of_le zero_le_one] at hc
    have hcomp := (hc 1 ⟨zero_le_one, le_rfl⟩).tendsto.comp <|
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (by simpa using ((by fun_prop : Continuous fun x : ℝ ↦ 1 - x).continuousWithinAt
          (x := 0) (s := Ioi 0)).tendsto)
        (by filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
            exact ⟨by linarith [hx.2], by linarith [hx.1]⟩)
    rwa [Real.integral_rpow_sub_one_div_one_sub ha.1] at hcomp
  have hcomb := ((tendsto_smooth_euler_piece ha).add (h1x_lim.mul hprim)).sub <| by
    simpa using Real.tendsto_sub_mul_log_nhdsGT_zero (f := fun x : ℝ ↦ (1 - x) ^ (-a))
      (((Real.hasDerivAt_rpow_const (p := -a) (Or.inl (by norm_num))).comp 0
        ((hasDerivAt_id 0).const_sub 1)).differentiableAt)
  rw [one_mul, sub_zero, ← two_mul] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
  rw [eulerZeroBalanced_eq_split ha hx]; ring

private theorem tendsto_realU2_add_log {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x ↦ realU2 a x + Real.log x) (𝓝[>] 0)
      (𝓝 (2 * (Real.digamma 1 - Real.digamma a))) := by
  have hv_0 : realV a 0 = 2 * (Real.digamma 1 - Real.digamma a) := by
    simp [realV, FormalMultilinearSeries.ofScalarsSum_zero, realDigammaCoeff, realDigammaDiff,
      ordinaryHypergeometricCoefficient]
  have hv_lim : Tendsto (realV a) (𝓝[>] 0) (𝓝 (2 * (Real.digamma 1 - Real.digamma a))) :=
    hv_0 ▸ ((hasFPowerSeriesOnBall_realV ha).analyticAt_of_mem
      (Metric.mem_eball_self zero_lt_one)).continuousAt.continuousWithinAt.tendsto
  have hu1_diff : DifferentiableAt ℝ (₂F₁ a a 1 : ℝ → ℝ) 0 :=
    ((hasFPowerSeriesOnBall_ordinaryHypergeometric_real a a 1).analyticAt_of_mem
      (Metric.mem_eball_self zero_lt_one)).differentiableAt
  have hsub := hv_lim.sub <| by
    simpa [ordinaryHypergeometric_zero] using Real.tendsto_sub_mul_log_nhdsGT_zero hu1_diff
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x _; dsimp [realU2]; ring

/-! ### Wronskian constancy and uniqueness on `(0, 1)` -/

private noncomputable def realDiff (a x : ℝ) : ℝ := eulerZeroBalanced a x - realU2 a x
private noncomputable def realWronskian (a x : ℝ) : ℝ :=
  ₂F₁ a a 1 x * (x * (1 - x) ^ (2 * a) * deriv (realDiff a) x) -
    (x * (1 - x) ^ (2 * a) * deriv (₂F₁ a a 1) x) * realDiff a x

private theorem realU1_bounds {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    (∀ {x : ℝ}, x ∈ Ioo (0 : ℝ) 1 → 1 ≤ ₂F₁ a a 1 x) ∧
    (∀ {x : ℝ}, x ∈ Ioc (0 : ℝ) (1 / 2) → ₂F₁ a a 1 x ≤ 2) := by
  have hx_sum {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) :
      HasSum (fun k : ℕ ↦ ordinaryHypergeometricCoefficient a a 1 k * x ^ k) (₂F₁ a a 1 x) := by
    have hxb : x ∈ Metric.eball (0 : ℝ) 1 := by
      rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one,
        Real.norm_of_nonneg hx0]
      exact hx1
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using
      (hasFPowerSeriesOnBall_ordinaryHypergeometric_real a a 1).hasSum hxb
  refine ⟨fun {x} hx ↦ ?_, fun {x} hx ↦ ?_⟩
  · have hs := hx_sum hx.1.le hx.2
    rw [← hs.tsum_eq]
    simpa [ordinaryHypergeometricCoefficient] using hs.summable.sum_le_tsum ({0} : Finset ℕ)
      fun k _ ↦ mul_nonneg (realCoeff_bounds ha k).1 (pow_nonneg hx.1.le k)
  · have hgeom : HasSum (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k) 2 := by
      have h := hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
      norm_num at h; exact h
    have hs := hx_sum hx.1.le (by linarith [hx.2])
    rw [← hs.tsum_eq, ← hgeom.tsum_eq]
    refine hs.summable.tsum_le_tsum (fun k ↦ ?_) hgeom.summable
    have hck := (abs_of_nonneg (realCoeff_bounds ha k).1) ▸ (realCoeff_bounds ha k).2
    exact (mul_le_mul hck (pow_le_pow_left₀ hx.1.le hx.2 k)
      (pow_nonneg hx.1.le k) zero_le_one).trans_eq (one_mul _)

private theorem differentiableAt_realParts {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (eulerZeroBalanced a) x ∧ DifferentiableAt ℝ (₂F₁ a a 1 : ℝ → ℝ) x ∧
    DifferentiableAt ℝ (realU2 a) x ∧ DifferentiableAt ℝ (realDiff a) x := by
  have hx_e : x ∈ Metric.eball (0 : ℝ) 1 := by
    rw [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one, Real.norm_eq_abs,
      abs_lt]
    exact ⟨by linarith [hx.1], hx.2⟩
  have hdE := (differentiableAt_and_sturmLiouville_eulerZeroBalanced ha hx).1
  have hdu1 := ((hasFPowerSeriesOnBall_ordinaryHypergeometric_real a a 1).analyticAt_of_mem
    hx_e).differentiableAt
  have hdv := ((hasFPowerSeriesOnBall_realV ha).analyticAt_of_mem hx_e).differentiableAt
  have hdu2 : DifferentiableAt ℝ (realU2 a) x :=
    ((Real.differentiableAt_log hx.1.ne').neg.mul hdu1).add hdv
  exact ⟨hdE, hdu1, hdu2, hdE.sub hdu2⟩

private theorem hasDerivAt_realWronskian {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (realWronskian a) 0 x := by
  obtain ⟨_, hdu1, _, hdD⟩ := differentiableAt_realParts ha hx
  have hpD : HasDerivAt (fun y ↦ y * (1 - y) ^ (2 * a) * deriv (realDiff a) y)
      (a ^ 2 * (1 - x) ^ (2 * a - 1) * realDiff a x) x := by
    refine ((differentiableAt_and_sturmLiouville_eulerZeroBalanced ha hx).2.sub
      (hasDerivAt_sturmLiouville_realU2 ha hx)).congr_of_eventuallyEq ?_ |>.congr_deriv
      (by dsimp [realDiff]; ring)
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    obtain ⟨hdEy, _, hdu2y, _⟩ := differentiableAt_realParts ha hy
    have hfn : realDiff a = fun y ↦ eulerZeroBalanced a y - realU2 a y := rfl
    rw [hfn, deriv_fun_sub hdEy hdu2y]; simp only [Pi.sub_apply]; ring
  exact ((hdu1.hasDerivAt.mul hpD).sub
    ((hasDerivAt_sturmLiouville_realU1 hx).mul hdD.hasDerivAt)).congr_deriv (by ring)

private theorem realWronskian_eq_const {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    realWronskian a x = realWronskian a (1 / 2) :=
  isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun y hy ↦ (hasDerivAt_realWronskian ha hy).differentiableAt.differentiableWithinAt)
    (fun y hy ↦ (hasDerivAt_realWronskian ha hy).deriv) hx ⟨by norm_num, by norm_num⟩

private theorem hasDerivAt_realDiff_div_realU1 {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y ↦ realDiff a y / ₂F₁ a a 1 y)
      (realWronskian a (1 / 2) / (x * (1 - x) ^ (2 * a) * (₂F₁ a a 1 x) ^ 2)) x := by
  obtain ⟨_, hdu1, _, hdD⟩ := differentiableAt_realParts ha hx
  have hu1_pos : 0 < ₂F₁ a a 1 x := lt_of_lt_of_le zero_lt_one ((realU1_bounds ha).1 hx)
  refine (hdD.hasDerivAt.div hdu1.hasDerivAt hu1_pos.ne').congr_deriv ?_
  rw [← realWronskian_eq_const ha hx]; dsimp [realWronskian]
  field_simp [hu1_pos.ne', hx.1.ne', (Real.rpow_pos_of_pos (sub_pos.mpr hx.2) (2 * a)).ne']

private theorem tendsto_realDiff_div_realU1 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x ↦ realDiff a x / ₂F₁ a a 1 x) (𝓝[>] 0) (𝓝 0) := by
  have hD : Tendsto (realDiff a) (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_eulerZeroBalanced_add_log ha).sub (tendsto_realU2_add_log ha)
    rw [sub_self] at h; exact h.congr fun _ ↦ by dsimp [realDiff]; ring
  have hu1_lim : Tendsto (₂F₁ a a 1 : ℝ → ℝ) (𝓝[>] 0) (𝓝 1) := by
    simpa [ordinaryHypergeometric_zero] using
      ((hasFPowerSeriesOnBall_ordinaryHypergeometric_real a a 1).analyticAt_of_mem
        (Metric.mem_eball_self zero_lt_one)).continuousAt.continuousWithinAt.tendsto
  exact (zero_div (1 : ℝ) ▸ hD.div hu1_lim one_ne_zero).congr fun _ ↦ Pi.div_apply _ _ _

private theorem realWronskian_half_eq_zero {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    realWronskian a (1 / 2) = 0 := by
  by_contra hC
  let C := realWronskian a (1 / 2)
  let g : ℝ → ℝ := fun y ↦ C * (realDiff a y / ₂F₁ a a 1 y) - (C ^ 2 / 4) * Real.log y
  have hdg (y : ℝ) (hy : y ∈ Ioc (0 : ℝ) (1 / 2)) :
      HasDerivAt g (C ^ 2 / (y * (1 - y) ^ (2 * a) * (₂F₁ a a 1 y) ^ 2) - C ^ 2 / (4 * y)) y :=
    (((hasDerivAt_realDiff_div_realU1 ha ⟨hy.1, by linarith [hy.2]⟩).const_mul C).sub
      ((Real.hasDerivAt_log hy.1.ne').const_mul (C ^ 2 / 4))).congr_deriv (by ring)
  have hmono : MonotoneOn g (Ioc 0 (1 / 2)) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ioc 0 (1 / 2))
      (fun y hy ↦ (hdg y hy).continuousAt.continuousWithinAt)
      (fun y hy ↦ (hdg y (interior_subset hy)).hasDerivWithinAt) fun y hy ↦ ?_
    have hy' := interior_subset hy
    have hy_oo : y ∈ Ioo (0 : ℝ) 1 := ⟨hy'.1, by linarith [hy'.2]⟩
    have h1y := Real.rpow_le_one (by linarith [hy'.2] : 0 ≤ 1 - y) (by linarith [hy'.1])
      (by linarith [ha.1] : 0 ≤ 2 * a)
    exact sub_nonneg.mpr <| div_le_div_of_nonneg_left (sq_nonneg C)
      (mul_pos (mul_pos hy'.1 (Real.rpow_pos_of_pos (sub_pos.mpr hy_oo.2) (2 * a)))
        (pow_pos (lt_of_lt_of_le zero_lt_one ((realU1_bounds ha).1 hy_oo)) 2)) <|
      (mul_le_mul (mul_le_of_le_one_right hy'.1.le h1y)
        (by nlinarith [(realU1_bounds ha).1 hy_oo, (realU1_bounds ha).2 hy'] :
          (₂F₁ a a 1 y) ^ 2 ≤ 4)
        (sq_nonneg _) hy'.1.le).trans_eq (by ring)
  have hg_top : Tendsto g (𝓝[>] 0) atTop :=
    (((by simpa using (tendsto_realDiff_div_realU1 ha).const_mul C :
        Tendsto (fun y ↦ C * (realDiff a y / ₂F₁ a a 1 y)) (𝓝[>] 0) (𝓝 0)).add_atTop
      (Tendsto.const_mul_atTop (div_pos (sq_pos_of_ne_zero hC) (by norm_num : (0 : ℝ) < 4))
        (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)))).congr
      fun _ ↦ by dsimp [g]; ring
  obtain ⟨x, hgx, hx_mem⟩ := ((hg_top.eventually (eventually_gt_atTop (g (1 / 2)))).and
    (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2))).exists
  exact not_le_of_gt hgx (hmono ⟨hx_mem.1, hx_mem.2.le⟩ ⟨by norm_num, le_rfl⟩ hx_mem.2.le)

private theorem eulerZeroBalanced_eq_realU2 {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    eulerZeroBalanced a x = realU2 a x := by
  let Q : ℝ → ℝ := fun y ↦ realDiff a y / ₂F₁ a a 1 y
  have hQ_deriv (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1) : HasDerivAt Q 0 y := by
    have h0 := hasDerivAt_realDiff_div_realU1 ha hy
    rw [realWronskian_half_eq_zero ha, zero_div] at h0; exact h0
  have hQ_const (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1) : Q y = Q (1 / 2) :=
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun z hz ↦ (hQ_deriv z hz).differentiableAt.differentiableWithinAt)
      (fun z hz ↦ (hQ_deriv z hz).deriv) hy ⟨by norm_num, by norm_num⟩
  have hQ_lim : Tendsto Q (𝓝[>] 0) (𝓝 (Q (1 / 2))) := tendsto_const_nhds.congr' <| by
    filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with y hy using (hQ_const y hy).symm
  exact sub_eq_zero.mp ((div_eq_zero_iff.mp ((hQ_const x hx).trans
    (tendsto_nhds_unique hQ_lim (tendsto_realDiff_div_realU1 ha)))).resolve_right
    (lt_of_lt_of_le zero_lt_one ((realU1_bounds ha).1 hx)).ne')

/-! ### Complex analytic continuation and the connection theorem -/

private theorem ordinaryHypergeometric_ofReal_eq_zeroBalancedSeries {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ordinaryHypergeometric (a : ℂ) (a : ℂ) (2 * (a : ℂ)) (1 - (x : ℂ)) =
      zeroBalancedSeries (a : ℂ) (x : ℂ) := by
  have hreal := (ordinaryHypergeometric_eq_mul_eulerZeroBalanced ha.1 hx).trans
    (congrArg (Real.Gamma (2 * a) / Real.Gamma a ^ 2 * ·) (eulerZeroBalanced_eq_realU2 ha hx))
  have hlhs : Complex.ofReal (₂F₁ a a (2 * a) (1 - x)) =
      ordinaryHypergeometric (a : ℂ) (a : ℂ) (2 * (a : ℂ)) (1 - (x : ℂ)) := by
    simpa [Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_mul] using
      ofReal_ordinaryHypergeometric a a (2 * a) (1 - x)
  have hp (u : ℝ) (k : ℕ) :
      (ascPochhammer ℂ k).eval (u : ℂ) = Complex.ofReal ((ascPochhammer ℝ k).eval u) := by
    simpa [ascPochhammer_map] using
      Polynomial.eval_map_apply (p := ascPochhammer ℝ k) (f := Complex.ofRealHom) u
  have hx_norm : ‖(x : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hx.1.le]; exact hx.2
  refine hlhs.symm.trans ((congrArg Complex.ofReal hreal).trans ?_)
  rw [zeroBalancedSeries_eq_log_mul_add (a : ℂ) hx_norm,
    (by simpa using Complex.Gamma_ofReal (2 * a) :
      Complex.Gamma (2 * (a : ℂ)) = Complex.ofReal (Real.Gamma (2 * a))),
    Complex.Gamma_ofReal a, (Complex.ofReal_log hx.1.le).symm]
  simp only [realU2, realV, ordinaryHypergeometric_eq_ofScalarsSum,
    FormalMultilinearSeries.ofScalarsSum_eq_tsum, smul_eq_mul, realDigammaCoeff, realDigammaDiff,
    ordinaryHypergeometricCoefficient_one_eq, Complex.ofReal_mul, Complex.ofReal_div,
    Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_neg, Complex.ofReal_sub,
    Complex.ofReal_tsum, Complex.ofReal_ofNat]
  congr 1; congr 1
  · congr 1; exact tsum_congr fun k ↦ by simp [hp, div_pow]
  · refine tsum_congr fun k ↦ ?_
    rw [(by simpa using Complex.digamma_ofReal (x := (k : ℝ) + 1) :
        Complex.digamma ((k : ℂ) + 1) = Complex.ofReal (Real.digamma (k + 1))),
      (by simpa using Complex.digamma_ofReal (x := (k : ℝ) + a) :
        Complex.digamma ((k : ℂ) + a) = Complex.ofReal (Real.digamma (k + a)))]
    simp [hp, div_pow]

/-- On the overlap lens `‖x‖ < 1`, `‖1 - x‖ < 1`, the zero-balanced Gauss hypergeometric function
`₂F₁(a, a; 2a; 1 - x)` agrees with `zeroBalancedSeries a x` whenever `2a` is not a nonpositive
integer. -/
theorem ordinaryHypergeometric_one_sub_eq_zeroBalancedSeries {a x : ℂ}
    (ha : ∀ n : ℕ, 2 * a ≠ -(n : ℂ)) (hx0 : ‖x‖ < 1) (hx1 : ‖1 - x‖ < 1) :
    ordinaryHypergeometric a a (2 * a) (1 - x) = zeroBalancedSeries a x := by
  let L : Set ℂ := ball 0 1 ∩ ball 1 1
  have hL_conn : IsPreconnected L :=
    ((convex_ball (0 : ℂ) 1).inter (convex_ball (1 : ℂ) 1)).isPreconnected
  have hhalf_L : (1 / 2 : ℂ) ∈ L := by
    simp only [L, mem_inter_iff, mem_ball, dist_eq_norm]; norm_num
  have hL_slit : L ⊆ ball 0 1 ∩ Complex.slitPlane := fun z hz ↦ ⟨hz.1, by
    rw [Complex.mem_slitPlane_iff]
    refine Or.inl ?_
    have h1 : ‖1 - z‖ < 1 := by simpa [mem_ball, dist_eq_norm, norm_sub_rev] using hz.2
    have hre : 1 - z.re ≤ ‖1 - z‖ := by simpa using Complex.re_le_norm (1 - z)
    linarith⟩
  have hfreq : ∃ᶠ z : ℂ in 𝓝[≠] (1 / 2 : ℂ), ∃ t ∈ Ioo (0 : ℝ) 1, (t : ℂ) = z := by
    simpa using accPt_iff_frequently_nhdsNE.mp
      (Complex.accPt_ofReal_Ioo (by norm_num : (1 / 2 : ℝ) ∈ Ioo 0 1))
  have hstage1 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
      ordinaryHypergeometric (t : ℂ) (t : ℂ) (2 * (t : ℂ)) (1 - x) =
        zeroBalancedSeries (t : ℂ) x :=
    AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
      (f := fun z ↦ ordinaryHypergeometric (t : ℂ) (t : ℂ) (2 * (t : ℂ)) (1 - z))
      (fun z hz ↦ (analyticOnNhd_ordinaryHypergeometric ℂ (t : ℂ) (t : ℂ) (2 * (t : ℂ)) (1 - z)
        (by simpa [mem_ball, dist_eq_norm, norm_sub_rev] using hz.2)).comp
        (analyticAt_const.sub analyticAt_id))
      ((analyticOnNhd_zeroBalancedSeries (t : ℂ)).mono hL_slit) hL_conn hhalf_L
      (hfreq.mono fun _ ⟨_, hs, hsz⟩ ↦
        hsz ▸ ordinaryHypergeometric_ofReal_eq_zeroBalancedSeries ht hs)
      ⟨by simpa using hx0, by rwa [mem_ball, dist_eq_norm, norm_sub_rev]⟩
  have hhalf_Ω : (1 / 2 : ℂ) ∈ {b : ℂ | ∀ n : ℕ, 2 * b ≠ -(n : ℂ)} := fun n hn ↦ by
    have hr := congrArg Complex.re hn; norm_num at hr; linarith [n.cast_nonneg (α := ℝ)]
  have hΩ_conn : IsPreconnected {b : ℂ | ∀ n : ℕ, 2 * b ≠ -(n : ℂ)} := by
    have hpre : {b : ℂ | ∀ n : ℕ, 2 * b ≠ -(n : ℂ)} =
        Homeomorph.mulLeft₀ (2 : ℂ) two_ne_zero ⁻¹' {s : ℂ | ∀ n : ℕ, s ≠ -(n : ℂ)} := by
      ext b; simp
    rw [hpre]
    exact (Homeomorph.mulLeft₀ (2 : ℂ) two_ne_zero).isPreconnected_preimage.mpr
      Complex.isPreconnected_ne_neg_natCast
  exact AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq
    (f := fun b : ℂ ↦ ₂F₁ b b (2 * b) (1 - x))
    (fun _ hb ↦ analyticAt_id.ordinaryHypergeometric analyticAt_id
      (analyticAt_const.mul analyticAt_id) analyticAt_const hb hx1)
    (analyticOnNhd_zeroBalancedSeries_left hx0) hΩ_conn hhalf_Ω
    (hfreq.mono fun _ ⟨_, ht, htb⟩ ↦ htb ▸ hstage1 ht) ha

/-- The zero-balanced connection formula: when `2a` is not a nonpositive integer, the series is
analytic on the slit unit disc `Metric.ball 0 1 ∩ Complex.slitPlane` and equals the native
`₂F₁(a, a; 2a; 1 - x)` on the lens `‖x‖ < 1`, `‖1 - x‖ < 1`; by the identity theorem it is the
continuation of the native series across the slit disc (CDT Lemma 5.1.20, p. 672). -/
theorem zero_balanced_connection (a : ℂ) (ha : ∀ n : ℕ, 2 * a ≠ -(n : ℂ)) :
    AnalyticOnNhd ℂ (zeroBalancedSeries a) (ball 0 1 ∩ Complex.slitPlane) ∧
    ∀ x : ℂ, ‖x‖ < 1 → ‖1 - x‖ < 1 →
      ordinaryHypergeometric a a (2 * a) (1 - x) = zeroBalancedSeries a x :=
  ⟨analyticOnNhd_zeroBalancedSeries a,
    fun _ hx0 hx1 ↦ ordinaryHypergeometric_one_sub_eq_zeroBalancedSeries ha hx0 hx1⟩

end TauCeti
