/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.ZeroBalanced.Basic
public import TauCeti.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.Analysis.SpecialFunctions.Beta
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.GaussSeries
import TauCeti.Analysis.SpecialFunctions.Pow.Integral

/-!
# The zero-balanced hypergeometric connection formula

When `2a` is not a nonpositive integer, the zero-balanced Gauss hypergeometric function
`₂F₁(a, a; 2a; 1 - x)` agrees on the overlap lens `‖x‖ < 1`, `‖1 - x‖ < 1` with the logarithmic
series `TauCeti.zeroBalancedSeries a x` defined in
`TauCeti.Analysis.SpecialFunctions.Hypergeometric.ZeroBalanced.Basic`. Since
`zeroBalancedSeries a` is complex analytic on `Metric.ball 0 1 \ {x | x.re ≤ 0 ∧ x.im = 0}`, the
identity theorem identifies it as the analytic continuation of `₂F₁(a, a; 2a; 1 - ·)` across the
slit unit disc.

For `a, x ∈ (0, 1)`, Euler's integral represents `₂F₁(a, a; 2a; 1 - x)` as `Γ(2a) / Γ(a)²` times
`∫ t in 0..1, t^(a - 1) (1 - t)^(a - 1) (1 - (1 - x) t)^(-a)`. Both this integral and the real
logarithmic series `-log x · u₁(a, x) + v(a, x)` satisfy the self-adjoint Sturm-Liouville equation
`(x (1 - x)^(2a) y')' = a² (1 - x)^(2a - 1) y` on `(0, 1)` and share the asymptotic
`-log x + 2(ψ(1) - ψ(a)) + o(1)` at `0⁺` via Gauss's digamma series. Wronskian constancy against
`u₁(a, ·)` equates them on `(0, 1)`, and two-stage analytic continuation in `x` and `a` completes
the complex identity.

## Main statements

* `TauCeti.ordinaryHypergeometric_one_sub_eq_zeroBalancedSeries`: equality on `‖x‖ < 1`,
  `‖1 - x‖ < 1` for `∀ n : ℕ, 2 * a ≠ -(n : ℂ)`.
* `TauCeti.zero_balanced_connection`: combined slit-disc analyticity and lens connection formula
  (CDT Lemma 5.1.20).

## References

* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. 38 (2025), Lemma 5.1.20 (p. 672).
* [NIST DLMF, equation 15.8.10](https://dlmf.nist.gov/15.8.E10) and
  [equation 15.6.1](https://dlmf.nist.gov/15.6.E1).
-/

public section

open Complex Filter MeasureTheory Metric Set
open scoped Nat Real Topology

namespace TauCeti

/-! ### Parameter analyticity of the native zero-balanced hypergeometric series -/

private theorem ascPochhammer_eval_add (n m : ℕ) (w : ℂ) :
    (ascPochhammer ℂ (n + m)).eval w =
      (ascPochhammer ℂ n).eval w * (ascPochhammer ℂ m).eval (w + n) := by
  rw [← ascPochhammer_mul ℂ n m, Polynomial.eval_mul, Polynomial.eval_comp, Polynomial.eval_add,
    Polynomial.eval_X, Polynomial.eval_natCast]

private theorem multichoose_nonneg_of_pos {S : ℝ} (hS : 0 < S) (k : ℕ) :
    0 ≤ Ring.multichoose S k := by
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer S k
  rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at h
  exact nonneg_of_mul_nonneg_right (h ▸ (ascPochhammer_pos k S hS).le) (by positivity)

private theorem norm_ascPochhammer_div_factorial_le' {a : ℂ} {R : ℝ}
    (ha : ‖a‖ ≤ R) (hR : 0 ≤ R) (k : ℕ) :
    ‖(ascPochhammer ℂ k).eval a / (k ! : ℂ)‖ ≤ Ring.multichoose R k := by
  have hnum : ‖(ascPochhammer ℂ k).eval a‖ ≤ (ascPochhammer ℝ k).eval R ∧
      0 ≤ (ascPochhammer ℝ k).eval R := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, norm_mul]
      have hstep : ‖a + (k : ℂ)‖ ≤ R + (k : ℝ) :=
        (norm_add_le a k).trans (by simpa [Complex.norm_natCast] using add_le_add_right ha (k : ℝ))
      exact ⟨mul_le_mul ih.1 hstep (norm_nonneg _) ih.2,
        mul_nonneg ih.2 (add_nonneg hR (Nat.cast_nonneg k))⟩
  have hc : Ring.multichoose R k = (ascPochhammer ℝ k).eval R / k ! := by
    have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer R k
    rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at h
    rw [← h]; field_simp
  rw [hc, norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right hnum.1 (Nat.cast_nonneg _)

private theorem summable_multichoose_sq_mul_pow' {R r : ℝ}
    (hR : 0 < R) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun k : ℕ ↦ (Ring.multichoose R k) ^ 2 * r ^ k := by
  have hs : Summable fun k : ℕ ↦ Ring.multichoose R k * (Real.sqrt r) ^ k :=
    (summable_multichoose_mul_geometric_iff_norm_lt_one (𝕂 := ℝ) hR).mpr <| by
      rw [Real.norm_of_nonneg (Real.sqrt_nonneg r)]
      nlinarith [Real.sqrt_nonneg r, Real.sq_sqrt hr0]
  refine hs.of_norm_bounded_eventually_nat ?_
  filter_upwards [hs.tendsto_atTop_zero.eventually (closedBall_mem_nhds 0 zero_lt_one)] with k hk
  have hu0 : 0 ≤ Ring.multichoose R k * (Real.sqrt r) ^ k :=
    mul_nonneg (multichoose_nonneg_of_pos hR k) (pow_nonneg (Real.sqrt_nonneg r) k)
  have hu1 : Ring.multichoose R k * (Real.sqrt r) ^ k ≤ 1 := by
    simpa [Real.norm_of_nonneg hu0] using mem_closedBall_zero_iff.mp hk
  have hsq : (Ring.multichoose R k * (Real.sqrt r) ^ k) ^ 2 =
      (Ring.multichoose R k) ^ 2 * r ^ k := by
    rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul, Real.sq_sqrt hr0]
  rw [Real.norm_of_nonneg (by positivity), ← hsq, sq]
  exact mul_le_of_le_one_right hu0 hu1

private theorem isOpen_two_mul_ne_neg_nat : IsOpen {a : ℂ | ∀ n : ℕ, 2 * a ≠ -(n : ℂ)} := by
  rw [Metric.isOpen_iff]; intro a ha
  let N := ⌈-2 * a.re⌉₊ + 1
  let S : Finset ℂ := (Finset.range N).image fun n : ℕ ↦ -(n : ℂ) / 2
  have haS : a ∉ (S : Set ℂ) := by
    simp only [Finset.coe_image, Finset.coe_range, mem_image, mem_Iio, not_exists, not_and, S]
    rintro n _ rfl; exact ha n (by ring)
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp S.finite_toSet.isClosed.isOpen_compl a haS
  refine ⟨min r (1 / 4), lt_min hr (by norm_num), fun w hw n hn ↦ ?_⟩
  rcases lt_or_ge n N with hnN | hnN
  · exact hball (Metric.ball_subset_ball (min_le_left _ _) hw)
      (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨n, Finset.mem_range.mpr hnN,
        by linear_combination -hn / 2⟩))
  · have hdist : ‖w - a‖ < 1 / 4 := (mem_ball_iff_norm.mp hw).trans_le (min_le_right _ _)
    have hwsub := (abs_le.mp (abs_re_le_norm (w - a))).1
    have hnN' : ((⌈-2 * a.re⌉₊ + 1 : ℕ) : ℝ) ≤ n := Nat.cast_le.mpr hnN
    push_cast at hnN'
    have hre := congrArg Complex.re hn
    simp only [sub_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero, neg_re, natCast_re]
      at hwsub hre
    linarith [Nat.le_ceil (-2 * a.re)]

private theorem factorial_le_norm_ascPochhammer_eval {a : ℂ} {R : ℝ} {M : ℕ}
    (ha : ‖a‖ ≤ R) (hM : 2 * R + 1 ≤ (M : ℝ)) (m : ℕ) :
    (m ! : ℝ) ≤ ‖(ascPochhammer ℂ m).eval (2 * a + M)‖ := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [ascPochhammer_succ_eval, norm_mul, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one, mul_comm ((m : ℝ) + 1)]
    have hare : -R ≤ a.re := (neg_le_neg ha).trans (abs_le.mp (abs_re_le_norm a)).1
    have hre := Complex.re_le_norm (2 * a + (M : ℂ) + (m : ℂ))
    simp only [add_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero, natCast_re] at hre
    exact mul_le_mul ih (by linarith) (by positivity) (norm_nonneg _)

private theorem multichoose_le_of_le {S : ℝ} (hS : 1 ≤ S) {m n : ℕ} (hmn : m ≤ n) :
    Ring.multichoose S m ≤ Ring.multichoose S n := by
  induction hmn with
  | refl => exact le_rfl
  | @step k _ ih =>
    have hpos := multichoose_nonneg_of_pos (S := S) (by linarith) k
    have h1 := Ring.factorial_nsmul_multichoose_eq_ascPochhammer S k
    have h2 := Ring.factorial_nsmul_multichoose_eq_ascPochhammer S (k + 1)
    rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at h1 h2
    rw [ascPochhammer_succ_eval, ← h1, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one] at h2
    have hstep : Ring.multichoose S k * ((k : ℝ) + 1) ≤
        Ring.multichoose S (k + 1) * ((k : ℝ) + 1) := by
      refine (mul_le_mul_of_nonneg_left (by linarith : (k : ℝ) + 1 ≤ S + k) hpos).trans_eq ?_
      exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr k.factorial_ne_zero) (by linear_combination -h2)
    exact ih.trans (le_of_mul_le_mul_right hstep (by positivity))

private noncomputable def zeroBalancedHyperTerm (a z : ℂ) (n : ℕ) : ℂ :=
  ((n !⁻¹ : ℂ) * (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval a *
    ((ascPochhammer ℂ n).eval (2 * a))⁻¹) * z ^ n

private theorem norm_zeroBalancedHyperTerm_le {a z : ℂ} {R δ : ℝ} {M m : ℕ}
    (hR : 1 ≤ R) (hδ : 0 < δ) (haR : ‖a‖ ≤ R) (hM : 2 * R + 1 ≤ (M : ℝ))
    (hmin : δ ≤ ‖(ascPochhammer ℂ M).eval (2 * a)‖) :
    ‖zeroBalancedHyperTerm a z (M + m)‖ ≤
      (Ring.multichoose R M * (M ! : ℝ) / δ) *
        ((Ring.multichoose (R + M) (M + m)) ^ 2 * ‖z‖ ^ (M + m)) := by
  let C := Ring.multichoose R M * (M ! : ℝ) / δ
  have hmcM : 0 ≤ Ring.multichoose R M := multichoose_nonneg_of_pos (by linarith) M
  have hCR : 0 ≤ C := div_nonneg (mul_nonneg hmcM (Nat.cast_nonneg _)) hδ.le
  have hmc : 0 ≤ Ring.multichoose (R + M) (M + m) :=
    multichoose_nonneg_of_pos (by positivity) (M + m)
  have hden : δ * (m ! : ℝ) ≤ ‖(ascPochhammer ℂ (M + m)).eval (2 * a)‖ := by
    rw [ascPochhammer_eval_add, norm_mul]
    exact mul_le_mul hmin (factorial_le_norm_ascPochhammer_eval haR hM m)
      (Nat.cast_nonneg _) (norm_nonneg _)
  have hf1 : ‖(ascPochhammer ℂ (M + m)).eval a / ((M + m)! : ℂ)‖ ≤
      Ring.multichoose (R + M) (M + m) :=
    norm_ascPochhammer_div_factorial_le' (haR.trans (le_add_of_nonneg_right (Nat.cast_nonneg M)))
      (by positivity) (M + m)
  have hf2 : ‖(ascPochhammer ℂ (M + m)).eval a / (ascPochhammer ℂ (M + m)).eval (2 * a)‖ ≤
      C * Ring.multichoose (R + M) (M + m) := by
    rw [ascPochhammer_eval_add M m a, norm_div, norm_mul,
      div_le_iff₀ (lt_of_lt_of_le (by positivity) hden)]
    have hPM : ‖(ascPochhammer ℂ M).eval a‖ ≤ Ring.multichoose R M * (M ! : ℝ) := by
      have h := norm_ascPochhammer_div_factorial_le' haR (by linarith) M
      rwa [norm_div, Complex.norm_natCast, div_le_iff₀ (by positivity)] at h
    have hPm : ‖(ascPochhammer ℂ m).eval (a + M)‖ ≤
        Ring.multichoose (R + M) (M + m) * (m ! : ℝ) := by
      have h := (norm_ascPochhammer_div_factorial_le' (a := a + M) (R := R + M)
        ((norm_add_le a M).trans (by simpa using add_le_add_right haR (M : ℝ)))
        (by positivity) m).trans (multichoose_le_of_le (by linarith [Nat.cast_nonneg (α := ℝ) M])
          (Nat.le_add_left m M))
      rwa [norm_div, Complex.norm_natCast, div_le_iff₀ (by positivity)] at h
    calc ‖(ascPochhammer ℂ M).eval a‖ * ‖(ascPochhammer ℂ m).eval (a + M)‖
        ≤ (Ring.multichoose R M * (M ! : ℝ)) * (Ring.multichoose (R + M) (M + m) * (m ! : ℝ)) :=
          mul_le_mul hPM hPm (norm_nonneg _) (mul_nonneg hmcM (Nat.cast_nonneg _))
      _ = C * Ring.multichoose (R + M) (M + m) * (δ * (m ! : ℝ)) := by
          dsimp [C]; field_simp [hδ.ne']
      _ ≤ C * Ring.multichoose (R + M) (M + m) * ‖(ascPochhammer ℂ (M + m)).eval (2 * a)‖ :=
          mul_le_mul_of_nonneg_left hden (mul_nonneg hCR hmc)
  rw [show zeroBalancedHyperTerm a z (M + m) =
    ((ascPochhammer ℂ (M + m)).eval a / ((M + m)! : ℂ)) *
      ((ascPochhammer ℂ (M + m)).eval a / (ascPochhammer ℂ (M + m)).eval (2 * a)) * z ^ (M + m) by
      dsimp [zeroBalancedHyperTerm]; ring, norm_mul, norm_mul, norm_pow]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul hf1 hf2 (norm_nonneg _) hmc)
    (pow_nonneg (norm_nonneg z) _)).trans_eq (by ring)

private theorem hasSumUniformlyOn_zeroBalancedHyperTerm {z : ℂ} (hz : ‖z‖ < 1) {K : Set ℂ}
    (hKU : K ⊆ {a : ℂ | ∀ n : ℕ, 2 * a ≠ -(n : ℂ)}) (hK : IsCompact K) :
    HasSumUniformlyOn (fun n a ↦ zeroBalancedHyperTerm a z n) (fun a ↦ ₂F₁ a a (2 * a) z) K := by
  have heq : ∀ a : ℂ, ₂F₁ a a (2 * a) z = ∑' n : ℕ, zeroBalancedHyperTerm a z n := fun a ↦ by
    simpa [ordinaryHypergeometric, zeroBalancedHyperTerm] using
      ordinaryHypergeometric_sum_eq a a (2 * a) z
  simp_rw [heq]
  rcases K.eq_empty_or_nonempty with rfl | hKne
  · exact hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr tendstoUniformlyOn_empty
  obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
  let R := max B 1
  let M : ℕ := 2 * ⌈R⌉₊ + 1
  obtain ⟨a₀, ha₀K, ha₀min⟩ := hK.exists_isMinOn hKne
    (((Polynomial.differentiable (ascPochhammer ℂ M)).comp
      (differentiable_id.const_mul 2)).continuous.norm.continuousOn)
  let δ := ‖(ascPochhammer ℂ M).eval (2 * a₀)‖
  have hδ : 0 < δ := norm_pos_iff.mpr fun h0 ↦ by
    obtain ⟨k, _, hk⟩ := (ascPochhammer_eval_eq_zero_iff M (2 * a₀)).mp h0
    exact hKU ha₀K k (neg_eq_iff_eq_neg.mp hk.symm)
  let C := Ring.multichoose R M * (M ! : ℝ) / δ
  apply HasSumUniformlyOn.of_norm_le_summable_eventually
    ((summable_multichoose_sq_mul_pow' (R := R + M) (by positivity) (norm_nonneg z) hz).mul_left C)
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [eventually_ge_atTop M] with n hn a haK
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact norm_zeroBalancedHyperTerm_le (le_max_right B 1) hδ ((hB a haK).trans (le_max_left _ _))
    (by dsimp [M]; push_cast; linarith [Nat.le_ceil R]) (isMinOn_iff.mp ha₀min a haK)

private theorem analyticOnNhd_ordinaryHypergeometric_param {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticOnNhd ℂ (fun a : ℂ ↦ ₂F₁ a a (2 * a) z) {a : ℂ | ∀ n : ℕ, 2 * a ≠ -(n : ℂ)} := by
  have hloc : HasSumLocallyUniformlyOn (fun n a ↦ zeroBalancedHyperTerm a z n)
      (fun a ↦ ₂F₁ a a (2 * a) z) {a : ℂ | ∀ n : ℕ, 2 * a ≠ -(n : ℂ)} :=
    hasSumLocallyUniformlyOn_of_forall_compact isOpen_two_mul_ne_neg_nat
      fun K hKU hK ↦ hasSumUniformlyOn_zeroBalancedHyperTerm hz hKU hK
  refine ((hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hloc).differentiableOn
    (Eventually.of_forall fun s ↦ ?_) isOpen_two_mul_ne_neg_nat).analyticOnNhd
      isOpen_two_mul_ne_neg_nat
  refine DifferentiableOn.fun_sum fun n _ a ha ↦ ?_
  have hne : (ascPochhammer ℂ n).eval (2 * a) ≠ 0 := fun h0 ↦ by
    obtain ⟨k, _, hk⟩ := (ascPochhammer_eval_eq_zero_iff n (2 * a)).mp h0
    exact ha k (neg_eq_iff_eq_neg.mp hk.symm)
  have hp1 : DifferentiableAt ℂ (fun b : ℂ ↦ (ascPochhammer ℂ n).eval b) a :=
    Polynomial.differentiableAt _
  have hp2 : DifferentiableAt ℂ (fun b : ℂ ↦ (ascPochhammer ℂ n).eval (2 * b)) a :=
    (Polynomial.differentiableAt (ascPochhammer ℂ n)).comp a (differentiableAt_id.const_mul 2)
  exact (((((differentiableAt_const _).mul hp1).mul hp1).mul (hp2.inv hne)).mul_const
    (z ^ n)).differentiableWithinAt

/-! ### Real Euler integral and Sturm-Liouville differential equation on `(0, 1)` -/

private noncomputable def eulerZeroBalanced (a x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, t ^ (a - 1) * (1 - t) ^ (a - 1) * (1 - (1 - x) * t) ^ (-a)

private theorem eulerTerm_integral_eq {a : ℝ} (ha : 0 < a) (x : ℝ) (n : ℕ) :
    Real.Gamma (2 * a) / Real.Gamma a ^ 2 *
      (∫ t in (0 : ℝ)..1,
        t ^ (a - 1) * (1 - t) ^ (a - 1) * (Ring.multichoose a n * ((1 - x) * t) ^ n)) =
      ((n !⁻¹ : ℝ) * (ascPochhammer ℝ n).eval a * (ascPochhammer ℝ n).eval a *
        ((ascPochhammer ℝ n).eval (2 * a))⁻¹) * (1 - x) ^ n := by
  have hcongr : ∫ t in (0 : ℝ)..1,
      t ^ (a - 1) * (1 - t) ^ (a - 1) * (Ring.multichoose a n * ((1 - x) * t) ^ n) =
      Ring.multichoose a n * (1 - x) ^ n *
        ∫ t in (0 : ℝ)..1, t ^ (a + n - 1) * (1 - t) ^ (a - 1) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun t ht ↦ ?_)
    rw [uIoc_of_le zero_le_one] at ht
    rw [mul_pow, show t ^ (a + (n : ℝ) - 1) = t ^ (a - 1) * t ^ n by
      rw [show a + (n : ℝ) - 1 = (a - 1) + n by ring, Real.rpow_add ht.1, Real.rpow_natCast]]
    ring
  rw [hcongr, integral_rpow_mul_one_sub_rpow (by positivity) ha, ProbabilityTheory.beta]
  have hmc : Ring.multichoose a n = (ascPochhammer ℝ n).eval a / n ! := by
    have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer a n
    rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at h
    rw [← h]; field_simp
  have hGa := Real.Gamma_add_nat_div_Gamma_eq (n := n) a fun k ↦ by
    linarith [k.cast_nonneg (α := ℝ)]
  have hG2a := Real.Gamma_add_nat_div_Gamma_eq (n := n) (2 * a) fun k ↦ by
    linarith [k.cast_nonneg (α := ℝ)]
  have hGa0 : Real.Gamma a ≠ 0 := (Real.Gamma_pos_of_pos ha).ne'
  have hG2a0 : Real.Gamma (2 * a) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hG2an0 : Real.Gamma (2 * a + n) ≠ 0 := (Real.Gamma_pos_of_pos (by positivity)).ne'
  have hP2a0 : (ascPochhammer ℝ n).eval (2 * a) ≠ 0 := hG2a ▸ div_ne_zero hG2an0 hG2a0
  rw [show a + (n : ℝ) + a = 2 * a + n by ring, hmc,
    show Real.Gamma (a + n) = (ascPochhammer ℝ n).eval a * Real.Gamma a by
      rw [← hGa, div_mul_cancel₀ _ hGa0],
    show Real.Gamma (2 * a + n) = (ascPochhammer ℝ n).eval (2 * a) * Real.Gamma (2 * a) by
      rw [← hG2a, div_mul_cancel₀ _ hG2a0]]
  field_simp

private theorem ordinaryHypergeometric_one_sub_eq_eulerZeroBalanced {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ₂F₁ a a (2 * a) (1 - x) =
      Real.Gamma (2 * a) / Real.Gamma a ^ 2 * eulerZeroBalanced a x := by
  let w : ℝ → ℝ := fun t ↦ t ^ (a - 1) * (1 - t) ^ (a - 1)
  let F : ℕ → ℝ → ℝ := fun n t ↦ w t * (Ring.multichoose a n * ((1 - x) * t) ^ n)
  let bound : ℕ → ℝ → ℝ := fun n t ↦ w t * (Ring.multichoose a n * (1 - x) ^ n)
  have hx1 : |1 - x| < 1 := abs_lt.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩
  have hsum_x := hasSum_multichoose_mul_geometric_of_abs_lt_one (r := a) hx1
  have hw_int : IntervalIntegrable w volume 0 1 :=
    intervalIntegrable_rpow_mul_one_sub_rpow ha.1 ha.1 ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
  have hdct : HasSum (fun n ↦ ∫ t in (0 : ℝ)..1, F n t) (eulerZeroBalanced a x) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence bound ?_ ?_ ?_ ?_ ?_
    · intro n; rw [uIoc_of_le zero_le_one]
      exact (hw_int.mul_continuousOn (by fun_prop)).1.aestronglyMeasurable
    · intro n; refine Eventually.of_forall fun t ht ↦ ?_
      rw [uIoc_of_le zero_le_one] at ht
      have hw0 : 0 ≤ w t := mul_nonneg (Real.rpow_nonneg ht.1.le _)
        (Real.rpow_nonneg (sub_nonneg.mpr ht.2) _)
      have hmc0 := multichoose_nonneg_of_pos ha.1 n
      have h1x : 0 ≤ 1 - x := sub_nonneg.mpr hx.2.le
      dsimp [F, bound]
      rw [abs_of_nonneg (mul_nonneg hw0 (mul_nonneg hmc0
        (pow_nonneg (mul_nonneg h1x ht.1.le) n))), mul_pow]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (pow_nonneg h1x n) (pow_le_one₀ ht.1.le ht.2)) hmc0) hw0
    · exact Eventually.of_forall fun t _ ↦ hsum_x.summable.mul_left (w t)
    · refine (hw_int.mul_const (1 / (1 - (1 - x)) ^ a)).congr fun t _ ↦ ?_
      dsimp [bound]; rw [tsum_mul_left, hsum_x.tsum_eq]
    · refine Eventually.of_forall fun t ht ↦ ?_
      rw [uIoc_of_le zero_le_one] at ht
      have hxt : |(1 - x) * t| < 1 := by
        rw [abs_of_nonneg (mul_nonneg (sub_nonneg.mpr hx.2.le) ht.1.le)]
        nlinarith [hx.1, hx.2, ht.2]
      have hst := (hasSum_multichoose_mul_geometric_of_abs_lt_one (r := a) hxt).mul_left (w t)
      rwa [one_div, ← Real.rpow_neg (by nlinarith [hx.1, hx.2, ht.1, ht.2])] at hst
  have hmul := (hdct.mul_left (Real.Gamma (2 * a) / Real.Gamma a ^ 2)).congr_fun fun n ↦
    (eulerTerm_integral_eq ha.1 x n).symm
  simpa [ordinaryHypergeometric, ordinaryHypergeometric_sum_eq] using hmul.tsum_eq

private theorem intervalIntegrable_eulerKernel {p q : ℝ} (hp : 0 < p) (hq : 0 < q)
    (r : ℝ) {x : ℝ} (hx : 0 < x) :
    IntervalIntegrable
      (fun t ↦ t ^ (p - 1) * (1 - t) ^ (q - 1) * (1 - (1 - x) * t) ^ (-r)) volume 0 1 :=
  (intervalIntegrable_rpow_mul_one_sub_rpow hp hq ⟨le_rfl, zero_le_one⟩
    ⟨zero_le_one, le_rfl⟩).mul_continuousOn <|
    ContinuousOn.rpow_const (by fun_prop) fun t ht ↦ Or.inl <| by
      rw [uIcc_of_le zero_le_one] at ht
      rcases le_or_gt x 1 with hx1 | hx1 <;> nlinarith [ht.1, ht.2]

private theorem hasDerivAt_eulerKernel {p q r x₀ : ℝ}
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hx₀ : x₀ ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt
      (fun x ↦ ∫ t in (0 : ℝ)..1, t ^ (p - 1) * (1 - t) ^ (q - 1) * (1 - (1 - x) * t) ^ (-r))
      (∫ t in (0 : ℝ)..1,
        -r * (t ^ p * (1 - t) ^ (q - 1) * (1 - (1 - x₀) * t) ^ (-r - 1))) x₀ := by
  let s := Ioo (x₀ / 2) 2
  have hs : s ∈ 𝓝 x₀ := Ioo_mem_nhds (by linarith [hx₀.1]) (by linarith [hx₀.2])
  let w : ℝ → ℝ := fun t ↦ t ^ (p - 1) * (1 - t) ^ (q - 1)
  have hw_int : IntervalIntegrable w volume 0 1 :=
    intervalIntegrable_rpow_mul_one_sub_rpow hp hq ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
  have hpos_z : ∀ {x t : ℝ}, x ∈ s → t ∈ Icc (0 : ℝ) 1 → x₀ / 2 ≤ 1 - (1 - x) * t :=
    fun hx ht ↦ by nlinarith [hx.1, hx₀.2, ht.1, ht.2]
  refine (intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun x t ↦ t ^ (p - 1) * (1 - t) ^ (q - 1) * (1 - (1 - x) * t) ^ (-r))
    (F' := fun x t ↦ -r * (t ^ p * (1 - t) ^ (q - 1) * (1 - (1 - x) * t) ^ (-r - 1)))
    hs ?_ (intervalIntegrable_eulerKernel hp hq r hx₀.1) ?_ ?_
    (hw_int.const_mul (r * (x₀ / 2) ^ (-r - 1))) ?_).2
  · filter_upwards [hs] with x hx; rw [uIoc_of_le zero_le_one]
    exact (intervalIntegrable_eulerKernel hp hq r
      (by linarith [hx.1, hx₀.1])).1.aestronglyMeasurable
  · have h2 := (intervalIntegrable_eulerKernel (p := p + 1) (by linarith) hq (r + 1)
      hx₀.1).const_mul (-r)
    simp only [add_sub_cancel_right, show -(r + 1) = -r - 1 by ring] at h2
    rw [uIoc_of_le zero_le_one]; exact h2.1.aestronglyMeasurable
  · refine Eventually.of_forall fun t ht x hx ↦ ?_
    rw [uIoc_of_le zero_le_one] at ht
    have hz : x₀ / 2 ≤ 1 - (1 - x) * t := hpos_z hx ⟨ht.1.le, ht.2⟩
    have hzr : (1 - (1 - x) * t) ^ (-r - 1) ≤ (x₀ / 2) ^ (-r - 1) :=
      Real.rpow_le_rpow_of_nonpos (by linarith [hx₀.1]) hz (by linarith)
    have htp : t ^ p ≤ t ^ (p - 1) := by
      rw [show t ^ p = t ^ (p - 1) * t by rw [← Real.rpow_add_one ht.1.ne', sub_add_cancel]]
      exact mul_le_of_le_one_right (Real.rpow_nonneg ht.1.le _) ht.2
    have h1t : 0 ≤ 1 - t := sub_nonneg.mpr ht.2
    have hz0 : 0 ≤ 1 - (1 - x) * t := by linarith [hx₀.1]
    rw [Real.norm_eq_abs, abs_mul, abs_neg, abs_of_pos hr,
      abs_of_nonneg (mul_nonneg (mul_nonneg (Real.rpow_nonneg ht.1.le _)
        (Real.rpow_nonneg h1t _)) (Real.rpow_nonneg hz0 _))]
    exact (mul_le_mul_of_nonneg_left (mul_le_mul (mul_le_mul_of_nonneg_right htp
      (Real.rpow_nonneg h1t _)) hzr (Real.rpow_nonneg hz0 _)
      (mul_nonneg (Real.rpow_nonneg ht.1.le _) (Real.rpow_nonneg h1t _))) hr.le).trans_eq
      (by dsimp [w]; ring)
  · refine Eventually.of_forall fun t ht x hx ↦ ?_
    rw [uIoc_of_le zero_le_one] at ht
    have hz0 : 0 < 1 - (1 - x) * t :=
      lt_of_lt_of_le (by linarith [hx₀.1]) (hpos_z hx ⟨ht.1.le, ht.2⟩)
    have hlin : HasDerivAt (fun y : ℝ ↦ 1 - (1 - y) * t) t x := by
      simpa using ((hasDerivAt_id x).const_sub 1).mul_const t |>.const_sub 1
    refine (((Real.hasDerivAt_rpow_const (p := -r) (Or.inl hz0.ne')).comp x hlin).const_mul
      (w t)).congr_deriv ?_
    dsimp [w]
    rw [show t ^ p = t ^ (p - 1) * t by rw [← Real.rpow_add_one ht.1.ne', sub_add_cancel]]; ring

private theorem hasDerivAt_eulerAntideriv {a x t : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (ht : t ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun s ↦ -a * (s ^ a * (1 - s) ^ a * (1 - (1 - x) * s) ^ (-a - 1)))
      (x * (1 - x) * ((-a) * (-(a + 1) * (t ^ (a + 1) * (1 - t) ^ (a - 1) *
        (1 - (1 - x) * t) ^ (-a - 2)))) +
      (1 - (2 * a + 1) * x) * (-a * (t ^ a * (1 - t) ^ (a - 1) * (1 - (1 - x) * t) ^ (-a - 1))) -
      a ^ 2 * (t ^ (a - 1) * (1 - t) ^ (a - 1) * (1 - (1 - x) * t) ^ (-a))) t := by
  have hz : 0 < 1 - (1 - x) * t := by nlinarith [hx.1, hx.2, ht.1, ht.2]
  have h1 := hasDerivAt_rpow_mul_one_sub_rpow a a (Or.inl ht.1.ne') (Or.inl ht.2.ne)
  have h2 := (Real.hasDerivAt_rpow_const (p := -a - 1) (Or.inl hz.ne')).comp t
    (((hasDerivAt_id t).const_mul (1 - x)).const_sub 1)
  refine ((h1.mul h2).const_mul (-a)).congr_deriv ?_
  have ht1 : t ^ a = t ^ (a - 1) * t := by rw [← Real.rpow_add_one ht.1.ne', sub_add_cancel]
  have ht2 : t ^ (a + 1) = t ^ (a - 1) * t ^ 2 := by
    rw [show a + 1 = (a - 1) + 2 by ring, Real.rpow_add ht.1, Real.rpow_two]
  have hs1 : (1 - t) ^ a = (1 - t) ^ (a - 1) * (1 - t) := by
    rw [← Real.rpow_add_one (sub_pos.mpr ht.2).ne', sub_add_cancel]
  have hz1 : (1 - (1 - x) * t) ^ (-a - 1) = (1 - (1 - x) * t) ^ (-a - 2) * (1 - (1 - x) * t) := by
    rw [← Real.rpow_add_one hz.ne', show -a - 2 + 1 = -a - 1 by ring]
  have hz2 : (1 - (1 - x) * t) ^ (-a) = (1 - (1 - x) * t) ^ (-a - 2) * (1 - (1 - x) * t) ^ 2 := by
    conv_lhs => rw [show -a = -a - 2 + 2 by ring]
    rw [Real.rpow_add hz, Real.rpow_two]
  simp only [Function.comp_apply, id_eq, show -a - 1 - 1 = -a - 2 by ring]
  rw [ht1, ht2, hs1, hz1, hz2]; ring

private theorem eulerZeroBalanced_ode_integral {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    x * (1 - x) * ((-a) * ∫ t in (0 : ℝ)..1,
      -(a + 1) * (t ^ (a + 1) * (1 - t) ^ (a - 1) * (1 - (1 - x) * t) ^ (-a - 2))) +
    (1 - (2 * a + 1) * x) * (∫ t in (0 : ℝ)..1,
      -a * (t ^ a * (1 - t) ^ (a - 1) * (1 - (1 - x) * t) ^ (-a - 1))) -
    a ^ 2 * eulerZeroBalanced a x = 0 := by
  have hint0 := intervalIntegrable_eulerKernel ha.1 ha.1 a hx.1
  have hd1 : IntervalIntegrable
      (fun t ↦ -a * (t ^ a * (1 - t) ^ (a - 1) * (1 - (1 - x) * t) ^ (-a - 1))) volume 0 1 := by
    simpa only [add_sub_cancel_right, show -(a + 1) = -a - 1 by ring] using
      (intervalIntegrable_eulerKernel (p := a + 1) (by linarith [ha.1]) ha.1 (a + 1) hx.1).const_mul
        (-a)
  have hd2 : IntervalIntegrable (fun t ↦ (-a) * (-(a + 1) *
      (t ^ (a + 1) * (1 - t) ^ (a - 1) * (1 - (1 - x) * t) ^ (-a - 2)))) volume 0 1 := by
    simpa only [show a + 2 - 1 = a + 1 by ring, show -(a + 2) = -a - 2 by ring] using
      ((intervalIntegrable_eulerKernel (p := a + 2) (by linarith [ha.1]) ha.1 (a + 2)
        hx.1).const_mul (-(a + 1))).const_mul (-a)
  let U : ℝ → ℝ := fun t ↦ -a * (t ^ a * (1 - t) ^ a * (1 - (1 - x) * t) ^ (-a - 1))
  have hU_cont : ContinuousOn U (Icc 0 1) :=
    continuousOn_const.mul <|
      ((continuousOn_id.rpow_const fun _ _ ↦ Or.inr ha.1.le).mul
        ((by fun_prop : ContinuousOn (fun t : ℝ ↦ 1 - t) (Icc 0 1)).rpow_const
          fun _ _ ↦ Or.inr ha.1.le)).mul
        ((by fun_prop : ContinuousOn (fun t : ℝ ↦ 1 - (1 - x) * t) (Icc 0 1)).rpow_const fun t ht ↦
          Or.inl (by nlinarith [hx.1, hx.2, ht.1, ht.2]))
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hU_cont
    (fun t ht ↦ hasDerivAt_eulerAntideriv hx ht)
    (((hd2.const_mul (x * (1 - x))).add (hd1.const_mul (1 - (2 * a + 1) * x))).sub
      (hint0.const_mul (a ^ 2)))
  simp only [U, Real.zero_rpow ha.1.ne', zero_mul, mul_zero, sub_self] at hftc
  rwa [intervalIntegral.integral_sub
    ((hd2.const_mul (x * (1 - x))).add (hd1.const_mul (1 - (2 * a + 1) * x)))
    (hint0.const_mul (a ^ 2)),
    intervalIntegral.integral_add (hd2.const_mul (x * (1 - x)))
      (hd1.const_mul (1 - (2 * a + 1) * x)),
    intervalIntegral.integral_const_mul (x * (1 - x)),
    intervalIntegral.integral_const_mul (-a),
    intervalIntegral.integral_const_mul (1 - (2 * a + 1) * x),
    intervalIntegral.integral_const_mul (a ^ 2)] at hftc

private theorem hasDerivAt_mul_one_sub_rpow (a : ℝ) {x : ℝ} (hx : x < 1) :
    HasDerivAt (fun y : ℝ ↦ y * (1 - y) ^ (2 * a))
      ((1 - x) ^ (2 * a) - 2 * a * x * (1 - x) ^ (2 * a - 1)) x := by
  have h2 := (Real.hasDerivAt_rpow_const (p := 2 * a) (Or.inl (sub_pos.mpr hx).ne')).comp x
    ((hasDerivAt_id x).const_sub 1)
  exact ((hasDerivAt_id x).mul h2).congr_deriv (by simp only [Function.comp_apply, id_eq]; ring)

private theorem hasDerivAt_sturmLiouville_eulerZeroBalanced {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y ↦ y * (1 - y) ^ (2 * a) * deriv (eulerZeroBalanced a) y)
      (a ^ 2 * (1 - x) ^ (2 * a - 1) * eulerZeroBalanced a x) x := by
  let E₁ : ℝ → ℝ := fun y ↦
    ∫ t in (0 : ℝ)..1, -a * (t ^ a * (1 - t) ^ (a - 1) * (1 - (1 - y) * t) ^ (-a - 1))
  have hd2 := hasDerivAt_eulerKernel (p := a + 1) (q := a) (r := a + 1)
    (by linarith [ha.1]) ha.1 (by linarith [ha.1]) hx
  have hE1_eq : deriv (eulerZeroBalanced a) =ᶠ[𝓝 x] E₁ := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact (hasDerivAt_eulerKernel ha.1 ha.1 ha.1 hy).deriv
  have hdE1 : HasDerivAt E₁
      ((-a) * ∫ t in (0 : ℝ)..1,
        -(a + 1) * (t ^ (a + 1) * (1 - t) ^ (a - 1) * (1 - (1 - x) * t) ^ (-a - 2))) x := by
    refine (hd2.const_mul (-a)).congr_of_eventuallyEq (Eventually.of_forall fun y ↦ ?_)
      |>.congr_deriv (by congr 2; ext t; rw [show -(a + 1) - 1 = -a - 2 by ring])
    dsimp [E₁]; rw [← intervalIntegral.integral_const_mul]
    exact intervalIntegral.integral_congr_ae (Eventually.of_forall fun t _ ↦ by
      rw [add_sub_cancel_right, show -(a + 1) = -a - 1 by ring])
  have hode := eulerZeroBalanced_ode_integral ha hx
  refine (((hasDerivAt_mul_one_sub_rpow a hx.2).mul hdE1).congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [hE1_eq] with y hy; simp [hy]
  · rw [show (1 - x) ^ (2 * a) = (1 - x) ^ (2 * a - 1) * (1 - x) by
      rw [← Real.rpow_add_one (sub_pos.mpr hx.2).ne', sub_add_cancel]]
    dsimp [E₁]; linear_combination (1 - x) ^ (2 * a - 1) * hode

private theorem summable_of_poly_bound {A : ℕ → ℝ} {C : ℝ} {m : ℕ}
    (hA : ∀ k : ℕ, |A k| ≤ C * ((k : ℝ) + 1) ^ m) {r : ℝ} (hr : |r| < 1) :
    Summable fun k : ℕ ↦ A k * r ^ k := by
  have hgeom := (summable_nat_add_iff 1).mpr
    (summable_pow_mul_geometric_of_norm_lt_one m (r := |r|) (by simpa [Real.norm_eq_abs] using hr))
  have hdom : Summable fun k : ℕ ↦ C * (((k : ℝ) + 1) ^ m * |r| ^ k) := by
    rcases eq_or_ne |r| 0 with hr0 | hr0
    · refine summable_of_ne_finset_zero (s := {0}) fun k hk ↦ ?_
      rcases k with _ | k
      · exact absurd (Finset.mem_singleton_self 0) hk
      · simp [hr0]
    · have hrpos : 0 < |r| := lt_of_le_of_ne (abs_nonneg r) hr0.symm
      exact (hgeom.mul_left (C / |r|)).congr fun k ↦ by
        push_cast; rw [pow_succ']; field_simp [hrpos.ne']
  refine hdom.of_norm_bounded fun k ↦ ?_
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact (mul_le_mul_of_nonneg_right (hA k) (pow_nonneg (abs_nonneg r) k)).trans_eq (by ring)

private theorem hasDerivAt_tsum_pow_of_poly_bound {A : ℕ → ℝ} {C : ℝ} {m : ℕ}
    (hC : 0 ≤ C) (hA : ∀ k : ℕ, |A k| ≤ C * ((k : ℝ) + 1) ^ m) {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (fun y ↦ ∑' k : ℕ, A k * y ^ k)
      (∑' k : ℕ, ((k : ℝ) + 1) * A (k + 1) * x ^ k) x := by
  let r := (|x| + 1) / 2
  have hr_pos : 0 < r := by dsimp [r]; positivity
  have hr_lt : r < 1 := by dsimp [r]; linarith
  have hxr : x ∈ Ioo (-r) r := abs_lt.mp (by dsimp [r]; linarith)
  let g : ℕ → ℝ → ℝ := fun k y ↦ A k * y ^ k
  let g' : ℕ → ℝ → ℝ := fun k y ↦ A k * ((k : ℝ) * y ^ (k - 1))
  let u : ℕ → ℝ := fun k ↦ C * ((k : ℝ) + 1) ^ (m + 1) * r ^ (k - 1)
  have hu : Summable u := by
    rw [← summable_nat_add_iff 1]
    refine (summable_of_poly_bound (A := fun k ↦ C * ((k : ℝ) + 2) ^ (m + 1))
      (C := C * 2 ^ (m + 1)) (m := m + 1) (fun k ↦ ?_) (abs_of_pos hr_pos ▸ hr_lt)).congr
      fun k ↦ by dsimp [u]; push_cast; ring
    have h2 : (k : ℝ) + 2 ≤ 2 * ((k : ℝ) + 1) := by linarith [k.cast_nonneg (α := ℝ)]
    rw [abs_of_nonneg (by positivity), mul_assoc, ← mul_pow]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by positivity) h2 _) hC
  have hg'_bd : ∀ k : ℕ, ∀ y ∈ Ioo (-r) r, ‖g' k y‖ ≤ u k := fun k y hy ↦ by
    rcases k with _ | k
    · simp only [g', u, Nat.cast_zero, zero_mul, mul_zero, norm_zero]; positivity
    · have hyr : |y| ≤ r := (abs_lt.mpr hy).le
      simp only [g', u, Nat.add_sub_cancel, Real.norm_eq_abs, abs_mul, abs_pow,
        Nat.cast_add, Nat.cast_one]
      have hk1 : |(k : ℝ) + 1| ≤ (k : ℝ) + 1 + 1 := by rw [abs_of_pos (by positivity)]; linarith
      exact (mul_le_mul (by simpa [Nat.cast_add, Nat.cast_one] using hA (k + 1))
        (mul_le_mul hk1 (pow_le_pow_left₀ (abs_nonneg y) hyr k)
          (pow_nonneg (abs_nonneg y) k) (by positivity))
        (by positivity) (by positivity)).trans_eq (by ring)
  have hd := hasDerivAt_tsum_of_isPreconnected (g := g) (g' := g') hu isOpen_Ioo isPreconnected_Ioo
    (fun k y _ ↦ by
      rcases k with _ | k
      · simp [g, g', hasDerivAt_const]
      · simpa [g, g', Nat.cast_add, Nat.cast_one] using
          (hasDerivAt_pow (k + 1) y).const_mul (A (k + 1)))
    hg'_bd (y₀ := 0) ⟨by linarith, hr_pos⟩ (summable_of_poly_bound hA (by simp)) hxr
  refine hd.congr_deriv ?_
  rw [(Summable.of_norm_bounded hu fun k ↦ hg'_bd k x hxr).tsum_eq_zero_add]
  simp only [g', Nat.cast_zero, zero_mul, mul_zero, zero_add, Nat.add_sub_cancel,
    Nat.cast_add, Nat.cast_one]
  exact tsum_congr fun k ↦ by ring

private theorem tsum_mul_pow_shifts {A : ℕ → ℝ} {C : ℝ} {m : ℕ}
    (hA : ∀ k : ℕ, |A k| ≤ C * ((k : ℝ) + 1) ^ m)
    (hA1 : ∀ k : ℕ, |((k : ℝ) + 1) * A (k + 1)| ≤ 2 ^ m * C * ((k : ℝ) + 1) ^ (m + 1))
    {x : ℝ} (hx : |x| < 1) :
    (Summable fun k : ℕ ↦ (k : ℝ) * A k * x ^ k) ∧
    (Summable fun k : ℕ ↦ (k : ℝ) * ((k : ℝ) + 1) * A (k + 1) * x ^ k) ∧
    (Summable fun k : ℕ ↦ (k : ℝ) * ((k : ℝ) - 1) * A k * x ^ k) ∧
    (x * (∑' k : ℕ, ((k : ℝ) + 1) * A (k + 1) * x ^ k) =
      ∑' k : ℕ, (k : ℝ) * A k * x ^ k) ∧
    (x * (∑' k : ℕ, ((k : ℝ) + 2) * ((k : ℝ) + 1) * A (k + 2) * x ^ k) =
      ∑' k : ℕ, (k : ℝ) * ((k : ℝ) + 1) * A (k + 1) * x ^ k) ∧
    (x ^ 2 * (∑' k : ℕ, ((k : ℝ) + 2) * ((k : ℝ) + 1) * A (k + 2) * x ^ k) =
      ∑' k : ℕ, (k : ℝ) * ((k : ℝ) - 1) * A k * x ^ k) := by
  have hs_x1 : Summable fun k : ℕ ↦ (k : ℝ) * A k * x ^ k :=
    summable_of_poly_bound (C := C) (m := m + 1) (fun k ↦ by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k)]
      exact (mul_le_mul (by linarith : (k : ℝ) ≤ (k : ℝ) + 1) (hA k) (abs_nonneg _)
        (by positivity)).trans_eq (by ring)) hx
  have hs_x2a : Summable fun k : ℕ ↦ (k : ℝ) * ((k : ℝ) + 1) * A (k + 1) * x ^ k :=
    summable_of_poly_bound (C := 2 ^ m * C) (m := m + 2) (fun k ↦ by
      have h := hA1 k
      rw [abs_mul, abs_of_pos (by positivity)] at h
      rw [abs_mul, abs_mul, abs_of_nonneg (Nat.cast_nonneg k), abs_of_pos (by positivity)]
      calc (k : ℝ) * ((k : ℝ) + 1) * |A (k + 1)|
          ≤ ((k : ℝ) + 1) * (((k : ℝ) + 1) * |A (k + 1)|) := by
            have := abs_nonneg (A (k + 1)); nlinarith [k.cast_nonneg (α := ℝ)]
        _ ≤ ((k : ℝ) + 1) * (2 ^ m * C * ((k : ℝ) + 1) ^ (m + 1)) :=
            mul_le_mul_of_nonneg_left h (by positivity)
        _ = 2 ^ m * C * ((k : ℝ) + 1) ^ (m + 2) := by ring) hx
  have hs_x2b : Summable fun k : ℕ ↦ (k : ℝ) * ((k : ℝ) - 1) * A k * x ^ k :=
    summable_of_poly_bound (C := C) (m := m + 2) (fun k ↦ by
      have hkk : |(k : ℝ) * ((k : ℝ) - 1)| ≤ ((k : ℝ) + 1) ^ 2 := by
        rcases k with _ | k
        · simp
        · push_cast; rw [add_sub_cancel_right, abs_of_nonneg (by positivity)]; nlinarith
      rw [abs_mul]
      exact (mul_le_mul hkk (hA k) (abs_nonneg _) (by positivity)).trans_eq (by ring)) hx
  refine ⟨hs_x1, hs_x2a, hs_x2b, ?_, ?_, ?_⟩
  · rw [hs_x1.tsum_eq_zero_add, Nat.cast_zero, zero_mul, zero_mul, zero_add, ← tsum_mul_left]
    exact tsum_congr fun k ↦ by push_cast; rw [pow_succ']; ring
  · rw [hs_x2a.tsum_eq_zero_add, Nat.cast_zero, zero_mul, zero_mul, zero_mul, zero_add,
      ← tsum_mul_left]
    exact tsum_congr fun k ↦ by push_cast; rw [pow_succ']; ring
  · rw [hs_x2b.tsum_eq_zero_add, ((summable_nat_add_iff 1).mpr hs_x2b).tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_mul, zero_add, Nat.cast_one, sub_self, mul_zero]
    rw [← tsum_mul_left]
    exact tsum_congr fun k ↦ by push_cast; rw [show x ^ (k + 2) = x ^ 2 * x ^ k by ring]; ring

private theorem hypergeometricOp_tsum_pow {A : ℕ → ℝ} {C : ℝ} {m : ℕ}
    (hC : 0 ≤ C) (hA : ∀ k : ℕ, |A k| ≤ C * ((k : ℝ) + 1) ^ m) (a : ℝ) {x : ℝ} (hx : |x| < 1) :
    let S := fun y ↦ ∑' k : ℕ, A k * y ^ k
    let S₁ := fun y ↦ ∑' k : ℕ, ((k : ℝ) + 1) * A (k + 1) * y ^ k
    let S₂ := fun y ↦ ∑' k : ℕ, ((k : ℝ) + 2) * ((k : ℝ) + 1) * A (k + 2) * y ^ k
    HasDerivAt S (S₁ x) x ∧ HasDerivAt S₁ (S₂ x) x ∧
      x * (1 - x) * S₂ x + (1 - (2 * a + 1) * x) * S₁ x - a ^ 2 * S x =
        ∑' k : ℕ, (((k : ℝ) + 1) ^ 2 * A (k + 1) - ((k : ℝ) + a) ^ 2 * A k) * x ^ k := by
  dsimp only
  have hA1 : ∀ k : ℕ, |((k : ℝ) + 1) * A (k + 1)| ≤ 2 ^ m * C * ((k : ℝ) + 1) ^ (m + 1) := by
    intro k
    have h2 : (k : ℝ) + 2 ≤ 2 * ((k : ℝ) + 1) := by linarith [k.cast_nonneg (α := ℝ)]
    have hAk := hA (k + 1)
    rw [Nat.cast_add, Nat.cast_one, show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by ring] at hAk
    rw [abs_mul, abs_of_pos (by positivity)]
    exact (mul_le_mul_of_nonneg_left (hAk.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) h2 m) hC)) (by positivity)).trans_eq (by rw [mul_pow]; ring)
  have hd1 := hasDerivAt_tsum_pow_of_poly_bound hC hA hx
  have hd2 : HasDerivAt (fun y ↦ ∑' k : ℕ, ((k : ℝ) + 1) * A (k + 1) * y ^ k)
      (∑' k : ℕ, ((k : ℝ) + 2) * ((k : ℝ) + 1) * A (k + 2) * x ^ k) x :=
    (hasDerivAt_tsum_pow_of_poly_bound (mul_nonneg (by positivity) hC) hA1
      hx).congr_deriv (tsum_congr fun k ↦ by push_cast; ring)
  refine ⟨hd1, hd2, ?_⟩
  have hs0 := summable_of_poly_bound hA hx
  have hs1 := summable_of_poly_bound hA1 hx
  obtain ⟨hs_x1, hs_x2a, hs_x2b, hx1_eq, hx2a_eq, hx2b_eq⟩ := tsum_mul_pow_shifts hA hA1 hx
  rw [show x * (1 - x) * (∑' k : ℕ, ((k : ℝ) + 2) * ((k : ℝ) + 1) * A (k + 2) * x ^ k) +
      (1 - (2 * a + 1) * x) * (∑' k : ℕ, ((k : ℝ) + 1) * A (k + 1) * x ^ k) -
      a ^ 2 * (∑' k : ℕ, A k * x ^ k) =
      (x * ∑' k : ℕ, ((k : ℝ) + 2) * ((k : ℝ) + 1) * A (k + 2) * x ^ k) -
      (x ^ 2 * ∑' k : ℕ, ((k : ℝ) + 2) * ((k : ℝ) + 1) * A (k + 2) * x ^ k) +
      (∑' k : ℕ, ((k : ℝ) + 1) * A (k + 1) * x ^ k) -
      (2 * a + 1) * (x * ∑' k : ℕ, ((k : ℝ) + 1) * A (k + 1) * x ^ k) -
      a ^ 2 * (∑' k : ℕ, A k * x ^ k) by ring, hx2a_eq, hx2b_eq, hx1_eq]
  exact (((((hs_x2a.hasSum.sub hs_x2b.hasSum).add hs1.hasSum).sub
    (hs_x1.hasSum.mul_left (2 * a + 1))).sub (hs0.hasSum.mul_left (a ^ 2))).congr_fun
      fun k ↦ by ring).tsum_eq.symm

private noncomputable def realCoeff (a : ℝ) (k : ℕ) : ℝ := ((ascPochhammer ℝ k).eval a / k !) ^ 2
private noncomputable def realDigammaDiff (a : ℝ) (k : ℕ) : ℝ :=
  2 * (Real.digamma (k + 1) - Real.digamma (k + a))
private noncomputable def realU1 (a x : ℝ) : ℝ := ∑' k : ℕ, realCoeff a k * x ^ k
private noncomputable def realV (a x : ℝ) : ℝ :=
  ∑' k : ℕ, realCoeff a k * realDigammaDiff a k * x ^ k
private noncomputable def realU2 (a x : ℝ) : ℝ := -Real.log x * realU1 a x + realV a x

private theorem eval_ofReal_ascPochhammer (a : ℝ) (k : ℕ) :
    (ascPochhammer ℂ k).eval (a : ℂ) = Complex.ofReal ((ascPochhammer ℝ k).eval a) := by
  induction k with
  | zero => simp
  | succ k ih => simp [ascPochhammer_succ_eval, ih]

private theorem realCoeff_bounds {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (k : ℕ) :
    0 ≤ realCoeff a k ∧ |realCoeff a k| ≤ 1 := by
  have ha0 : 0 < a := ha.1
  have hq : 0 ≤ (ascPochhammer ℝ k).eval a / k ! ∧ (ascPochhammer ℝ k).eval a / k ! ≤ 1 := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ascPochhammer_succ_eval, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
        mul_comm ((k : ℝ) + 1), ← div_mul_div_comm]
      have hstep_nn : 0 ≤ (a + k) / ((k : ℝ) + 1) := by positivity
      have hstep_le : (a + k) / ((k : ℝ) + 1) ≤ 1 :=
        (div_le_one (by positivity)).mpr (by linarith [ha.2])
      exact ⟨mul_nonneg ih.1 hstep_nn, (mul_le_mul ih.2 hstep_le hstep_nn zero_le_one).trans_eq
        (one_mul 1)⟩
  exact ⟨sq_nonneg _, by rw [abs_of_nonneg (sq_nonneg _), realCoeff]; exact pow_le_one₀ hq.1 hq.2⟩

private theorem realCoeff_poly_bound {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (k : ℕ) :
    |realCoeff a k| ≤ 1 * ((k : ℝ) + 1) ^ 0 := by
  simpa using (realCoeff_bounds ha k).2

private theorem realU1_zero (a : ℝ) : realU1 a 0 = 1 := by
  rw [realU1, tsum_eq_single 0 fun k hk ↦ by simp [zero_pow hk]]
  simp [realCoeff]

private theorem realCoeff_recurrence (a : ℝ) (k : ℕ) :
    ((k : ℝ) + 1) ^ 2 * realCoeff a (k + 1) = ((k : ℝ) + a) ^ 2 * realCoeff a k := by
  dsimp [realCoeff]
  rw [ascPochhammer_succ_eval, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp; ring

private theorem realDigammaCoeff_recurrence {a : ℝ} (ha : 0 < a) (k : ℕ) :
    ((k : ℝ) + 1) ^ 2 * (realCoeff a (k + 1) * realDigammaDiff a (k + 1)) -
      ((k : ℝ) + a) ^ 2 * (realCoeff a k * realDigammaDiff a k) =
    2 * ((k : ℝ) + 1) * realCoeff a (k + 1) - 2 * ((k : ℝ) + a) * realCoeff a k := by
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have hka : (k : ℝ) + a ≠ 0 := by positivity
  have hd : realDigammaDiff a (k + 1) =
      realDigammaDiff a k + 2 / ((k : ℝ) + 1) - 2 / ((k : ℝ) + a) := by
    dsimp [realDigammaDiff]
    rw [Nat.cast_add, Nat.cast_one,
      Real.digamma_apply_add_one (x := (k : ℝ) + 1) (fun m ↦ by
        have := m.cast_nonneg (α := ℝ); have := k.cast_nonneg (α := ℝ); linarith),
      show (k : ℝ) + 1 + a = ((k : ℝ) + a) + 1 by ring,
      Real.digamma_apply_add_one (x := (k : ℝ) + a) (fun m ↦ by
        have := m.cast_nonneg (α := ℝ); have := k.cast_nonneg (α := ℝ); linarith)]
    ring
  have hc := realCoeff_recurrence a k
  rw [hd]
  calc ((k : ℝ) + 1) ^ 2 * (realCoeff a (k + 1) *
        (realDigammaDiff a k + 2 / ((k : ℝ) + 1) - 2 / ((k : ℝ) + a))) -
        ((k : ℝ) + a) ^ 2 * (realCoeff a k * realDigammaDiff a k)
      = (((k : ℝ) + 1) ^ 2 * realCoeff a (k + 1)) * realDigammaDiff a k +
        ((k : ℝ) + 1) ^ 2 * realCoeff a (k + 1) * (2 / ((k : ℝ) + 1)) -
        (((k : ℝ) + 1) ^ 2 * realCoeff a (k + 1)) * (2 / ((k : ℝ) + a)) -
        ((k : ℝ) + a) ^ 2 * (realCoeff a k * realDigammaDiff a k) := by ring
    _ = (((k : ℝ) + a) ^ 2 * realCoeff a k) * realDigammaDiff a k +
        ((k : ℝ) + 1) ^ 2 * realCoeff a (k + 1) * (2 / ((k : ℝ) + 1)) -
        (((k : ℝ) + a) ^ 2 * realCoeff a k) * (2 / ((k : ℝ) + a)) -
        ((k : ℝ) + a) ^ 2 * (realCoeff a k * realDigammaDiff a k) := by rw [hc]
    _ = 2 * ((k : ℝ) + 1) * realCoeff a (k + 1) - 2 * ((k : ℝ) + a) * realCoeff a k := by
        field_simp [hk1, hka]; ring

private theorem realDigammaCoeff_bound {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ k : ℕ, |realCoeff a k * realDigammaDiff a k| ≤ B := by
  have hd_nn : ∀ k : ℕ, 0 ≤ realDigammaDiff a k := fun k ↦
    mul_nonneg zero_le_two <| sub_nonneg.mpr <| Real.monotoneOn_digamma
      (mem_Ioi.mpr (by have := k.cast_nonneg (α := ℝ); linarith [ha.1]))
      (mem_Ioi.mpr (by positivity)) (by linarith [ha.2])
  refine ⟨realDigammaDiff a 0, hd_nn 0, fun k ↦ ?_⟩
  have hle : realDigammaDiff a k ≤ realDigammaDiff a 0 := by
    have h := Real.antitone_digamma_nat_add_one_sub_digamma_nat_add ha.1 ha.2.le (Nat.zero_le k)
    simpa [realDigammaDiff] using mul_le_mul_of_nonneg_left h zero_le_two
  rw [abs_mul, abs_of_nonneg (hd_nn k)]
  exact (mul_le_mul (realCoeff_bounds ha k).2 hle (hd_nn k) zero_le_one).trans_eq (one_mul _)

private theorem hasDerivAt_sturmLiouville_realU1 {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y ↦ y * (1 - y) ^ (2 * a) * deriv (realU1 a) y)
      (a ^ 2 * (1 - x) ^ (2 * a - 1) * realU1 a x) x := by
  have hop := hypergeometricOp_tsum_pow zero_le_one (realCoeff_poly_bound ha) a
    (abs_lt.mpr ⟨by linarith [hx.1], hx.2⟩)
  have hderiv_eq : deriv (realU1 a) =ᶠ[𝓝 x]
      fun y ↦ ∑' k : ℕ, ((k : ℝ) + 1) * realCoeff a (k + 1) * y ^ k := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    exact (hypergeometricOp_tsum_pow zero_le_one (realCoeff_poly_bound ha) a
      (abs_lt.mpr ⟨by linarith [hy.1], hy.2⟩)).1.deriv
  refine (((hasDerivAt_mul_one_sub_rpow a hx.2).mul hop.2.1).congr_of_eventuallyEq
    ?_).congr_deriv ?_
  · filter_upwards [hderiv_eq] with y hy; simp [hy]
  · have heq := hop.2.2.trans (show _ = (0 : ℝ) by simp [realCoeff_recurrence a])
    rw [show (1 - x) ^ (2 * a) = (1 - x) ^ (2 * a - 1) * (1 - x) by
      rw [← Real.rpow_add_one (sub_pos.mpr hx.2).ne', sub_add_cancel]]
    dsimp [realU1]; linear_combination (1 - x) ^ (2 * a - 1) * heq

private theorem realV_ode {a x : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hxa : |x| < 1) :
    x * (1 - x) * (∑' k : ℕ, ((k : ℝ) + 2) * ((k : ℝ) + 1) *
      (realCoeff a (k + 2) * realDigammaDiff a (k + 2)) * x ^ k) +
    (1 - (2 * a + 1) * x) * (∑' k : ℕ, ((k : ℝ) + 1) *
      (realCoeff a (k + 1) * realDigammaDiff a (k + 1)) * x ^ k) -
    a ^ 2 * realV a x =
    2 * (1 - x) * (∑' k : ℕ, ((k : ℝ) + 1) * realCoeff a (k + 1) * x ^ k) -
      2 * a * realU1 a x := by
  obtain ⟨B, hB0, hB⟩ := realDigammaCoeff_bound ha
  have hb_bd : ∀ k : ℕ, |realCoeff a k * realDigammaDiff a k| ≤ B * ((k : ℝ) + 1) ^ 0 := fun k ↦ by
    simpa using hB k
  have hopV := (hypergeometricOp_tsum_pow hB0 hb_bd a hxa).2.2
  dsimp only at hopV
  rw [show realV a x = ∑' k : ℕ, (realCoeff a k * realDigammaDiff a k) * x ^ k from rfl, hopV]
  have hc1 : ∀ k : ℕ, |((k : ℝ) + 1) * realCoeff a (k + 1)| ≤
      2 ^ 0 * 1 * ((k : ℝ) + 1) ^ (0 + 1) := fun k ↦ by
    rw [abs_mul, abs_of_pos (by positivity)]
    simpa [mul_comm] using mul_le_mul_of_nonneg_left (realCoeff_bounds ha (k + 1)).2
      (by positivity : 0 ≤ (k : ℝ) + 1)
  have hs_u1 := summable_of_poly_bound (realCoeff_poly_bound ha) hxa
  have hs_u1' := summable_of_poly_bound hc1 hxa
  obtain ⟨hs_xu1', _, _, hxu1'_eq, _, _⟩ := tsum_mul_pow_shifts (realCoeff_poly_bound ha) hc1 hxa
  rw [show 2 * (1 - x) * (∑' k : ℕ, ((k : ℝ) + 1) * realCoeff a (k + 1) * x ^ k) -
      2 * a * realU1 a x =
      2 * (∑' k : ℕ, ((k : ℝ) + 1) * realCoeff a (k + 1) * x ^ k) -
      2 * (x * ∑' k : ℕ, ((k : ℝ) + 1) * realCoeff a (k + 1) * x ^ k) -
      2 * a * realU1 a x by ring, hxu1'_eq]
  exact ((((hs_u1'.hasSum.mul_left 2).sub (hs_xu1'.hasSum.mul_left 2)).sub
    (hs_u1.hasSum.mul_left (2 * a))).congr_fun fun k ↦ by
      linear_combination x ^ k * realDigammaCoeff_recurrence ha.1 k).tsum_eq

private theorem hasDerivAt_sturmLiouville_realU2 {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y ↦ y * (1 - y) ^ (2 * a) * deriv (realU2 a) y)
      (a ^ 2 * (1 - x) ^ (2 * a - 1) * realU2 a x) x := by
  obtain ⟨B, hB0, hB⟩ := realDigammaCoeff_bound ha
  have hb_bd : ∀ k : ℕ, |realCoeff a k * realDigammaDiff a k| ≤ B * ((k : ℝ) + 1) ^ 0 := fun k ↦ by
    simpa using hB k
  have hxa : |x| < 1 := abs_lt.mpr ⟨by linarith [hx.1], hx.2⟩
  have hop1 := hypergeometricOp_tsum_pow zero_le_one (realCoeff_poly_bound ha) a hxa
  have hopV := hypergeometricOp_tsum_pow hB0 hb_bd a hxa
  let u1' := fun y : ℝ ↦ ∑' k : ℕ, ((k : ℝ) + 1) * realCoeff a (k + 1) * y ^ k
  let v' := fun y : ℝ ↦
    ∑' k : ℕ, ((k : ℝ) + 1) * (realCoeff a (k + 1) * realDigammaDiff a (k + 1)) * y ^ k
  let u2' := fun y : ℝ ↦ -y⁻¹ * realU1 a y - Real.log y * u1' y + v' y
  have hderiv_eq : deriv (realU2 a) =ᶠ[𝓝 x] u2' := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    have hya : |y| < 1 := abs_lt.mpr ⟨by linarith [hy.1], hy.2⟩
    refine (((((Real.hasDerivAt_log hy.1.ne').neg.mul
      (hypergeometricOp_tsum_pow zero_le_one (realCoeff_poly_bound ha) a hya).1).add
      (hypergeometricOp_tsum_pow hB0 hb_bd a hya).1).congr_of_eventuallyEq
      (Eventually.of_forall fun _ ↦ rfl)).congr_deriv
      (by dsimp [u2', realU1, u1', v']; ring)).deriv
  have hdu2' : HasDerivAt u2'
      ((x⁻¹) ^ 2 * realU1 a x - 2 * x⁻¹ * u1' x -
        Real.log x * (∑' k : ℕ, ((k : ℝ) + 2) * ((k : ℝ) + 1) * realCoeff a (k + 2) * x ^ k) +
        ∑' k : ℕ, ((k : ℝ) + 2) * ((k : ℝ) + 1) *
          (realCoeff a (k + 2) * realDigammaDiff a (k + 2)) * x ^ k) x :=
    (((((hasDerivAt_inv hx.1.ne').neg.mul hop1.1).sub
      ((Real.hasDerivAt_log hx.1.ne').mul hop1.2.1)).add hopV.2.1).congr_of_eventuallyEq
        (Eventually.of_forall fun _ ↦ rfl)).congr_deriv
        (by rw [← inv_pow]; dsimp [realU1, u1']; ring)
  refine (((hasDerivAt_mul_one_sub_rpow a hx.2).mul hdu2').congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [hderiv_eq] with y hy; simp [hy]
  · have hzero1 := hop1.2.2.trans (show _ = (0 : ℝ) by simp [realCoeff_recurrence a])
    have hV_eq := realV_ode ha hxa
    have hxix : x * x⁻¹ = 1 := mul_inv_cancel₀ hx.1.ne'
    rw [show (1 - x) ^ (2 * a) = (1 - x) ^ (2 * a - 1) * (1 - x) by
      rw [← Real.rpow_add_one (sub_pos.mpr hx.2).ne', sub_add_cancel]]
    dsimp only [u2', realU2, u1', v'] at hzero1 hV_eq ⊢
    rw [show (∑' k : ℕ, realCoeff a k * x ^ k) = realU1 a x from rfl] at hzero1
    linear_combination (1 - x) ^ (2 * a - 1) *
      (-Real.log x * hzero1 + hV_eq +
        ((2 * a + x⁻¹ - x * x⁻¹) * realU1 a x - 2 * (1 - x) * u1' x) * hxix)

/-! ### Logarithmic asymptotic at `0⁺`, Wronskian uniqueness, and complex continuation -/

private theorem ae_ne_one : ∀ᵐ w : ℝ ∂volume, w ≠ 1 := ae_iff.mpr (by simp)

private theorem rpow_sub_one_div_one_sub_bounds {a w : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hw : w ∈ Ioo (0 : ℝ) 1) :
    0 ≤ (w ^ (a - 1) - 1) / (1 - w) ∧ (w ^ (a - 1) - 1) / (1 - w) ≤ w ^ (a - 1) := by
  have hw1 : w ≤ w ^ (1 - a) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hw.1 hw.2.le (by linarith [ha.1] : 1 - a ≤ 1)
  have hw_gt : 1 ≤ w ^ (a - 1) := by
    simpa using Real.rpow_le_rpow_of_exponent_ge hw.1 hw.2.le (by linarith [ha.2] : a - 1 ≤ 0)
  refine ⟨div_nonneg (sub_nonneg.mpr hw_gt) (sub_nonneg.mpr hw.2.le), ?_⟩
  rw [show w ^ (a - 1) - 1 = w ^ (a - 1) * (1 - w ^ (1 - a)) by
    rw [mul_sub, mul_one, ← Real.rpow_add hw.1, show a - 1 + (1 - a) = 0 by ring, Real.rpow_zero],
    mul_div_assoc]
  exact mul_le_of_le_one_right (Real.rpow_nonneg hw.1.le _)
    ((div_le_one (sub_pos.mpr hw.2)).mpr (by linarith))

private theorem intervalIntegrable_rpow_sub_one_div_one_sub {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    IntervalIntegrable (fun w ↦ (w ^ (a - 1) - 1) / (1 - w)) volume 0 1 := by
  have hdom : IntervalIntegrable (fun w : ℝ ↦ w ^ (a - 1)) volume 0 1 :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith [ha.1])
  rw [intervalIntegrable_iff, IntegrableOn, uIoc_of_le zero_le_one,
    ← Measure.restrict_congr_set Ioo_ae_eq_Ioc] at hdom ⊢
  refine hdom.mono' ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    exact ((ContinuousOn.rpow_const (s := Ioo (0 : ℝ) 1) continuousOn_id
      fun w hw ↦ Or.inl hw.1.ne').sub continuousOn_const).div (by fun_prop)
      fun w hw ↦ sub_ne_zero.mpr hw.2.ne'
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
    rw [Real.norm_eq_abs, abs_of_nonneg (rpow_sub_one_div_one_sub_bounds ha hw).1]
    exact (rpow_sub_one_div_one_sub_bounds ha hw).2

private theorem integral_finset_rpow_sub_pow {a : ℝ} (ha : 0 < a) (N : ℕ) :
    IntervalIntegrable (fun w : ℝ ↦ ∑ k ∈ Finset.range N, (w ^ ((k : ℝ) + a - 1) - w ^ k))
      volume 0 1 ∧
    (∫ w in (0 : ℝ)..1, ∑ k ∈ Finset.range N, (w ^ ((k : ℝ) + a - 1) - w ^ k)) =
      ∑ k ∈ Finset.range N, (1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + 1)) := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hterm_int : IntervalIntegrable (fun w : ℝ ↦ w ^ ((n : ℝ) + a - 1) - w ^ n) volume 0 1 :=
      (intervalIntegral.intervalIntegrable_rpow'
        (by have := n.cast_nonneg (α := ℝ); linarith)).sub
        (Continuous.intervalIntegrable (by fun_prop) 0 1)
    have hsum_eq : (fun w : ℝ ↦ ∑ k ∈ Finset.range (n + 1), (w ^ ((k : ℝ) + a - 1) - w ^ k)) =
        fun w : ℝ ↦ (∑ k ∈ Finset.range n, (w ^ ((k : ℝ) + a - 1) - w ^ k)) +
          (w ^ ((n : ℝ) + a - 1) - w ^ n) := by
      ext w; exact Finset.sum_range_succ _ n
    rw [hsum_eq, Finset.sum_range_succ]
    refine ⟨ih.1.add hterm_int, ?_⟩
    have hna : (0 : ℝ) < (n : ℝ) + a := by positivity
    rw [intervalIntegral.integral_add ih.1 hterm_int, ih.2,
      intervalIntegral.integral_sub
        (intervalIntegral.intervalIntegrable_rpow' (by linarith))
        (Continuous.intervalIntegrable (by fun_prop) 0 1),
      integral_rpow (Or.inl (by linarith)), integral_pow,
      show (n : ℝ) + a - 1 + 1 = (n : ℝ) + a by ring, Real.one_rpow, Real.zero_rpow hna.ne']
    simp [zero_pow (Nat.succ_ne_zero n)]

private theorem integral_rpow_sub_one_div_one_sub {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ∫ w in (0 : ℝ)..1, (w ^ (a - 1) - 1) / (1 - w) = Real.digamma 1 - Real.digamma a := by
  let F : ℕ → ℝ → ℝ := fun N w ↦ ∑ k ∈ Finset.range N, (w ^ ((k : ℝ) + a - 1) - w ^ k)
  have hrpow_mul {w : ℝ} (hw : 0 < w) (k : ℕ) :
      w ^ ((k : ℝ) + a - 1) - w ^ k = (w ^ (a - 1) - 1) * w ^ k := by
    rw [sub_mul, one_mul, show w ^ ((k : ℝ) + a - 1) = w ^ (a - 1) * w ^ k by
      rw [show (k : ℝ) + a - 1 = (a - 1) + k by ring, Real.rpow_add hw, Real.rpow_natCast]]
  have hsum_w : ∀ {w : ℝ}, w ∈ Ioo (0 : ℝ) 1 →
      HasSum (fun k : ℕ ↦ w ^ ((k : ℝ) + a - 1) - w ^ k) ((w ^ (a - 1) - 1) / (1 - w)) := by
    intro w hw; rw [div_eq_mul_inv]
    exact ((hasSum_geometric_of_lt_one hw.1.le hw.2).mul_left
      (w ^ (a - 1) - 1)).congr_fun fun k ↦ hrpow_mul hw.1 k
  have hdct : Tendsto (fun N ↦ ∫ w in (0 : ℝ)..1, F N w) atTop
      (𝓝 (∫ w in (0 : ℝ)..1, (w ^ (a - 1) - 1) / (1 - w))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (F := F) (fun w ↦ w ^ (a - 1)) ?_ ?_
      (intervalIntegral.intervalIntegrable_rpow' (by linarith [ha.1])) ?_
    · exact Eventually.of_forall fun N ↦
        (intervalIntegrable_iff.mp (integral_finset_rpow_sub_pow ha.1 N).1).aestronglyMeasurable
    · refine Eventually.of_forall fun N ↦ ?_
      filter_upwards [ae_ne_one] with w hw1 hw
      rw [uIoc_of_le zero_le_one] at hw
      have hwoo : w ∈ Ioo (0 : ℝ) 1 := ⟨hw.1, lt_of_le_of_ne hw.2 hw1⟩
      have hterm_nn : ∀ k : ℕ, 0 ≤ w ^ ((k : ℝ) + a - 1) - w ^ k := fun k ↦ by
        have hgt : 1 ≤ w ^ (a - 1) := by
          simpa using Real.rpow_le_rpow_of_exponent_ge hwoo.1 hwoo.2.le
            (by linarith [ha.2] : a - 1 ≤ 0)
        rw [hrpow_mul hwoo.1 k]
        exact mul_nonneg (sub_nonneg.mpr hgt) (pow_nonneg hwoo.1.le k)
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ ↦ hterm_nn k)]
      exact (sum_le_hasSum (Finset.range N) (fun k _ ↦ hterm_nn k) (hsum_w hwoo)).trans
        (rpow_sub_one_div_one_sub_bounds ha hwoo).2
    · filter_upwards [ae_ne_one] with w hw1 hw
      rw [uIoc_of_le zero_le_one] at hw
      exact (hsum_w ⟨hw.1, lt_of_le_of_ne hw.2 hw1⟩).tendsto_sum_nat
  dsimp only [F] at hdct
  simp_rw [fun N ↦ (integral_finset_rpow_sub_pow ha.1 N).2] at hdct
  have hgauss : HasSum (fun k : ℕ ↦ 1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + 1))
      (Real.digamma 1 - Real.digamma a) := by
    have hd := Real.digamma_eq_gaussSeries (x := a) fun m ↦ by
      have := m.cast_nonneg (α := ℝ); linarith [ha.1]
    have hval : -(∑' n : ℕ, (1 / ((n : ℝ) + 1) - 1 / (a + n))) =
        Real.digamma 1 - Real.digamma a := by rw [Real.digamma_one]; linarith
    have h := (Real.summable_gaussSeries a).hasSum.neg
    rw [hval] at h
    exact h.congr_fun fun k ↦ by ring
  exact tendsto_nhds_unique hdct hgauss.tendsto_sum_nat

private theorem integral_singular_euler_piece {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    (1 - x) ^ a * (∫ s in (0 : ℝ)..1, s ^ (a - 1) * (x + (1 - x) * s) ^ (-a)) =
      (∫ w in (0 : ℝ)..(1 - x), (w ^ (a - 1) - 1) / (1 - w)) - Real.log x := by
  let u : ℝ → ℝ := fun s ↦ (1 - x) * s / (x + (1 - x) * s)
  let u' : ℝ → ℝ := fun s ↦ x * (1 - x) / (x + (1 - x) * s) ^ 2
  let g : ℝ → ℝ := fun w ↦ w ^ (a - 1) / (1 - w)
  have hu_cont : ContinuousOn u (uIcc 0 1) := by
    rw [uIcc_of_le zero_le_one]
    exact ContinuousOn.div (by fun_prop) (by fun_prop) fun s hs ↦
      (by nlinarith [hx.1, hx.2, hs.1, hs.2] : 0 < x + (1 - x) * s).ne'
  have hu_deriv : ∀ s ∈ Ioo (min (0 : ℝ) 1) (max (0 : ℝ) 1), HasDerivAt u (u' s) s := by
    rw [min_eq_left zero_le_one, max_eq_right zero_le_one]; intro s hs
    have hD : 0 < x + (1 - x) * s := by nlinarith [hx.1, hx.2, hs.1, hs.2]
    exact (((hasDerivAt_id s).const_mul (1 - x)).div
      (((hasDerivAt_id s).const_mul (1 - x)).const_add x) hD.ne').congr_deriv (by dsimp [u']; ring)
  have hsub := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg hu_cont hu_deriv
    (fun s _ ↦ div_nonneg (mul_nonneg hx.1.le (sub_nonneg.mpr hx.2.le)) (sq_nonneg _)) (g := g)
  rw [show u 0 = 0 by simp [u],
    show u 1 = 1 - x by dsimp [u]; rw [mul_one, add_sub_cancel, div_one]] at hsub
  have hlhs : (1 - x) ^ a * (∫ s in (0 : ℝ)..1, s ^ (a - 1) * (x + (1 - x) * s) ^ (-a)) =
      ∫ s in (0 : ℝ)..1, (g ∘ u) s * u' s := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr_ae (Eventually.of_forall fun s hs ↦ ?_)
    rw [uIoc_of_le zero_le_one] at hs
    have h1x := sub_pos.mpr hx.2
    have hD : 0 < x + (1 - x) * s := by nlinarith [hx.1, h1x, hs.1]
    dsimp [g, u, u']
    rw [Real.div_rpow (mul_nonneg h1x.le hs.1.le) hD.le, Real.mul_rpow h1x.le hs.1.le,
      show 1 - (1 - x) * s / (x + (1 - x) * s) = x / (x + (1 - x) * s) by field_simp [hD.ne']; ring,
      show (1 - x) ^ a = (1 - x) ^ (a - 1) * (1 - x) by
        rw [← Real.rpow_add_one h1x.ne', sub_add_cancel],
      show (x + (1 - x) * s) ^ (-a) = ((x + (1 - x) * s) ^ (a - 1) * (x + (1 - x) * s))⁻¹ by
        rw [← Real.rpow_add_one hD.ne', sub_add_cancel, Real.rpow_neg hD.le]]
    field_simp [hx.1.ne', hD.ne', (Real.rpow_pos_of_pos hD (a - 1)).ne']
  have hint1 : IntervalIntegrable (fun w ↦ (w ^ (a - 1) - 1) / (1 - w)) volume 0 (1 - x) :=
    (intervalIntegrable_rpow_sub_one_div_one_sub ha).mono_set <| by
      rw [uIcc_of_le (sub_nonneg.mpr hx.2.le), uIcc_of_le zero_le_one]
      exact Icc_subset_Icc_right (by linarith [hx.1])
  have hint2 : IntervalIntegrable (fun w : ℝ ↦ (1 - w)⁻¹) volume 0 (1 - x) :=
    (ContinuousOn.inv₀ (by fun_prop) fun w hw ↦ by
      rw [uIcc_of_le (sub_nonneg.mpr hx.2.le)] at hw; linarith [hw.2, hx.1]).intervalIntegrable
  have hlog : ∫ w in (0 : ℝ)..(1 - x), (1 - w)⁻¹ = -Real.log x := by
    simpa [sub_sub_cancel] using intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le
      (sub_nonneg.mpr hx.2.le) (f := fun w ↦ -Real.log (1 - w))
      (ContinuousOn.neg <| ContinuousOn.log (by fun_prop) fun w hw ↦ by linarith [hw.2, hx.1])
      (fun w hw ↦ ((((hasDerivAt_id w).const_sub 1).log
        (by simp only [id_eq]; linarith [hw.2, hx.1])).neg).congr_deriv
        (by simp only [id_eq]; ring)) hint2
  rw [hlhs, hsub, show ∫ w in (0 : ℝ)..(1 - x), g w =
      ∫ w in (0 : ℝ)..(1 - x), ((w ^ (a - 1) - 1) / (1 - w) + (1 - w)⁻¹) from
      intervalIntegral.integral_congr fun w _ ↦ by dsimp [g]; ring,
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
      rw [sub_sub_cancel, show 1 - (1 - x) * (1 - s) = x + (1 - x) * s by ring]
  obtain ⟨htot, hsing⟩ := intervalIntegrable_swappedEuler ha hx
  have hsmooth := (htot.sub hsing).congr fun s _ ↦
    show (1 - s) ^ (a - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a) -
      s ^ (a - 1) * (x + (1 - x) * s) ^ (-a) =
      ((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a) by ring
  have hsing_val : ∫ s in (0 : ℝ)..1, s ^ (a - 1) * (x + (1 - x) * s) ^ (-a) =
      (1 - x) ^ (-a) * ((∫ w in (0 : ℝ)..(1 - x), (w ^ (a - 1) - 1) / (1 - w)) - Real.log x) := by
    rw [← integral_singular_euler_piece ha hx, ← mul_assoc, ← Real.rpow_add (sub_pos.mpr hx.2),
      neg_add_cancel, Real.rpow_zero, one_mul]
  rw [hswap, show (∫ s in (0 : ℝ)..1, (1 - s) ^ (a - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a)) =
      ∫ s in (0 : ℝ)..1, (((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a) +
        s ^ (a - 1) * (x + (1 - x) * s) ^ (-a)) from
      intervalIntegral.integral_congr fun s _ ↦ by ring,
    intervalIntegral.integral_add hsmooth hsing, hsing_val]

private theorem smooth_euler_integrand_le {a x s : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) (1 / 2)) (hs : s ∈ Ioo (0 : ℝ) 1) :
    ‖((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a)‖ ≤
      2 ^ a * (1 - s) ^ (a - 1) := by
  have hbd_1s := rpow_sub_one_div_one_sub_bounds ha ⟨sub_pos.mpr hs.2, by linarith [hs.1]⟩
  rw [sub_sub_cancel] at hbd_1s
  have h1s_nn : 0 ≤ (1 - s) ^ (a - 1) - 1 :=
    (div_nonneg_iff.mp hbd_1s.1).resolve_right (fun h ↦ by linarith [h.2, hs.1]) |>.1
  have hD_rpow : (x + (1 - x) * s) ^ (-a) ≤ 2 ^ a * s ^ (-a) :=
    (Real.rpow_le_rpow_of_nonpos (half_pos hs.1) (by nlinarith [hx.1, hx.2, hs.1])
      (by linarith [ha.1])).trans_eq <| by
        rw [div_eq_mul_inv, Real.mul_rpow hs.1.le (by norm_num),
          Real.inv_rpow zero_le_two, ← Real.rpow_neg zero_le_two, neg_neg, mul_comm]
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg h1s_nn
    (Real.rpow_nonneg hs.1.le _)) (Real.rpow_nonneg (by nlinarith [hx.1, hx.2, hs.1]) _))]
  have hs_comb : s ^ (a - 1) * s ^ (-a) = s⁻¹ := by
    rw [← Real.rpow_add hs.1, show a - 1 + -a = -1 by ring, Real.rpow_neg_one]
  calc ((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a)
      ≤ ((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (2 ^ a * s ^ (-a)) :=
        mul_le_mul_of_nonneg_left hD_rpow (mul_nonneg h1s_nn (Real.rpow_nonneg hs.1.le _))
    _ = 2 ^ a * (((1 - s) ^ (a - 1) - 1) / s) := by
        rw [div_eq_mul_inv, ← hs_comb]; ring
    _ ≤ 2 ^ a * (1 - s) ^ (a - 1) := mul_le_mul_of_nonneg_left hbd_1s.2 (by positivity)

private theorem tendsto_smooth_euler_piece {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x ↦ ∫ s in (0 : ℝ)..1,
      ((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a))
      (𝓝[>] 0) (𝓝 (Real.digamma 1 - Real.digamma a)) := by
  let bound : ℝ → ℝ := fun s ↦ 2 ^ a * (1 - s) ^ (a - 1)
  have hb_int : IntervalIntegrable bound volume 0 1 :=
    ((intervalIntegrable_rpow_mul_one_sub_rpow (a := 1) (b := a) zero_lt_one ha.1
      ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩).const_mul (2 ^ a)).congr
      fun s _ ↦ by simp [bound]
  have hdct := intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (l := 𝓝[>] (0 : ℝ))
    (F := fun x s ↦ ((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a))
    (f := fun s ↦ ((1 - s) ^ (a - 1) - 1) / s) bound ?_ ?_ hb_int ?_
  · have h := intervalIntegral.integral_comp_sub_left
      (fun w ↦ (w ^ (a - 1) - 1) / (1 - w)) 1 (a := 0) (b := 1)
    simp only [sub_self, sub_zero, sub_sub_cancel] at h
    rwa [h.trans (integral_rpow_sub_one_div_one_sub ha)] at hdct
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
    obtain ⟨h1, h2⟩ := intervalIntegrable_swappedEuler ha ⟨hx.1, by linarith [hx.2]⟩
    have htot : IntervalIntegrable
        (fun s ↦ ((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a)) volume 0 1 :=
      (h1.sub h2).congr fun s _ ↦ by ring
    exact (intervalIntegrable_iff.mp htot).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
    filter_upwards [ae_ne_one] with s hs1 hs
    rw [uIoc_of_le zero_le_one] at hs
    exact smooth_euler_integrand_le ha hx ⟨hs.1, lt_of_le_of_ne hs.2 hs1⟩
  · filter_upwards [ae_ne_one] with s hs1 hs
    rw [uIoc_of_le zero_le_one] at hs
    have hsoo : s ∈ Ioo (0 : ℝ) 1 := ⟨hs.1, lt_of_le_of_ne hs.2 hs1⟩
    have hcont : ContinuousAt (fun x : ℝ ↦
        ((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a)) 0 :=
      continuousAt_const.mul <|
        ContinuousAt.rpow_const (by fun_prop) (Or.inl (by simp [hsoo.1.ne']))
    have hlim := (hcont.continuousWithinAt (s := Ioi (0 : ℝ))).tendsto
    have heval : ((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * ((0 : ℝ) + (1 - 0) * s) ^ (-a) =
        ((1 - s) ^ (a - 1) - 1) / s := by
      simp only [zero_add, sub_zero, one_mul, mul_assoc]
      rw [← Real.rpow_add hsoo.1, show a - 1 + -a = -1 by ring, Real.rpow_neg_one, div_eq_mul_inv]
    rwa [heval] at hlim

private theorem tendsto_slope_mul_log_nhdsGT_zero {f : ℝ → ℝ} {f' : ℝ}
    (hf : HasDerivAt f f' 0) (hf0 : f 0 = 1) :
    Tendsto (fun x : ℝ ↦ (f x - 1) * Real.log x) (𝓝[>] 0) (𝓝 0) := by
  have hslope : Tendsto (fun x : ℝ ↦ (f x - 1) / x) (𝓝[>] 0) (𝓝 f') :=
    ((hasDerivAt_iff_tendsto_slope.mp hf).mono_left
      (nhdsWithin_mono 0 fun x (hx : x ∈ Ioi (0 : ℝ)) ↦ hx.ne')).congr
      fun x ↦ by simp [slope_def_field, hf0]
  have hlog : Tendsto (fun x : ℝ ↦ x * Real.log x) (𝓝[>] 0) (𝓝 0) := by
    simpa using (Real.continuous_mul_log.continuousWithinAt (x := 0) (s := Ioi 0)).tendsto
  have hmul := hslope.mul hlog; rw [mul_zero] at hmul
  refine hmul.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x (hx : 0 < x); field_simp [hx.ne']

private theorem tendsto_eulerZeroBalanced_add_log {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x ↦ eulerZeroBalanced a x + Real.log x) (𝓝[>] 0)
      (𝓝 (2 * (Real.digamma 1 - Real.digamma a))) := by
  have h1x_lim : Tendsto (fun x : ℝ ↦ (1 - x) ^ (-a)) (𝓝[>] 0) (𝓝 1) := by
    have hc : ContinuousAt (fun x : ℝ ↦ (1 - x) ^ (-a)) 0 :=
      ContinuousAt.rpow_const (by fun_prop) (Or.inl (by norm_num))
    simpa using (hc.continuousWithinAt (s := Ioi (0 : ℝ))).tendsto
  have hprim : Tendsto (fun x : ℝ ↦ ∫ w in (0 : ℝ)..(1 - x), (w ^ (a - 1) - 1) / (1 - w))
      (𝓝[>] 0) (𝓝 (Real.digamma 1 - Real.digamma a)) := by
    have hc := intervalIntegral.continuousOn_primitive_interval'
      (intervalIntegrable_rpow_sub_one_div_one_sub ha) (left_mem_uIcc (a := (0 : ℝ)) (b := 1))
    rw [uIcc_of_le zero_le_one] at hc
    have hsub0 : Tendsto (fun x : ℝ ↦ 1 - x) (𝓝[>] 0) (𝓝 1) := by
      simpa using ((by fun_prop : Continuous fun x : ℝ ↦ 1 - x).continuousWithinAt
        (x := 0) (s := Ioi 0)).tendsto
    have hmap : Tendsto (fun x : ℝ ↦ 1 - x) (𝓝[>] 0) (𝓝[Icc 0 1] 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hsub0
        (by filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
            exact ⟨by linarith [hx.2], by linarith [hx.1]⟩)
    have hp := (hc 1 ⟨zero_le_one, le_rfl⟩).tendsto.comp hmap
    rwa [integral_rpow_sub_one_div_one_sub ha] at hp
  have hrem : Tendsto (fun x : ℝ ↦ ((1 - x) ^ (-a) - 1) * Real.log x) (𝓝[>] 0) (𝓝 0) :=
    tendsto_slope_mul_log_nhdsGT_zero
      ((Real.hasDerivAt_rpow_const (p := -a) (Or.inl (by norm_num))).comp 0
        ((hasDerivAt_id 0).const_sub 1)) (by simp)
  have hcomb := ((tendsto_smooth_euler_piece ha).add (h1x_lim.mul hprim)).sub hrem
  rw [one_mul, sub_zero, ← two_mul] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
  rw [eulerZeroBalanced_eq_split ha hx]; ring

private theorem tendsto_realU2_add_log {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x ↦ realU2 a x + Real.log x) (𝓝[>] 0)
      (𝓝 (2 * (Real.digamma 1 - Real.digamma a))) := by
  obtain ⟨B, hB0, hB⟩ := realDigammaCoeff_bound ha
  have hb_bd : ∀ k : ℕ, |realCoeff a k * realDigammaDiff a k| ≤ B * ((k : ℝ) + 1) ^ 0 := fun k ↦ by
    simpa using hB k
  have hv_0 : realV a 0 = 2 * (Real.digamma 1 - Real.digamma a) := by
    rw [realV, tsum_eq_single 0 fun k hk ↦ by simp [zero_pow hk]]; simp [realCoeff, realDigammaDiff]
  have hu1_deriv :=
    hasDerivAt_tsum_pow_of_poly_bound zero_le_one (realCoeff_poly_bound ha) (x := 0) (by simp)
  have hv_cont := (hasDerivAt_tsum_pow_of_poly_bound hB0 hb_bd (x := 0) (by simp)).continuousAt
  have hv_lim : Tendsto (realV a) (𝓝[>] 0) (𝓝 (2 * (Real.digamma 1 - Real.digamma a))) := by
    have h := (hv_cont.continuousWithinAt (s := Ioi (0 : ℝ))).tendsto
    change Tendsto (realV a) (𝓝[>] 0) (𝓝 (realV a 0)) at h; rwa [hv_0] at h
  have hsub := hv_lim.sub (tendsto_slope_mul_log_nhdsGT_zero hu1_deriv (realU1_zero a))
  rw [sub_zero] at hsub
  refine hsub.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x _; dsimp [realU2, realU1]; ring

/-! ### Wronskian constancy and uniqueness on `(0, 1)` -/

private noncomputable def realDiff (a x : ℝ) : ℝ := eulerZeroBalanced a x - realU2 a x
private noncomputable def realWronskian (a x : ℝ) : ℝ :=
  realU1 a x * (x * (1 - x) ^ (2 * a) * deriv (realDiff a) x) -
    (x * (1 - x) ^ (2 * a) * deriv (realU1 a) x) * realDiff a x

private theorem realU1_bounds {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    (∀ {x : ℝ}, x ∈ Ioo (0 : ℝ) 1 → 1 ≤ realU1 a x) ∧
    (∀ {x : ℝ}, x ∈ Ioc (0 : ℝ) (1 / 2) → realU1 a x ≤ 2) := by
  refine ⟨fun {x} hx ↦ ?_, fun {x} hx ↦ ?_⟩
  · have hs := summable_of_poly_bound (realCoeff_poly_bound ha)
      (abs_lt.mpr ⟨by linarith [hx.1], hx.2⟩)
    simpa [realU1, realCoeff] using hs.sum_le_tsum ({0} : Finset ℕ) fun k _ ↦
      mul_nonneg (realCoeff_bounds ha k).1 (pow_nonneg hx.1.le k)
  · have hs := summable_of_poly_bound (realCoeff_poly_bound ha)
      (abs_lt.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩)
    have hgeom : HasSum (fun k : ℕ ↦ (1 / 2 : ℝ) ^ k) 2 := by
      have h := hasSum_geometric_of_lt_one (r := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
      norm_num at h; exact h
    rw [realU1, ← hgeom.tsum_eq]
    refine hs.tsum_le_tsum (fun k ↦ ?_) hgeom.summable
    have hck : realCoeff a k ≤ 1 := by
      have h := (realCoeff_bounds ha k).2; rwa [abs_of_nonneg (realCoeff_bounds ha k).1] at h
    exact (mul_le_mul hck (pow_le_pow_left₀ hx.1.le hx.2 k)
      (pow_nonneg hx.1.le k) zero_le_one).trans_eq (one_mul _)

private theorem differentiableAt_realParts {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (eulerZeroBalanced a) x ∧ DifferentiableAt ℝ (realU1 a) x ∧
    DifferentiableAt ℝ (realU2 a) x ∧ DifferentiableAt ℝ (realDiff a) x := by
  obtain ⟨B, hB0, hB⟩ := realDigammaCoeff_bound ha
  have hb_bd : ∀ k : ℕ, |realCoeff a k * realDigammaDiff a k| ≤ B * ((k : ℝ) + 1) ^ 0 := fun k ↦ by
    simpa using hB k
  have hxa : |x| < 1 := abs_lt.mpr ⟨by linarith [hx.1], hx.2⟩
  have hdE := (hasDerivAt_eulerKernel ha.1 ha.1 ha.1 hx).differentiableAt
  have hdu1 := (hasDerivAt_tsum_pow_of_poly_bound zero_le_one
    (realCoeff_poly_bound ha) hxa).differentiableAt
  have hdu2 : DifferentiableAt ℝ (realU2 a) x :=
    ((Real.differentiableAt_log hx.1.ne').neg.mul hdu1).add
      (hasDerivAt_tsum_pow_of_poly_bound hB0 hb_bd hxa).differentiableAt
  exact ⟨hdE, hdu1, hdu2, hdE.sub hdu2⟩

private theorem hasDerivAt_realWronskian {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (realWronskian a) 0 x := by
  obtain ⟨_, hdu1, _, hdD⟩ := differentiableAt_realParts ha hx
  have hpD : HasDerivAt (fun y ↦ y * (1 - y) ^ (2 * a) * deriv (realDiff a) y)
      (a ^ 2 * (1 - x) ^ (2 * a - 1) * realDiff a x) x := by
    refine ((hasDerivAt_sturmLiouville_eulerZeroBalanced ha hx).sub
      (hasDerivAt_sturmLiouville_realU2 ha hx)).congr_of_eventuallyEq ?_ |>.congr_deriv
      (by dsimp [realDiff]; ring)
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    obtain ⟨hdEy, _, hdu2y, _⟩ := differentiableAt_realParts ha hy
    have hsub : realDiff a = eulerZeroBalanced a - realU2 a := rfl
    rw [hsub, deriv_sub hdEy hdu2y]; simp only [Pi.sub_apply]; ring
  exact ((hdu1.hasDerivAt.mul hpD).sub
    ((hasDerivAt_sturmLiouville_realU1 ha hx).mul hdD.hasDerivAt)).congr_deriv (by ring)

private theorem realWronskian_eq_const {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    realWronskian a x = realWronskian a (1 / 2) :=
  isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
    (fun y hy ↦ (hasDerivAt_realWronskian ha hy).differentiableAt.differentiableWithinAt)
    (fun y hy ↦ (hasDerivAt_realWronskian ha hy).deriv) hx ⟨by norm_num, by norm_num⟩

private theorem hasDerivAt_realDiff_div_realU1 {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y ↦ realDiff a y / realU1 a y)
      (realWronskian a (1 / 2) / (x * (1 - x) ^ (2 * a) * (realU1 a x) ^ 2)) x := by
  obtain ⟨_, hdu1, _, hdD⟩ := differentiableAt_realParts ha hx
  have hu1_pos : 0 < realU1 a x := lt_of_lt_of_le zero_lt_one ((realU1_bounds ha).1 hx)
  have hrp : (1 - x) ^ (2 * a) ≠ 0 := (Real.rpow_pos_of_pos (sub_pos.mpr hx.2) _).ne'
  refine (hdD.hasDerivAt.div hdu1.hasDerivAt hu1_pos.ne').congr_deriv ?_
  rw [← realWronskian_eq_const ha hx]; dsimp [realWronskian]
  field_simp [hu1_pos.ne', hx.1.ne', hrp]

private theorem tendsto_realDiff_div_realU1 {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x ↦ realDiff a x / realU1 a x) (𝓝[>] 0) (𝓝 0) := by
  have hD : Tendsto (realDiff a) (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_eulerZeroBalanced_add_log ha).sub (tendsto_realU2_add_log ha)
    rw [sub_self] at h; exact h.congr fun x ↦ by dsimp [realDiff]; ring
  have hu1_cont := (hasDerivAt_tsum_pow_of_poly_bound zero_le_one
    (realCoeff_poly_bound ha) (x := 0) (by simp)).continuousAt
  have hu1_lim : Tendsto (realU1 a) (𝓝[>] 0) (𝓝 1) := by
    have h := (hu1_cont.continuousWithinAt (s := Ioi (0 : ℝ))).tendsto
    change Tendsto (realU1 a) (𝓝[>] 0) (𝓝 (realU1 a 0)) at h; rwa [realU1_zero a] at h
  have h := hD.div hu1_lim one_ne_zero; rwa [zero_div] at h

private theorem realDiff_div_realU1_sub_ge {a x₀ : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx₀_pos : 0 < x₀) (hx₀_half : x₀ ≤ 1 / 2) :
    |realWronskian a (1 / 2)| * ((4 : ℝ)⁻¹ * (Real.log (1 / 2) - Real.log x₀)) ≤
      |realDiff a (1 / 2) / realU1 a (1 / 2) - realDiff a x₀ / realU1 a x₀| := by
  let C := realWronskian a (1 / 2)
  let w : ℝ → ℝ := fun y ↦ (y * (1 - y) ^ (2 * a) * (realU1 a y) ^ 2)⁻¹
  have hw_cont : ContinuousOn w (uIcc x₀ (1 / 2)) := by
    rw [uIcc_of_le hx₀_half]
    refine ContinuousOn.inv₀ ?_ fun y hy ↦ ?_
    · refine ((continuousOn_id.mul ((by fun_prop : ContinuousOn (fun y : ℝ ↦ 1 - y)
        (Icc x₀ (1 / 2))).rpow_const fun y hy ↦ Or.inl (by linarith [hy.2]))).mul ?_)
      exact ContinuousOn.pow (s := Icc x₀ (1 / 2)) (fun y hy ↦ (differentiableAt_realParts ha
        ⟨lt_of_lt_of_le hx₀_pos hy.1, by linarith [hy.2]⟩).2.1.continuousAt.continuousWithinAt) 2
    · have hy_oo : y ∈ Ioo (0 : ℝ) 1 := ⟨lt_of_lt_of_le hx₀_pos hy.1, by linarith [hy.2]⟩
      have hu1 := lt_of_lt_of_le zero_lt_one ((realU1_bounds ha).1 hy_oo)
      exact mul_ne_zero (mul_ne_zero hy_oo.1.ne'
        (Real.rpow_pos_of_pos (sub_pos.mpr hy_oo.2) _).ne') (pow_ne_zero 2 hu1.ne')
  have hftc : realDiff a (1 / 2) / realU1 a (1 / 2) - realDiff a x₀ / realU1 a x₀ =
      C * ∫ y in x₀..(1 / 2), w y := by
    rw [← intervalIntegral.integral_const_mul]
    exact (intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hx₀_half
      (fun y hy ↦ (hasDerivAt_realDiff_div_realU1 ha
        ⟨lt_of_lt_of_le hx₀_pos hy.1, by linarith [hy.2]⟩).continuousAt.continuousWithinAt)
      (fun y hy ↦ by
        simpa [div_eq_mul_inv, C, w] using
          hasDerivAt_realDiff_div_realU1 ha ⟨hx₀_pos.trans hy.1, by linarith [hy.2]⟩)
      (hw_cont.intervalIntegrable.const_mul C)).symm
  have hw_ge : (4 : ℝ)⁻¹ * (Real.log (1 / 2) - Real.log x₀) ≤ ∫ y in x₀..(1 / 2), w y := by
    rw [← Real.log_div (by norm_num) hx₀_pos.ne', ← integral_inv_of_pos hx₀_pos (by norm_num),
      ← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on hx₀_half
      ((ContinuousOn.inv₀ (s := Icc x₀ (1 / 2)) continuousOn_id fun y hy ↦
        (lt_of_lt_of_le hx₀_pos hy.1).ne').intervalIntegrable_of_Icc hx₀_half |>.const_mul _)
      hw_cont.intervalIntegrable fun y hy ↦ ?_
    have hy0 : 0 < y := lt_of_lt_of_le hx₀_pos hy.1
    have hy_oo : y ∈ Ioo (0 : ℝ) 1 := ⟨hy0, by linarith [hy.2]⟩
    have h1y : (1 - y) ^ (2 * a) ≤ 1 :=
      Real.rpow_le_one (by linarith [hy.2]) (by linarith [hy0]) (by linarith [ha.1])
    have hu1_sq : (realU1 a y) ^ 2 ≤ 4 := by
      nlinarith [(realU1_bounds ha).1 hy_oo, (realU1_bounds ha).2 ⟨hy0, hy.2⟩]
    have hden_pos : 0 < y * (1 - y) ^ (2 * a) * (realU1 a y) ^ 2 :=
      mul_pos (mul_pos hy0 (Real.rpow_pos_of_pos (sub_pos.mpr hy_oo.2) _))
        (pow_pos (lt_of_lt_of_le zero_lt_one ((realU1_bounds ha).1 hy_oo)) 2)
    rw [show (4 : ℝ)⁻¹ * y⁻¹ = (4 * y)⁻¹ by rw [mul_inv_rev, mul_comm]]
    exact inv_anti₀ hden_pos ((mul_le_mul (mul_le_mul_of_nonneg_left h1y hy0.le) hu1_sq
      (sq_nonneg _) (by positivity)).trans_eq (by ring))
  have hlog_nn : 0 ≤ (4 : ℝ)⁻¹ * (Real.log (1 / 2) - Real.log x₀) :=
    mul_nonneg (by norm_num) (sub_nonneg.mpr (Real.log_le_log hx₀_pos hx₀_half))
  rw [hftc, abs_mul, abs_of_nonneg (hlog_nn.trans hw_ge)]
  exact mul_le_mul_of_nonneg_left hw_ge (abs_nonneg C)

private theorem realWronskian_half_eq_zero {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    realWronskian a (1 / 2) = 0 := by
  by_contra hC
  let Q : ℝ → ℝ := fun x ↦ realDiff a x / realU1 a x
  let C := realWronskian a (1 / 2)
  have hC_pos : 0 < |C| := abs_pos.mpr hC
  obtain ⟨δ, hδ0, hδsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp <|
    (tendsto_realDiff_div_realU1 ha) (Ioo_mem_nhds (by norm_num : (-1 : ℝ) < 0)
      (by norm_num : (0 : ℝ) < 1))
  let d := min δ (1 / 4)
  have hd0 : 0 < d := lt_min hδ0 (by norm_num)
  let M := max (-Real.log d + 1) (4 * (|Q (1 / 2)| + 1) / |C| - Real.log (1 / 2) + 1)
  let x₀ := Real.exp (-M)
  have hx₀_pos : 0 < x₀ := Real.exp_pos _
  have hx₀_lt_d : x₀ < d := by
    have hM1 : -Real.log d + 1 ≤ M := le_max_left _ _
    exact (Real.exp_lt_exp.mpr (by linarith)).trans_eq (Real.exp_log hd0)
  have hx₀_half : x₀ ≤ 1 / 2 :=
    le_of_lt (hx₀_lt_d.trans_le ((min_le_right _ _).trans (by norm_num)))
  have hQ_x₀ : |Q x₀| < 1 := abs_lt.mpr (hδsub ⟨hx₀_pos, hx₀_lt_d.trans_le (min_le_left _ _)⟩)
  have hupper : |Q (1 / 2) - Q x₀| < |Q (1 / 2)| + 1 :=
    (abs_sub _ _).trans_lt (by linarith [hQ_x₀])
  have hge := realDiff_div_realU1_sub_ge ha hx₀_pos hx₀_half
  rw [show x₀ = Real.exp (-M) from rfl, Real.log_exp, sub_neg_eq_add] at hge
  have hM_big : 4 * (|Q (1 / 2)| + 1) / |C| - Real.log (1 / 2) + 1 ≤ M := le_max_right _ _
  have h1 : 4 * (|Q (1 / 2)| + 1) < (Real.log (1 / 2) + M) * |C| :=
    (div_lt_iff₀ hC_pos).mp (by linarith)
  linarith

private theorem eulerZeroBalanced_eq_realU2 {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    eulerZeroBalanced a x = realU2 a x := by
  let Q : ℝ → ℝ := fun y ↦ realDiff a y / realU1 a y
  have hQ_deriv : ∀ y ∈ Ioo (0 : ℝ) 1, HasDerivAt Q 0 y := fun y hy ↦ by
    have h := hasDerivAt_realDiff_div_realU1 ha hy
    rwa [realWronskian_half_eq_zero ha, zero_div] at h
  have hQ_const : ∀ y ∈ Ioo (0 : ℝ) 1, Q y = Q (1 / 2) := fun y hy ↦
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun z hz ↦ (hQ_deriv z hz).differentiableAt.differentiableWithinAt)
      (fun z hz ↦ (hQ_deriv z hz).deriv) hy ⟨by norm_num, by norm_num⟩
  have hQ_lim : Tendsto Q (𝓝[>] 0) (𝓝 (Q (1 / 2))) :=
    tendsto_const_nhds.congr' <| by
      filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with y hy using (hQ_const y hy).symm
  have hQ_zero : Q x = 0 :=
    (hQ_const x hx).trans (tendsto_nhds_unique hQ_lim (tendsto_realDiff_div_realU1 ha))
  have hu1_pos : realU1 a x ≠ 0 := (lt_of_lt_of_le zero_lt_one ((realU1_bounds ha).1 hx)).ne'
  exact sub_eq_zero.mp ((div_eq_zero_iff.mp hQ_zero).resolve_right hu1_pos)

/-! ### Complex analytic continuation and the connection theorem -/

private theorem isPreconnected_two_mul_ne_neg_nat :
    IsPreconnected {a : ℂ | ∀ n : ℕ, 2 * a ≠ -(n : ℂ)} := by
  have heq : {a : ℂ | ∀ n : ℕ, 2 * a ≠ -(n : ℂ)} =
      (Set.range fun n : ℕ ↦ -(n : ℂ) / 2)ᶜ := by
    ext a; simp only [Set.mem_ofPred, mem_compl_iff, mem_range, not_exists]
    exact forall_congr' fun n ↦ not_congr
      ⟨fun h ↦ by linear_combination -h / 2, fun h ↦ by linear_combination -2 * h⟩
  rw [heq]
  exact ((Set.countable_range _).isConnected_compl_of_one_lt_rank
    (Complex.rank_real_complex ▸ Nat.one_lt_ofNat)).isPreconnected

private theorem ordinaryHypergeometric_ofReal_eq_zeroBalancedSeries {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    ordinaryHypergeometric (a : ℂ) (a : ℂ) (2 * (a : ℂ)) (1 - (x : ℂ)) =
      zeroBalancedSeries (a : ℂ) (x : ℂ) := by
  have hreal : ₂F₁ a a (2 * a) (1 - x) =
      Real.Gamma (2 * a) / Real.Gamma a ^ 2 * realU2 a x :=
    (ordinaryHypergeometric_one_sub_eq_eulerZeroBalanced ha hx).trans
      (by rw [eulerZeroBalanced_eq_realU2 ha hx])
  have hlhs : Complex.ofReal (₂F₁ a a (2 * a) (1 - x)) =
      ordinaryHypergeometric (a : ℂ) (a : ℂ) (2 * (a : ℂ)) (1 - (x : ℂ)) := by
    simp only [ordinaryHypergeometric, ordinaryHypergeometric_sum_eq, Complex.ofReal_tsum]
    refine tsum_congr fun n ↦ ?_
    have hp2 : (ascPochhammer ℂ n).eval (2 * (a : ℂ)) =
        Complex.ofReal ((ascPochhammer ℝ n).eval (2 * a)) := by
      simpa using eval_ofReal_ascPochhammer (2 * a) n
    simp [eval_ofReal_ascPochhammer, hp2]
  have hx_norm : ‖(x : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg hx.1.le]; exact hx.2
  have hrhs : Complex.ofReal (Real.Gamma (2 * a) / Real.Gamma a ^ 2 * realU2 a x) =
      zeroBalancedSeries (a : ℂ) (x : ℂ) := by
    rw [zeroBalancedSeries_eq_log_mul_add (a : ℂ) hx_norm,
      show Complex.Gamma (2 * (a : ℂ)) = Complex.ofReal (Real.Gamma (2 * a)) by
        simpa using Complex.Gamma_ofReal (2 * a),
      Complex.Gamma_ofReal a, (Complex.ofReal_log hx.1.le).symm]
    simp only [realU2, realU1, realV, realCoeff, realDigammaDiff, Complex.ofReal_mul,
      Complex.ofReal_div, Complex.ofReal_pow, Complex.ofReal_add, Complex.ofReal_neg,
      Complex.ofReal_sub, Complex.ofReal_tsum]
    congr 1; congr 1
    · congr 1; exact tsum_congr fun k ↦ by simp [eval_ofReal_ascPochhammer, div_pow]
    · refine tsum_congr fun k ↦ ?_
      have hd1 : Complex.digamma ((k : ℂ) + 1) = Complex.ofReal (Real.digamma (k + 1)) := by
        simpa using (Complex.digamma_ofReal (x := (k : ℝ) + 1))
      have hda : Complex.digamma ((k : ℂ) + a) = Complex.ofReal (Real.digamma (k + a)) := by
        simpa using (Complex.digamma_ofReal (x := (k : ℝ) + a))
      rw [hd1, hda]; simp [eval_ofReal_ascPochhammer, div_pow]
  exact hlhs.symm.trans (congrArg Complex.ofReal hreal |>.trans hrhs)

private theorem frequently_mem_ofReal_Ioo_nhdsNE_half :
    ∃ᶠ z : ℂ in 𝓝[≠] (1 / 2 : ℂ), ∃ t ∈ Ioo (0 : ℝ) 1, (t : ℂ) = z := by
  let v : ℕ → ℝ := fun n ↦ 1 / 2 + 1 / ((n : ℝ) + 1)
  have hv_ne : ∀ n : ℕ, ((v n : ℝ) : ℂ) ≠ (1 / 2 : ℂ) := fun n h ↦ by
    have hr : v n = 1 / 2 := Complex.ofReal_injective (h.trans (by norm_num))
    have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
    dsimp [v] at hr; linarith
  have hv_lim : Tendsto (fun n : ℕ ↦ ((v n : ℝ) : ℂ)) atTop (𝓝 (1 / 2 : ℂ)) := by
    have hr : Tendsto v atTop (𝓝 (1 / 2 : ℝ)) := by
      have h := (tendsto_const_nhds (x := (1 / 2 : ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat
      rwa [add_zero] at h
    have hc := Complex.continuous_ofReal.continuousAt.tendsto.comp hr
    rwa [show ((1 / 2 : ℝ) : ℂ) = 1 / 2 by norm_num] at hc
  have hv_ne_lim : Tendsto (fun n : ℕ ↦ ((v n : ℝ) : ℂ)) atTop (𝓝[≠] (1 / 2 : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hv_lim (Eventually.of_forall hv_ne)
  have hev : ∀ᶠ n : ℕ in atTop, ∃ t ∈ Ioo (0 : ℝ) 1, (t : ℂ) = v n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hnR : (2 : ℝ) ≤ n := Nat.ofNat_le_cast.mpr hn
    have hle : 1 / ((n : ℝ) + 1) ≤ 1 / 3 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    exact ⟨v n, ⟨by dsimp [v]; positivity, by dsimp [v]; linarith⟩, rfl⟩
  exact hv_ne_lim.frequently hev.frequently

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
  have hxL : x ∈ L := by
    refine ⟨by simpa using hx0, ?_⟩
    rw [mem_ball, dist_eq_norm, norm_sub_rev]; exact hx1
  have hL_slit : L ⊆ ball 0 1 \ {z : ℂ | z.re ≤ 0 ∧ z.im = 0} := fun z hz ↦ by
    refine ⟨hz.1, fun h ↦ ?_⟩
    have h1 : ‖1 - z‖ < 1 := by simpa [mem_ball, dist_eq_norm, norm_sub_rev] using hz.2
    have hre : 1 - z.re ≤ ‖1 - z‖ := by simpa using Complex.re_le_norm (1 - z)
    linarith [h.1]
  have hstage1 : ∀ {t : ℝ}, t ∈ Ioo (0 : ℝ) 1 →
      ordinaryHypergeometric (t : ℂ) (t : ℂ) (2 * (t : ℂ)) (1 - x) =
        zeroBalancedSeries (t : ℂ) x := by
    intro t ht
    have han1 : AnalyticOnNhd ℂ
        (fun z : ℂ ↦ ordinaryHypergeometric (t : ℂ) (t : ℂ) (2 * (t : ℂ)) (1 - z)) L := fun z hz ↦
      (analyticOnNhd_ordinaryHypergeometric ℂ (t : ℂ) (t : ℂ) (2 * (t : ℂ)) (1 - z)
        (by simpa [mem_ball, dist_eq_norm, norm_sub_rev] using hz.2)).comp
        (analyticAt_const.sub analyticAt_id)
    have han2 : AnalyticOnNhd ℂ (zeroBalancedSeries (t : ℂ)) L :=
      (analyticOnNhd_zeroBalancedSeries (t : ℂ)).mono hL_slit
    refine han1.eqOn_of_preconnected_of_frequently_eq han2 hL_conn hhalf_L ?_ hxL
    exact frequently_mem_ofReal_Ioo_nhdsNE_half.mono fun z ⟨s, hs, hsz⟩ ↦ by
      rw [← hsz]; exact ordinaryHypergeometric_ofReal_eq_zeroBalancedSeries ht hs
  have hhalf_Ω : (1 / 2 : ℂ) ∈ {b : ℂ | ∀ n : ℕ, 2 * b ≠ -(n : ℂ)} := fun n hn ↦ by
    have hr := congrArg Complex.re hn; norm_num at hr; linarith [n.cast_nonneg (α := ℝ)]
  refine (analyticOnNhd_ordinaryHypergeometric_param hx1).eqOn_of_preconnected_of_frequently_eq
    (analyticOnNhd_zeroBalancedSeries_left hx0) isPreconnected_two_mul_ne_neg_nat hhalf_Ω ?_ ha
  exact frequently_mem_ofReal_Ioo_nhdsNE_half.mono fun b ⟨t, ht, htb⟩ ↦ by
    rw [← htb]; exact hstage1 ht

/-- The zero-balanced connection formula: when `2a` is not a nonpositive integer, the series is
analytic on the unit disc slit along the closed negative real axis and equals the native
`₂F₁(a, a; 2a; 1 - x)` on the lens `‖x‖ < 1`, `‖1 - x‖ < 1`; by the identity theorem it is the
continuation of the native series across the slit disc (CDT Lemma 5.1.20, p. 672). -/
theorem zero_balanced_connection (a : ℂ) (ha : ∀ n : ℕ, 2 * a ≠ -(n : ℂ)) :
    AnalyticOnNhd ℂ (zeroBalancedSeries a) (ball 0 1 \ {x | x.re ≤ 0 ∧ x.im = 0}) ∧
    ∀ x : ℂ, ‖x‖ < 1 → ‖1 - x‖ < 1 →
      ordinaryHypergeometric a a (2 * a) (1 - x) = zeroBalancedSeries a x :=
  ⟨analyticOnNhd_zeroBalancedSeries a,
    fun _ hx0 hx1 ↦ ordinaryHypergeometric_one_sub_eq_zeroBalancedSeries ha hx0 hx1⟩

end TauCeti
