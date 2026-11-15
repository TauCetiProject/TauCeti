/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Hypergeometric.ZeroBalanced.Basic
public import TauCeti.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Convex
import Mathlib.Analysis.Normed.Module.Connected
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog
import Mathlib.LinearAlgebra.Complex.FiniteDimensional
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Algebra.InfiniteSum.Order
import TauCeti.Analysis.SpecialFunctions.Beta
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.GaussSeries
import TauCeti.Analysis.SpecialFunctions.Pow.Integral

/-!
# The zero-balanced hypergeometric connection formula

When `2a ∉ -ℕ`, `₂F₁(a, a; 2a; 1 - x)` agrees on the lens `‖x‖ < 1`, `‖1 - x‖ < 1` with
`TauCeti.zeroBalancedSeries`, identifying that series as the analytic continuation across
`Metric.ball 0 1 \ (-∞, 0]`. For `a, x ∈ (0, 1)`, Euler's integral and `-log x · u₁(a, x) + v(a, x)`
both solve `(x (1 - x)^(2a) y')' = a² (1 - x)^(2a - 1) y` with `0⁺` asymptotic
`-log x + 2(ψ(1) - ψ(a)) + o(1)`; Wronskian constancy against `u₁` equates them on `(0, 1)`, and
analytic continuation yields `TauCeti.ordinaryHypergeometric_one_sub_eq_zeroBalancedSeries` and
`TauCeti.zero_balanced_connection` (CDT Lemma 5.1.20; NIST DLMF 15.8.10, 15.6.1).
-/

public section

open Complex Filter MeasureTheory Metric Set
open scoped Nat Real Topology

namespace TauCeti

/-! ### Sturm-Liouville differential equation on `(0, 1)` -/

private noncomputable def eulerZeroBalanced (a x : ℝ) : ℝ :=
  ∫ t in (0 : ℝ)..1, t ^ (a - 1) * (1 - t) ^ (a - 1) * (1 - (1 - x) * t) ^ (-a)

private theorem hasDerivAt_mul_one_sub_rpow (a : ℝ) {x : ℝ} (hx : x < 1) :
    HasDerivAt (fun y : ℝ ↦ y * (1 - y) ^ (2 * a))
      ((1 - x) ^ (2 * a) - 2 * a * x * (1 - x) ^ (2 * a - 1)) x := by
  have h2 := (Real.hasDerivAt_rpow_const (p := 2 * a) (Or.inl (sub_pos.mpr hx).ne')).comp x
    ((hasDerivAt_id x).const_sub 1)
  exact ((hasDerivAt_id x).mul h2).congr_deriv (by simp only [Function.comp_apply, id_eq]; ring)

private theorem summable_of_poly_bound {A : ℕ → ℝ} {C : ℝ} {m : ℕ}
    (hA : ∀ k : ℕ, |A k| ≤ C * ((k : ℝ) + 1) ^ m) {r : ℝ} (hr : |r| < 1) :
    Summable fun k : ℕ ↦ A k * r ^ k := by
  have hC := nonneg_of_mul_nonneg_left ((abs_nonneg (A 0)).trans (by simpa using hA 0)) zero_lt_one
  refine ((summable_pow_mul_geometric_of_norm_lt_one m (r := |r|)
    (by simpa [Real.norm_eq_abs] using hr)).mul_left (C * 2 ^ m)).of_norm_bounded_eventually_nat ?_
  filter_upwards [eventually_ge_atTop 1] with k hk
  have hk1 : (k : ℝ) + 1 ≤ 2 * (k : ℝ) := by linarith [(Nat.one_le_cast (α := ℝ)).mpr hk]
  rw [Real.norm_eq_abs, abs_mul, abs_pow]
  exact (mul_le_mul_of_nonneg_right ((hA k).trans (mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (by positivity) hk1 m) hC)) (pow_nonneg (abs_nonneg r) k)).trans_eq
    (by rw [mul_pow]; ring)

private theorem hasDerivAt_tsum_pow_of_poly_bound {A : ℕ → ℝ} {C : ℝ} {m : ℕ}
    (hC : 0 ≤ C) (hA : ∀ k : ℕ, |A k| ≤ C * ((k : ℝ) + 1) ^ m) {x : ℝ} (hx : |x| < 1) :
    HasDerivAt (fun y ↦ ∑' k : ℕ, A k * y ^ k)
      (∑' k : ℕ, ((k : ℝ) + 1) * A (k + 1) * x ^ k) x := by
  let r := (|x| + 1) / 2
  have hr_pos : 0 < r := by dsimp [r]; positivity
  have hr_lt : r < 1 := by dsimp [r]; linarith
  have hxr : x ∈ Ioo (-r) r := abs_lt.mp (by dsimp [r]; linarith)
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
    · simp only [g', u, Nat.add_sub_cancel, Real.norm_eq_abs, abs_mul, abs_pow,
        Nat.cast_add, Nat.cast_one]
      have hk1 : |(k : ℝ) + 1| ≤ (k : ℝ) + 1 + 1 := by rw [abs_of_pos (by positivity)]; linarith
      exact (mul_le_mul (by simpa [Nat.cast_add, Nat.cast_one] using hA (k + 1))
        (mul_le_mul hk1 (pow_le_pow_left₀ (abs_nonneg y) (abs_lt.mpr hy).le k)
          (pow_nonneg (abs_nonneg y) k) (by positivity))
        (by positivity) (by positivity)).trans_eq (by ring)
  refine (hasDerivAt_tsum_of_isPreconnected (g := fun k y ↦ A k * y ^ k) (g' := g') hu
    isOpen_Ioo isPreconnected_Ioo (fun k y _ ↦ ?_) hg'_bd (y₀ := 0) ⟨by linarith, hr_pos⟩
    (summable_of_poly_bound hA (by simp)) hxr).congr_deriv ?_
  · rcases k with _ | k
    · simp [g', hasDerivAt_const]
    · simpa [g', Nat.cast_add, Nat.cast_one] using (hasDerivAt_pow (k + 1) y).const_mul (A (k + 1))
  · rw [(Summable.of_norm_bounded hu fun k ↦ hg'_bd k x hxr).tsum_eq_zero_add]
    simp only [g', Nat.cast_zero, zero_mul, mul_zero, zero_add, Nat.add_sub_cancel,
      Nat.cast_add, Nat.cast_one]
    exact tsum_congr fun k ↦ by ring

private theorem mul_tsum_pow_eq {f : ℕ → ℝ} (hf0 : f 0 = 0) {x : ℝ}
    (hs : Summable fun k : ℕ ↦ f k * x ^ k) :
    x * (∑' k : ℕ, f (k + 1) * x ^ k) = ∑' k : ℕ, f k * x ^ k := by
  rw [hs.tsum_eq_zero_add, hf0, zero_mul, zero_add, ← tsum_mul_left]
  exact tsum_congr fun k ↦ by rw [pow_succ']; ring

private theorem mul_natCast_tsum_pow_eq {A : ℕ → ℝ} {C : ℝ} {m : ℕ}
    (hA : ∀ k : ℕ, |A k| ≤ C * ((k : ℝ) + 1) ^ m) {x : ℝ} (hx : |x| < 1) :
    Summable (fun k : ℕ ↦ (k : ℝ) * A k * x ^ k) ∧
      x * (∑' k : ℕ, ((k : ℝ) + 1) * A (k + 1) * x ^ k) =
        ∑' k : ℕ, (k : ℝ) * A k * x ^ k := by
  have hs : Summable fun k : ℕ ↦ ((k : ℝ) * A k) * x ^ k :=
    summable_of_poly_bound (C := C) (m := m + 1) (fun k ↦ by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg k), pow_succ]
      exact (mul_le_mul (by linarith : (k : ℝ) ≤ (k : ℝ) + 1) (hA k) (abs_nonneg _)
        (by positivity)).trans_eq (by ring)) hx
  have heq := mul_tsum_pow_eq (f := fun k ↦ (k : ℝ) * A k) (by simp) hs
  simp only [Nat.cast_add, Nat.cast_one] at heq
  exact ⟨hs, heq⟩

private theorem hypergeometricOp_tsum_pow {A : ℕ → ℝ} {C : ℝ} {m : ℕ}
    (hC : 0 ≤ C) (hA : ∀ k : ℕ, |A k| ≤ C * ((k : ℝ) + 1) ^ m) (a c : ℝ) {x : ℝ} (hx : |x| < 1) :
    let S := fun y ↦ ∑' k : ℕ, A k * y ^ k
    let S₁ := fun y ↦ ∑' k : ℕ, ((k : ℝ) + 1) * A (k + 1) * y ^ k
    let S₂ := fun y ↦ ∑' k : ℕ, ((k : ℝ) + 2) * ((k : ℝ) + 1) * A (k + 2) * y ^ k
    HasDerivAt S (S₁ x) x ∧ HasDerivAt S₁ (S₂ x) x ∧
      x * (1 - x) * S₂ x + (c - (2 * a + 1) * x) * S₁ x - a ^ 2 * S x =
        ∑' k : ℕ,
          (((k : ℝ) + 1) * ((k : ℝ) + c) * A (k + 1) - ((k : ℝ) + a) ^ 2 * A k) * x ^ k := by
  dsimp only
  let A₁ : ℕ → ℝ := fun k ↦ ((k : ℝ) + 1) * A (k + 1)
  have hA1 : ∀ k : ℕ, |A₁ k| ≤ 2 ^ m * C * ((k : ℝ) + 1) ^ (m + 1) := fun k ↦ by
    have h2 : (k : ℝ) + 2 ≤ 2 * ((k : ℝ) + 1) := by linarith [k.cast_nonneg (α := ℝ)]
    have hAk := hA (k + 1)
    rw [Nat.cast_add, Nat.cast_one, show (k : ℝ) + 1 + 1 = (k : ℝ) + 2 by ring] at hAk
    dsimp [A₁]; rw [abs_mul, abs_of_pos (by positivity), pow_succ]
    exact (mul_le_mul_of_nonneg_left (hAk.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (by positivity) h2 m) hC)) (by positivity)).trans_eq (by rw [mul_pow]; ring)
  have hd1 := hasDerivAt_tsum_pow_of_poly_bound hC hA hx
  have hd2 : HasDerivAt (fun y ↦ ∑' k : ℕ, ((k : ℝ) + 1) * A (k + 1) * y ^ k)
      (∑' k : ℕ, ((k : ℝ) + 2) * ((k : ℝ) + 1) * A (k + 2) * x ^ k) x :=
    (hasDerivAt_tsum_pow_of_poly_bound (mul_nonneg (by positivity) hC) hA1
      hx).congr_deriv (tsum_congr fun k ↦ by dsimp [A₁]; push_cast; ring)
  refine ⟨hd1, hd2, ?_⟩
  have hs0 := summable_of_poly_bound hA hx
  have hs1 := summable_of_poly_bound hA1 hx
  obtain ⟨hs_x1, hx_s1⟩ := mul_natCast_tsum_pow_eq hA hx
  obtain ⟨hs_x2a, hx_s2'⟩ := mul_natCast_tsum_pow_eq hA1 hx
  have hx_s2 : x * (∑' k : ℕ, ((k : ℝ) + 2) * ((k : ℝ) + 1) * A (k + 2) * x ^ k) =
      ∑' k : ℕ, (k : ℝ) * A₁ k * x ^ k := by
    refine (congrArg (x * ·) (tsum_congr fun k ↦ ?_)).trans hx_s2'
    dsimp [A₁]; push_cast; ring
  have hs_x2b : Summable fun k : ℕ ↦ ((k : ℝ) * ((k : ℝ) - 1) * A k) * x ^ k :=
    summable_of_poly_bound (C := C) (m := m + 2) (fun k ↦ by
      have hkk : |(k : ℝ) * ((k : ℝ) - 1)| ≤ ((k : ℝ) + 1) ^ 2 := by
        rcases k with _ | k
        · simp
        · push_cast; rw [add_sub_cancel_right, abs_of_nonneg (by positivity)]; nlinarith
      rw [abs_mul, pow_add]
      exact (mul_le_mul hkk (hA k) (abs_nonneg _)
        (by positivity)).trans_eq (by ring)) hx
  have hx2_s2 : x ^ 2 * (∑' k : ℕ, ((k : ℝ) + 2) * ((k : ℝ) + 1) * A (k + 2) * x ^ k) =
      ∑' k : ℕ, (k : ℝ) * ((k : ℝ) - 1) * A k * x ^ k := by
    have hstep := mul_tsum_pow_eq (f := fun k ↦ (k : ℝ) * ((k : ℝ) - 1) * A k) (by simp) hs_x2b
    rw [sq, mul_assoc, hx_s2, ← hstep]
    exact congrArg (x * ·) (tsum_congr fun k ↦ by dsimp [A₁]; push_cast; ring)
  set s₀ := ∑' k : ℕ, A k * x ^ k
  set s₁ := ∑' k : ℕ, ((k : ℝ) + 1) * A (k + 1) * x ^ k
  set s₂ := ∑' k : ℕ, ((k : ℝ) + 2) * ((k : ℝ) + 1) * A (k + 2) * x ^ k
  rw [show x * (1 - x) * s₂ + (c - (2 * a + 1) * x) * s₁ - a ^ 2 * s₀ =
    (x * s₂) - (x ^ 2 * s₂) + c * s₁ - (2 * a + 1) * (x * s₁) - a ^ 2 * s₀ by ring,
    hx_s2, hx2_s2, hx_s1]
  exact (((((hs_x2a.hasSum.sub hs_x2b.hasSum).add (hs1.hasSum.mul_left c)).sub
    (hs_x1.hasSum.mul_left (2 * a + 1))).sub (hs0.hasSum.mul_left (a ^ 2))).congr_fun
      fun k ↦ by dsimp [A₁]; ring).tsum_eq.symm

private noncomputable def realHyperCoeff (a : ℝ) (k : ℕ) : ℝ :=
  (k !⁻¹ : ℝ) * (ascPochhammer ℝ k).eval a * (ascPochhammer ℝ k).eval a *
    ((ascPochhammer ℝ k).eval (2 * a))⁻¹

private theorem realHyperCoeff_rec_and_bound {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    (∀ k : ℕ, ((k : ℝ) + 1) * ((k : ℝ) + 2 * a) * realHyperCoeff a (k + 1) =
      ((k : ℝ) + a) ^ 2 * realHyperCoeff a k) ∧
    ∀ k : ℕ, |realHyperCoeff a k| ≤ 1 * ((k : ℝ) + 1) ^ 0 := by
  have hrec : ∀ k : ℕ, ((k : ℝ) + 1) * ((k : ℝ) + 2 * a) * realHyperCoeff a (k + 1) =
      ((k : ℝ) + a) ^ 2 * realHyperCoeff a k := fun k ↦ by
    have hP := (ascPochhammer_pos k (2 * a) (by linarith [ha.1])).ne'
    have h2ak : 2 * a + (k : ℝ) ≠ 0 := by linarith [ha.1, k.cast_nonneg (α := ℝ)]
    dsimp [realHyperCoeff]
    rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, Nat.factorial_succ, Nat.cast_mul,
      Nat.cast_add, Nat.cast_one]
    field_simp [hP, h2ak]; ring
  refine ⟨hrec, fun k ↦ ?_⟩
  have hbd : 0 ≤ realHyperCoeff a k ∧ realHyperCoeff a k ≤ 1 := by
    induction k with
    | zero => simp [realHyperCoeff]
    | succ k ih =>
      have hden : 0 < ((k : ℝ) + 1) * ((k : ℝ) + 2 * a) :=
        mul_pos (by positivity) (by linarith [ha.1, k.cast_nonneg (α := ℝ)])
      have heq : realHyperCoeff a (k + 1) =
          realHyperCoeff a k * (((k : ℝ) + a) ^ 2 / (((k : ℝ) + 1) * ((k : ℝ) + 2 * a))) := by
        rw [mul_div_assoc', eq_div_iff hden.ne']; linear_combination hrec k
      have hrat_le : ((k : ℝ) + a) ^ 2 / (((k : ℝ) + 1) * ((k : ℝ) + 2 * a)) ≤ 1 :=
        (div_le_one hden).mpr (by nlinarith [ha.1, ha.2, k.cast_nonneg (α := ℝ)])
      rw [heq]
      exact ⟨mul_nonneg ih.1 (div_nonneg (sq_nonneg _) hden.le),
        (mul_le_mul ih.2 hrat_le (div_nonneg (sq_nonneg _) hden.le) zero_le_one).trans_eq
          (one_mul 1)⟩
  simpa [abs_of_nonneg hbd.1] using hbd.2

private theorem differentiableAt_and_sturmLiouville_eulerZeroBalanced {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (eulerZeroBalanced a) x ∧
    HasDerivAt (fun y ↦ y * (1 - y) ^ (2 * a) * deriv (eulerZeroBalanced a) y)
      (a ^ 2 * (1 - x) ^ (2 * a - 1) * eulerZeroBalanced a x) x := by
  obtain ⟨hrec, hbd⟩ := realHyperCoeff_rec_and_bound ha
  let γ := Real.Gamma a ^ 2 / Real.Gamma (2 * a)
  let S := fun z : ℝ ↦ ∑' k : ℕ, realHyperCoeff a k * z ^ k
  let S₁ := fun z : ℝ ↦ ∑' k : ℕ, ((k : ℝ) + 1) * realHyperCoeff a (k + 1) * z ^ k
  let S₂ := fun z : ℝ ↦ ∑' k : ℕ, ((k : ℝ) + 2) * ((k : ℝ) + 1) * realHyperCoeff a (k + 2) * z ^ k
  have hE_eq {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) : eulerZeroBalanced a y = γ * S (1 - y) := by
    have h : ₂F₁ a a (2 * a) (1 - y) =
        Real.Gamma (2 * a) / Real.Gamma a ^ 2 * eulerZeroBalanced a y :=
      ordinaryHypergeometric_zeroBalanced_eq_integral ha.1
        (abs_lt.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩)
    rw [show ₂F₁ a a (2 * a) (1 - y) = S (1 - y) by
      simpa [ordinaryHypergeometric, S, realHyperCoeff] using
        ordinaryHypergeometric_sum_eq a a (2 * a) (1 - y)] at h
    have hGa := (Real.Gamma_pos_of_pos ha.1).ne'
    have hG2a := (Real.Gamma_pos_of_pos (by linarith [ha.1] : 0 < 2 * a)).ne'
    dsimp [γ]; field_simp [hGa, hG2a] at h ⊢; linarith
  have hd_at {y : ℝ} (hy : y ∈ Ioo (0 : ℝ) 1) :
      HasDerivAt (eulerZeroBalanced a) (-γ * S₁ (1 - y)) y := by
    have hop := hypergeometricOp_tsum_pow zero_le_one hbd a (2 * a)
      (x := 1 - y) (abs_lt.mpr ⟨by linarith [hy.2], by linarith [hy.1]⟩)
    refine (((hop.1.comp y ((hasDerivAt_id y).const_sub 1)).const_mul γ).congr_of_eventuallyEq
      ?_).congr_deriv (by ring)
    filter_upwards [Ioo_mem_nhds hy.1 hy.2] with u hu using hE_eq hu
  refine ⟨(hd_at hx).differentiableAt, ?_⟩
  have hop := hypergeometricOp_tsum_pow zero_le_one hbd a (2 * a)
    (x := 1 - x) (abs_lt.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩)
  have hd2 : HasDerivAt (fun y ↦ -γ * S₁ (1 - y)) (γ * S₂ (1 - x)) x :=
    ((hop.2.1.comp x ((hasDerivAt_id x).const_sub 1)).const_mul (-γ)).congr_deriv (by ring)
  refine (((hasDerivAt_mul_one_sub_rpow a hx.2).mul hd2).congr_of_eventuallyEq ?_).congr_deriv ?_
  · filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy; simp [(hd_at hy).deriv]
  · have hzero := hop.2.2.trans (show _ = (0 : ℝ) by simp [hrec])
    rw [hE_eq hx, show (1 - x) ^ (2 * a) = (1 - x) ^ (2 * a - 1) * (1 - x) by
      rw [← Real.rpow_add_one (sub_pos.mpr hx.2).ne', sub_add_cancel]]
    dsimp only [S, S₁, S₂] at hzero ⊢
    linear_combination γ * (1 - x) ^ (2 * a - 1) * hzero

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
      exact ⟨mul_nonneg ih.1 hstep_nn, (mul_le_mul ih.2
        ((div_le_one (by positivity)).mpr (by linarith [ha.2])) hstep_nn zero_le_one).trans_eq
        (one_mul 1)⟩
  exact ⟨sq_nonneg _, by rw [abs_of_nonneg (sq_nonneg _), realCoeff]; exact pow_le_one₀ hq.1 hq.2⟩

private theorem realCoeff_poly_bound {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (k : ℕ) :
    |realCoeff a k| ≤ 1 * ((k : ℝ) + 1) ^ 0 := by simpa using (realCoeff_bounds ha k).2

private theorem realU1_zero (a : ℝ) : realU1 a 0 = 1 := by
  rw [realU1, tsum_eq_single 0 fun k hk ↦ by simp [zero_pow hk]]; simp [realCoeff]

private theorem realCoeff_recurrence (a : ℝ) (k : ℕ) :
    ((k : ℝ) + 1) * ((k : ℝ) + 1) * realCoeff a (k + 1) = ((k : ℝ) + a) ^ 2 * realCoeff a k := by
  dsimp [realCoeff]
  rw [ascPochhammer_succ_eval, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  field_simp; ring

private theorem realDigammaCoeff_recurrence {a : ℝ} (ha : 0 < a) (k : ℕ) :
    ((k : ℝ) + 1) * ((k : ℝ) + 1) * (realCoeff a (k + 1) * realDigammaDiff a (k + 1)) -
      ((k : ℝ) + a) ^ 2 * (realCoeff a k * realDigammaDiff a k) =
    2 * ((k : ℝ) + 1) * realCoeff a (k + 1) - 2 * ((k : ℝ) + a) * realCoeff a k := by
  have hk1 : (k : ℝ) + 1 ≠ 0 := by positivity
  have hka : (k : ℝ) + a ≠ 0 := by positivity
  have hd : realDigammaDiff a (k + 1) =
      realDigammaDiff a k + 2 / ((k : ℝ) + 1) - 2 / ((k : ℝ) + a) := by
    dsimp [realDigammaDiff]
    rw [Nat.cast_add, Nat.cast_one,
      Real.digamma_apply_add_one (x := (k : ℝ) + 1) (fun m ↦ by
        linarith [m.cast_nonneg (α := ℝ), k.cast_nonneg (α := ℝ)]),
      show (k : ℝ) + 1 + a = ((k : ℝ) + a) + 1 by ring,
      Real.digamma_apply_add_one (x := (k : ℝ) + a) (fun m ↦ by
        linarith [m.cast_nonneg (α := ℝ), k.cast_nonneg (α := ℝ)])]
    ring
  rw [hd]
  have hc := realCoeff_recurrence a k
  have h1 : ((k : ℝ) + 1) * (2 / ((k : ℝ) + 1)) = 2 := mul_div_cancel₀ 2 hk1
  have h2 : ((k : ℝ) + a) * (2 / ((k : ℝ) + a)) = 2 := mul_div_cancel₀ 2 hka
  linear_combination (realDigammaDiff a k - 2 / ((k : ℝ) + a)) * hc +
    ((k : ℝ) + 1) * realCoeff a (k + 1) * h1 - ((k : ℝ) + a) * realCoeff a k * h2

private theorem realDigammaCoeff_bound {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ k : ℕ, |realCoeff a k * realDigammaDiff a k| ≤ B * ((k : ℝ) + 1) ^ 0 := by
  have hd_nn (k : ℕ) : 0 ≤ realDigammaDiff a k :=
    mul_nonneg zero_le_two <| sub_nonneg.mpr <| Real.strictMonoOn_digamma.monotoneOn
      (mem_Ioi.mpr (by linarith [k.cast_nonneg (α := ℝ), ha.1]))
      (mem_Ioi.mpr (by positivity)) (by linarith [ha.2])
  refine ⟨realDigammaDiff a 0, hd_nn 0, fun k ↦ ?_⟩
  have hle : realDigammaDiff a k ≤ realDigammaDiff a 0 := by
    simpa [realDigammaDiff] using mul_le_mul_of_nonneg_left
      (Real.antitone_digamma_nat_add_one_sub_digamma_nat_add ha.1 ha.2.le (Nat.zero_le k))
      zero_le_two
  rw [pow_zero, mul_one, abs_mul, abs_of_nonneg (hd_nn k)]
  exact (mul_le_mul (realCoeff_bounds ha k).2 hle (hd_nn k) zero_le_one).trans_eq (one_mul _)

private theorem hasDerivAt_sturmLiouville_realU1 {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y ↦ y * (1 - y) ^ (2 * a) * deriv (realU1 a) y)
      (a ^ 2 * (1 - x) ^ (2 * a - 1) * realU1 a x) x := by
  have hop := hypergeometricOp_tsum_pow zero_le_one (realCoeff_poly_bound ha) a 1
    (abs_lt.mpr ⟨by linarith [hx.1], hx.2⟩)
  refine (((hasDerivAt_mul_one_sub_rpow a hx.2).mul hop.2.1).congr_of_eventuallyEq
    ?_).congr_deriv ?_
  · filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    have hd : deriv (realU1 a) y = ∑' k : ℕ, ((k : ℝ) + 1) * realCoeff a (k + 1) * y ^ k :=
      (hypergeometricOp_tsum_pow zero_le_one (realCoeff_poly_bound ha) a 1
        (abs_lt.mpr ⟨by linarith [hy.1], hy.2⟩)).1.deriv
    simp [hd]
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
  have hopV := (hypergeometricOp_tsum_pow hB0 hB a 1 hxa).2.2
  dsimp only at hopV
  rw [show realV a x = ∑' k : ℕ, (realCoeff a k * realDigammaDiff a k) * x ^ k from rfl, hopV]
  have hs_u1 := summable_of_poly_bound (realCoeff_poly_bound ha) hxa
  have hs_u1' : Summable fun k : ℕ ↦ ((k : ℝ) + 1) * realCoeff a (k + 1) * x ^ k :=
    summable_of_poly_bound (C := 1) (m := 1) (fun k ↦ by
      rw [abs_mul, abs_of_pos (by positivity), pow_one, one_mul]
      exact (mul_le_mul_of_nonneg_left (realCoeff_bounds ha (k + 1)).2 (by positivity)).trans_eq
        (mul_one _)) hxa
  obtain ⟨hs_xu1', hxu1'_eq⟩ := mul_natCast_tsum_pow_eq (realCoeff_poly_bound ha) hxa
  set s₁ := ∑' k : ℕ, ((k : ℝ) + 1) * realCoeff a (k + 1) * x ^ k
  rw [show 2 * (1 - x) * s₁ - 2 * a * realU1 a x =
    2 * s₁ - 2 * (x * s₁) - 2 * a * realU1 a x by ring, hxu1'_eq]
  exact ((((hs_u1'.hasSum.mul_left 2).sub (hs_xu1'.hasSum.mul_left 2)).sub
    (hs_u1.hasSum.mul_left (2 * a))).congr_fun fun k ↦ by
      linear_combination x ^ k * realDigammaCoeff_recurrence ha.1 k).tsum_eq

private theorem hasDerivAt_sturmLiouville_realU2 {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt (fun y ↦ y * (1 - y) ^ (2 * a) * deriv (realU2 a) y)
      (a ^ 2 * (1 - x) ^ (2 * a - 1) * realU2 a x) x := by
  obtain ⟨B, hB0, hB⟩ := realDigammaCoeff_bound ha
  have hxa : |x| < 1 := abs_lt.mpr ⟨by linarith [hx.1], hx.2⟩
  have hop1 := hypergeometricOp_tsum_pow zero_le_one (realCoeff_poly_bound ha) a 1 hxa
  have hopV := hypergeometricOp_tsum_pow hB0 hB a 1 hxa
  let u1' := fun y : ℝ ↦ ∑' k : ℕ, ((k : ℝ) + 1) * realCoeff a (k + 1) * y ^ k
  let v' := fun y : ℝ ↦
    ∑' k : ℕ, ((k : ℝ) + 1) * (realCoeff a (k + 1) * realDigammaDiff a (k + 1)) * y ^ k
  let u2' := fun y : ℝ ↦ -y⁻¹ * realU1 a y - Real.log y * u1' y + v' y
  have hderiv_eq : deriv (realU2 a) =ᶠ[𝓝 x] u2' := by
    filter_upwards [Ioo_mem_nhds hx.1 hx.2] with y hy
    have hya : |y| < 1 := abs_lt.mpr ⟨by linarith [hy.1], hy.2⟩
    refine (((((Real.hasDerivAt_log hy.1.ne').neg.mul
      (hypergeometricOp_tsum_pow zero_le_one (realCoeff_poly_bound ha) a 1 hya).1).add
      (hypergeometricOp_tsum_pow hB0 hB a 1 hya).1).congr_of_eventuallyEq
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
    have hxix := mul_inv_cancel₀ hx.1.ne'
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
  have hcont : ContinuousOn (fun w : ℝ ↦ (w ^ (a - 1) - 1) / (1 - w)) (Ioo 0 1) :=
    ((ContinuousOn.rpow_const (s := Ioo (0 : ℝ) 1) continuousOn_id
      fun w hw ↦ Or.inl hw.1.ne').sub continuousOn_const).div
      (continuousOn_const.sub continuousOn_id) fun w hw ↦ sub_ne_zero.mpr hw.2.ne'
  refine hdom.mono' (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with w hw
  rw [Real.norm_eq_abs, abs_of_nonneg (rpow_sub_one_div_one_sub_bounds ha hw).1]
  exact (rpow_sub_one_div_one_sub_bounds ha hw).2

private theorem integral_finset_rpow_sub_pow {a : ℝ} (ha : 0 < a) (N : ℕ) :
    ∫ w in (0 : ℝ)..1, (∑ k ∈ Finset.range N, (w ^ ((k : ℝ) + a - 1) - w ^ k)) =
      ∑ k ∈ Finset.range N, (1 / ((k : ℝ) + a) - 1 / ((k : ℝ) + 1)) := by
  rw [intervalIntegral.integral_finsetSum fun k _ ↦
    (intervalIntegral.intervalIntegrable_rpow' (by linarith [k.cast_nonneg (α := ℝ)])).sub
      (Continuous.intervalIntegrable (by fun_prop) 0 1)]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  have hka : (0 : ℝ) < (k : ℝ) + a := by linarith [k.cast_nonneg (α := ℝ)]
  rw [intervalIntegral.integral_sub (intervalIntegral.intervalIntegrable_rpow' (by linarith))
      (Continuous.intervalIntegrable (by fun_prop) 0 1),
    integral_rpow (Or.inl (by linarith)), integral_pow,
    show (k : ℝ) + a - 1 + 1 = (k : ℝ) + a by ring, Real.one_rpow, Real.zero_rpow hka.ne']
  simp [zero_pow (Nat.succ_ne_zero k)]

private theorem integral_rpow_sub_one_div_one_sub {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    ∫ w in (0 : ℝ)..1, (w ^ (a - 1) - 1) / (1 - w) = Real.digamma 1 - Real.digamma a := by
  let F : ℕ → ℝ → ℝ := fun N w ↦ ∑ k ∈ Finset.range N, (w ^ ((k : ℝ) + a - 1) - w ^ k)
  have hrpow_mul {w : ℝ} (hw : 0 < w) (k : ℕ) :
      w ^ ((k : ℝ) + a - 1) - w ^ k = (w ^ (a - 1) - 1) * w ^ k := by
    rw [sub_mul, one_mul, show (k : ℝ) + a - 1 = (a - 1) + k by ring, Real.rpow_add hw,
      Real.rpow_natCast]
  have hsum_w {w : ℝ} (hw : w ∈ Ioo (0 : ℝ) 1) :
      HasSum (fun k : ℕ ↦ w ^ ((k : ℝ) + a - 1) - w ^ k) ((w ^ (a - 1) - 1) / (1 - w)) :=
    div_eq_mul_inv (w ^ (a - 1) - 1) (1 - w) ▸
      ((hasSum_geometric_of_lt_one hw.1.le hw.2).mul_left (w ^ (a - 1) - 1)).congr_fun
        fun k ↦ hrpow_mul hw.1 k
  have hdct : Tendsto (fun N ↦ ∫ w in (0 : ℝ)..1, F N w) atTop
      (𝓝 (∫ w in (0 : ℝ)..1, (w ^ (a - 1) - 1) / (1 - w))) := by
    refine intervalIntegral.tendsto_integral_filter_of_dominated_convergence
      (F := F) (fun w ↦ w ^ (a - 1)) ?_ ?_
      (intervalIntegral.intervalIntegrable_rpow' (by linarith [ha.1])) ?_
    · refine Eventually.of_forall fun N ↦ ?_
      have hint : IntervalIntegrable
          (∑ k ∈ Finset.range N, fun w : ℝ ↦ w ^ ((k : ℝ) + a - 1) - w ^ k) volume 0 1 :=
        IntervalIntegrable.sum (Finset.range N) fun k _ ↦
          (intervalIntegral.intervalIntegrable_rpow'
            (by linarith [k.cast_nonneg (α := ℝ), ha.1])).sub
            (Continuous.intervalIntegrable (by fun_prop) 0 1)
      exact (intervalIntegrable_iff.mp hint).aestronglyMeasurable.congr
        (Eventually.of_forall fun w ↦ Finset.sum_apply w _ _)
    · refine Eventually.of_forall fun N ↦ ?_
      filter_upwards [ae_ne_one] with w hw1 hw
      rw [uIoc_of_le zero_le_one] at hw
      have hwoo : w ∈ Ioo (0 : ℝ) 1 := ⟨hw.1, lt_of_le_of_ne hw.2 hw1⟩
      have h1w : 1 ≤ w ^ (a - 1) := by
        simpa using Real.rpow_le_rpow_of_exponent_ge hwoo.1 hwoo.2.le
          (by linarith [ha.2] : a - 1 ≤ 0)
      have hterm_nn (k : ℕ) : 0 ≤ w ^ ((k : ℝ) + a - 1) - w ^ k :=
        (hrpow_mul hwoo.1 k).symm ▸ mul_nonneg (sub_nonneg.mpr h1w) (pow_nonneg hwoo.1.le k)
      rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun k _ ↦ hterm_nn k)]
      exact (sum_le_hasSum (Finset.range N) (fun k _ ↦ hterm_nn k) (hsum_w hwoo)).trans
        (rpow_sub_one_div_one_sub_bounds ha hwoo).2
    · filter_upwards [ae_ne_one] with w hw1 hw
      rw [uIoc_of_le zero_le_one] at hw
      exact (hsum_w ⟨hw.1, lt_of_le_of_ne hw.2 hw1⟩).tendsto_sum_nat
  dsimp only [F] at hdct
  simp_rw [integral_finset_rpow_sub_pow ha.1] at hdct
  have hd := Real.digamma_eq_gaussSeries (x := a) fun m ↦ by linarith [m.cast_nonneg (α := ℝ), ha.1]
  have hgauss := (Real.summable_gaussSeries a).hasSum.neg
  rw [show -(∑' n : ℕ, (1 / ((n : ℝ) + 1) - 1 / (a + n))) =
    Real.digamma 1 - Real.digamma a by rw [Real.digamma_one]; linarith] at hgauss
  exact tendsto_nhds_unique hdct (hgauss.congr_fun fun k ↦ by ring).tendsto_sum_nat

private theorem integral_singular_euler_piece {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    (1 - x) ^ a * (∫ s in (0 : ℝ)..1, s ^ (a - 1) * (x + (1 - x) * s) ^ (-a)) =
      (∫ w in (0 : ℝ)..(1 - x), (w ^ (a - 1) - 1) / (1 - w)) - Real.log x := by
  let u : ℝ → ℝ := fun s ↦ (1 - x) * s / (x + (1 - x) * s)
  let u' : ℝ → ℝ := fun s ↦ x * (1 - x) / (x + (1 - x) * s) ^ 2
  let g : ℝ → ℝ := fun w ↦ w ^ (a - 1) / (1 - w)
  have hu_cont : ContinuousOn u (uIcc 0 1) := ContinuousOn.div (by fun_prop) (by fun_prop)
    fun s hs ↦ (by rw [uIcc_of_le zero_le_one] at hs; nlinarith [hx.1, hx.2, hs.1, hs.2] :
      0 < x + (1 - x) * s).ne'
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
    have h := intervalIntegral.integral_comp_sub_left (fun u : ℝ ↦ u⁻¹) 1 (a := 0) (b := 1 - x)
    simp only [sub_sub_cancel, sub_zero] at h
    rw [h, integral_inv_of_pos hx.1 zero_lt_one, one_div, Real.log_inv]
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
  have hdiff : ∫ s in (0 : ℝ)..1,
      ((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a) =
      eulerZeroBalanced a x - ∫ s in (0 : ℝ)..1, s ^ (a - 1) * (x + (1 - x) * s) ^ (-a) := by
    rw [hswap, ← intervalIntegral.integral_sub htot hsing]
    exact intervalIntegral.integral_congr fun s _ ↦ by ring
  have hsing_val : ∫ s in (0 : ℝ)..1, s ^ (a - 1) * (x + (1 - x) * s) ^ (-a) =
      (1 - x) ^ (-a) * ((∫ w in (0 : ℝ)..(1 - x), (w ^ (a - 1) - 1) / (1 - w)) - Real.log x) := by
    rw [← integral_singular_euler_piece ha hx, ← mul_assoc, ← Real.rpow_add (sub_pos.mpr hx.2),
      neg_add_cancel, Real.rpow_zero, one_mul]
  linarith

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
    _ = 2 ^ a * (((1 - s) ^ (a - 1) - 1) / s) := by rw [div_eq_mul_inv, ← hs_comb]; ring
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
    exact (intervalIntegrable_iff.mp ((h1.sub h2).congr fun s _ ↦ by ring)).aestronglyMeasurable
  · filter_upwards [Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)] with x hx
    filter_upwards [ae_ne_one] with s hs1 hs
    rw [uIoc_of_le zero_le_one] at hs
    exact smooth_euler_integrand_le ha hx ⟨hs.1, lt_of_le_of_ne hs.2 hs1⟩
  · refine Eventually.of_forall fun s hs ↦ ?_
    rw [uIoc_of_le zero_le_one] at hs
    have hcont : ContinuousAt (fun x : ℝ ↦
        ((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (x + (1 - x) * s) ^ (-a)) 0 :=
      continuousAt_const.mul <| ContinuousAt.rpow_const (by fun_prop) (Or.inl (by simp [hs.1.ne']))
    have hlim := (hcont.continuousWithinAt (s := Ioi (0 : ℝ))).tendsto
    rwa [show ((1 - s) ^ (a - 1) - 1) * s ^ (a - 1) * (0 + (1 - 0) * s) ^ (-a) =
      ((1 - s) ^ (a - 1) - 1) / s by
        rw [zero_add, sub_zero, one_mul, mul_assoc, ← Real.rpow_add hs.1,
          show a - 1 + -a = -1 by ring, Real.rpow_neg_one, div_eq_mul_inv]] at hlim

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
    simpa using ((ContinuousAt.rpow_const (by fun_prop)
      (Or.inl (by norm_num : (1 : ℝ) - 0 ≠ 0))).continuousWithinAt (s := Ioi (0 : ℝ))).tendsto
  have hprim : Tendsto (fun x : ℝ ↦ ∫ w in (0 : ℝ)..(1 - x), (w ^ (a - 1) - 1) / (1 - w))
      (𝓝[>] 0) (𝓝 (Real.digamma 1 - Real.digamma a)) := by
    have hc := intervalIntegral.continuousOn_primitive_interval'
      (intervalIntegrable_rpow_sub_one_div_one_sub ha) (left_mem_uIcc (a := (0 : ℝ)) (b := 1))
    rw [uIcc_of_le zero_le_one] at hc
    have hmap : Tendsto (fun x : ℝ ↦ 1 - x) (𝓝[>] 0) (𝓝[Icc 0 1] 1) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        (by simpa using ((by fun_prop : Continuous fun x : ℝ ↦ 1 - x).continuousWithinAt
          (x := 0) (s := Ioi 0)).tendsto)
        (by filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
            exact ⟨by linarith [hx.2], by linarith [hx.1]⟩)
    have hcomp := (hc 1 ⟨zero_le_one, le_rfl⟩).tendsto.comp hmap
    rw [integral_rpow_sub_one_div_one_sub ha] at hcomp
    exact hcomp
  have hrem := tendsto_slope_mul_log_nhdsGT_zero (f := fun x : ℝ ↦ (1 - x) ^ (-a))
    (((Real.hasDerivAt_rpow_const (p := -a) (Or.inl (by norm_num))).comp 0
      ((hasDerivAt_id 0).const_sub 1))) (by simp)
  have hcomb := ((tendsto_smooth_euler_piece ha).add (h1x_lim.mul hprim)).sub hrem
  rw [one_mul, sub_zero, ← two_mul] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with x hx
  rw [eulerZeroBalanced_eq_split ha hx]; ring

private theorem tendsto_realU2_add_log {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    Tendsto (fun x ↦ realU2 a x + Real.log x) (𝓝[>] 0)
      (𝓝 (2 * (Real.digamma 1 - Real.digamma a))) := by
  obtain ⟨B, hB0, hB⟩ := realDigammaCoeff_bound ha
  have hv_0 : realV a 0 = 2 * (Real.digamma 1 - Real.digamma a) := by
    rw [realV, tsum_eq_single 0 fun k hk ↦ by simp [zero_pow hk]]; simp [realCoeff, realDigammaDiff]
  have hu1_deriv :=
    hasDerivAt_tsum_pow_of_poly_bound zero_le_one (realCoeff_poly_bound ha) (x := 0) (by simp)
  have hv_cont := (hasDerivAt_tsum_pow_of_poly_bound hB0 hB (x := 0) (by simp)).continuousAt
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
    have hck := (abs_of_nonneg (realCoeff_bounds ha k).1) ▸ (realCoeff_bounds ha k).2
    exact (mul_le_mul hck (pow_le_pow_left₀ hx.1.le hx.2 k)
      (pow_nonneg hx.1.le k) zero_le_one).trans_eq (one_mul _)

private theorem differentiableAt_realParts {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    DifferentiableAt ℝ (eulerZeroBalanced a) x ∧ DifferentiableAt ℝ (realU1 a) x ∧
    DifferentiableAt ℝ (realU2 a) x ∧ DifferentiableAt ℝ (realDiff a) x := by
  obtain ⟨B, hB0, hB⟩ := realDigammaCoeff_bound ha
  have hxa : |x| < 1 := abs_lt.mpr ⟨by linarith [hx.1], hx.2⟩
  have hdE := (differentiableAt_and_sturmLiouville_eulerZeroBalanced ha hx).1
  have hdu1 := (hasDerivAt_tsum_pow_of_poly_bound zero_le_one
    (realCoeff_poly_bound ha) hxa).differentiableAt
  have hdu2 : DifferentiableAt ℝ (realU2 a) x :=
    ((Real.differentiableAt_log hx.1.ne').neg.mul hdu1).add
      (hasDerivAt_tsum_pow_of_poly_bound hB0 hB hxa).differentiableAt
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
  have hrp := (Real.rpow_pos_of_pos (sub_pos.mpr hx.2) (2 * a)).ne'
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

private theorem realWronskian_half_eq_zero {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) :
    realWronskian a (1 / 2) = 0 := by
  by_contra hC
  let C := realWronskian a (1 / 2)
  let Q : ℝ → ℝ := fun y ↦ realDiff a y / realU1 a y
  let g : ℝ → ℝ := fun y ↦ C * Q y - (C ^ 2 / 4) * Real.log y
  have hdg (y : ℝ) (hy : y ∈ Ioc (0 : ℝ) (1 / 2)) :
      HasDerivAt g (C ^ 2 / (y * (1 - y) ^ (2 * a) * (realU1 a y) ^ 2) - C ^ 2 / (4 * y)) y :=
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
    have hu1_sq : (realU1 a y) ^ 2 ≤ 4 := by
      nlinarith [(realU1_bounds ha).1 hy_oo, (realU1_bounds ha).2 hy']
    have hden := mul_pos (mul_pos hy'.1 (Real.rpow_pos_of_pos (sub_pos.mpr hy_oo.2) (2 * a)))
      (pow_pos (lt_of_lt_of_le zero_lt_one ((realU1_bounds ha).1 hy_oo)) 2)
    exact sub_nonneg.mpr <| div_le_div_of_nonneg_left (sq_nonneg C) hden <|
      (mul_le_mul (mul_le_of_le_one_right hy'.1.le h1y) hu1_sq (sq_nonneg _)
        hy'.1.le).trans_eq (by ring)
  have hC2 : 0 < C ^ 2 / 4 := div_pos (sq_pos_of_ne_zero hC) (by norm_num)
  have hg_top : Tendsto g (𝓝[>] 0) atTop := by
    have h1 : Tendsto (fun y ↦ C * Q y) (𝓝[>] 0) (𝓝 0) := by
      simpa using (tendsto_realDiff_div_realU1 ha).const_mul C
    have h2 : Tendsto (fun y ↦ (C ^ 2 / 4) * -Real.log y) (𝓝[>] 0) atTop :=
      Tendsto.const_mul_atTop hC2 (tendsto_neg_atBot_atTop.comp Real.tendsto_log_nhdsGT_zero)
    exact (h1.add_atTop h2).congr fun y ↦ by dsimp [g]; ring
  obtain ⟨x, hgx, hx_mem⟩ := (((hg_top.eventually (eventually_gt_atTop (g (1 / 2)))).and
    (Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1 / 2)))).exists
  exact not_le_of_gt hgx (hmono ⟨hx_mem.1, hx_mem.2.le⟩ ⟨by norm_num, le_rfl⟩ hx_mem.2.le)

private theorem eulerZeroBalanced_eq_realU2 {a x : ℝ}
    (ha : a ∈ Ioo (0 : ℝ) 1) (hx : x ∈ Ioo (0 : ℝ) 1) :
    eulerZeroBalanced a x = realU2 a x := by
  let Q : ℝ → ℝ := fun y ↦ realDiff a y / realU1 a y
  have hQ_deriv (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1) : HasDerivAt Q 0 y := by
    have h := hasDerivAt_realDiff_div_realU1 ha hy
    rwa [realWronskian_half_eq_zero ha, zero_div] at h
  have hQ_const (y : ℝ) (hy : y ∈ Ioo (0 : ℝ) 1) : Q y = Q (1 / 2) :=
    isOpen_Ioo.is_const_of_deriv_eq_zero isPreconnected_Ioo
      (fun z hz ↦ (hQ_deriv z hz).differentiableAt.differentiableWithinAt)
      (fun z hz ↦ (hQ_deriv z hz).deriv) hy ⟨by norm_num, by norm_num⟩
  have hQ_lim : Tendsto Q (𝓝[>] 0) (𝓝 (Q (1 / 2))) :=
    tendsto_const_nhds.congr' <| by
      filter_upwards [Ioo_mem_nhdsGT zero_lt_one] with y hy using (hQ_const y hy).symm
  have hQ_zero :=
    (hQ_const x hx).trans (tendsto_nhds_unique hQ_lim (tendsto_realDiff_div_realU1 ha))
  exact sub_eq_zero.mp ((div_eq_zero_iff.mp hQ_zero).resolve_right
    (lt_of_lt_of_le zero_lt_one ((realU1_bounds ha).1 hx)).ne')

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
    (ordinaryHypergeometric_zeroBalanced_eq_integral ha.1
      (abs_lt.mpr ⟨by linarith [hx.2], by linarith [hx.1]⟩)).trans
      (congrArg (Real.Gamma (2 * a) / Real.Gamma a ^ 2 * ·) (eulerZeroBalanced_eq_realU2 ha hx))
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
  have hv_ne (n : ℕ) : ((v n : ℝ) : ℂ) ≠ (1 / 2 : ℂ) := fun h ↦ by
    have hr : v n = 1 / 2 := Complex.ofReal_injective (h.trans (by norm_num))
    dsimp [v] at hr; linarith [show (0 : ℝ) < 1 / ((n : ℝ) + 1) by positivity]
  have hr : Tendsto v atTop (𝓝 (1 / 2 : ℝ)) := by
    have h := (tendsto_const_nhds (x := (1 / 2 : ℝ))).add tendsto_one_div_add_atTop_nhds_zero_nat
    rw [add_zero] at h; exact h.congr fun n ↦ by simp [v]
  have hv_lim : Tendsto (fun n : ℕ ↦ ((v n : ℝ) : ℂ)) atTop (𝓝 (1 / 2 : ℂ)) := by
    have h := (Complex.continuous_ofReal.continuousAt (x := (1 / 2 : ℝ))).tendsto.comp hr
    rwa [show Complex.ofReal (1 / 2 : ℝ) = (1 / 2 : ℂ) by push_cast; rfl] at h
  have hv_ne_lim : Tendsto (fun n : ℕ ↦ ((v n : ℝ) : ℂ)) atTop (𝓝[≠] (1 / 2 : ℂ)) :=
    tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ hv_lim (Eventually.of_forall hv_ne)
  have hev : ∀ᶠ n : ℕ in atTop, ∃ t ∈ Ioo (0 : ℝ) 1, (t : ℂ) = v n := by
    filter_upwards [eventually_ge_atTop 2] with n hn
    have hn2 : (2 : ℝ) ≤ n := Nat.ofNat_le_cast.mpr hn
    have hle := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 3) (by linarith : (3 : ℝ) ≤ n + 1)
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
  have hxL : x ∈ L := ⟨by simpa using hx0, by rwa [mem_ball, dist_eq_norm, norm_sub_rev]⟩
  have hL_slit : L ⊆ ball 0 1 \ {z : ℂ | z.re ≤ 0 ∧ z.im = 0} := fun z hz ↦ by
    refine ⟨hz.1, fun h ↦ ?_⟩
    have h1 : ‖1 - z‖ < 1 := by simpa [mem_ball, dist_eq_norm, norm_sub_rev] using hz.2
    have hre : 1 - z.re ≤ ‖1 - z‖ := by simpa using Complex.re_le_norm (1 - z)
    linarith [h.1]
  have hstage1 {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) :
      ordinaryHypergeometric (t : ℂ) (t : ℂ) (2 * (t : ℂ)) (1 - x) =
        zeroBalancedSeries (t : ℂ) x := by
    have han1 : AnalyticOnNhd ℂ
        (fun z : ℂ ↦ ordinaryHypergeometric (t : ℂ) (t : ℂ) (2 * (t : ℂ)) (1 - z)) L := fun z hz ↦
      (analyticOnNhd_ordinaryHypergeometric ℂ (t : ℂ) (t : ℂ) (2 * (t : ℂ)) (1 - z)
        (by simpa [mem_ball, dist_eq_norm, norm_sub_rev] using hz.2)).comp
        (analyticAt_const.sub analyticAt_id)
    exact han1.eqOn_of_preconnected_of_frequently_eq
      ((analyticOnNhd_zeroBalancedSeries (t : ℂ)).mono hL_slit) hL_conn hhalf_L
      (frequently_mem_ofReal_Ioo_nhdsNE_half.mono fun z ⟨s, hs, hsz⟩ ↦
        hsz ▸ ordinaryHypergeometric_ofReal_eq_zeroBalancedSeries ht hs) hxL
  have hhalf_Ω : (1 / 2 : ℂ) ∈ {b : ℂ | ∀ n : ℕ, 2 * b ≠ -(n : ℂ)} := fun n hn ↦ by
    have hr := congrArg Complex.re hn; norm_num at hr; linarith [n.cast_nonneg (α := ℝ)]
  exact (analyticOnNhd_ordinaryHypergeometric_zeroBalanced_left
    hx1).eqOn_of_preconnected_of_frequently_eq
    (analyticOnNhd_zeroBalancedSeries_left hx0) isPreconnected_two_mul_ne_neg_nat hhalf_Ω
    (frequently_mem_ofReal_Ioo_nhdsNE_half.mono fun b ⟨t, ht, htb⟩ ↦ htb ▸ hstage1 ht) ha

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
