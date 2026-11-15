/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
public import Mathlib.RingTheory.Polynomial.Pochhammer
public import TauCeti.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.Analysis.Complex.SlitPlane
import TauCeti.Analysis.SpecialFunctions.Beta
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.GaussSeries
import TauCeti.Analysis.SpecialFunctions.Gamma.Order
import TauCeti.Analysis.SpecialFunctions.Pow.Integral

/-!
# The zero-balanced hypergeometric logarithmic series and its remainder estimates

Specializing DLMF 15.8.10 to `m = 0` and `b = a` gives `TauCeti.zeroBalancedSeries a x`,
`Γ(2a) / Γ(a)² * ∑' k, (a)_k² / (k!)² * x^k * (-log x + 2(ψ(k + 1) - ψ(k + a)))`, written with
Mathlib's principal logarithm `Complex.log`, together with its `k ≥ 1` inner tail
`TauCeti.zeroBalancedTail`:

* `zeroBalancedSeries` is analytic on `Metric.ball 0 1 \ {x | x.re ≤ 0 ∧ x.im = 0}`, analytic in `a`
  away from `2a ∈ -ℕ` for `‖x‖ < 1` (as is `₂F₁(a, a; 2a; z)` for `‖z‖ < 1`), and on `0 < ‖x‖ < 1`
  equals its limit from `{z | 0 < z.im}`; for real `0 < a` and `|z| < 1`, `₂F₁(a, a; 2a; z)` admits
  Euler's integral representation (`ordinaryHypergeometric_zeroBalanced_eq_integral`).
* Splitting off `k = 0` writes `zeroBalancedSeries a x` on `‖x‖ < 1` as
  `Γ(2a) / Γ(a)² * (-log x - 2γ - 2ψ(a) + zeroBalancedTail a x)` with explicit
  `O(‖x‖(1 + ‖log x‖) / (1 - ‖x‖))` bounds on `zeroBalancedTail` and its `a`-derivatives.

The lens identity with `₂F₁(a, a; 2a; 1 - x)` is proved in
`TauCeti.Analysis.SpecialFunctions.Hypergeometric.ZeroBalanced.Connection`.

## References

* F. Calegari, V. Dimitrov and Y. Tang, *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. 38 (2025), Lemma 5.1.20 (p. 672) and Lemma 5.2.9 (p. 676).
* [NIST DLMF, 15.8.10](https://dlmf.nist.gov/15.8.E10), [15.6.1](https://dlmf.nist.gov/15.6.E1).
-/

public section

open Complex Filter MeasureTheory Metric Set
open scoped Nat Real Topology

namespace TauCeti

/-! ### Definitions and basic series properties -/

/-- The zero-balanced hypergeometric series at parameter `a`, using Mathlib's principal logarithm:
`Γ(2a) / Γ(a)² · ∑' k, (a)_k² / (k!)² · x^k · (-log x + 2(ψ(k + 1) - ψ(k + a)))`
(CDT Lemma 5.1.20; DLMF 15.8.10 at `m = 0` and `b = a`). Outside the open unit disc the infinite
sum takes its junk value. -/
noncomputable def zeroBalancedSeries (a x : ℂ) : ℂ :=
  Complex.Gamma (2 * a) / Complex.Gamma a ^ 2 *
    ∑' k : ℕ, (Polynomial.eval a (ascPochhammer ℂ k)) ^ 2 / ((k.factorial : ℂ) ^ 2) *
      x ^ k * (-Complex.log x + 2 * (Complex.digamma (k + 1) - Complex.digamma (k + a)))

/-- Unfolding lemma for `zeroBalancedSeries`. -/
theorem zeroBalancedSeries_def (a x : ℂ) :
    zeroBalancedSeries a x =
      Complex.Gamma (2 * a) / Complex.Gamma a ^ 2 *
        ∑' k : ℕ, (Polynomial.eval a (ascPochhammer ℂ k)) ^ 2 / ((k.factorial : ℂ) ^ 2) *
          x ^ k * (-Complex.log x + 2 * (Complex.digamma (k + 1) - Complex.digamma (k + a))) := by
  rfl

/-- The `k ≥ 1` inner tail of `zeroBalancedSeries`, indexed by `k ↦ k + 1` without the Gamma
prefactor. -/
noncomputable def zeroBalancedTail (a x : ℂ) : ℂ :=
  ∑' k : ℕ, (Polynomial.eval a (ascPochhammer ℂ (k + 1))) ^ 2 / (((k + 1).factorial : ℂ) ^ 2) *
    x ^ (k + 1) *
      (-Complex.log x + 2 *
        (Complex.digamma ((k + 1 : ℕ) + 1) - Complex.digamma ((k + 1 : ℕ) + a)))

/-- Unfolding lemma for `zeroBalancedTail`. -/
theorem zeroBalancedTail_def (a x : ℂ) :
    zeroBalancedTail a x =
      ∑' k : ℕ, (Polynomial.eval a (ascPochhammer ℂ (k + 1))) ^ 2 /
        (((k + 1).factorial : ℂ) ^ 2) * x ^ (k + 1) *
          (-Complex.log x + 2 *
            (Complex.digamma ((k + 1 : ℕ) + 1) - Complex.digamma ((k + 1 : ℕ) + a))) := by rfl

/-- Every term of `zeroBalancedTail` carries a positive power of `x`, so the tail vanishes at `0`.
-/
@[simp]
theorem zeroBalancedTail_zero_right (a : ℂ) : zeroBalancedTail a 0 = 0 := by
  simp [zeroBalancedTail]

private noncomputable def zeroBalancedCoeff (a : ℂ) (k : ℕ) : ℂ :=
  (Polynomial.eval a (ascPochhammer ℂ k)) ^ 2 / ((k.factorial : ℂ) ^ 2)

private noncomputable def zeroBalancedTerm (a x : ℂ) (k : ℕ) : ℂ :=
  zeroBalancedCoeff a k * x ^ k *
    (-Complex.log x + 2 * (Complex.digamma (k + 1) - Complex.digamma (k + a)))

private theorem multichoose_nonneg_of_pos {R : ℝ} (hR : 0 < R) (k : ℕ) :
    0 ≤ Ring.multichoose R k := by
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer R k
  rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at h
  exact nonneg_of_mul_nonneg_right (h ▸ (ascPochhammer_pos k R hR).le) (by positivity)

private theorem norm_ascPochhammer_div_factorial_le {a : ℂ} {R : ℝ}
    (ha : ‖a‖ ≤ R) (hR : 0 ≤ R) (k : ℕ) :
    ‖Polynomial.eval a (ascPochhammer ℂ k) / (k.factorial : ℂ)‖ ≤ Ring.multichoose R k := by
  have hnum : ‖Polynomial.eval a (ascPochhammer ℂ k)‖ ≤ Polynomial.eval R (ascPochhammer ℝ k) ∧
      0 ≤ Polynomial.eval R (ascPochhammer ℝ k) := by
    induction k with
    | zero => simp
    | succ k ih =>
      rw [ascPochhammer_succ_eval, ascPochhammer_succ_eval, norm_mul]
      have hstep : ‖a + (k : ℂ)‖ ≤ R + (k : ℝ) :=
        (norm_add_le a k).trans (by simpa [Complex.norm_natCast] using add_le_add_right ha (k : ℝ))
      exact ⟨mul_le_mul ih.1 hstep (norm_nonneg _) ih.2,
        mul_nonneg ih.2 (add_nonneg hR (Nat.cast_nonneg k))⟩
  have hc : Ring.multichoose R k = Polynomial.eval R (ascPochhammer ℝ k) / k ! := by
    have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer R k
    rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval] at h
    rw [← h]; field_simp
  rw [hc, norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right hnum.1 (Nat.cast_nonneg _)

private theorem norm_ascPochhammer_div_factorial_le_one {a : ℂ} (ha : ‖a‖ ≤ 1) (k : ℕ) :
    ‖Polynomial.eval a (ascPochhammer ℂ k) / (k.factorial : ℂ)‖ ≤ 1 := by
  refine (norm_ascPochhammer_div_factorial_le ha zero_le_one k).trans_eq ?_
  have h := Ring.factorial_nsmul_multichoose_eq_ascPochhammer (1 : ℝ) k
  rw [nsmul_eq_mul, Polynomial.ascPochhammer_smeval_eq_eval, ascPochhammer_eval_one] at h
  exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr k.factorial_ne_zero) (h.trans (mul_one _).symm)

private theorem summable_multichoose_sq_mul_pow {R r : ℝ}
    (hR : 0 < R) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    Summable fun k : ℕ ↦ (Ring.multichoose R k) ^ 2 * r ^ k := by
  have hs : Summable fun k : ℕ ↦ Ring.multichoose R k * (Real.sqrt r) ^ k := by
    have hlt : ‖Real.sqrt r‖ < 1 := by
      rw [Real.norm_of_nonneg (Real.sqrt_nonneg r)]
      nlinarith [Real.sqrt_nonneg r, Real.sq_sqrt hr0]
    exact (summable_multichoose_mul_geometric_iff_norm_lt_one (𝕂 := ℝ) hR).mpr hlt
  refine hs.of_norm_bounded_eventually_nat ?_
  filter_upwards [hs.tendsto_atTop_zero.eventually (closedBall_mem_nhds 0 zero_lt_one)] with k hk
  have hu0 := mul_nonneg (multichoose_nonneg_of_pos hR k) (pow_nonneg (Real.sqrt_nonneg r) k)
  have hu1 : Ring.multichoose R k * (Real.sqrt r) ^ k ≤ 1 := by
    simpa [Real.norm_of_nonneg hu0] using mem_closedBall_zero_iff.mp hk
  have hsq : (Ring.multichoose R k * (Real.sqrt r) ^ k) ^ 2 =
      (Ring.multichoose R k) ^ 2 * r ^ k := by
    rw [mul_pow, ← pow_mul, mul_comm k 2, pow_mul, Real.sq_sqrt hr0]
  rw [Real.norm_of_nonneg (by positivity), ← hsq, sq]
  exact mul_le_of_le_one_right hu0 hu1

private theorem norm_zeroBalancedCoeff_le {a : ℂ} {R : ℝ}
    (ha : ‖a‖ ≤ R) (hR : 0 ≤ R) (k : ℕ) :
    ‖zeroBalancedCoeff a k‖ ≤ (Ring.multichoose R k) ^ 2 := by
  have h := norm_ascPochhammer_div_factorial_le ha hR k
  rw [zeroBalancedCoeff, ← div_pow, norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) h 2

private theorem summable_zeroBalancedCoeff_mul_pow (a : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    Summable fun k : ℕ ↦ zeroBalancedCoeff a k * x ^ k := by
  refine (summable_multichoose_sq_mul_pow (R := max ‖a‖ 1) (by positivity)
    (norm_nonneg x) hx).of_norm_bounded fun k ↦ ?_
  rw [norm_mul, norm_pow]
  exact mul_le_mul_of_nonneg_right
    (norm_zeroBalancedCoeff_le (le_max_left _ _) (by positivity) k) (pow_nonneg (norm_nonneg x) k)

private theorem norm_digamma_sub_le_of_re_ge_one {s w : ℂ}
    (hs : 1 ≤ s.re) (hw : 1 ≤ w.re) :
    ‖Complex.digamma s - Complex.digamma w‖ ≤ ‖s - w‖ * (Real.pi ^ 2 / 6) := by
  have hp2 : HasSum (fun n : ℕ ↦ 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    simpa [Nat.cast_add, Nat.cast_one] using (hasSum_nat_add_iff' 1).mpr hasSum_zeta_two
  have hsum := hp2.mul_left ‖s - w‖
  have hbd (n : ℕ) : ‖(s - w) / ((w + n) * (s + n))‖ ≤ ‖s - w‖ * (1 / ((n : ℝ) + 1) ^ 2) := by
    have hsn : (n : ℝ) + 1 ≤ ‖s + n‖ := by
      have := Complex.re_le_norm (s + n); simp at this; linarith
    have hwn : (n : ℝ) + 1 ≤ ‖w + n‖ := by
      have := Complex.re_le_norm (w + n); simp at this; linarith
    rw [norm_div, norm_mul, mul_one_div]
    exact div_le_div_of_nonneg_left (norm_nonneg _) (by positivity)
      (by nlinarith [n.cast_nonneg (α := ℝ)])
  rw [Complex.digamma_sub_digamma_eq_tsum (ne_neg_natCast_of_re_pos (by linarith))
    (ne_neg_natCast_of_re_pos (by linarith)), ← hsum.tsum_eq]
  exact (norm_tsum_le_tsum_norm (Complex.summable_sub_div_add_mul_add s w).norm).trans
    ((Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hbd hsum.summable).tsum_le_tsum
      hbd hsum.summable)

private theorem norm_two_mul_digamma_sub_le {b : ℂ} {R : ℝ} {k : ℕ}
    (hb : ‖b‖ ≤ R) (hk : ⌈R⌉₊ + 1 ≤ k) :
    ‖(2 : ℂ) * (Complex.digamma ((k : ℂ) + 1) - Complex.digamma ((k : ℂ) + b))‖ ≤
      2 * (1 + R) * (Real.pi ^ 2 / 6) := by
  have hkR : R + 1 ≤ (k : ℝ) := by
    linarith [Nat.le_ceil R, (by exact_mod_cast hk : (⌈R⌉₊ : ℝ) + 1 ≤ k)]
  have hbre : -R ≤ b.re := (neg_le_neg hb).trans (abs_le.mp (abs_re_le_norm b)).1
  have hdig := norm_digamma_sub_le_of_re_ge_one (s := (k : ℂ) + 1) (w := (k : ℂ) + b)
    (by simp) (by simp; linarith)
  rw [show (k : ℂ) + 1 - ((k : ℂ) + b) = 1 - b by ring] at hdig
  have h1b : ‖1 - b‖ ≤ 1 + R := (norm_sub_le 1 b).trans (by norm_num; linarith)
  rw [norm_mul, Complex.norm_ofNat]
  nlinarith [Real.pi_pos]

private theorem summable_zeroBalancedDigammaSeries (a : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    Summable fun k : ℕ ↦
      zeroBalancedCoeff a k *
        (2 * (Complex.digamma (k + 1) - Complex.digamma (k + a))) * x ^ k := by
  let R := max ‖a‖ 1
  let C := 2 * (1 + R) * (Real.pi ^ 2 / 6)
  refine ((summable_multichoose_sq_mul_pow (R := R) (by positivity) (norm_nonneg x) hx).mul_left
    C).of_norm_bounded_eventually_nat ?_
  filter_upwards [eventually_ge_atTop (⌈R⌉₊ + 1)] with k hk
  rw [norm_mul, norm_mul, norm_pow]
  exact (mul_le_mul_of_nonneg_right
    (mul_le_mul (norm_zeroBalancedCoeff_le (le_max_left ‖a‖ 1) (by positivity) k)
      (norm_two_mul_digamma_sub_le (le_max_left ‖a‖ 1) hk) (norm_nonneg _) (by positivity))
    (pow_nonneg (norm_nonneg x) k)).trans_eq (by ring)

private theorem summable_zeroBalancedTerm (a : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    Summable (zeroBalancedTerm a x) :=
  (((summable_zeroBalancedCoeff_mul_pow a hx).mul_right (-Complex.log x)).add
    (summable_zeroBalancedDigammaSeries a hx)).congr fun k ↦ by dsimp [zeroBalancedTerm]; ring

private theorem tsum_zeroBalancedTerm_eq_split (a : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    ∑' k : ℕ, zeroBalancedTerm a x k =
      -Complex.log x * (∑' k : ℕ, zeroBalancedCoeff a k * x ^ k) +
        ∑' k : ℕ, zeroBalancedCoeff a k *
          (2 * (Complex.digamma (k + 1) - Complex.digamma (k + a))) * x ^ k :=
  ((((summable_zeroBalancedCoeff_mul_pow a hx).hasSum.mul_left (-Complex.log x)).add
    (summable_zeroBalancedDigammaSeries a hx).hasSum).congr_fun fun k ↦ by
      dsimp [zeroBalancedTerm]; ring).tsum_eq

/-- On the open unit disc, `zeroBalancedSeries a x` separates into `-log x` times the squared
Pochhammer power series plus the holomorphic digamma-weighted power series. -/
theorem zeroBalancedSeries_eq_log_mul_add (a : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    zeroBalancedSeries a x =
      Complex.Gamma (2 * a) / Complex.Gamma a ^ 2 *
        (-Complex.log x *
          (∑' k : ℕ, (Polynomial.eval a (ascPochhammer ℂ k)) ^ 2 / ((k.factorial : ℂ) ^ 2) *
            x ^ k) +
        ∑' k : ℕ, (Polynomial.eval a (ascPochhammer ℂ k)) ^ 2 / ((k.factorial : ℂ) ^ 2) *
          (2 * (Complex.digamma (k + 1) - Complex.digamma (k + a))) * x ^ k) := by
  change Complex.Gamma (2 * a) / Complex.Gamma a ^ 2 * ∑' k, zeroBalancedTerm a x k = _
  rw [tsum_zeroBalancedTerm_eq_split a hx]; rfl

/-- On the open unit disc, `zeroBalancedSeries a x` splits into its `k = 0` logarithmic term
`-log x - 2γ - 2ψ(a)` and `zeroBalancedTail a x`. -/
theorem zeroBalancedSeries_eq_add_zeroBalancedTail (a : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    zeroBalancedSeries a x =
      Complex.Gamma (2 * a) / Complex.Gamma a ^ 2 *
        (-Complex.log x - 2 * Real.eulerMascheroniConstant - 2 * Complex.digamma a +
          zeroBalancedTail a x) := by
  change Complex.Gamma (2 * a) / Complex.Gamma a ^ 2 * ∑' k, zeroBalancedTerm a x k = _
  rw [(summable_zeroBalancedTerm a hx).tsum_eq_zero_add]
  congr 1
  have h0 : zeroBalancedTerm a x 0 =
      -Complex.log x - 2 * Real.eulerMascheroniConstant - 2 * Complex.digamma a := by
    simp [zeroBalancedTerm, zeroBalancedCoeff, Complex.digamma_one]; ring
  rw [h0]; rfl

/-! ### Uniform remainder and parameter-derivative bounds -/

/-- Explicit uniform bound on `zeroBalancedTail a x` for `0 ≤ a.re`, `‖a‖ ≤ 1`, and `‖x‖ < 1`. -/
theorem norm_zeroBalancedTail_le {a x : ℂ} (hre : 0 ≤ a.re) (ha : ‖a‖ ≤ 1) (hx : ‖x‖ < 1) :
    ‖zeroBalancedTail a x‖ ≤ 8 / (1 - ‖x‖) * ‖x‖ * (1 + ‖Complex.log x‖) := by
  let M : ℝ := 8 * (1 + ‖Complex.log x‖)
  have hgeom : HasSum (fun k : ℕ ↦ ‖x‖ ^ (k + 1) * M)
      (8 / (1 - ‖x‖) * ‖x‖ * (1 + ‖Complex.log x‖)) := by
    have hg := ((hasSum_geometric_of_lt_one (norm_nonneg x) hx).mul_left ‖x‖).mul_right M
    convert (hg.congr_fun fun k ↦ by rw [← pow_succ']) using 1
    dsimp [M]; ring
  have hterm (k : ℕ) : ‖zeroBalancedTerm a x (k + 1)‖ ≤ ‖x‖ ^ (k + 1) * M := by
    have hc : ‖zeroBalancedCoeff a (k + 1)‖ ≤ 1 := by
      rw [zeroBalancedCoeff, ← div_pow, norm_pow]
      exact pow_le_one₀ (norm_nonneg _) (norm_ascPochhammer_div_factorial_le_one ha (k + 1))
    have hdig : ‖Complex.digamma (((k + 1 : ℕ) : ℂ) + 1) -
        Complex.digamma (((k + 1 : ℕ) : ℂ) + a)‖ ≤ 7 / 2 := by
      have h1 := norm_digamma_sub_le_of_re_ge_one
        (s := ((k + 1 : ℕ) : ℂ) + 1) (w := ((k + 1 : ℕ) : ℂ) + a)
        (by simp only [Nat.cast_add, Nat.cast_one, add_re, natCast_re, one_re]
            linarith [k.cast_nonneg (α := ℝ)])
        (by simp; linarith)
      have hsub : ((k + 1 : ℕ) : ℂ) + 1 - (((k + 1 : ℕ) : ℂ) + a) = 1 - a := by ring
      rw [hsub] at h1
      have h1a : ‖1 - a‖ ≤ 2 := (norm_sub_le 1 a).trans (by norm_num; linarith)
      have hpi : Real.pi ^ 2 < 3.15 ^ 2 :=
        pow_lt_pow_left₀ Real.pi_lt_d2 Real.pi_pos.le (by norm_num)
      nlinarith [Real.pi_pos]
    have hlog : ‖-Complex.log x + 2 * (Complex.digamma (((k + 1 : ℕ) : ℂ) + 1) -
        Complex.digamma (((k + 1 : ℕ) : ℂ) + a))‖ ≤ M := by
      calc ‖-Complex.log x + 2 * _‖ ≤ ‖-Complex.log x‖ + ‖(2 : ℂ) * _‖ := norm_add_le _ _
        _ ≤ M := by
          rw [norm_neg, norm_mul, Complex.norm_ofNat]
          dsimp [M]; linarith [norm_nonneg (Complex.log x)]
    rw [zeroBalancedTerm, norm_mul, norm_mul, norm_pow]
    calc ‖zeroBalancedCoeff a (k + 1)‖ * ‖x‖ ^ (k + 1) * _
        ≤ (1 * ‖x‖ ^ (k + 1)) * M :=
          mul_le_mul (mul_le_mul_of_nonneg_right hc (pow_nonneg (norm_nonneg x) _)) hlog
            (norm_nonneg _) (by positivity)
      _ = ‖x‖ ^ (k + 1) * M := by ring
  rw [zeroBalancedTail, ← hgeom.tsum_eq]
  exact (norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm
    hgeom.summable)).trans ((Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm
      hgeom.summable).tsum_le_tsum hterm hgeom.summable)

private theorem isOpen_ne_neg_succ : IsOpen {b : ℂ | ∀ m : ℕ, b ≠ -((m + 1 : ℕ) : ℂ)} := by
  rw [Metric.isOpen_iff]
  intro b hb
  let N := ⌈-b.re⌉₊ + 1
  let S : Finset ℂ := (Finset.range N).image fun m : ℕ ↦ -((m + 1 : ℕ) : ℂ)
  have hbS : b ∉ (S : Set ℂ) := by
    simp only [Finset.coe_image, Finset.coe_range, mem_image, mem_Iio, not_exists, not_and, S]
    intro m _; exact (hb m).symm
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp S.finite_toSet.isClosed.isOpen_compl b hbS
  refine ⟨min r (1 / 2), lt_min hr (by norm_num), fun w hw m hm ↦ ?_⟩
  rcases lt_or_ge m N with hmN | hmN
  · exact hball (Metric.ball_subset_ball (min_le_left _ _) hw)
      (Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hmN, hm.symm⟩))
  · have hdist : ‖w - b‖ < 1 / 2 := (mem_ball_iff_norm.mp hw).trans_le (min_le_right _ _)
    have hwsub := (abs_le.mp (abs_re_le_norm (w - b))).1
    simp only [sub_re] at hwsub
    have hmR : (-b.re) + 1 ≤ (m : ℝ) := by
      linarith [Nat.le_ceil (-b.re), (by exact_mod_cast hmN : (⌈-b.re⌉₊ : ℝ) + 1 ≤ m)]
    have hre := congrArg Complex.re hm
    simp only [neg_re, Nat.cast_add, Nat.cast_one, add_re, natCast_re, one_re] at hre
    linarith

private theorem analyticAt_digamma {s : ℂ} (hs : ∀ m : ℕ, s ≠ -(m : ℂ)) :
    AnalyticAt ℂ Complex.digamma s := by
  have hΓ := Complex.analyticAt_Gamma hs
  simpa only [Complex.digamma_def, logDeriv, Pi.div_def] using
    hΓ.deriv.div hΓ (Complex.Gamma_ne_zero hs)

/-- For fixed `‖x‖ < 1`, `b ↦ zeroBalancedTail b x` is complex differentiable away from the
negative integers `-1, -2, …`. -/
theorem differentiableOn_zeroBalancedTail_left {x : ℂ} (hx : ‖x‖ < 1) :
    DifferentiableOn ℂ (fun b : ℂ ↦ zeroBalancedTail b x)
      {b : ℂ | ∀ m : ℕ, b ≠ -((m + 1 : ℕ) : ℂ)} := by
  let V := {b : ℂ | ∀ m : ℕ, b ≠ -((m + 1 : ℕ) : ℂ)}
  have hloc : HasSumLocallyUniformlyOn (fun k b ↦ zeroBalancedTerm b x (k + 1))
      (fun b ↦ zeroBalancedTail b x) V := by
    apply hasSumLocallyUniformlyOn_of_forall_compact isOpen_ne_neg_succ
    intro K _ hK
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
    let R := max B 1
    let C := ‖Complex.log x‖ + 2 * (1 + R) * (Real.pi ^ 2 / 6)
    have hu : Summable fun k : ℕ ↦ C * ((Ring.multichoose R (k + 1)) ^ 2 * ‖x‖ ^ (k + 1)) :=
      ((summable_nat_add_iff 1).mpr
        (summable_multichoose_sq_mul_pow (by positivity) (norm_nonneg x) hx)).mul_left C
    apply HasSumUniformlyOn.of_norm_le_summable_eventually hu
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop (⌈R⌉₊ + 1)] with k hk b hbK
    have hbR : ‖b‖ ≤ R := (hB b hbK).trans (le_max_left _ _)
    have h2 := norm_two_mul_digamma_sub_le (k := k + 1) hbR (by omega)
    have hlog : ‖-Complex.log x + 2 * (Complex.digamma (((k + 1 : ℕ) : ℂ) + 1) -
        Complex.digamma (((k + 1 : ℕ) : ℂ) + b))‖ ≤ C :=
      (norm_add_le _ _).trans (by rw [norm_neg]; dsimp [C]; linarith)
    rw [zeroBalancedTerm, norm_mul, norm_mul, norm_pow]
    calc ‖zeroBalancedCoeff b (k + 1)‖ * ‖x‖ ^ (k + 1) * _
        ≤ ((Ring.multichoose R (k + 1)) ^ 2 * ‖x‖ ^ (k + 1)) * C :=
          mul_le_mul (mul_le_mul_of_nonneg_right
            (norm_zeroBalancedCoeff_le hbR (by positivity) (k + 1)) (pow_nonneg (norm_nonneg x) _))
            hlog (norm_nonneg _) (by positivity)
      _ = C * ((Ring.multichoose R (k + 1)) ^ 2 * ‖x‖ ^ (k + 1)) := by ring
  refine (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hloc).differentiableOn
    (Eventually.of_forall fun s ↦ ?_) isOpen_ne_neg_succ
  refine DifferentiableOn.fun_sum fun k _ b hb ↦ ?_
  have hbp : ∀ m : ℕ, ((k + 1 : ℕ) : ℂ) + b ≠ -(m : ℂ) := fun m hm ↦
    hb (k + m) (by push_cast at hm ⊢; linear_combination hm)
  have hpoly : DifferentiableAt ℂ (fun b : ℂ ↦ zeroBalancedCoeff b (k + 1) * x ^ (k + 1)) b :=
    (((Polynomial.differentiableAt (ascPochhammer ℂ (k + 1))).pow 2).div_const _).mul_const _
  have hdig : DifferentiableAt ℂ (fun b : ℂ ↦ -Complex.log x +
      2 * (Complex.digamma (((k + 1 : ℕ) : ℂ) + 1) -
        Complex.digamma (((k + 1 : ℕ) : ℂ) + b))) b :=
    (differentiableAt_const _).add <| (differentiableAt_const 2).mul <|
      (differentiableAt_const _).sub <|
        (analyticAt_digamma hbp).differentiableAt.comp b (differentiableAt_id.const_add _)
  exact (hpoly.mul hdig).differentiableWithinAt

private theorem ne_neg_succ_of_re_nonneg {b : ℂ} (hb : 0 ≤ b.re) (m : ℕ) :
    b ≠ -((m + 1 : ℕ) : ℂ) := fun hm ↦ by
  have h := congrArg Complex.re hm
  simp only [neg_re, Nat.cast_add, Nat.cast_one, add_re, natCast_re, one_re] at h
  linarith [m.cast_nonneg (α := ℝ)]

/-- Cauchy derivative estimate for `b ↦ zeroBalancedTail b x` on `closedBall (1 / 2 : ℂ) (3 / 8)`
and `‖x‖ < 1`. -/
theorem norm_deriv_zeroBalancedTail_le {a x : ℂ}
    (ha : a ∈ closedBall (1 / 2 : ℂ) (3 / 8)) (hx : ‖x‖ < 1) :
    ‖deriv (fun b : ℂ ↦ zeroBalancedTail b x) a‖ ≤
      64 / (1 - ‖x‖) * ‖x‖ * (1 + ‖Complex.log x‖) := by
  have hmem {b : ℂ} (hb : b ∈ closedBall a (1 / 8)) : 0 ≤ b.re ∧ ‖b‖ ≤ 1 := by
    have hba : ‖b - a‖ ≤ 1 / 8 := mem_closedBall_iff_norm.mp hb
    have ha0 : ‖a - (1 / 2 : ℂ)‖ ≤ 3 / 8 := mem_closedBall_iff_norm.mp ha
    have hb12 : ‖b - (1 / 2 : ℂ)‖ ≤ 1 / 2 :=
      ((norm_add_le (b - a) (a - (1 / 2 : ℂ))).trans_eq' (by ring_nf)).trans (by linarith)
    have hbre := (abs_le.mp (abs_re_le_norm (b - (1 / 2 : ℂ)))).1
    have hre12 : ((1 / 2 : ℂ)).re = 1 / 2 := by norm_num
    simp only [sub_re, hre12] at hbre
    have hbn : ‖b‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖b - (1 / 2 : ℂ)‖ :=
      (norm_add_le (1 / 2 : ℂ) (b - (1 / 2 : ℂ))).trans_eq' (by ring_nf)
    have hn12 : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
    exact ⟨by linarith, by linarith⟩
  have hdiff : DifferentiableOn ℂ (fun b : ℂ ↦ zeroBalancedTail b x) (closedBall a (1 / 8)) :=
    (differentiableOn_zeroBalancedTail_left hx).mono fun _ hb ↦
      ne_neg_succ_of_re_nonneg (hmem hb).1
  have hcauchy := norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1 / 8)
    (hdiff.mono closure_ball_subset_closedBall).diffContOnCl
    (C := 8 / (1 - ‖x‖) * ‖x‖ * (1 + ‖Complex.log x‖)) fun b hb ↦ by
      obtain ⟨hb0, hb1⟩ := hmem (sphere_subset_closedBall hb)
      exact norm_zeroBalancedTail_le hb0 hb1 hx
  exact hcauchy.trans_eq (by ring)

/-- Real parameter derivative bound for `zeroBalancedTail` on `[1 / 8, 7 / 8]` and `‖x‖ < 1`. -/
theorem norm_deriv_ofReal_zeroBalancedTail_le {a : ℝ}
    (ha₁ : 1 / 8 ≤ a) (ha₂ : a ≤ 7 / 8) {x : ℂ} (hx : ‖x‖ < 1) :
    ‖deriv (fun b : ℝ ↦ zeroBalancedTail b x) a‖ ≤
      64 / (1 - ‖x‖) * ‖x‖ * (1 + ‖Complex.log x‖) := by
  have hd : DifferentiableAt ℂ (fun b : ℂ ↦ zeroBalancedTail b x) a :=
    (differentiableOn_zeroBalancedTail_left hx).differentiableAt
      (isOpen_ne_neg_succ.mem_nhds (ne_neg_succ_of_re_nonneg (by simp; linarith)))
  rw [hd.hasDerivAt.comp_ofReal.deriv]
  refine norm_deriv_zeroBalancedTail_le (mem_closedBall_iff_norm.mpr ?_) hx
  rw [show (a : ℂ) - 1 / 2 = ((a - 1 / 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs, abs_le]
  exact ⟨by linarith, by linarith⟩

/-- Mean-value Lipschitz bound on `a ↦ zeroBalancedTail a x` across `[1 / 8, 7 / 8]` for
`‖x‖ < 1`. -/
theorem norm_zeroBalancedTail_sub_le {a₁ a₂ : ℝ}
    (ha₁ : a₁ ∈ Icc (1 / 8 : ℝ) (7 / 8)) (ha₂ : a₂ ∈ Icc (1 / 8 : ℝ) (7 / 8))
    {x : ℂ} (hx : ‖x‖ < 1) :
    ‖zeroBalancedTail a₁ x - zeroBalancedTail a₂ x‖ ≤
      64 / (1 - ‖x‖) * |a₁ - a₂| * ‖x‖ * (1 + ‖Complex.log x‖) := by
  have hdiff : ∀ b ∈ Icc (1 / 8 : ℝ) (7 / 8),
      DifferentiableAt ℝ (fun b : ℝ ↦ zeroBalancedTail b x) b := fun b hb ↦
    ((differentiableOn_zeroBalancedTail_left hx).differentiableAt
      (isOpen_ne_neg_succ.mem_nhds (ne_neg_succ_of_re_nonneg
        (by simp; linarith [hb.1])))).hasDerivAt.comp_ofReal.differentiableAt
  exact ((convex_Icc (1 / 8 : ℝ) (7 / 8)).norm_image_sub_le_of_norm_deriv_le hdiff
    (fun b hb ↦ norm_deriv_ofReal_zeroBalancedTail_le hb.1 hb.2 hx) ha₂ ha₁).trans_eq
    (by rw [Real.norm_eq_abs]; ring)

private theorem analyticOnNhd_gammaRatio_closedBall :
    AnalyticOnNhd ℂ (fun b : ℂ ↦ Complex.Gamma (2 * b) / Complex.Gamma b ^ 2)
      (closedBall (1 / 2 : ℂ) (5 / 16)) := by
  intro b hb
  have hba : ‖b - (1 / 2 : ℂ)‖ ≤ 5 / 16 := mem_closedBall_iff_norm.mp hb
  have hsub := (abs_le.mp (abs_re_le_norm (b - (1 / 2 : ℂ)))).1
  have hbre : 3 / 16 ≤ b.re := by simp at hsub; linarith
  have hb1 : AnalyticAt ℂ Complex.Gamma b :=
    Complex.analyticAt_Gamma (ne_neg_natCast_of_re_pos (by linarith))
  have hb2 : AnalyticAt ℂ (fun z : ℂ ↦ Complex.Gamma (2 * z)) b :=
    (Complex.analyticAt_Gamma (ne_neg_natCast_of_re_pos (by simp; linarith))).comp
      (analyticAt_const.mul analyticAt_id)
  exact hb2.div (hb1.pow 2) (pow_ne_zero 2 (Gamma_ne_zero_of_re_pos (by linarith)))

private theorem closedBall_real_mem_bounds {a : ℝ} (ha : a ∈ Icc (1 / 4 : ℝ) (3 / 4))
    {b : ℂ} (hb : b ∈ closedBall (a : ℂ) (1 / 16)) :
    b ∈ closedBall (1 / 2 : ℂ) (5 / 16) ∧ 3 / 16 ≤ b.re ∧ ‖b‖ ≤ 1 := by
  have hba : ‖b - a‖ ≤ 1 / 16 := mem_closedBall_iff_norm.mp hb
  have ha12 : ‖(a : ℂ) - 1 / 2‖ ≤ 1 / 4 := by
    rw [show (a : ℂ) - 1 / 2 = ((a - 1 / 2 : ℝ) : ℂ) by push_cast; ring,
      Complex.norm_real, Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have hsub : b ∈ closedBall (1 / 2 : ℂ) (5 / 16) := by
    rw [mem_closedBall_iff_norm]
    calc ‖b - (1 / 2 : ℂ)‖ = ‖(b - a) + ((a : ℂ) - 1 / 2)‖ := by ring_nf
      _ ≤ ‖b - a‖ + ‖(a : ℂ) - 1 / 2‖ := norm_add_le _ _
      _ ≤ 5 / 16 := by linarith
  have hbre := (abs_le.mp (abs_re_le_norm (b - a))).1
  simp only [sub_re, ofReal_re] at hbre
  have han : ‖(a : ℂ)‖ ≤ 3 / 4 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith [ha.1])]; exact ha.2
  have hbn : ‖b‖ ≤ ‖(a : ℂ)‖ + ‖b - a‖ :=
    (norm_add_le (a : ℂ) (b - a)).trans_eq' (by ring_nf)
  exact ⟨hsub, by linarith [ha.1], by linarith⟩

/-- Uniform `O(‖x‖(1 + ‖log x‖) / (1 - ‖x‖))` bound on the Gamma-normalized `k ≥ 1` remainder
`Γ(2a) / Γ(a)² * zeroBalancedTail a x` and its real `a`-derivative on `[1 / 4, 3 / 4]`
(CDT Lemma 5.2.9). -/
theorem exists_norm_mul_zeroBalancedTail_and_deriv_le :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃a : ℝ⦄, a ∈ Icc (1 / 4 : ℝ) (3 / 4) → ∀ ⦃x : ℂ⦄, ‖x‖ < 1 →
      ‖Complex.Gamma (2 * a) / Complex.Gamma a ^ 2 * zeroBalancedTail a x‖ ≤
        C / (1 - ‖x‖) * ‖x‖ * (1 + ‖Complex.log x‖) ∧
      ‖deriv (fun b : ℝ ↦ Complex.Gamma (2 * b) / Complex.Gamma b ^ 2 * zeroBalancedTail b x) a‖ ≤
        C / (1 - ‖x‖) * ‖x‖ * (1 + ‖Complex.log x‖) := by
  let g : ℂ → ℂ := fun b ↦ Complex.Gamma (2 * b) / Complex.Gamma b ^ 2
  obtain ⟨M, hM⟩ := (isCompact_closedBall (1 / 2 : ℂ) (5 / 16)).exists_bound_of_continuousOn
    analyticOnNhd_gammaRatio_closedBall.continuousOn
  let M' := max M 1
  have hM' : 0 < M' := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  refine ⟨128 * M', by positivity, fun a ha x hx ↦ ?_⟩
  have hbound : ∀ b ∈ closedBall (a : ℂ) (1 / 16),
      ‖g b * zeroBalancedTail b x‖ ≤ 8 * M' / (1 - ‖x‖) * ‖x‖ * (1 + ‖Complex.log x‖) := by
    intro b hb
    obtain ⟨hsub, hb0, hb1⟩ := closedBall_real_mem_bounds ha hb
    rw [norm_mul]
    exact (mul_le_mul ((hM b hsub).trans (le_max_left _ _))
      (norm_zeroBalancedTail_le (by linarith) hb1 hx) (norm_nonneg _) hM'.le).trans_eq (by ring)
  have hdiff : DifferentiableOn ℂ (fun b : ℂ ↦ g b * zeroBalancedTail b x)
      (closedBall (a : ℂ) (1 / 16)) :=
    ((analyticOnNhd_gammaRatio_closedBall.mono
      fun b hb ↦ (closedBall_real_mem_bounds ha hb).1).differentiableOn).mul
      ((differentiableOn_zeroBalancedTail_left hx).mono fun b hb ↦
        ne_neg_succ_of_re_nonneg (by linarith [(closedBall_real_mem_bounds ha hb).2.1]))
  have hcauchy := norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1 / 16)
    (hdiff.mono closure_ball_subset_closedBall).diffContOnCl
    (fun b hb ↦ hbound b (sphere_subset_closedBall hb))
  have hda := hdiff.differentiableAt (closedBall_mem_nhds _ (by norm_num))
  refine ⟨(hbound a (mem_closedBall_self (by norm_num))).trans ?_, ?_⟩
  · have hpos : 0 ≤ M' / (1 - ‖x‖) * ‖x‖ * (1 + ‖Complex.log x‖) := by
      have : 0 ≤ 1 - ‖x‖ := sub_nonneg.mpr hx.le; positivity
    linarith [show 128 * M' / (1 - ‖x‖) * ‖x‖ * (1 + ‖Complex.log x‖) -
      8 * M' / (1 - ‖x‖) * ‖x‖ * (1 + ‖Complex.log x‖) =
      120 * (M' / (1 - ‖x‖) * ‖x‖ * (1 + ‖Complex.log x‖)) by ring]
  · change ‖deriv (fun b : ℝ ↦ g b * zeroBalancedTail b x) a‖ ≤ _
    rw [hda.hasDerivAt.comp_ofReal.deriv]
    exact hcauchy.trans_eq (by ring)

/-! ### Analyticity in `x` and `a` and upper-half-plane boundary limit -/

private theorem slitBall_eq_inter :
    Metric.ball (0 : ℂ) 1 \ {x : ℂ | x.re ≤ 0 ∧ x.im = 0} =
      Metric.ball (0 : ℂ) 1 ∩ Complex.slitPlane := by
  ext x
  simp only [Set.mem_sdiff, mem_inter_iff, Complex.mem_slitPlane_iff, Set.mem_ofPred,
    not_and_or, not_le]

private theorem isOpen_two_mul_ne_neg_nat :
    IsOpen {a : ℂ | ∀ n : ℕ, 2 * a ≠ -(n : ℂ)} := by
  have heq : {a : ℂ | ∀ n : ℕ, 2 * a ≠ -(n : ℂ)} =
      (fun a : ℂ ↦ 2 * a - 1) ⁻¹' {b : ℂ | ∀ m : ℕ, b ≠ -((m + 1 : ℕ) : ℂ)} := by
    ext a
    simp only [Set.mem_ofPred, mem_preimage]
    exact ⟨fun ha m hm ↦ ha m (by push_cast at hm; linear_combination hm),
      fun ha n hn ↦ ha n (by push_cast; linear_combination hn)⟩
  exact heq ▸ isOpen_ne_neg_succ.preimage (by fun_prop)

private theorem analyticOnNhd_tsum_pow_of_eventually_le {c : ℕ → ℂ} {R C : ℝ} {N : ℕ}
    (hR : 0 < R) (hC : 0 ≤ C)
    (hc : ∀ k : ℕ, N ≤ k → ‖c k‖ ≤ C * (Ring.multichoose R k) ^ 2) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦ ∑' k : ℕ, c k * z ^ k) (Metric.ball 0 1) := by
  have hloc : HasSumLocallyUniformlyOn (fun k z ↦ c k * z ^ k)
      (fun z ↦ ∑' k : ℕ, c k * z ^ k) (Metric.ball 0 1) := by
    apply hasSumLocallyUniformlyOn_of_forall_compact Metric.isOpen_ball
    intro K hKU hK
    rcases K.eq_empty_or_nonempty with rfl | hKne
    · exact hasSumUniformlyOn_iff_tendstoUniformlyOn.mpr tendstoUniformlyOn_empty
    obtain ⟨z₀, hz₀K, hz₀max⟩ := hK.exists_isMaxOn hKne continuous_norm.continuousOn
    let r := ‖z₀‖
    have hr1 : r < 1 := by simpa [r] using hKU hz₀K
    apply HasSumUniformlyOn.of_norm_le_summable_eventually
      ((summable_multichoose_sq_mul_pow hR (norm_nonneg z₀) hr1).mul_left C)
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop N] with k hk z hz
    rw [norm_mul, norm_pow]
    exact (mul_le_mul (hc k hk) (pow_le_pow_left₀ (norm_nonneg z) (isMaxOn_iff.mp hz₀max z hz) k)
      (pow_nonneg (norm_nonneg z) k) (by positivity)).trans_eq (by ring)
  have hd : DifferentiableOn ℂ (fun z : ℂ ↦ ∑' k : ℕ, c k * z ^ k) (Metric.ball 0 1) :=
    (hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hloc).differentiableOn
      (Eventually.of_forall fun s ↦ DifferentiableOn.fun_sum fun k _ _ _ ↦ by fun_prop)
      Metric.isOpen_ball
  exact hd.analyticOnNhd Metric.isOpen_ball

private theorem analyticOnNhd_zeroBalancedCoeffSeries (a : ℂ) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦ ∑' k : ℕ, zeroBalancedCoeff a k * z ^ k) (Metric.ball 0 1) :=
  analyticOnNhd_tsum_pow_of_eventually_le (R := max ‖a‖ 1) (C := 1) (N := 0) (by positivity)
    zero_le_one fun k _ ↦ by
      simpa using norm_zeroBalancedCoeff_le (le_max_left ‖a‖ 1) (by positivity) k

private theorem analyticOnNhd_zeroBalancedDigammaSeries (a : ℂ) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦ ∑' k : ℕ, zeroBalancedCoeff a k *
      (2 * (Complex.digamma (k + 1) - Complex.digamma (k + a))) * z ^ k) (Metric.ball 0 1) := by
  let R := max ‖a‖ 1
  refine analyticOnNhd_tsum_pow_of_eventually_le (R := R)
    (C := 2 * (1 + R) * (Real.pi ^ 2 / 6)) (N := ⌈R⌉₊ + 1) (by positivity) (by positivity)
    fun k hk ↦ ?_
  rw [norm_mul]
  exact (mul_le_mul (norm_zeroBalancedCoeff_le (le_max_left ‖a‖ 1) (by positivity) k)
    (norm_two_mul_digamma_sub_le (le_max_left ‖a‖ 1) hk) (norm_nonneg _)
    (by positivity)).trans_eq (by ring)

/-- For fixed `‖x‖ < 1`, `a ↦ zeroBalancedSeries a x` is complex analytic away from the poles
`2a = -n` (`n : ℕ`). -/
theorem analyticOnNhd_zeroBalancedSeries_left {x : ℂ} (hx : ‖x‖ < 1) :
    AnalyticOnNhd ℂ (fun a : ℂ ↦ zeroBalancedSeries a x)
      {a : ℂ | ∀ n : ℕ, 2 * a ≠ -(n : ℂ)} := by
  have htail : AnalyticOnNhd ℂ (fun b : ℂ ↦ zeroBalancedTail b x)
      {b : ℂ | ∀ m : ℕ, b ≠ -((m + 1 : ℕ) : ℂ)} :=
    (differentiableOn_zeroBalancedTail_left hx).analyticOnNhd isOpen_ne_neg_succ
  intro a ha
  have ha' : ∀ m : ℕ, a ≠ -(m : ℂ) := fun m hm ↦
    ha (2 * m) (by push_cast; linear_combination 2 * hm)
  have hΓ2 : AnalyticAt ℂ (fun b : ℂ ↦ Complex.Gamma (2 * b)) a :=
    (Complex.analyticAt_Gamma ha).comp (analyticAt_const.mul analyticAt_id)
  have hΓ1 : AnalyticAt ℂ (fun b : ℂ ↦ Complex.Gamma b ^ 2) a :=
    (Complex.analyticAt_Gamma ha').pow 2
  have hinner : AnalyticAt ℂ (fun b : ℂ ↦
      -Complex.log x - 2 * Real.eulerMascheroniConstant - 2 * Complex.digamma b +
        zeroBalancedTail b x) a :=
    ((analyticAt_const.sub (analyticAt_const.mul (analyticAt_digamma ha'))).add
      (htail a fun m ↦ ha' (m + 1)))
  refine ((hΓ2.div hΓ1 (pow_ne_zero 2 (Complex.Gamma_ne_zero ha'))).mul hinner).congr ?_
  filter_upwards [isOpen_two_mul_ne_neg_nat.mem_nhds ha] with b _
  exact (zeroBalancedSeries_eq_add_zeroBalancedTail b hx).symm

/-- For every `a : ℂ`, `zeroBalancedSeries a` is complex analytic on the slit unit disc
`ball 0 1 \ (-∞, 0]`. -/
theorem analyticOnNhd_zeroBalancedSeries (a : ℂ) :
    AnalyticOnNhd ℂ (zeroBalancedSeries a)
      (Metric.ball 0 1 \ {x : ℂ | x.re ≤ 0 ∧ x.im = 0}) := by
  rw [slitBall_eq_inter]
  intro x hx
  have hopen := Metric.isOpen_ball (x := (0 : ℂ)) (ε := 1) |>.inter Complex.isOpen_slitPlane
  have hlog : AnalyticAt ℂ (fun z : ℂ ↦ -Complex.log z) x := (analyticAt_clog hx.2).neg
  have h1 := analyticOnNhd_zeroBalancedCoeffSeries a x hx.1
  have h2 := analyticOnNhd_zeroBalancedDigammaSeries a x hx.1
  have hconst : AnalyticAt ℂ (fun _ : ℂ ↦ Complex.Gamma (2 * a) / Complex.Gamma a ^ 2) x :=
    analyticAt_const
  refine (hconst.mul ((hlog.mul h1).add h2)).congr ?_
  filter_upwards [hopen.mem_nhds hx] with z hz
  change _ = Complex.Gamma (2 * a) / Complex.Gamma a ^ 2 * ∑' k, zeroBalancedTerm a z k
  rw [tsum_zeroBalancedTerm_eq_split a (mem_ball_zero_iff.mp hz.1)]; rfl

/-- On the punctured unit disc `0 < ‖x‖ < 1`, `zeroBalancedSeries a x` equals its limit from the
open upper half-plane `{z : ℂ | 0 < z.im}`: on the negative real axis Mathlib's principal
logarithm takes the boundary value `log |x| + π i` from above. -/
theorem tendsto_zeroBalancedSeries_nhdsWithin_im_pos (a : ℂ) {x : ℂ}
    (hx0 : x ≠ 0) (hx1 : ‖x‖ < 1) :
    Tendsto (zeroBalancedSeries a) (𝓝[{z : ℂ | 0 < z.im}] x) (𝓝 (zeroBalancedSeries a x)) := by
  have hx_ball : x ∈ Metric.ball (0 : ℂ) 1 := by simpa using hx1
  have hlog : Tendsto Complex.log (𝓝[{z : ℂ | 0 < z.im}] x) (𝓝 (Complex.log x)) := by
    by_cases hsp : x ∈ Complex.slitPlane
    · exact (continuousAt_clog hsp).continuousWithinAt.tendsto
    · rw [Complex.mem_slitPlane_iff, not_or, not_lt, not_ne_iff] at hsp
      have hre : x.re < 0 := hsp.1.lt_of_ne fun h ↦ hx0 (Complex.ext h hsp.2)
      have hsub : {z : ℂ | 0 < z.im} ⊆ {z : ℂ | 0 ≤ z.im} := fun _ hz ↦ by
        simp only [Set.mem_ofPred] at hz ⊢; exact hz.le
      exact ((Complex.continuousWithinAt_log_of_re_neg_of_im_zero hre hsp.2).mono hsub).tendsto
  have hS1 := (analyticOnNhd_zeroBalancedCoeffSeries a x hx_ball).continuousAt
  have hS2 := (analyticOnNhd_zeroBalancedDigammaSeries a x hx_ball).continuousAt
  have htend := (tendsto_const_nhds (x := Complex.Gamma (2 * a) / Complex.Gamma a ^ 2)).mul
    ((hlog.neg.mul hS1.continuousWithinAt.tendsto).add hS2.continuousWithinAt.tendsto)
  have hval : Complex.Gamma (2 * a) / Complex.Gamma a ^ 2 *
      (-Complex.log x * (∑' k : ℕ, zeroBalancedCoeff a k * x ^ k) +
        ∑' k : ℕ, zeroBalancedCoeff a k *
          (2 * (Complex.digamma (k + 1) - Complex.digamma (k + a))) * x ^ k) =
      zeroBalancedSeries a x := by
    change _ = Complex.Gamma (2 * a) / Complex.Gamma a ^ 2 * ∑' k, zeroBalancedTerm a x k
    rw [tsum_zeroBalancedTerm_eq_split a hx1]
  rw [hval] at htend
  refine htend.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hx_ball)] with z hz
  change _ = Complex.Gamma (2 * a) / Complex.Gamma a ^ 2 * ∑' k, zeroBalancedTerm a z k
  rw [tsum_zeroBalancedTerm_eq_split a (mem_ball_zero_iff.mp hz)]

/-! ### Parameter analyticity and Euler integral of the native zero-balanced series -/

private noncomputable def zeroBalancedHyperTerm (a z : ℂ) (n : ℕ) : ℂ :=
  ((n !⁻¹ : ℂ) * (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval a *
    ((ascPochhammer ℂ n).eval (2 * a))⁻¹) * z ^ n

private theorem zeroBalancedHyperTerm_succ (a z : ℂ) (k : ℕ) :
    zeroBalancedHyperTerm a z (k + 1) =
      zeroBalancedHyperTerm a z k * (((a + k) / (k + 1)) * ((a + k) / (2 * a + k)) * z) := by
  simp only [zeroBalancedHyperTerm, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    ascPochhammer_succ_eval, mul_inv, pow_succ, div_eq_mul_inv]
  ring

private theorem norm_zeroBalancedHyperTerm_ratio_le {a z : ℂ} {R : ℝ} {k : ℕ}
    (hz : ‖z‖ < 1) (ha : ‖a‖ ≤ R) (hR : 1 ≤ R) (hk : 16 * R / (1 - ‖z‖) ≤ k) :
    2 * a + k ≠ 0 ∧
      ‖((a + k) / (k + 1)) * ((a + k) / (2 * a + k)) * z‖ ≤ (1 + ‖z‖) / 2 := by
  set d := 1 - ‖z‖
  have hd0 : 0 < d := sub_pos.mpr hz
  have hdk : 16 * R ≤ k * d := (div_le_iff₀ hd0).mp hk
  have hkR : 16 * R ≤ k := hdk.trans (mul_le_of_le_one_right (Nat.cast_nonneg k)
    (sub_le_self 1 (norm_nonneg z)))
  have hare : -R ≤ a.re := (neg_le_neg ha).trans (abs_le.mp (abs_re_le_norm a)).1
  have h2a_re : (k : ℝ) - 2 * R ≤ ‖2 * a + k‖ := by
    have h := Complex.re_le_norm (2 * a + k)
    simp only [add_re, mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero, natCast_re] at h
    linarith
  have h2a_pos : 0 < ‖2 * a + k‖ := by linarith
  have hak : ‖a + k‖ ≤ R + k :=
    (norm_add_le a k).trans (by simpa [Complex.norm_natCast] using add_le_add_right ha (k : ℝ))
  have hf1 : ‖(a + k) / ((k : ℂ) + 1)‖ ≤ 1 + d / 4 := by
    rw [norm_div, show ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) by push_cast; rfl,
      Complex.norm_natCast, Nat.cast_add, Nat.cast_one, div_le_iff₀ (by positivity)]
    nlinarith
  have hf2 : ‖(a + k) / (2 * a + k)‖ ≤ 1 + d / 4 := by
    rw [norm_div, div_le_iff₀ h2a_pos]; nlinarith
  have hz0 := norm_nonneg z
  refine ⟨norm_pos_iff.mp h2a_pos, ?_⟩
  rw [norm_mul, norm_mul]
  exact (mul_le_mul_of_nonneg_right (mul_le_mul hf1 hf2 (norm_nonneg _) (by positivity))
    hz0).trans (by dsimp [d]; nlinarith [sq_nonneg (1 - ‖z‖), mul_nonneg (sq_nonneg (1 - ‖z‖)) hz0])

private theorem norm_zeroBalancedHyperTerm_add_le {a z : ℂ} {R : ℝ} {M : ℕ}
    (hz : ‖z‖ < 1) (ha : ‖a‖ ≤ R) (hR : 1 ≤ R) (hM : 16 * R / (1 - ‖z‖) ≤ M) (m : ℕ) :
    ‖zeroBalancedHyperTerm a z (M + m)‖ ≤
      ‖zeroBalancedHyperTerm a z M‖ * ((1 + ‖z‖) / 2) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_succ, zeroBalancedHyperTerm_succ, norm_mul, pow_succ]
    have hrat := (norm_zeroBalancedHyperTerm_ratio_le hz ha hR
      (hM.trans (Nat.cast_le.mpr (Nat.le_add_right M m)))).2
    exact (mul_le_mul ih hrat (norm_nonneg _)
      (mul_nonneg (norm_nonneg _) (pow_nonneg (by positivity) m))).trans_eq (by ring)

private theorem exists_closedBall_zeroBalancedHyperTerm {a₀ z : ℂ} {M : ℕ}
    (ha₀ : ∀ n : ℕ, 2 * a₀ ≠ -(n : ℂ)) (hz : ‖z‖ < 1)
    (hM : 16 * (‖a₀‖ + 1) / (1 - ‖z‖) ≤ M) :
    ∃ r > 0, (∀ a ∈ closedBall a₀ r, ‖a‖ ≤ ‖a₀‖ + 1) ∧
      ∀ n : ℕ, DifferentiableOn ℂ (fun a ↦ zeroBalancedHyperTerm a z n) (closedBall a₀ r) := by
  have hR : 1 ≤ ‖a₀‖ + 1 := le_add_of_nonneg_left (norm_nonneg a₀)
  have hP_cont : Continuous fun a : ℂ ↦ (ascPochhammer ℂ M).eval (2 * a) :=
    (Polynomial.differentiable (ascPochhammer ℂ M)).continuous.comp
      (continuous_const.mul continuous_id)
  have hPa₀ : (ascPochhammer ℂ M).eval (2 * a₀) ≠ 0 := fun h0 ↦ by
    obtain ⟨k, _, hk⟩ := (ascPochhammer_eval_eq_zero_iff M (2 * a₀)).mp h0
    exact ha₀ k (neg_eq_iff_eq_neg.mp hk.symm)
  obtain ⟨r₀, hr₀, hball⟩ := Metric.isOpen_iff.mp (isOpen_ne.preimage hP_cont) a₀ hPa₀
  let r := min (r₀ / 2) (1 / 2)
  have haR : ∀ a ∈ closedBall a₀ r, ‖a‖ ≤ ‖a₀‖ + 1 := fun a ha ↦
    ((norm_add_le a₀ (a - a₀)).trans_eq' (by ring_nf)).trans
      (by linarith [mem_closedBall_iff_norm.mp ha, min_le_right (r₀ / 2) (1 / 2)])
  refine ⟨r, lt_min (half_pos hr₀) (by norm_num), haR, fun n a ha ↦ ?_⟩
  have hne : (ascPochhammer ℂ n).eval (2 * a) ≠ 0 := fun h0 ↦ by
    obtain ⟨k, _, hk⟩ := (ascPochhammer_eval_eq_zero_iff n (2 * a)).mp h0
    rcases lt_or_ge k M with hkM | hkM
    · exact hball (mem_ball_iff_norm.mpr ((mem_closedBall_iff_norm.mp ha).trans_lt
        ((min_le_left _ _).trans_lt (half_lt_self hr₀))))
        ((ascPochhammer_eval_eq_zero_iff M (2 * a)).mpr ⟨k, hkM, hk⟩)
    · exact (norm_zeroBalancedHyperTerm_ratio_le hz (haR a ha) hR
        (hM.trans (Nat.cast_le.mpr hkM))).1 (by linear_combination hk)
  have hp1 : DifferentiableAt ℂ (fun b : ℂ ↦ (ascPochhammer ℂ n).eval b) a :=
    Polynomial.differentiableAt _
  have hp2 : DifferentiableAt ℂ (fun b : ℂ ↦ (ascPochhammer ℂ n).eval (2 * b)) a :=
    (Polynomial.differentiableAt (ascPochhammer ℂ n)).comp a (differentiableAt_id.const_mul 2)
  exact (((((differentiableAt_const _).mul hp1).mul hp1).mul (hp2.inv hne)).mul_const
    (z ^ n)).differentiableWithinAt

/-- For fixed `‖z‖ < 1`, `a ↦ ₂F₁(a, a; 2a; z)` is complex analytic away from the poles
`2a = -n` (`n : ℕ`). -/
theorem analyticOnNhd_ordinaryHypergeometric_zeroBalanced_left {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticOnNhd ℂ (fun a : ℂ ↦ ₂F₁ a a (2 * a) z) {a : ℂ | ∀ n : ℕ, 2 * a ≠ -(n : ℂ)} := by
  intro a₀ ha₀
  let M : ℕ := ⌈16 * (‖a₀‖ + 1) / (1 - ‖z‖)⌉₊ + 1
  have hM : 16 * (‖a₀‖ + 1) / (1 - ‖z‖) ≤ M := by
    dsimp [M]; push_cast; linarith [Nat.le_ceil (16 * (‖a₀‖ + 1) / (1 - ‖z‖))]
  obtain ⟨r, hr, hcb_R, hterm_diff⟩ := exists_closedBall_zeroBalancedHyperTerm ha₀ hz hM
  obtain ⟨C, hC⟩ := (isCompact_closedBall a₀ r).exists_bound_of_continuousOn
    (hterm_diff M).continuousOn
  have hu : Summable fun n : ℕ ↦ max C 0 * ((1 + ‖z‖) / 2) ^ (n - M) :=
    (summable_nat_add_iff M).mp <| by
      simpa using (summable_geometric_of_lt_one (by positivity) (by linarith)).mul_left (max C 0)
  have huni : HasSumUniformlyOn (fun n a ↦ zeroBalancedHyperTerm a z n)
      (fun a ↦ ₂F₁ a a (2 * a) z) (ball a₀ r) := by
    have heq (a : ℂ) : ₂F₁ a a (2 * a) z = ∑' n : ℕ, zeroBalancedHyperTerm a z n := by
      simpa [ordinaryHypergeometric, zeroBalancedHyperTerm] using
        ordinaryHypergeometric_sum_eq a a (2 * a) z
    simp_rw [heq]
    apply HasSumUniformlyOn.of_norm_le_summable_eventually hu
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop M] with n hn a ha
    have hacb := ball_subset_closedBall ha
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    simpa using (norm_zeroBalancedHyperTerm_add_le hz (hcb_R a hacb)
      (le_add_of_nonneg_left (norm_nonneg a₀)) hM m).trans
      (mul_le_mul_of_nonneg_right ((hC a hacb).trans (le_max_left C 0))
        (pow_nonneg (by positivity) m))
  exact ((hasSumUniformlyOn_iff_tendstoUniformlyOn.mp
    huni).tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall fun _ ↦ DifferentiableOn.fun_sum fun n _ ↦
      (hterm_diff n).mono ball_subset_closedBall) Metric.isOpen_ball).analyticOnNhd
    Metric.isOpen_ball a₀ (mem_ball_self hr)

private theorem eulerTerm_integral_eq {a : ℝ} (ha : 0 < a) (z : ℝ) (n : ℕ) :
    Real.Gamma (2 * a) / Real.Gamma a ^ 2 *
      (∫ t in (0 : ℝ)..1,
        t ^ (a - 1) * (1 - t) ^ (a - 1) * (Ring.multichoose a n * (z * t) ^ n)) =
      ((n !⁻¹ : ℝ) * (ascPochhammer ℝ n).eval a * (ascPochhammer ℝ n).eval a *
        ((ascPochhammer ℝ n).eval (2 * a))⁻¹) * z ^ n := by
  have hcongr : ∫ t in (0 : ℝ)..1,
      t ^ (a - 1) * (1 - t) ^ (a - 1) * (Ring.multichoose a n * (z * t) ^ n) =
      Ring.multichoose a n * z ^ n *
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
  have hGa0 := (Real.Gamma_pos_of_pos ha).ne'
  have hG2a0 := (Real.Gamma_pos_of_pos (by positivity : 0 < 2 * a)).ne'
  have hP2a0 := (ascPochhammer_pos n (2 * a) (by positivity)).ne'
  rw [show a + (n : ℝ) + a = 2 * a + n by ring, hmc,
    show Real.Gamma (a + n) = (ascPochhammer ℝ n).eval a * Real.Gamma a by
      rw [← hGa, div_mul_cancel₀ _ hGa0],
    show Real.Gamma (2 * a + n) = (ascPochhammer ℝ n).eval (2 * a) * Real.Gamma (2 * a) by
      rw [← hG2a, div_mul_cancel₀ _ hG2a0]]
  field_simp

/-- Euler's integral representation for the real zero-balanced hypergeometric series (DLMF 15.6.1):
for `0 < a` and `|z| < 1`,
`₂F₁(a, a; 2a; z) = (Γ(2a) / Γ(a)²) ∫₀¹ t^(a - 1) (1 - t)^(a - 1) (1 - z t)^(-a) dt`. -/
theorem ordinaryHypergeometric_zeroBalanced_eq_integral {a z : ℝ}
    (ha : 0 < a) (hz : |z| < 1) :
    ₂F₁ a a (2 * a) z =
      Real.Gamma (2 * a) / Real.Gamma a ^ 2 *
        ∫ t in (0 : ℝ)..1, t ^ (a - 1) * (1 - t) ^ (a - 1) * (1 - z * t) ^ (-a) := by
  let w : ℝ → ℝ := fun t ↦ t ^ (a - 1) * (1 - t) ^ (a - 1)
  let F : ℕ → ℝ → ℝ := fun n t ↦ w t * (Ring.multichoose a n * (z * t) ^ n)
  let bound : ℕ → ℝ → ℝ := fun n t ↦ w t * (Ring.multichoose a n * |z| ^ n)
  have hsum_z := hasSum_multichoose_mul_geometric_of_abs_lt_one (r := a) (x := |z|)
    (by rwa [abs_abs])
  have hw_int : IntervalIntegrable w volume 0 1 :=
    intervalIntegrable_rpow_mul_one_sub_rpow ha ha ⟨le_rfl, zero_le_one⟩ ⟨zero_le_one, le_rfl⟩
  have hdct : HasSum (fun n ↦ ∫ t in (0 : ℝ)..1, F n t)
      (∫ t in (0 : ℝ)..1, w t * (1 - z * t) ^ (-a)) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence bound ?_ ?_ ?_ ?_ ?_
    · intro n; rw [uIoc_of_le zero_le_one]
      exact (hw_int.mul_continuousOn (by fun_prop)).1.aestronglyMeasurable
    · intro n; refine Eventually.of_forall fun t ht ↦ ?_
      rw [uIoc_of_le zero_le_one] at ht
      have hw0 : 0 ≤ w t := mul_nonneg (Real.rpow_nonneg ht.1.le (a - 1))
        (Real.rpow_nonneg (sub_nonneg.mpr ht.2) (a - 1))
      have hmc0 := multichoose_nonneg_of_pos ha n
      dsimp only [F, bound]
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hw0, abs_mul, abs_of_nonneg hmc0, abs_pow,
        abs_mul, abs_of_pos ht.1, mul_pow]
      exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_of_le_one_right (pow_nonneg (abs_nonneg z) n)
          (pow_le_one₀ ht.1.le ht.2)) hmc0) hw0
    · exact Eventually.of_forall fun t _ ↦ hsum_z.summable.mul_left (w t)
    · refine (hw_int.mul_const (1 / (1 - |z|) ^ a)).congr fun t _ ↦ ?_
      dsimp [bound]; rw [tsum_mul_left, hsum_z.tsum_eq]
    · refine Eventually.of_forall fun t ht ↦ ?_
      rw [uIoc_of_le zero_le_one] at ht
      have hzt : |z * t| < 1 := by
        rw [abs_mul, abs_of_pos ht.1]
        exact (mul_le_of_le_one_right (abs_nonneg z) ht.2).trans_lt hz
      have hst := (hasSum_multichoose_mul_geometric_of_abs_lt_one (r := a) hzt).mul_left (w t)
      rwa [one_div, ← Real.rpow_neg (by linarith [(abs_lt.mp hzt).2])] at hst
  simpa [ordinaryHypergeometric, ordinaryHypergeometric_sum_eq, w, mul_assoc] using
    ((hdct.mul_left (Real.Gamma (2 * a) / Real.Gamma a ^ 2)).congr_fun fun n ↦
      (eulerTerm_integral_eq ha z n).symm).tsum_eq

end TauCeti
