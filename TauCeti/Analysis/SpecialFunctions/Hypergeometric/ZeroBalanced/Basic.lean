/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Gamma.Digamma
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Real.Pi.Bounds
import TauCeti.Analysis.Analytic.Binomial
import TauCeti.Analysis.Complex.NegNatTopology
import TauCeti.Analysis.SpecialFunctions.Gamma.Analytic
import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Digamma.Basic
import TauCeti.Analysis.SpecialFunctions.Gamma.Digamma.Bounds
import TauCeti.Analysis.SpecialFunctions.Hypergeometric.Ordinary.Basic

/-!
# The zero-balanced hypergeometric logarithmic series and its remainder estimates

Specializing DLMF 15.8.10 to `m = 0` and `b = a` (with the ordinary normalization in DLMF 15.2.2)
gives `TauCeti.zeroBalancedSeries a x`,
`Γ(2a) / Γ(a)² * ∑' k, (a)_k² / (k!)² * x^k * (-log x + 2(ψ(k + 1) - ψ(k + a)))`, written with
Mathlib's principal logarithm `Complex.log`, together with its `k ≥ 1` inner tail
`TauCeti.zeroBalancedTail`:

* `zeroBalancedSeries` and `zeroBalancedTail` are analytic on `Metric.ball 0 1 ∩ Complex.slitPlane`,
  analytic in `a` away from `2a ∈ -ℕ` (resp. `a ∈ -ℕ_{≥1}`) for `‖x‖ < 1`, and on
  `0 < ‖x‖ < 1` `zeroBalancedSeries` equals its limit from `{z | 0 < z.im}`.
* Splitting off `k = 0` writes `zeroBalancedSeries a x` on `‖x‖ < 1` as
  `Γ(2a) / Γ(a)² * (-log x - 2γ - 2ψ(a) + zeroBalancedTail a x)` with explicit
  `O(‖x‖(1 + ‖log x‖) / (1 - ‖x‖))` bounds on `zeroBalancedTail` and its `a`-derivatives.

The lens identity with `₂F₁(a, a; 2a; 1 - x)` is proved in
`TauCeti.Analysis.SpecialFunctions.Hypergeometric.ZeroBalanced.Connection`.

## References

* F. Calegari, V. Dimitrov and Y. Tang (CDT), *The unbounded denominators conjecture*,
  J. Amer. Math. Soc. 38 (2025), Lemma 5.1.20 (p. 672) and Lemma 5.2.9 (p. 676).
* [NIST DLMF, 15.8.10](https://dlmf.nist.gov/15.8.E10), [15.2.2](https://dlmf.nist.gov/15.2.E2).
-/

public section

open Complex Filter Metric Set
open scoped ENNReal Nat Real Topology

namespace TauCeti

/-! ### Definitions and basic series properties -/

/-- The zero-balanced hypergeometric series at parameter `a`, using Mathlib's principal logarithm:
`Γ(2a) / Γ(a)² · ∑' k, (a)_k² / (k!)² · x^k · (-log x + 2(ψ(k + 1) - ψ(k + a)))`
(CDT Lemma 5.1.20; DLMF 15.8.10 at `m = 0` and `b = a`). Outside `0 < ‖x‖ < 1` (including `x = 0`,
where `Complex.log 0 = 0`) and at poles of `Gamma` or `digamma`, this is only the totalized value.
-/
noncomputable def zeroBalancedSeries (a x : ℂ) : ℂ :=
  Complex.Gamma (2 * a) / Complex.Gamma a ^ 2 *
    ∑' k : ℕ, ordinaryHypergeometricCoefficient a a 1 k * x ^ k *
      (-Complex.log x + 2 * (Complex.digamma (k + 1) - Complex.digamma (k + a)))

/-- Unfolding lemma for `zeroBalancedSeries`. -/
theorem zeroBalancedSeries_def (a x : ℂ) :
    zeroBalancedSeries a x =
      Complex.Gamma (2 * a) / Complex.Gamma a ^ 2 *
        ∑' k : ℕ, ordinaryHypergeometricCoefficient a a 1 k * x ^ k *
          (-Complex.log x + 2 * (Complex.digamma (k + 1) - Complex.digamma (k + a))) :=
  (rfl)

/-- The `k ≥ 1` inner tail of `zeroBalancedSeries`, indexed by `k ↦ k + 1` without the Gamma
prefactor. -/
noncomputable def zeroBalancedTail (a x : ℂ) : ℂ :=
  ∑' k : ℕ, ordinaryHypergeometricCoefficient a a 1 (k + 1) * x ^ (k + 1) *
    (-Complex.log x + 2 *
      (Complex.digamma ((k + 1 : ℕ) + 1) - Complex.digamma ((k + 1 : ℕ) + a)))

/-- Unfolding lemma for `zeroBalancedTail`. -/
theorem zeroBalancedTail_def (a x : ℂ) :
    zeroBalancedTail a x =
      ∑' k : ℕ, ordinaryHypergeometricCoefficient a a 1 (k + 1) * x ^ (k + 1) *
        (-Complex.log x + 2 *
          (Complex.digamma ((k + 1 : ℕ) + 1) - Complex.digamma ((k + 1 : ℕ) + a))) := (rfl)

/-- Every term of `zeroBalancedTail` carries a positive power of `x`, so the tail vanishes at `0`.
-/
@[simp]
theorem zeroBalancedTail_zero_right (a : ℂ) : zeroBalancedTail a 0 = 0 := by
  simp [zeroBalancedTail]

/-- At `a = 0`, every Pochhammer factor `(0)_(k + 1)` vanishes, so `zeroBalancedTail 0 x = 0`. -/
@[simp]
theorem zeroBalancedTail_zero_left (x : ℂ) : zeroBalancedTail 0 x = 0 := by
  simp [zeroBalancedTail, ordinaryHypergeometricCoefficient, ascPochhammer_succ_left]

/-- At `a = 0`, the prefactor `Γ(0) / Γ(0)²` vanishes, so `zeroBalancedSeries 0 x = 0`. -/
@[simp]
theorem zeroBalancedSeries_zero_left (x : ℂ) : zeroBalancedSeries 0 x = 0 := by
  simp [zeroBalancedSeries]

/-- At `x = 0`, only the `k = 0` term of `zeroBalancedSeries` survives, giving
`Γ(2a) / Γ(a)² * (2 * (ψ(1) - ψ(a)))`. -/
@[simp]
theorem zeroBalancedSeries_zero_right (a : ℂ) :
    zeroBalancedSeries a 0 =
      Complex.Gamma (2 * a) / Complex.Gamma a ^ 2 *
        (2 * (Complex.digamma 1 - Complex.digamma a)) := by
  simp only [zeroBalancedSeries, Complex.log_zero, neg_zero, zero_add]
  rw [tsum_eq_single 0 fun k hk ↦ by simp [zero_pow hk]]
  simp [ordinaryHypergeometricCoefficient]

private noncomputable def zeroBalancedTerm (a x : ℂ) (k : ℕ) : ℂ :=
  ordinaryHypergeometricCoefficient a a 1 k * x ^ k *
    (-Complex.log x + 2 * (Complex.digamma (k + 1) - Complex.digamma (k + a)))

private theorem zeroBalancedSeries_eq_tsum_term (a x : ℂ) :
    zeroBalancedSeries a x =
      Complex.Gamma (2 * a) / Complex.Gamma a ^ 2 * ∑' k : ℕ, zeroBalancedTerm a x k := (rfl)

-- `zeroBalancedTail a x` is definitionally `∑' k, zeroBalancedTerm a x (k + 1)`
-- (aligning the `((k + 1 : ℕ) : ℂ) + 1` cast shape in the digamma arguments).
private theorem zeroBalancedTail_eq_tsum_term (a x : ℂ) :
    zeroBalancedTail a x = ∑' k : ℕ, zeroBalancedTerm a x (k + 1) := (rfl)

private theorem norm_coeff_mul_two_mul_digamma_sub_le {b : ℂ} {R : ℝ} (hb : ‖b‖ ≤ R)
    {k : ℕ} (hk : ⌈R⌉₊ + 1 ≤ k) :
    ‖ordinaryHypergeometricCoefficient b b 1 k *
        (2 * (Complex.digamma (k + 1) - Complex.digamma (k + b)))‖ ≤
      2 * (1 + R) * (Real.pi ^ 2 / 6) * (Ring.multichoose R k) ^ 2 := by
  have hdig := Complex.norm_digamma_add_one_sub_digamma_add_le (z := (k : ℂ)) (b := b) hb (by
    simp only [natCast_re]
    linarith [Nat.le_ceil R, (by exact_mod_cast hk : (⌈R⌉₊ : ℝ) + 1 ≤ k)])
  have hdig2 : ‖(2 : ℂ) * (Complex.digamma (k + 1) - Complex.digamma (k + b))‖ ≤
      2 * (1 + R) * (Real.pi ^ 2 / 6) := by
    rw [norm_mul, Complex.norm_ofNat]
    exact (mul_le_mul_of_nonneg_left hdig zero_le_two).trans_eq (by ring)
  have hc : ‖ordinaryHypergeometricCoefficient b b 1 k‖ ≤ (Ring.multichoose R k) ^ 2 :=
    (norm_ordinaryHypergeometricCoefficient_one_le hb hb k).trans_eq (sq _).symm
  rw [norm_mul]
  exact (mul_le_mul hc hdig2 (norm_nonneg _) (by positivity)).trans_eq (by ring)

private theorem one_le_radius_zeroBalancedDigammaSeries (a : ℂ) :
    1 ≤ (FormalMultilinearSeries.ofScalars ℂ fun k : ℕ ↦
      ordinaryHypergeometricCoefficient a a 1 k *
        (2 * (Complex.digamma (k + 1) - Complex.digamma (k + a)))).radius := by
  refine ENNReal.le_of_forall_nnreal_lt fun r hr ↦ ?_
  rw [ENNReal.coe_lt_one_iff] at hr
  let R := max ‖a‖ 1
  refine FormalMultilinearSeries.le_radius_ofScalars_of_eventually_le
    ((hasSum_multichoose_sq_mul_pow R (x := (r : ℝ))
      (by simpa [abs_of_nonneg r.coe_nonneg] using NNReal.coe_lt_one.mpr hr)).summable.mul_left
      (2 * (1 + R) * (Real.pi ^ 2 / 6))) ?_
  filter_upwards [eventually_ge_atTop (⌈R⌉₊ + 1)] with k hk
  exact (mul_le_mul_of_nonneg_right
    (norm_coeff_mul_two_mul_digamma_sub_le (le_max_left ‖a‖ 1) hk)
    (pow_nonneg r.coe_nonneg k)).trans_eq (by ring)

/-- On the open unit disc, the digamma-weighted component series in
`zeroBalancedSeries_eq_log_mul_add` is summable. -/
theorem summable_zeroBalancedSeries_digamma (a : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    Summable fun k : ℕ ↦
      ordinaryHypergeometricCoefficient a a 1 k *
        (2 * (Complex.digamma (k + 1) - Complex.digamma (k + a))) * x ^ k := by
  have hx_r : ‖x‖ₑ < (FormalMultilinearSeries.ofScalars ℂ fun k : ℕ ↦
      ordinaryHypergeometricCoefficient a a 1 k *
        (2 * (Complex.digamma (k + 1) - Complex.digamma (k + a)))).radius :=
    (by rw [← ofReal_norm]; exact ENNReal.ofReal_lt_one.mpr hx : ‖x‖ₑ < 1).trans_le
      (one_le_radius_zeroBalancedDigammaSeries a)
  exact (FormalMultilinearSeries.summable_norm_mul_pow_of_lt_radius _ hx_r).of_norm

/-- On the open unit disc, the inner series of `zeroBalancedSeries` is summable. -/
theorem summable_zeroBalancedSeries (a : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    Summable fun k : ℕ ↦
      ordinaryHypergeometricCoefficient a a 1 k * x ^ k *
        (-Complex.log x + 2 * (Complex.digamma (k + 1) - Complex.digamma (k + a))) :=
  (((hasSum_ordinaryHypergeometric (𝔸 := ℂ) a a 1 hx).summable.mul_right
    (-Complex.log x)).add (summable_zeroBalancedSeries_digamma a hx)).congr fun k ↦ by
      simp only [smul_eq_mul]; ring

/-- On the open unit disc, the `zeroBalancedSeries` summand has sum `zeroBalancedSeries a x`. -/
theorem hasSum_zeroBalancedSeries (a : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun k : ℕ ↦
      Complex.Gamma (2 * a) / Complex.Gamma a ^ 2 *
        (ordinaryHypergeometricCoefficient a a 1 k * x ^ k *
          (-Complex.log x + 2 * (Complex.digamma (k + 1) - Complex.digamma (k + a)))))
      (zeroBalancedSeries a x) :=
  (summable_zeroBalancedSeries a hx).hasSum.mul_left _

/-- On the open unit disc, the `zeroBalancedTail` series is summable. -/
theorem summable_zeroBalancedTail (a : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    Summable fun k : ℕ ↦
      ordinaryHypergeometricCoefficient a a 1 (k + 1) * x ^ (k + 1) *
        (-Complex.log x +
          2 * (Complex.digamma ((k + 1 : ℕ) + 1) - Complex.digamma ((k + 1 : ℕ) + a))) :=
  (summable_nat_add_iff 1).mpr (summable_zeroBalancedSeries a hx)

/-- On the open unit disc, the `zeroBalancedTail` series sums to `zeroBalancedTail a x`. -/
theorem hasSum_zeroBalancedTail (a : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    HasSum (fun k : ℕ ↦
      ordinaryHypergeometricCoefficient a a 1 (k + 1) * x ^ (k + 1) *
        (-Complex.log x +
          2 * (Complex.digamma ((k + 1 : ℕ) + 1) - Complex.digamma ((k + 1 : ℕ) + a))))
      (zeroBalancedTail a x) :=
  (summable_zeroBalancedTail a hx).hasSum

private theorem tsum_zeroBalancedTerm_eq_split (a : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    ∑' k : ℕ, zeroBalancedTerm a x k =
      -Complex.log x * ordinaryHypergeometric a a 1 x +
        ∑' k : ℕ, ordinaryHypergeometricCoefficient a a 1 k *
          (2 * (Complex.digamma (k + 1) - Complex.digamma (k + a))) * x ^ k :=
  ((((hasSum_ordinaryHypergeometric (𝔸 := ℂ) a a 1 hx).mul_left (-Complex.log x)).add
    (summable_zeroBalancedSeries_digamma a hx).hasSum).congr_fun fun k ↦ by
      dsimp [zeroBalancedTerm]; ring).tsum_eq

/-- On the open unit disc, `zeroBalancedSeries a x` separates into `-log x * ₂F₁(a, a; 1; x)`
plus the holomorphic digamma-weighted power series. -/
theorem zeroBalancedSeries_eq_log_mul_add (a : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    zeroBalancedSeries a x =
      Complex.Gamma (2 * a) / Complex.Gamma a ^ 2 *
        (-Complex.log x * ordinaryHypergeometric a a 1 x +
        ∑' k : ℕ, ordinaryHypergeometricCoefficient a a 1 k *
          (2 * (Complex.digamma (k + 1) - Complex.digamma (k + a))) * x ^ k) := by
  rw [zeroBalancedSeries_eq_tsum_term, tsum_zeroBalancedTerm_eq_split a hx]

/-- On the open unit disc, `zeroBalancedTail a x` separates into
`-log x * (₂F₁(a, a; 1; x) - 1)` plus the digamma-weighted power series minus its constant term
`2 * (ψ(1) - ψ(a))`. -/
theorem zeroBalancedTail_eq_log_mul_add (a : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    zeroBalancedTail a x =
      -Complex.log x * (ordinaryHypergeometric a a 1 x - 1) +
        ((∑' k : ℕ, ordinaryHypergeometricCoefficient a a 1 k *
          (2 * (Complex.digamma (k + 1) - Complex.digamma (k + a))) * x ^ k) -
          2 * (Complex.digamma 1 - Complex.digamma a)) := by
  have h0 : zeroBalancedTerm a x 0 =
      -Complex.log x + 2 * (Complex.digamma 1 - Complex.digamma a) := by
    simp [zeroBalancedTerm, ordinaryHypergeometricCoefficient]
  have hsum : ∑' k : ℕ, zeroBalancedTerm a x k = zeroBalancedTerm a x 0 + zeroBalancedTail a x := by
    rw [zeroBalancedTail_eq_tsum_term]
    exact (summable_zeroBalancedSeries a hx).tsum_eq_zero_add
  rw [tsum_zeroBalancedTerm_eq_split a hx, h0] at hsum
  linear_combination -hsum

/-- On the open unit disc, `zeroBalancedSeries a x` splits into its `k = 0` logarithmic term
`-log x - 2γ - 2ψ(a)` and `zeroBalancedTail a x`. -/
theorem zeroBalancedSeries_eq_add_zeroBalancedTail (a : ℂ) {x : ℂ} (hx : ‖x‖ < 1) :
    zeroBalancedSeries a x =
      Complex.Gamma (2 * a) / Complex.Gamma a ^ 2 *
        (-Complex.log x - 2 * Real.eulerMascheroniConstant - 2 * Complex.digamma a +
          zeroBalancedTail a x) := by
  rw [zeroBalancedSeries_eq_tsum_term]
  have hsum : Summable (zeroBalancedTerm a x) := summable_zeroBalancedSeries a hx
  rw [hsum.tsum_eq_zero_add, ← zeroBalancedTail_eq_tsum_term]
  congr 1
  rw [(by simp [zeroBalancedTerm, ordinaryHypergeometricCoefficient, Complex.digamma_one]; ring :
    zeroBalancedTerm a x 0 =
      -Complex.log x - 2 * Real.eulerMascheroniConstant - 2 * Complex.digamma a)]

/-! ### Uniform remainder and parameter-derivative bounds -/

/-- Explicit uniform bound on `zeroBalancedTail a x` for `0 ≤ a.re`, `‖a‖ ≤ 1`, and `‖x‖ < 1`. -/
theorem norm_zeroBalancedTail_le {a x : ℂ} (hre : 0 ≤ a.re) (ha : ‖a‖ ≤ 1) (hx : ‖x‖ < 1) :
    ‖zeroBalancedTail a x‖ ≤ 8 / (1 - ‖x‖) * ‖x‖ * (1 + ‖Complex.log x‖) := by
  let M : ℝ := 8 * (1 + ‖Complex.log x‖)
  have hgeom : HasSum (fun k : ℕ ↦ ‖x‖ ^ (k + 1) * M)
      (8 / (1 - ‖x‖) * ‖x‖ * (1 + ‖Complex.log x‖)) := by
    convert ((((hasSum_geometric_of_lt_one (norm_nonneg x) hx).mul_left ‖x‖).mul_right M).congr_fun
      fun k ↦ by rw [← pow_succ']) using 1
    dsimp [M]; ring
  have hterm (k : ℕ) : ‖zeroBalancedTerm a x (k + 1)‖ ≤ ‖x‖ ^ (k + 1) * M := by
    have hc : ‖ordinaryHypergeometricCoefficient a a 1 (k + 1)‖ ≤ 1 :=
      norm_ordinaryHypergeometricCoefficient_one_le_one ha ha (k + 1)
    have h1 := Complex.norm_digamma_sub_digamma_le_of_one_le_re
      (s := ((k + 1 : ℕ) : ℂ) + 1) (w := ((k + 1 : ℕ) : ℂ) + a)
      (by simp only [add_re, natCast_re, Nat.cast_add, Nat.cast_one, one_re]; linarith)
      (by simp only [add_re, natCast_re, Nat.cast_add, Nat.cast_one, one_re]; linarith)
    rw [add_sub_add_left_eq_sub] at h1
    have h1a : ‖(1 : ℂ) - a‖ ≤ 2 := (norm_sub_le 1 a).trans (by rw [norm_one]; linarith)
    have hdig : ‖Complex.digamma (((k + 1 : ℕ) : ℂ) + 1) -
        Complex.digamma (((k + 1 : ℕ) : ℂ) + a)‖ ≤ 7 / 2 := by
      nlinarith [Real.pi_pos, Real.pi_lt_d2, pow_lt_pow_left₀ Real.pi_lt_d2 Real.pi_pos.le
        (by norm_num : 2 ≠ 0)]
    have hlog : ‖-Complex.log x + 2 * (Complex.digamma (((k + 1 : ℕ) : ℂ) + 1) -
        Complex.digamma (((k + 1 : ℕ) : ℂ) + a))‖ ≤ M :=
      (norm_add_le _ _).trans <| by
        rw [norm_neg, norm_mul, Complex.norm_ofNat]
        dsimp [M]; linarith [norm_nonneg (Complex.log x)]
    rw [zeroBalancedTerm, norm_mul, norm_mul, norm_pow]
    exact (mul_le_mul (mul_le_mul_of_nonneg_right hc (pow_nonneg (norm_nonneg x) _)) hlog
      (norm_nonneg _) (by positivity)).trans_eq (by ring)
  have hns := Summable.of_nonneg_of_le (fun _ ↦ norm_nonneg _) hterm hgeom.summable
  rw [zeroBalancedTail_eq_tsum_term, ← hgeom.tsum_eq]
  exact (norm_tsum_le_tsum_norm hns).trans (hns.tsum_le_tsum hterm hgeom.summable)

/-- For fixed `‖x‖ < 1`, `b ↦ zeroBalancedTail b x` is complex analytic away from the negative
integers `-1, -2, …`. -/
theorem analyticOnNhd_zeroBalancedTail_left {x : ℂ} (hx : ‖x‖ < 1) :
    AnalyticOnNhd ℂ (fun b : ℂ ↦ zeroBalancedTail b x)
      {b : ℂ | ∀ m : ℕ, b ≠ -((m + 1 : ℕ) : ℂ)} := by
  have hloc : HasSumLocallyUniformlyOn (fun k b ↦ zeroBalancedTerm b x (k + 1))
      (fun b ↦ zeroBalancedTail b x) {b : ℂ | ∀ m : ℕ, b ≠ -((m + 1 : ℕ) : ℂ)} := by
    simp_rw [zeroBalancedTail_eq_tsum_term]
    apply hasSumLocallyUniformlyOn_of_forall_compact Complex.isOpen_ne_neg_succ
    intro K _ hK
    obtain ⟨B, hB⟩ := hK.exists_bound_of_continuousOn continuous_id.continuousOn
    let R := max B 1
    let C := ‖Complex.log x‖ + 2 * (1 + R) * (Real.pi ^ 2 / 6)
    apply HasSumUniformlyOn.of_norm_le_summable_eventually
      (((summable_nat_add_iff 1).mpr
        (hasSum_multichoose_sq_mul_pow R (x := ‖x‖)
          (by simpa [abs_of_nonneg (norm_nonneg x)] using hx)).summable).mul_left C)
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop (⌈R⌉₊ + 1)] with k hk b hbK
    have hbR : ‖b‖ ≤ R := (hB b hbK).trans (le_max_left _ _)
    have hc : ‖ordinaryHypergeometricCoefficient b b 1 (k + 1)‖ ≤
        (Ring.multichoose R (k + 1)) ^ 2 :=
      (norm_ordinaryHypergeometricCoefficient_one_le hbR hbR (k + 1)).trans_eq (sq _).symm
    have hdig := norm_coeff_mul_two_mul_digamma_sub_le hbR (hk.trans (Nat.le_succ k))
    have hterm : zeroBalancedTerm b x (k + 1) =
        ordinaryHypergeometricCoefficient b b 1 (k + 1) * (-Complex.log x) * x ^ (k + 1) +
          ordinaryHypergeometricCoefficient b b 1 (k + 1) *
            (2 * (Complex.digamma ((k + 1 : ℕ) + 1) - Complex.digamma ((k + 1 : ℕ) + b))) *
            x ^ (k + 1) := by
      dsimp [zeroBalancedTerm]; ring
    rw [hterm]
    refine (norm_add_le _ _).trans ?_
    have h1 : ‖ordinaryHypergeometricCoefficient b b 1 (k + 1) * (-Complex.log x) *
          x ^ (k + 1)‖ ≤
        (Ring.multichoose R (k + 1)) ^ 2 * ‖Complex.log x‖ * ‖x‖ ^ (k + 1) := by
      rw [norm_mul, norm_mul, norm_neg, norm_pow]
      gcongr
    have h2 : ‖ordinaryHypergeometricCoefficient b b 1 (k + 1) *
          (2 * (Complex.digamma ((k + 1 : ℕ) + 1) - Complex.digamma ((k + 1 : ℕ) + b))) *
          x ^ (k + 1)‖ ≤
        2 * (1 + R) * (Real.pi ^ 2 / 6) * (Ring.multichoose R (k + 1)) ^ 2 * ‖x‖ ^ (k + 1) := by
      rw [norm_mul, norm_pow]
      gcongr
    exact (add_le_add h1 h2).trans_eq (by dsimp [C]; ring)
  refine ((hasSumLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hloc).differentiableOn
    (Eventually.of_forall fun _ ↦ DifferentiableOn.fun_sum fun k _ b hb ↦ ?_)
    Complex.isOpen_ne_neg_succ).analyticOnNhd Complex.isOpen_ne_neg_succ
  have hbp : ∀ m : ℕ, ((k + 1 : ℕ) : ℂ) + b ≠ -(m : ℂ) := fun m hm ↦
    hb (k + m) (by push_cast at hm ⊢; linear_combination hm)
  have hcoeff :
      DifferentiableAt ℂ (fun z : ℂ ↦ ordinaryHypergeometricCoefficient z z 1 (k + 1)) b :=
    ((((differentiableAt_const _).mul (Polynomial.differentiableAt (ascPochhammer ℂ (k + 1)))).mul
      (Polynomial.differentiableAt (ascPochhammer ℂ (k + 1)))).mul_const _)
  exact ((hcoeff.mul_const _).mul
    ((differentiableAt_const _).add <| (differentiableAt_const 2).mul <|
      (differentiableAt_const _).sub <| (Complex.analyticAt_digamma hbp).differentiableAt.comp b
        (differentiableAt_id.const_add _))).differentiableWithinAt

private theorem norm_ofReal_sub_half (a : ℝ) : ‖(a : ℂ) - 1 / 2‖ = |a - 1 / 2| := by
  rw [show (a : ℂ) - 1 / 2 = ((a - 1 / 2 : ℝ) : ℂ) by push_cast; ring,
    Complex.norm_real, Real.norm_eq_abs]

/-- Cauchy derivative estimate for `b ↦ zeroBalancedTail b x` on `closedBall (1 / 2 : ℂ) (3 / 8)`
and `‖x‖ < 1`. -/
theorem norm_deriv_zeroBalancedTail_le {a x : ℂ}
    (ha : a ∈ closedBall (1 / 2 : ℂ) (3 / 8)) (hx : ‖x‖ < 1) :
    ‖deriv (fun b : ℂ ↦ zeroBalancedTail b x) a‖ ≤
      64 / (1 - ‖x‖) * ‖x‖ * (1 + ‖Complex.log x‖) := by
  have hre_half : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
  have hnorm_half : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  have hmem {b : ℂ} (hb : b ∈ closedBall a (1 / 8)) : 0 ≤ b.re ∧ ‖b‖ ≤ 1 := by
    have hb12 : ‖b - (1 / 2 : ℂ)‖ ≤ 1 / 2 :=
      ((norm_add_le (b - a) (a - (1 / 2 : ℂ))).trans_eq' (by ring_nf)).trans
        (by linarith [mem_closedBall_iff_norm.mp hb, mem_closedBall_iff_norm.mp ha])
    have hbre := (abs_le.mp (abs_re_le_norm (b - (1 / 2 : ℂ)))).1
    have hbn : ‖b‖ ≤ ‖(1 / 2 : ℂ)‖ + ‖b - (1 / 2 : ℂ)‖ :=
      (norm_add_le (1 / 2 : ℂ) (b - (1 / 2 : ℂ))).trans_eq' (by ring_nf)
    rw [sub_re, hre_half] at hbre
    rw [hnorm_half] at hbn
    exact ⟨by linarith, by linarith⟩
  have hdiff : DifferentiableOn ℂ (fun b : ℂ ↦ zeroBalancedTail b x) (closedBall a (1 / 8)) :=
    ((analyticOnNhd_zeroBalancedTail_left hx).mono fun b hb ↦
      Complex.ne_neg_succ_of_neg_one_lt_re (by linarith [(hmem hb).1])).differentiableOn
  exact (norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1 / 8)
    (hdiff.mono closure_ball_subset_closedBall).diffContOnCl
    (C := 8 / (1 - ‖x‖) * ‖x‖ * (1 + ‖Complex.log x‖)) fun _ hb ↦
      norm_zeroBalancedTail_le (hmem (sphere_subset_closedBall hb)).1
        (hmem (sphere_subset_closedBall hb)).2 hx).trans_eq (by ring)

/-- Real parameter derivative bound for `zeroBalancedTail` on `[1 / 8, 7 / 8]` and `‖x‖ < 1`. -/
theorem norm_deriv_ofReal_zeroBalancedTail_le {a : ℝ}
    (ha₁ : 1 / 8 ≤ a) (ha₂ : a ≤ 7 / 8) {x : ℂ} (hx : ‖x‖ < 1) :
    ‖deriv (fun b : ℝ ↦ zeroBalancedTail b x) a‖ ≤
      64 / (1 - ‖x‖) * ‖x‖ * (1 + ‖Complex.log x‖) := by
  have hd : DifferentiableAt ℂ (fun b : ℂ ↦ zeroBalancedTail b x) a :=
    (analyticOnNhd_zeroBalancedTail_left hx a
      (Complex.ne_neg_succ_of_neg_one_lt_re
        (by simp only [Complex.ofReal_re]; linarith))).differentiableAt
  rw [hd.hasDerivAt.comp_ofReal.deriv]
  refine norm_deriv_zeroBalancedTail_le (mem_closedBall_iff_norm.mpr ?_) hx
  rw [norm_ofReal_sub_half, abs_le]
  exact ⟨by linarith, by linarith⟩

/-- Mean-value Lipschitz bound on `a ↦ zeroBalancedTail a x` across `[1 / 8, 7 / 8]` for
`‖x‖ < 1`. -/
theorem norm_zeroBalancedTail_sub_le {a₁ a₂ : ℝ}
    (ha₁ : a₁ ∈ Icc (1 / 8 : ℝ) (7 / 8)) (ha₂ : a₂ ∈ Icc (1 / 8 : ℝ) (7 / 8))
    {x : ℂ} (hx : ‖x‖ < 1) :
    ‖zeroBalancedTail a₁ x - zeroBalancedTail a₂ x‖ ≤
      64 / (1 - ‖x‖) * |a₁ - a₂| * ‖x‖ * (1 + ‖Complex.log x‖) :=
  ((convex_Icc (1 / 8 : ℝ) (7 / 8)).norm_image_sub_le_of_norm_deriv_le
    (f := fun b : ℝ ↦ zeroBalancedTail b x) (fun b hb ↦
      ((analyticOnNhd_zeroBalancedTail_left hx b
        (Complex.ne_neg_succ_of_neg_one_lt_re
          (by simp only [Complex.ofReal_re]; linarith [hb.1]))).differentiableAt.hasDerivAt
        |>.comp_ofReal.differentiableAt))
    (fun _ (hb : _ ∈ Icc (1 / 8 : ℝ) (7 / 8)) ↦
      norm_deriv_ofReal_zeroBalancedTail_le hb.1 hb.2 hx) ha₂ ha₁).trans_eq
    (by rw [Real.norm_eq_abs]; ring)

private theorem closedBall_real_mem_bounds {a : ℝ} (ha : a ∈ Icc (1 / 4 : ℝ) (3 / 4))
    {b : ℂ} (hb : b ∈ closedBall (a : ℂ) (1 / 16)) :
    b ∈ closedBall (1 / 2 : ℂ) (5 / 16) ∧ 3 / 16 ≤ b.re ∧ ‖b‖ ≤ 1 := by
  have hba : ‖b - a‖ ≤ 1 / 16 := mem_closedBall_iff_norm.mp hb
  have ha12 : ‖(a : ℂ) - 1 / 2‖ ≤ 1 / 4 := by
    rw [norm_ofReal_sub_half, abs_le]
    exact ⟨by linarith [ha.1], by linarith [ha.2]⟩
  have hbre := (abs_le.mp (abs_re_le_norm (b - a))).1
  simp only [sub_re, ofReal_re] at hbre
  have han : ‖(a : ℂ)‖ ≤ 3 / 4 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by linarith [ha.1])]; exact ha.2
  have hbn : ‖b‖ ≤ ‖(a : ℂ)‖ + ‖b - a‖ :=
    (norm_add_le (a : ℂ) (b - a)).trans_eq' (by ring_nf)
  exact ⟨mem_closedBall_iff_norm.mpr (((norm_add_le (b - a) ((a : ℂ) - 1 / 2)).trans_eq'
    (by ring_nf)).trans (by linarith)), by linarith [ha.1], by linarith⟩

/-- Uniform `O(‖x‖(1 + ‖log x‖) / (1 - ‖x‖))` bound on the Gamma-normalized `k ≥ 1` remainder
`Γ(2a) / Γ(a)² * zeroBalancedTail a x` and its real `a`-derivative on `[1 / 4, 3 / 4]`
(CDT Lemma 5.2.9). -/
theorem exists_norm_mul_zeroBalancedTail_and_deriv_le :
    ∃ C : ℝ, 0 < C ∧ ∀ ⦃a : ℝ⦄, a ∈ Icc (1 / 4 : ℝ) (3 / 4) → ∀ ⦃x : ℂ⦄, ‖x‖ < 1 →
      ‖Complex.Gamma (2 * a) / Complex.Gamma a ^ 2 * zeroBalancedTail a x‖ ≤
        C / (1 - ‖x‖) * ‖x‖ * (1 + ‖Complex.log x‖) ∧
      ‖deriv (fun b : ℝ ↦ Complex.Gamma (2 * b) / Complex.Gamma b ^ 2 * zeroBalancedTail b x) a‖ ≤
        C / (1 - ‖x‖) * ‖x‖ * (1 + ‖Complex.log x‖) := by
  have hre_half : (1 / 2 : ℂ).re = 1 / 2 := by norm_num
  have hgamma : AnalyticOnNhd ℂ (fun b : ℂ ↦ Complex.Gamma (2 * b) / Complex.Gamma b ^ 2)
      (closedBall (1 / 2 : ℂ) (5 / 16)) :=
    analyticOnNhd_Gamma_two_mul_div_Gamma_sq.mono fun b hb ↦ by
      have hba := mem_closedBall_iff_norm.mp hb
      have hsub := (abs_le.mp (abs_re_le_norm (b - (1 / 2 : ℂ)))).1
      rw [sub_re, hre_half] at hsub
      exact ne_neg_natCast_of_re_pos
        (by simp only [mul_re, re_ofNat, im_ofNat, zero_mul, sub_zero]; linarith)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (1 / 2 : ℂ) (5 / 16)).exists_bound_of_continuousOn
    hgamma.continuousOn
  let M' := max M 1
  have hM' : 0 < M' := lt_of_lt_of_le zero_lt_one (le_max_right M 1)
  refine ⟨128 * M', by positivity, fun a ha x hx ↦ ?_⟩
  have hbound : ∀ b ∈ closedBall (a : ℂ) (1 / 16),
      ‖Complex.Gamma (2 * b) / Complex.Gamma b ^ 2 * zeroBalancedTail b x‖ ≤
        8 * M' / (1 - ‖x‖) * ‖x‖ * (1 + ‖Complex.log x‖) := fun b hb ↦ by
    obtain ⟨hsub, hb0, hb1⟩ := closedBall_real_mem_bounds ha hb
    rw [norm_mul]
    exact (mul_le_mul ((hM b hsub).trans (le_max_left _ _))
      (norm_zeroBalancedTail_le (by linarith) hb1 hx) (norm_nonneg _) hM'.le).trans_eq (by ring)
  have hdiff : DifferentiableOn ℂ
      (fun b : ℂ ↦ Complex.Gamma (2 * b) / Complex.Gamma b ^ 2 * zeroBalancedTail b x)
      (closedBall (a : ℂ) (1 / 16)) :=
    ((hgamma.mono fun _ hb ↦ (closedBall_real_mem_bounds ha hb).1).differentiableOn).mul
      (((analyticOnNhd_zeroBalancedTail_left hx).mono fun b hb ↦
        Complex.ne_neg_succ_of_neg_one_lt_re
          (by linarith [(closedBall_real_mem_bounds ha hb).2.1])).differentiableOn)
  refine ⟨(hbound a (mem_closedBall_self (by norm_num))).trans
    (by have : 0 < 1 - ‖x‖ := sub_pos.mpr hx; gcongr; linarith), ?_⟩
  rw [(hdiff.differentiableAt (closedBall_mem_nhds _ (by norm_num))).hasDerivAt.comp_ofReal.deriv]
  exact (norm_deriv_le_of_forall_mem_sphere_norm_le (by norm_num : (0 : ℝ) < 1 / 16)
    (hdiff.mono closure_ball_subset_closedBall).diffContOnCl
    fun b hb ↦ hbound b (sphere_subset_closedBall hb)).trans_eq (by ring)

/-! ### Analyticity in `x` and `a` and upper-half-plane boundary limit -/

/-- For every `a : ℂ`, the digamma-weighted power series appearing in
`zeroBalancedSeries_eq_log_mul_add` is complex analytic on the open unit disc `Metric.ball 0 1`. -/
theorem analyticOnNhd_zeroBalancedDigammaSeries (a : ℂ) :
    AnalyticOnNhd ℂ (fun z : ℂ ↦ ∑' k : ℕ, ordinaryHypergeometricCoefficient a a 1 k *
      (2 * (Complex.digamma (k + 1) - Complex.digamma (k + a))) * z ^ k) (Metric.ball 0 1) := by
  have han := FormalMultilinearSeries.analyticOnNhd_ofScalarsSum_of_le_radius (𝕜 := ℂ) (E := ℂ)
    zero_lt_one (one_le_radius_zeroBalancedDigammaSeries a)
  simp_rw [FormalMultilinearSeries.ofScalarsSum_eq_tsum, smul_eq_mul] at han
  exact han.mono fun z hz ↦ by
    simpa only [Metric.mem_eball, edist_dist, ENNReal.ofReal_lt_one, Metric.mem_ball] using hz

/-- For fixed `‖x‖ < 1`, `a ↦ zeroBalancedSeries a x` is complex analytic away from the poles
`2a = -n` (`n : ℕ`). -/
theorem analyticOnNhd_zeroBalancedSeries_left {x : ℂ} (hx : ‖x‖ < 1) :
    AnalyticOnNhd ℂ (fun a : ℂ ↦ zeroBalancedSeries a x)
      {a : ℂ | ∀ n : ℕ, 2 * a ≠ -(n : ℂ)} := by
  intro a ha
  have ha' := ne_neg_natCast_of_two_mul_ne ha
  refine ((analyticAt_Gamma_two_mul_div_Gamma_sq ha).mul
    (((analyticAt_const (v := -Complex.log x - 2 * Real.eulerMascheroniConstant)).sub
      ((analyticAt_const (v := (2 : ℂ))).mul (Complex.analyticAt_digamma ha'))).add
      (analyticOnNhd_zeroBalancedTail_left hx a fun m ↦ ha' (m + 1)))).congr ?_
  exact Eventually.of_forall fun b ↦ (zeroBalancedSeries_eq_add_zeroBalancedTail b hx).symm

/-- For every `a : ℂ`, `zeroBalancedTail a` is complex analytic on the slit unit disc
`Metric.ball 0 1 ∩ Complex.slitPlane`. -/
theorem analyticOnNhd_zeroBalancedTail (a : ℂ) :
    AnalyticOnNhd ℂ (zeroBalancedTail a) (Metric.ball 0 1 ∩ Complex.slitPlane) := by
  intro x hx
  refine (((analyticAt_clog hx.2).neg.mul
    ((analyticOnNhd_ordinaryHypergeometric ℂ a a 1 x hx.1).sub
      (analyticAt_const (v := (1 : ℂ))))).add
    ((analyticOnNhd_zeroBalancedDigammaSeries a x hx.1).sub
      (analyticAt_const (v := 2 * (Complex.digamma 1 - Complex.digamma a))))).congr ?_
  filter_upwards [(Metric.isOpen_ball.inter Complex.isOpen_slitPlane).mem_nhds hx] with z hz
  simp only [Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.neg_apply,
    zeroBalancedTail_eq_log_mul_add a (mem_ball_zero_iff.mp hz.1)]

/-- For every `a : ℂ`, `zeroBalancedSeries a` is complex analytic on the slit unit disc
`Metric.ball 0 1 ∩ Complex.slitPlane`. -/
theorem analyticOnNhd_zeroBalancedSeries (a : ℂ) :
    AnalyticOnNhd ℂ (zeroBalancedSeries a) (Metric.ball 0 1 ∩ Complex.slitPlane) := by
  intro x hx
  refine ((analyticAt_const (v := Complex.Gamma (2 * a) / Complex.Gamma a ^ 2)).mul
    (((analyticAt_clog hx.2).neg.mul
      (analyticOnNhd_ordinaryHypergeometric ℂ a a 1 x hx.1)).add
      (analyticOnNhd_zeroBalancedDigammaSeries a x hx.1))).congr ?_
  filter_upwards [(Metric.isOpen_ball.inter Complex.isOpen_slitPlane).mem_nhds hx] with z hz
  rw [zeroBalancedSeries_eq_tsum_term, tsum_zeroBalancedTerm_eq_split a (mem_ball_zero_iff.mp hz.1)]
  simp only [Pi.mul_apply, Pi.add_apply, Pi.neg_apply]

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
      exact ((Complex.continuousWithinAt_log_of_re_neg_of_im_zero
        (hsp.1.lt_of_ne fun h ↦ hx0 (Complex.ext h hsp.2)) hsp.2).mono
          (by intro _ hz; simp only [Set.mem_ofPred] at hz ⊢; exact hz.le :
            {z : ℂ | 0 < z.im} ⊆ {z : ℂ | 0 ≤ z.im})).tendsto
  have htend := (tendsto_const_nhds (x := Complex.Gamma (2 * a) / Complex.Gamma a ^ 2)).mul
    ((hlog.neg.mul ((analyticOnNhd_ordinaryHypergeometric ℂ a a 1 x
        hx_ball).continuousAt.continuousWithinAt.tendsto)).add
      (analyticOnNhd_zeroBalancedDigammaSeries a x hx_ball).continuousAt.continuousWithinAt.tendsto)
  rw [← tsum_zeroBalancedTerm_eq_split a hx1, ← zeroBalancedSeries_eq_tsum_term] at htend
  refine htend.congr' ?_
  filter_upwards [nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds hx_ball)] with z hz
  rw [zeroBalancedSeries_eq_tsum_term, tsum_zeroBalancedTerm_eq_split a (mem_ball_zero_iff.mp hz)]

end TauCeti
