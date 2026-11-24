/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.Complex.LocallyUniformLimit
public import Mathlib.Analysis.SpecialFunctions.RegularizedHypergeometric
public import TauCeti.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.RingTheory.Binomial
import Mathlib.Algebra.Polynomial.OfFn
import Mathlib.Analysis.Analytic.Constructions
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import TauCeti.Analysis.Analytic.OfScalars
import TauCeti.Analysis.Complex.CauchyIntegralPolydisc
import TauCeti.Analysis.Complex.UniformLimit
import TauCeti.Analysis.SpecialFunctions.Pochhammer
import TauCeti.RingTheory.Polynomial.Pochhammer
import TauCeti.Topology.Algebra.InfiniteSum.Sigma

/-!
# Regularized hypergeometric functions `₀F₁` and `₂F₁`

Mathlib defines the regularized hypergeometric function `Complex.regularizedHGFun a b` as the sum
of its power series. This file records that series as a `HasSum` statement, develops the
function `₀F₁(; b; z) = ∑ zⁿ / (n! Γ(b + n))` (`a = 0`, `b = {b}`) underlying the Bessel and Airy
functions, and establishes the unit-disk calculus, parameter-shift relations, first-order
contiguous-derivative relations, and joint analyticity of the regularized Gaussian function
`Complex.regularizedGaussHGFun a b c z = ∑ (a)ₙ (b)ₙ zⁿ / (n! Γ(c + n))`.

For every complex `b`, Mathlib provides the contiguous relation
`₀F₁(; b; z) = b ₀F₁(; b + 1; z) + z ₀F₁(; b + 2; z)`.
For every pair of complex parameters `a`, `b`, the product `₀F₁(; a; z) ₀F₁(; b; z)` expands as
an everywhere convergent power series with coefficients
`(a + b + n - 1)_n / (n! Γ(a + n) Γ(b + n))`, valid without pole exclusions on `a` or `b`.
For real `b` and real `y` the value is real, given by the real series `∑ yⁿ / (n! Γ(b + n))`;
it is jointly continuous in `(b, y)` and has derivative `₀F₁(; b + 1; y)` in `y`.
Conjugating both `b` and `z` conjugates the value, so for real `b` the function commutes with
complex conjugation. For `y ≥ 0` all terms after the first are nonnegative when `b > -1`, so
`₀F₁(; b; y) ≥ 1 / Γ(b)`, which is positive when `b > 0`.
Likewise, on the open unit disk `‖z‖ < 1`, `Complex.regularizedGaussHGFun a b c` evaluates to
`(Gamma c)⁻¹` at `z = 0`, is analytic in `z`, has derivative
`a * b * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z`, satisfies the classical first-order
parameter-shift and derivative-contiguous relations, and is jointly analytic in `(a, b, c, z)`.
Because `1 / Γ` vanishes at the poles of `Γ`, none of these statements needs a pole-avoidance
hypothesis on the lower parameter.
For general parameter multisets, an upper parameter `-n` makes every coefficient of index greater
than `n` vanish, so the series terminates and the function is a polynomial of degree at most `n`,
with no condition on the lower parameters.

## Main results

* `Complex.hasSum_regularizedHGFun_of_mem_eball`,
  `Complex.summable_norm_regularizedHGFun_of_mem_eball` — `HasSum` and absolute convergence on the
  formal convergence ball of `regularizedHGFunSeries`.
* `Complex.hasSum_regularizedHGFun` — the power series of `regularizedHGFun a b` converges to it
  everywhere when `a.card ≤ b.card`, absolutely by `Complex.summable_norm_regularizedHGFun`.
* `Complex.differentiable_regularizedHGFun_of_card_le` — `regularizedHGFun a b` is entire when
  `a.card ≤ b.card`, and `Complex.hasSum_deriv_regularizedHGFun` expresses its derivative as the
  termwise differentiated series.
* `Complex.hasDerivAt_regularizedHGFun_zero_singleton` — the derivative of `₀F₁(; b; z)` is
  `₀F₁(; b + 1; z)`, the `a = 0`, `b = {b}` case of Mathlib's `Complex.hasDerivAt_regularizedHGFun`.
* `Complex.regularizedHGFun_of_zero_mem` — when `0 ∈ a`, `regularizedHGFun a b` is constant and
  equals `(b.map Gamma).prod⁻¹`.
* `Complex.hasSum_regularizedHGFun_of_card_eq_add_one`,
  `Complex.summable_norm_regularizedHGFun_of_card_eq_add_one` — unit-disk `HasSum` and absolute
  convergence when `a.card = b.card + 1`.
* `Complex.hasSum_regularizedGaussHGFun`, `Complex.summable_norm_regularizedGaussHGFun` —
  the power series of `regularizedGaussHGFun a b c` converges to it (and absolutely) on the open
  unit disk `‖z‖ < 1`.
* `Complex.regularizedHGFunCoeff_one_singleton` — the coefficients `1 / Γ(b + n)` of the Kummer
  function `𝐌(1, b, z) = ∑ zⁿ / Γ(b + n)`.
* `Complex.sum_regularizedHGFunCoeff_zero_singleton_mul` and
  `Complex.hasSum_regularizedHGFun_zero_singleton_mul` — the Cauchy product series of
  `₀F₁(; a; z) ₀F₁(; b; z)`, absolutely convergent by
  `Complex.summable_norm_regularizedHGFun_zero_singleton_mul`.
* `Complex.hasSum_regularizedHGFun_zero_singleton_ofReal_re` — the real series of `₀F₁` at real
  arguments, with Cauchy product `Complex.hasSum_regularizedHGFun_zero_singleton_ofReal_re_mul`.
* `Complex.regularizedHGFun_zero_singleton_conj` — `₀F₁(; conj b; conj z) = conj ₀F₁(; b; z)`,
  and `Complex.regularizedHGFun_zero_ofReal_singleton_conj` for real `b`.
* `Complex.inv_Gamma_le_regularizedHGFun_zero_singleton_ofReal_re`,
  `Complex.regularizedHGFun_zero_singleton_ofReal_re_pos` — for `y ≥ 0`, `₀F₁(; b; y) ≥ 1 / Γ(b)`
  when `b > -1`, and `₀F₁(; b; y) > 0` when `b > 0`.
* `Complex.continuous_regularizedHGFun_zero_singleton_ofReal_re` — joint continuity in `(b, y)`.
* `Complex.hasDerivAt_regularizedHGFun_zero_singleton_ofReal_re` — the derivative in `y`.
* `Complex.hasSum_regularizedHGFun_of_neg_natCast_mem`,
  `Complex.regularizedHGFun_eq_sum_range_of_neg_natCast_mem`,
  `Complex.exists_natDegree_le_regularizedHGFun_of_neg_natCast_mem` — if an upper parameter is a
  nonpositive integer `-n`, the series terminates, converges at every `z`, and is a polynomial of
  degree at most `n`.
* `Complex.regularizedGaussHGFun_zero`, `Complex.regularizedGaussHGFun_zero_left`,
  `Complex.regularizedGaussHGFun_zero_right`, `Complex.coeff_regularizedGaussHGFunSeries_zero` —
  origin and zero-parameter values `(Gamma c)⁻¹`.
* `Complex.hasSum_regularizedGaussHGFun_neg_natCast`,
  `Complex.regularizedGaussHGFun_neg_natCast_eq_sum`, `Complex.regularizedGaussHGFun_neg_natCast`,
  `Complex.regularizedGaussHGFun_neg_natCast_succ_eq_sub`,
  `Complex.regularizedGaussHGFun_neg_natCast_succ_eq_add` — all-argument `HasSum`, finite-sum
  formulas (regularized form of DLMF 15.2.4), and parameter-lowering recurrences for
  `regularizedGaussHGFun (-n) b c z`.
* `Complex.hasFPowerSeriesOnBall_regularizedGaussHGFun`, `Complex.analyticAt_regularizedGaussHGFun`,
  `Complex.analyticOnNhd_regularizedGaussHGFun` — power-series representation and analyticity of
  `regularizedGaussHGFun` on the open unit disk.
* `Complex.deriv_regularizedGaussHGFun`, `Complex.hasDerivAt_regularizedGaussHGFun` — the derivative
  `a * b * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z` on `‖z‖ < 1` (DLMF 15.5.1).
* `Complex.regularizedGaussHGFun_eq_sub_mul_add_mul`,
  `Complex.regularizedGaussHGFun_eq_regularizedGaussHGFun_sub_mul_mul`,
  `Complex.mul_deriv_regularizedGaussHGFun_add_mul_eq`,
  `Complex.mul_deriv_regularizedGaussHGFun_add_mul_eq_mul`,
  `Complex.mul_one_sub_mul_deriv_regularizedGaussHGFun` — parameter-shift and first-order
  contiguous-derivative identities on `‖z‖ < 1` (DLMF §15.5).
* `Complex.regularizedGaussHGFun_eq_mul_one_sub_mul_add_mul` — the three-term relation
  `𝐅(a, b; c; z) = c (1 - z) 𝐅(a + 1, b + 1; c + 1; z) + (c - a)(c - b) z 𝐅(a + 1, b + 1; c + 2; z)`
  on `‖z‖ < 1`.
* `Complex.choose_mul_coeff_regularizedGaussHGFunSeries` — the coefficient shift
  `C(m + i, m) 𝐅ₘ₊ᵢ = (a)ₘ (b)ₘ / m! · 𝐅(a + m, b + m; c + m)ᵢ`.
* `Complex.norm_regularizedGaussHGFun_le_tsum` — the majorant bound
  `‖𝐅(a, b; c; w)‖ ≤ ∑ ‖𝐅ⱼ‖ yʲ` for `‖w‖ ≤ y < 1`.
* `Complex.hasSum_choose_mul_coeff_regularizedGaussHGFunSeries`,
  `Complex.hasSum_norm_choose_mul_coeff_regularizedGaussHGFunSeries` — the absolutely convergent
  binomial double series of `𝐅(a, b; c; u + z)` in powers of `u` and `z` for `‖u‖ + ‖z‖ < 1`.
* `Complex.analyticAt_uncurry_regularizedGaussHGFun`, `AnalyticAt.regularizedGaussHGFun`,
  `DifferentiableAt.regularizedGaussHGFun`, `DifferentiableWithinAt.regularizedGaussHGFun`,
  `DifferentiableOn.regularizedGaussHGFun`, `Differentiable.regularizedGaussHGFun` — joint
  analyticity of `(a, b, c, z) ↦ regularizedGaussHGFun a b c z` on `‖z‖ < 1` and composition with
  analytic or holomorphic maps on complex normed spaces.
-/

public section

noncomputable section

open Filter Set
open scoped Nat Topology ENNReal

namespace Complex

/-- The coefficients of `₀F₁(; b; z)` are `1 / (n! Γ(b + n))`. -/
@[simp]
theorem regularizedHGFunCoeff_zero_singleton (b : ℂ) (n : ℕ) :
    regularizedHGFunCoeff 0 {b} n = (n ! * Gamma (b + n))⁻¹ := by
  simp [regularizedHGFunCoeff]

/-- At zero argument and a real parameter, the real part of `₀F₁(; b; 0)` is `1 / Γ(b)`,
including the poles of `Γ`, where its inverse vanishes. -/
theorem regularizedHGFun_zero_singleton_ofReal_zero_re (b : ℝ) :
    (regularizedHGFun 0 {(b : ℂ)} 0).re = (Real.Gamma b)⁻¹ := by
  have h : regularizedHGFun 0 {(b : ℂ)} 0 = (((Real.Gamma b)⁻¹ : ℝ) : ℂ) := by
    rw [ofReal_inv, ← Gamma_ofReal]
    simp
  rw [h, ofReal_re]

/-- If `0` is an upper parameter, all positive-degree terms of the regularized hypergeometric
series vanish, so `regularizedHGFun a b z = (b.map Gamma).prod⁻¹`. -/
theorem regularizedHGFun_of_zero_mem {a b : Multiset ℂ} (h : (0 : ℂ) ∈ a) (z : ℂ) :
    regularizedHGFun a b z = (b.map Gamma).prod⁻¹ := by
  rw [regularizedHGFun, regularizedHGFunSeries, FormalMultilinearSeries.sum, tsum_eq_single 0]
  · simp [regularizedHGFunCoeff]
  · intro n hn
    simp [regularizedHGFunCoeff_eq_zero_left a b n 0 (by simpa using h) (Nat.pos_of_ne_zero hn)]

private theorem regularizedHGFunCoeff_pair_singleton (a b c : ℂ) (k : ℕ) :
    regularizedHGFunCoeff {a, b} {c} k = (regularizedGaussHGFunSeries a b c).coeff k := by
  rw [regularizedGaussHGFunSeries, regularizedHGFunSeries_coeff]

/-- Inside the convergence ball of `regularizedHGFunSeries a b`, the regularized hypergeometric
series converges to `regularizedHGFun a b z`. -/
theorem hasSum_regularizedHGFun_of_mem_eball {a b : Multiset ℂ} {z : ℂ}
    (hz : z ∈ Metric.eball (0 : ℂ) (regularizedHGFunSeries a b).radius) :
    HasSum (fun n => regularizedHGFunCoeff a b n * z ^ n) (regularizedHGFun a b z) := by
  simpa [regularizedHGFun, regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq,
    mul_comm] using (regularizedHGFunSeries a b).hasSum hz

/-- Inside the convergence ball of `regularizedHGFunSeries a b`, the regularized hypergeometric
series converges absolutely. -/
theorem summable_norm_regularizedHGFun_of_mem_eball {a b : Multiset ℂ} {z : ℂ}
    (hz : z ∈ Metric.eball (0 : ℂ) (regularizedHGFunSeries a b).radius) :
    Summable fun n => ‖regularizedHGFunCoeff a b n * z ^ n‖ := by
  simpa [regularizedHGFunSeries, FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using
    (regularizedHGFunSeries a b).summable_norm_apply hz

/-- When there are at most as many upper as lower parameters, the regularized hypergeometric
series converges to `regularizedHGFun a b z` at every `z`. -/
theorem hasSum_regularizedHGFun {a b : Multiset ℂ} (h : a.card ≤ b.card) (z : ℂ) :
    HasSum (fun n => regularizedHGFunCoeff a b n * z ^ n) (regularizedHGFun a b z) :=
  hasSum_regularizedHGFun_of_mem_eball (by simp [radius_regularizedHGFunSeries_eq_top h])

/-- When there is one more upper than lower parameter, the regularized hypergeometric series
converges to `regularizedHGFun a b z` on the open unit disk `‖z‖ < 1`. -/
theorem hasSum_regularizedHGFun_of_card_eq_add_one {a b : Multiset ℂ}
    (h : a.card = b.card + 1) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n => regularizedHGFunCoeff a b n * z ^ n) (regularizedHGFun a b z) :=
  hasSum_regularizedHGFun_of_mem_eball <|
    Metric.eball_subset_eball (radius_regularizedHGFunSeries_ge_one h) <| by
      rwa [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one]

/-- When there is one more upper than lower parameter, the regularized hypergeometric series
converges absolutely on the open unit disk `‖z‖ < 1`. -/
theorem summable_norm_regularizedHGFun_of_card_eq_add_one {a b : Multiset ℂ}
    (h : a.card = b.card + 1) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n => ‖regularizedHGFunCoeff a b n * z ^ n‖ :=
  summable_norm_regularizedHGFun_of_mem_eball <|
    Metric.eball_subset_eball (radius_regularizedHGFunSeries_ge_one h) <| by
      rwa [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one]

/-- On the open unit disk `‖z‖ < 1`, the regularized Gauss hypergeometric power series converges
to `regularizedGaussHGFun a b c z`. -/
theorem hasSum_regularizedGaussHGFun (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasSum (fun n : ℕ => (regularizedGaussHGFunSeries a b c).coeff n * z ^ n)
      (regularizedGaussHGFun a b c z) := by
  rw [regularizedGaussHGFun, regularizedGaussHGFunSeries, ← regularizedHGFun]
  simpa only [regularizedHGFunSeries_coeff] using
    hasSum_regularizedHGFun_of_card_eq_add_one (a := {a, b}) (b := {c})
      (by rw [Multiset.card_pair, Multiset.card_singleton]) hz

/-- On the open unit disk `‖z‖ < 1`, the regularized Gauss hypergeometric power series converges
absolutely. -/
theorem summable_norm_regularizedGaussHGFun (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => ‖(regularizedGaussHGFunSeries a b c).coeff n * z ^ n‖ := by
  rw [regularizedGaussHGFunSeries]
  simpa only [regularizedHGFunSeries_coeff] using
    summable_norm_regularizedHGFun_of_card_eq_add_one (a := {a, b}) (b := {c})
      (by rw [Multiset.card_pair, Multiset.card_singleton]) hz

/-- When there are at most as many upper as lower parameters, the regularized hypergeometric
series converges absolutely at every `z`. -/
theorem summable_norm_regularizedHGFun {a b : Multiset ℂ} (h : a.card ≤ b.card) (z : ℂ) :
    Summable fun n => ‖regularizedHGFunCoeff a b n * z ^ n‖ :=
  summable_norm_regularizedHGFun_of_mem_eball (by simp [radius_regularizedHGFunSeries_eq_top h])

/-- When there are at most as many upper as lower parameters, `regularizedHGFun a b` is entire. -/
@[fun_prop]
theorem differentiable_regularizedHGFun_of_card_le {a b : Multiset ℂ} (h : a.card ≤ b.card) :
    Differentiable ℂ (regularizedHGFun a b) :=
  fun z => (analyticAt_regularizedHGFun_of_card_le h z).differentiableAt

/-- When there are at most as many upper as lower parameters, the derivative of
`regularizedHGFun a b` is the sum of its termwise differentiated power series. -/
theorem hasSum_deriv_regularizedHGFun {a b : Multiset ℂ} (h : a.card ≤ b.card) (z : ℂ) :
    HasSum (fun n : ℕ => ((n : ℂ) + 1) * regularizedHGFunCoeff a b (n + 1) * z ^ n)
      (deriv (regularizedHGFun a b) z) := by
  set R : ℝ := ‖z‖ + 1
  have hfun : regularizedHGFun a b = fun w => ∑' n, regularizedHGFunCoeff a b n * w ^ n :=
    funext fun w => (hasSum_regularizedHGFun h w).tsum_eq.symm
  have hd := hasSum_deriv_of_summable_norm (summable_norm_regularizedHGFun h (R : ℂ))
    (F := fun n w => regularizedHGFunCoeff a b n * w ^ n) (U := Metric.ball 0 R)
    (fun n => ((differentiable_pow n).const_mul _).differentiableOn) Metric.isOpen_ball
    (fun n w hw => ?_) (z := z) (by simp [R])
  · rw [hfun]
    convert (hasSum_nat_add_iff' 1).mpr hd using 1
    · ext n
      simp only [deriv_const_mul_field', deriv_pow_field, add_tsub_cancel_right]
      push_cast
      ring
    · simp
  · rw [Metric.mem_ball, dist_zero_right] at hw
    rw [norm_mul, norm_mul, norm_pow, norm_pow, Complex.norm_real,
      Real.norm_of_nonneg (by positivity)]
    gcongr

/-- The derivative of `₀F₁(; b; z)` in `z` is `₀F₁(; b + 1; z)`, for every complex `b`. -/
theorem hasDerivAt_regularizedHGFun_zero_singleton (b z : ℂ) :
    HasDerivAt (regularizedHGFun 0 {b}) (regularizedHGFun 0 {b + 1} z) z := by
  simpa using hasDerivAt_regularizedHGFun (a := 0) (b := {b}) (z := z) (by simp)

/-- The coefficients of the Kummer function `𝐌(1, b, z) = ₁F₁(1; b; z) / Γ(b)` are
`1 / Γ(b + n)`. -/
@[simp]
theorem regularizedHGFunCoeff_one_singleton (b : ℂ) (n : ℕ) :
    regularizedHGFunCoeff {1} {b} n = (Gamma (b + n))⁻¹ := by
  simpa [regularizedHGFunCoeff] using div_mul_cancel_left₀ (Nat.cast_ne_zero.2 n.factorial_ne_zero)
    (Gamma (b + n))

/-- The complex-valued `₀F₁` series at real parameters and arguments sums to its regularized
hypergeometric value. -/
theorem hasSum_ofReal_regularizedHGFun_zero_singleton (b y : ℝ) :
    HasSum (fun n : ℕ => ((y ^ n / (n ! * Real.Gamma (b + n)) : ℝ) : ℂ))
      (regularizedHGFun 0 {(b : ℂ)} y) := by
  convert hasSum_regularizedHGFun (a := 0) (b := {(b : ℂ)}) (by simp) (y : ℂ) with n
  push_cast [← Gamma_ofReal, regularizedHGFunCoeff_zero_singleton]
  ring

/-- At real arguments, `₀F₁(; b; y)` is real. -/
@[simp]
theorem regularizedHGFun_zero_singleton_ofReal_im (b y : ℝ) :
    (regularizedHGFun 0 {(b : ℂ)} y).im = 0 := by
  refine (hasSum_im (hasSum_ofReal_regularizedHGFun_zero_singleton b y)).unique ?_
  simpa only [ofReal_im] using hasSum_zero

/-- At real arguments, `₀F₁(; b; y)` is the sum of the real series `∑ yⁿ / (n! Γ(b + n))`. -/
theorem hasSum_regularizedHGFun_zero_singleton_ofReal_re (b y : ℝ) :
    HasSum (fun n : ℕ => y ^ n / (n ! * Real.Gamma (b + n)))
      (regularizedHGFun 0 {(b : ℂ)} y).re := by
  simpa only [ofReal_re] using hasSum_re (hasSum_ofReal_regularizedHGFun_zero_singleton b y)

open scoped ComplexConjugate in
/-- `₀F₁(; b; z)` commutes with complex conjugation of the parameter and the argument together:
`₀F₁(; conj b; conj z) = conj ₀F₁(; b; z)`.

Adapted from `regularized0F1_conj` in the lean-DLMF project
(<https://github.com/bjbraams/lean-DLMF>), file `DLMF/Bessel/Basic/RegularizedSeries.lean`. -/
theorem regularizedHGFun_zero_singleton_conj (b z : ℂ) :
    regularizedHGFun 0 {conj b} (conj z) = conj (regularizedHGFun 0 {b} z) := by
  refine (hasSum_regularizedHGFun (a := 0) (b := {conj b}) (by simp) (conj z)).unique ?_
  refine (hasSum_conj'.2 (hasSum_regularizedHGFun (a := 0) (b := {b}) (by simp) z)).congr_fun
    fun n => ?_
  simp [← Gamma_conj]

open scoped ComplexConjugate in
/-- For a real parameter `b`, `₀F₁(; b; z)` commutes with complex conjugation:
`₀F₁(; b; conj z) = conj ₀F₁(; b; z)`. -/
theorem regularizedHGFun_zero_ofReal_singleton_conj (z : ℂ) (b : ℝ) :
    regularizedHGFun 0 {(b : ℂ)} (conj z) = conj (regularizedHGFun 0 {(b : ℂ)} z) := by
  simpa using regularizedHGFun_zero_singleton_conj b z

/-- For `b > -1` and `y ≥ 0` every term of the real series of `₀F₁(; b; y)` after the first is
nonnegative, so `₀F₁(; b; y)` is at least its first term `1 / Γ(b)`. -/
theorem inv_Gamma_le_regularizedHGFun_zero_singleton_ofReal_re {b y : ℝ} (hb : -1 < b)
    (hy : 0 ≤ y) : (Real.Gamma b)⁻¹ ≤ (regularizedHGFun 0 {(b : ℂ)} y).re := by
  have h := le_hasSum (hasSum_regularizedHGFun_zero_singleton_ofReal_re b y) 0 fun n hn => by
    have hn : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
    have hbn : 0 < b + n := by linarith
    have := Real.Gamma_pos_of_pos hbn
    positivity
  simpa using h

/-- For `b > 0` and `y ≥ 0`, `₀F₁(; b; y)` is positive. -/
theorem regularizedHGFun_zero_singleton_ofReal_re_pos {b y : ℝ} (hb : 0 < b) (hy : 0 ≤ y) :
    0 < (regularizedHGFun 0 {(b : ℂ)} y).re :=
  (inv_pos.2 (Real.Gamma_pos_of_pos hb)).trans_le
    (inv_Gamma_le_regularizedHGFun_zero_singleton_ofReal_re (by linarith) hy)

/-- The real part of `₀F₁(; b; y)` is jointly continuous in the real parameter `b` and the real
argument `y`. -/
theorem continuous_regularizedHGFun_zero_singleton_ofReal_re :
    Continuous fun p : ℝ × ℝ => (regularizedHGFun 0 {(p.1 : ℂ)} p.2).re := by
  have heq : (fun p : ℝ × ℝ => (regularizedHGFun 0 {(p.1 : ℂ)} p.2).re) =
      fun p => ∑' n : ℕ, p.2 ^ n * ((n ! : ℝ)⁻¹ * (Real.Gamma (p.1 + n))⁻¹) := by
    ext p
    simp_rw [← mul_inv, ← div_eq_mul_inv]
    exact (hasSum_regularizedHGFun_zero_singleton_ofReal_re p.1 p.2).tsum_eq.symm
  rw [heq, continuous_iff_continuousAt]
  rintro ⟨b₀, y₀⟩
  obtain ⟨C, hC⟩ := Real.exists_abs_inv_Gamma_le (b₀ - 1)
  set R := |y₀| + 1
  have hmem : (b₀, y₀) ∈ Ioi (b₀ - 1) ×ˢ Ioo (-R) R :=
    ⟨by simp, by constructor <;> linarith [neg_abs_le y₀, le_abs_self y₀]⟩
  refine (continuousOn_tsum (u := fun n => C * (R ^ n / n !)) (fun n => ?_)
    ((Real.summable_pow_div_factorial R).mul_left C) (fun n p hp => ?_)).continuousAt
    ((isOpen_Ioi.prod isOpen_Ioo).mem_nhds hmem)
  · exact (continuous_snd.pow n).mul (continuous_const.mul
      (Real.continuous_inv_Gamma.comp (continuous_fst.add continuous_const))) |>.continuousOn
  · obtain ⟨hb, hy⟩ := hp
    have hy' : |p.2| ≤ R := (abs_lt.2 hy).le
    have hG := hC (p.1 + n) (by simp only [mem_Ioi] at hb; linarith [n.cast_nonneg (α := ℝ)])
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_inv, Nat.abs_cast]
    calc |p.2| ^ n * ((n ! : ℝ)⁻¹ * |(Real.Gamma (p.1 + n))⁻¹|)
        ≤ R ^ n * ((n ! : ℝ)⁻¹ * C) := by gcongr
      _ = C * (R ^ n / n !) := by ring

/-- The derivative of `₀F₁(; b; y)` in a real argument `y` is `₀F₁(; b + 1; y)`. -/
theorem hasDerivAt_regularizedHGFun_zero_singleton_ofReal_re (b y : ℝ) :
    HasDerivAt (fun y : ℝ => (regularizedHGFun 0 {(b : ℂ)} y).re)
      (regularizedHGFun 0 {(b : ℂ) + 1} y).re y := by
  simpa using (hasDerivAt_regularizedHGFun_zero_singleton (b : ℂ) y).real_of_complex

/-- The finite convolution of the coefficients of `₀F₁(; a; z)` and `₀F₁(; b; z)`, valid at every
pair of complex parameters `a`, `b`, including poles of `Γ`. -/
theorem sum_regularizedHGFunCoeff_zero_singleton_mul (a b : ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      regularizedHGFunCoeff 0 {a} k * regularizedHGFunCoeff 0 {b} (n - k) =
    (ascPochhammer ℂ n).eval (a + b + n - 1) / (n ! * Gamma (a + n) * Gamma (b + n)) := by
  have hterm : ∀ k ∈ Finset.range (n + 1),
      regularizedHGFunCoeff 0 {a} k * regularizedHGFunCoeff 0 {b} (n - k) =
        ((n.choose k : ℂ) *
          ((descPochhammer ℤ k).smeval (b + n - 1) *
            (descPochhammer ℤ (n - k)).smeval (a + n - 1))) /
          (n ! * Gamma (a + n) * Gamma (b + n)) := by
    intro k hk_mem
    have hk : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk_mem)
    have ha : (Gamma (a + k))⁻¹ =
        (descPochhammer ℤ (n - k)).smeval (a + n - 1) * (Gamma (a + n))⁻¹ := by
      have han : a + k + ((n - k : ℕ) : ℂ) = a + n := by rw [Nat.cast_sub hk]; ring
      have hsub : a + n - 1 - ((n - k : ℕ) : ℂ) + 1 = a + k := by rw [Nat.cast_sub hk]; ring
      rw [inv_Gamma_eq_ascPochhammer_mul_inv_Gamma_add (a + k) (n - k), han,
        Polynomial.descPochhammer_smeval_eq_ascPochhammer,
        Polynomial.ascPochhammer_smeval_eq_eval, hsub]
    have hb : (Gamma (b + (n - k : ℕ)))⁻¹ =
        (descPochhammer ℤ k).smeval (b + n - 1) * (Gamma (b + n))⁻¹ := by
      have hbn : b + ((n - k : ℕ) : ℂ) + k = b + n := by rw [Nat.cast_sub hk]; ring
      have hsub : b + n - 1 - k + 1 = b + ((n - k : ℕ) : ℂ) := by rw [Nat.cast_sub hk]; ring
      rw [inv_Gamma_eq_ascPochhammer_mul_inv_Gamma_add (b + (n - k : ℕ)) k, hbn,
        Polynomial.descPochhammer_smeval_eq_ascPochhammer,
        Polynomial.ascPochhammer_smeval_eq_eval, hsub]
    have hfac : (k ! : ℂ)⁻¹ * ((n - k)! : ℂ)⁻¹ = (n.choose k : ℂ) * (n ! : ℂ)⁻¹ := by
      have hchoose : (n.choose k : ℂ) * k ! * (n - k)! = n ! := by
        exact_mod_cast Nat.choose_mul_factorial_mul_factorial hk
      have hk0 : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 k.factorial_ne_zero
      have hnk0 : ((n - k)! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (n - k).factorial_ne_zero
      have hn0 : (n ! : ℂ) ≠ 0 := Nat.cast_ne_zero.2 n.factorial_ne_zero
      field_simp
      linear_combination -hchoose
    rw [regularizedHGFunCoeff_zero_singleton, regularizedHGFunCoeff_zero_singleton,
      mul_inv, mul_inv, mul_mul_mul_comm, hfac, ha, hb]
    ring
  have harg : b + n - 1 + (a + n - 1) - n + 1 = a + b + n - 1 := by ring
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_div,
    ← Finset.Nat.sum_antidiagonal_eq_sum_range_succ fun k l =>
      (n.choose k : ℂ) *
        ((descPochhammer ℤ k).smeval (b + n - 1) * (descPochhammer ℤ l).smeval (a + n - 1)),
    ← Ring.descPochhammer_smeval_add n (Commute.all _ _),
    Polynomial.descPochhammer_smeval_eq_ascPochhammer,
    Polynomial.ascPochhammer_smeval_eq_eval, harg]

private theorem sum_range_regularizedHGFun_zero_singleton_mul (a b z : ℂ) (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1),
      (regularizedHGFunCoeff 0 {a} k * z ^ k) *
        (regularizedHGFunCoeff 0 {b} (n - k) * z ^ (n - k)) =
    (ascPochhammer ℂ n).eval (a + b + n - 1) / (n ! * Gamma (a + n) * Gamma (b + n)) * z ^ n := by
  have hpow : ∀ k ∈ Finset.range (n + 1),
      (regularizedHGFunCoeff 0 {a} k * z ^ k) *
        (regularizedHGFunCoeff 0 {b} (n - k) * z ^ (n - k)) =
      (regularizedHGFunCoeff 0 {a} k * regularizedHGFunCoeff 0 {b} (n - k)) * z ^ n := by
    intro k hk_mem
    have hk : k ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hk_mem)
    rw [mul_mul_mul_comm, ← pow_add, Nat.add_sub_of_le hk]
  rw [Finset.sum_congr rfl hpow, ← Finset.sum_mul, sum_regularizedHGFunCoeff_zero_singleton_mul]

/-- The Cauchy product series of `₀F₁(; a; z) ₀F₁(; b; z)` converges everywhere, without pole
exclusions on `a` or `b`. -/
theorem hasSum_regularizedHGFun_zero_singleton_mul (a b z : ℂ) :
    HasSum
      (fun n : ℕ =>
        (ascPochhammer ℂ n).eval (a + b + n - 1) /
          (n ! * Gamma (a + n) * Gamma (b + n)) * z ^ n)
      (regularizedHGFun 0 {a} z * regularizedHGFun 0 {b} z) := by
  have ha := hasSum_regularizedHGFun (a := 0) (b := {a}) (by simp) z
  have hb := hasSum_regularizedHGFun (a := 0) (b := {b}) (by simp) z
  have h := hasSum_sum_range_mul_of_summable_norm
    (summable_norm_regularizedHGFun (a := 0) (b := {a}) (by simp) z)
    (summable_norm_regularizedHGFun (a := 0) (b := {b}) (by simp) z)
  rw [ha.tsum_eq, hb.tsum_eq] at h
  simpa only [sum_range_regularizedHGFun_zero_singleton_mul] using h

/-- The Cauchy product series of `₀F₁(; a; z) ₀F₁(; b; z)` converges absolutely everywhere. -/
theorem summable_norm_regularizedHGFun_zero_singleton_mul (a b z : ℂ) :
    Summable fun n : ℕ =>
      ‖(ascPochhammer ℂ n).eval (a + b + n - 1) /
        (n ! * Gamma (a + n) * Gamma (b + n)) * z ^ n‖ := by
  simpa only [sum_range_regularizedHGFun_zero_singleton_mul] using
    summable_norm_sum_mul_range_of_summable_norm
      (summable_norm_regularizedHGFun (a := 0) (b := {a}) (by simp) z)
      (summable_norm_regularizedHGFun (a := 0) (b := {b}) (by simp) z)

/-- At real parameters and a real argument, the product of two `₀F₁` functions is given by the real
Cauchy product series. -/
theorem hasSum_regularizedHGFun_zero_singleton_ofReal_re_mul (a b y : ℝ) :
    HasSum
      (fun n : ℕ =>
        (ascPochhammer ℝ n).eval (a + b + n - 1) /
          (n ! * Real.Gamma (a + n) * Real.Gamma (b + n)) * y ^ n)
      ((regularizedHGFun 0 {(a : ℂ)} y).re * (regularizedHGFun 0 {(b : ℂ)} y).re) := by
  have h := hasSum_re (hasSum_regularizedHGFun_zero_singleton_mul a b y)
  have hre : (regularizedHGFun 0 {(a : ℂ)} y * regularizedHGFun 0 {(b : ℂ)} y).re =
      (regularizedHGFun 0 {(a : ℂ)} y).re * (regularizedHGFun 0 {(b : ℂ)} y).re := by
    simp [mul_re]
  rw [hre] at h
  refine h.congr_fun fun n => ?_
  have heval : (ascPochhammer ℂ n).eval ((a + b + n - 1 : ℝ) : ℂ) =
      (((ascPochhammer ℝ n).eval (a + b + n - 1) : ℝ) : ℂ) := by
    simpa using Polynomial.eval_map_apply ofRealHom (a + b + n - 1) (p := ascPochhammer ℝ n)
  have hc : (a : ℂ) + b + n - 1 = ((a + b + n - 1 : ℝ) : ℂ) := by push_cast; ring
  have ha : (a : ℂ) + n = ((a + n : ℝ) : ℂ) := by push_cast; ring
  have hb : (b : ℂ) + n = ((b + n : ℝ) : ℂ) := by push_cast; ring
  rw [hc, ha, hb, heval, Gamma_ofReal, Gamma_ofReal]
  norm_cast

/-- If `-n` is an upper parameter, the regularized hypergeometric series converges to
`regularizedHGFun a b z` at every complex `z`. -/
theorem hasSum_regularizedHGFun_of_neg_natCast_mem {a b : Multiset ℂ} {n : ℕ}
    (ha : -(n : ℂ) ∈ a) (z : ℂ) :
    HasSum (fun k => regularizedHGFunCoeff a b k * z ^ k) (regularizedHGFun a b z) :=
  hasSum_regularizedHGFun_of_mem_eball
    (by simp [radius_regularizedHGFunSeries_eq_top_of_finite ha rfl])

/-- If `-n` is an upper parameter, the regularized hypergeometric series terminates at
degree `n`: `regularizedHGFun a b z` is the sum of its first `n + 1` terms. -/
theorem regularizedHGFun_eq_sum_range_of_neg_natCast_mem {a b : Multiset ℂ} {n : ℕ}
    (ha : -(n : ℂ) ∈ a) (z : ℂ) :
    regularizedHGFun a b z =
      ∑ k ∈ Finset.range (n + 1), regularizedHGFunCoeff a b k * z ^ k := by
  rw [regularizedHGFun, (regularizedHGFunSeries a b).sum_of_finite (n := n + 1) (fun m hm =>
    regularizedHGFunSeries_eq_zero.2 (regularizedHGFunCoeff_eq_zero_left a b m n ha hm)) z]
  simp only [FormalMultilinearSeries.partialSum, regularizedHGFunSeries,
    FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul]

open Polynomial in
/-- If `-n` is an upper parameter, `regularizedHGFun a b` is a polynomial of degree at most `n`,
whatever the other upper and the lower parameters are. -/
theorem exists_natDegree_le_regularizedHGFun_of_neg_natCast_mem {a b : Multiset ℂ} {n : ℕ}
    (ha : -(n : ℂ) ∈ a) :
    ∃ p : ℂ[X], p.natDegree ≤ n ∧ ∀ z, regularizedHGFun a b z = p.eval z := by
  refine ⟨ofFn (n + 1) fun k => regularizedHGFunCoeff a b k,
    Nat.lt_succ_iff.mp (ofFn_natDegree_lt n.succ_pos _), fun z => ?_⟩
  rw [regularizedHGFun_eq_sum_range_of_neg_natCast_mem ha z,
    eval_eq_sum_range' (ofFn_natDegree_lt n.succ_pos _)]
  exact Finset.sum_congr rfl fun k hk => by
    rw [ofFn_coeff_eq_val_of_lt _ (Finset.mem_range.mp hk)]

section Gaussian

/-- The regularized Gaussian hypergeometric function is represented on the open unit ball by
`regularizedGaussHGFunSeries a b c`, for all complex parameters `a`, `b`, `c`. -/
theorem hasFPowerSeriesOnBall_regularizedGaussHGFun (a b c : ℂ) :
    HasFPowerSeriesOnBall (regularizedGaussHGFun a b c)
      (regularizedGaussHGFunSeries a b c) 0 1 :=
  ((regularizedGaussHGFunSeries a b c).hasFPowerSeriesOnBall
    (zero_lt_one.trans_le (radius_regularizedGaussHGFunSeries_ge_one a b c))).mono
    zero_lt_one (radius_regularizedGaussHGFunSeries_ge_one a b c)

/-- For any complex parameters `a`, `b`, `c`, `regularizedGaussHGFun a b c` is analytic at every
point of the open unit disk. -/
theorem analyticAt_regularizedGaussHGFun (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    AnalyticAt ℂ (regularizedGaussHGFun a b c) z := by
  have hfun : regularizedGaussHGFun a b c = regularizedHGFun {a, b} {c} := by
    ext w
    rw [regularizedGaussHGFun, regularizedGaussHGFunSeries, regularizedHGFun]
  rw [hfun]
  exact analyticAt_regularizedHGFun_of_card_eq_add_one (a := {a, b}) (b := {c})
    (by rw [Multiset.card_pair, Multiset.card_singleton]) hz

/-- For any complex parameters `a`, `b`, `c`, `regularizedGaussHGFun a b c` is analytic on the open
unit disk. -/
theorem analyticOnNhd_regularizedGaussHGFun (a b c : ℂ) :
    AnalyticOnNhd ℂ (regularizedGaussHGFun a b c) (Metric.ball 0 1) := fun _ hz =>
  analyticAt_regularizedGaussHGFun a b c (by simpa using hz)

/-- The defining `tsum` expansion of `regularizedGaussHGFun a b c z` in powers of `z`. -/
theorem regularizedGaussHGFun_eq_tsum_coeff_mul_pow (a b c z : ℂ) :
    regularizedGaussHGFun a b c z =
      ∑' n : ℕ, (regularizedGaussHGFunSeries a b c).coeff n * z ^ n := by
  simp [regularizedGaussHGFun, FormalMultilinearSeries.sum, mul_comm]

/-- At `z = 0`, the regularized Gaussian hypergeometric function evaluates to `(Gamma c)⁻¹` for all
complex parameters `a`, `b`, `c`. -/
@[simp]
theorem regularizedGaussHGFun_zero (a b c : ℂ) :
    regularizedGaussHGFun a b c 0 = (Gamma c)⁻¹ := by
  rw [regularizedGaussHGFun, regularizedGaussHGFunSeries, ← regularizedHGFun, regularizedHGFun_zero]
  simp [regularizedHGFunCoeff]

/-- On the open unit disk, the power series of `regularizedGaussHGFun a b c` is summable. -/
theorem summable_coeff_regularizedGaussHGFunSeries_mul_pow (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    Summable fun n : ℕ => (regularizedGaussHGFunSeries a b c).coeff n * z ^ n := by
  simpa only [← regularizedHGFunCoeff_pair_singleton] using
    (summable_norm_regularizedHGFun_of_card_eq_add_one (a := {a, b}) (b := {c})
      (by rw [Multiset.card_pair, Multiset.card_singleton]) hz).of_norm

/-- When the first upper parameter is a nonpositive integer `-n`, the regularized Gauss
hypergeometric series terminates after `n + 1` terms. -/
theorem regularizedGaussHGFun_neg_natCast_eq_sum (b c z : ℂ) (n : ℕ) :
    regularizedGaussHGFun (-n) b c z =
      ∑ k ∈ Finset.range (n + 1),
        (ascPochhammer ℂ k).eval (-(n : ℂ)) * (ascPochhammer ℂ k).eval b /
          (k ! * Gamma (c + k)) * z ^ k := by
  rw [regularizedGaussHGFun, regularizedGaussHGFunSeries, ← regularizedHGFun]
  simpa only [regularizedHGFunCoeff_pair_singleton, coeff_regularizedGaussHGFunSeries] using
    regularizedHGFun_eq_sum_range_of_neg_natCast_mem (a := {-(n : ℂ), b}) (b := {c}) (by simp) z

/-- Binomial-coefficient form of the terminating regularized Gauss hypergeometric polynomial
(regularized form of DLMF 15.2.4). -/
theorem regularizedGaussHGFun_neg_natCast (b c z : ℂ) (n : ℕ) :
    regularizedGaussHGFun (-n) b c z =
      ∑ k ∈ Finset.range (n + 1),
        (-1) ^ k * n.choose k * (ascPochhammer ℂ k).eval b / Gamma (c + k) * z ^ k := by
  rw [regularizedGaussHGFun_neg_natCast_eq_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hfac : (k ! : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr k.factorial_ne_zero
  rw [TauCeti.ascPochhammer_eval_neg_natCast]
  field_simp

/-- With first upper parameter `0`, `regularizedGaussHGFun 0 b c z` reduces to `(Gamma c)⁻¹` at
every complex argument `z`. -/
@[simp]
theorem regularizedGaussHGFun_zero_left (b c z : ℂ) :
    regularizedGaussHGFun 0 b c z = (Gamma c)⁻¹ := by
  rw [regularizedGaussHGFun, regularizedGaussHGFunSeries, ← regularizedHGFun,
    regularizedHGFun_of_zero_mem (by simp)]
  simp

/-- With second upper parameter `0`, `regularizedGaussHGFun a 0 c z` reduces to `(Gamma c)⁻¹` at
every complex argument `z`. -/
@[simp]
theorem regularizedGaussHGFun_zero_right (a c z : ℂ) :
    regularizedGaussHGFun a 0 c z = (Gamma c)⁻¹ := by
  rw [funext_iff.mp (regularizedGaussHGFun_symm a 0 c) z, regularizedGaussHGFun_zero_left]

/-- When the first upper parameter is a nonpositive integer `-n`, the regularized Gauss
hypergeometric series converges to `regularizedGaussHGFun (-n) b c z` at every complex `z`. -/
theorem hasSum_regularizedGaussHGFun_neg_natCast (b c z : ℂ) (n : ℕ) :
    HasSum (fun k : ℕ => (regularizedGaussHGFunSeries (-n) b c).coeff k * z ^ k)
      (regularizedGaussHGFun (-n) b c z) := by
  rw [regularizedGaussHGFun, regularizedGaussHGFunSeries, ← regularizedHGFun]
  simpa only [regularizedHGFunSeries_coeff] using
    hasSum_regularizedHGFun_of_neg_natCast_mem (a := {-(n : ℂ), b}) (b := {c}) (n := n)
      (by simp) z

/-- The zeroth coefficient of `regularizedGaussHGFunSeries a b c` is `(Gamma c)⁻¹`. -/
@[simp]
theorem coeff_regularizedGaussHGFunSeries_zero (a b c : ℂ) :
    (regularizedGaussHGFunSeries a b c).coeff 0 = (Gamma c)⁻¹ := by
  simp [coeff_regularizedGaussHGFunSeries]

private theorem coeff_regularizedGaussHGFunSeries_c_shift (a b c : ℂ) (k : ℕ) :
    (regularizedGaussHGFunSeries a b c).coeff k =
      (c - a) * (regularizedGaussHGFunSeries a b (c + 1)).coeff k +
        a * (regularizedGaussHGFunSeries (a + 1) b (c + 1)).coeff k := by
  have hap : a * (ascPochhammer ℂ k).eval (a + 1) = (a + k) * (ascPochhammer ℂ k).eval a := by
    rw [ascPochhammer_eval_succ, mul_comm]
  have hΓ := one_div_Gamma_eq_self_mul_one_div_Gamma_add_one (c + k)
  simp only [coeff_regularizedGaussHGFunSeries, div_eq_mul_inv, mul_inv]
  rw [add_right_comm c 1 (k : ℂ), hΓ]
  linear_combination
    (ascPochhammer ℂ k).eval b * (k ! : ℂ)⁻¹ * (Gamma (c + k + 1))⁻¹ * (-hap)

private theorem coeff_regularizedGaussHGFunSeries_b_shift (a b c : ℂ) (k : ℕ) :
    (regularizedGaussHGFunSeries a b c).coeff (k + 1) =
      (regularizedGaussHGFunSeries a (b + 1) c).coeff (k + 1) -
        a * (regularizedGaussHGFunSeries (a + 1) (b + 1) (c + 1)).coeff k := by
  have hb₁ := (ascPochhammer_succ_eval k b).trans (ascPochhammer_eval_succ k b).symm
  have ha₁ := (ascPochhammer_succ_eval k a).trans (ascPochhammer_eval_succ k a).symm
  have hb₂ := ascPochhammer_succ_eval k (b + 1)
  have hn : (k : ℂ) + 1 ≠ 0 := mod_cast Nat.succ_ne_zero k
  have hc : c + ((k : ℂ) + 1) = c + 1 + k := by ring
  rw [coeff_regularizedGaussHGFunSeries, coeff_regularizedGaussHGFunSeries,
    coeff_regularizedGaussHGFunSeries, hb₁, ha₁, hb₂, Nat.factorial_succ, Nat.cast_mul,
    Nat.cast_add, Nat.cast_one, hc]
  field_simp
  ring

private theorem regularizedGaussHGFun_eq_sub_mul_add_mul_of_summable {a b c z : ℂ}
    (hs₁ : Summable fun k : ℕ => (regularizedGaussHGFunSeries a b (c + 1)).coeff k * z ^ k)
    (hs₂ : Summable fun k : ℕ => (regularizedGaussHGFunSeries (a + 1) b (c + 1)).coeff k * z ^ k) :
    regularizedGaussHGFun a b c z =
      (c - a) * regularizedGaussHGFun a b (c + 1) z +
        a * regularizedGaussHGFun (a + 1) b (c + 1) z := by
  simp_rw [regularizedGaussHGFun_eq_tsum_coeff_mul_pow, ← tsum_mul_left,
    ← (hs₁.mul_left (c - a)).tsum_add (hs₂.mul_left a)]
  refine tsum_congr fun k => ?_
  rw [coeff_regularizedGaussHGFunSeries_c_shift]
  ring

private theorem regularizedGaussHGFun_eq_sub_mul_mul_of_summable {a b c z : ℂ}
    (hs₀ : Summable fun k : ℕ => (regularizedGaussHGFunSeries a b c).coeff k * z ^ k)
    (hs₁ : Summable fun k : ℕ => (regularizedGaussHGFunSeries a (b + 1) c).coeff k * z ^ k)
    (hs₂ : Summable fun k : ℕ =>
      (regularizedGaussHGFunSeries (a + 1) (b + 1) (c + 1)).coeff k * z ^ k) :
    regularizedGaussHGFun a b c z =
      regularizedGaussHGFun a (b + 1) c z -
        a * z * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z := by
  rw [eq_sub_iff_add_eq]
  simp_rw [regularizedGaussHGFun_eq_tsum_coeff_mul_pow]
  rw [← tsum_mul_left, hs₀.tsum_eq_zero_add, hs₁.tsum_eq_zero_add, add_assoc,
    ← ((summable_nat_add_iff 1).2 hs₀).tsum_add (hs₂.mul_left (a * z))]
  simp only [coeff_regularizedGaussHGFunSeries_zero, pow_zero, mul_one]
  congr 1
  refine tsum_congr fun k => ?_
  rw [coeff_regularizedGaussHGFunSeries_b_shift, pow_succ]
  ring

/-- Recurrence relating `regularizedGaussHGFun (-(n + 1 : ℕ)) b c z` to lower-parameter values at
`c + 1`, valid at all complex parameters including nonpositive integer values of `c`. -/
theorem regularizedGaussHGFun_neg_natCast_succ_eq_sub (b c z : ℂ) (n : ℕ) :
    regularizedGaussHGFun (-((n + 1 : ℕ) : ℂ)) b c z =
      (c + n + 1) * regularizedGaussHGFun (-((n + 1 : ℕ) : ℂ)) b (c + 1) z -
        (n + 1) * regularizedGaussHGFun (-n) b (c + 1) z := by
  have hshift : -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) := by push_cast; ring
  have hs₂ := (hasSum_regularizedGaussHGFun_neg_natCast b (c + 1) z n).summable
  rw [← hshift] at hs₂
  have h := regularizedGaussHGFun_eq_sub_mul_add_mul_of_summable
    (hasSum_regularizedGaussHGFun_neg_natCast b (c + 1) z (n + 1)).summable hs₂
  rw [hshift] at h
  push_cast at h ⊢
  linear_combination h

/-- Recurrence relating `regularizedGaussHGFun (-(n + 1 : ℕ)) b c z` to shifted-parameter values at
`b + 1`, valid at all complex parameters including nonpositive integer values of `c`. -/
theorem regularizedGaussHGFun_neg_natCast_succ_eq_add (b c z : ℂ) (n : ℕ) :
    regularizedGaussHGFun (-((n + 1 : ℕ) : ℂ)) b c z =
      regularizedGaussHGFun (-((n + 1 : ℕ) : ℂ)) (b + 1) c z +
        (n + 1) * z * regularizedGaussHGFun (-n) (b + 1) (c + 1) z := by
  have hshift : -((n + 1 : ℕ) : ℂ) + 1 = -(n : ℂ) := by push_cast; ring
  have hs₂ := (hasSum_regularizedGaussHGFun_neg_natCast (b + 1) (c + 1) z n).summable
  rw [← hshift] at hs₂
  have h := regularizedGaussHGFun_eq_sub_mul_mul_of_summable
    (hasSum_regularizedGaussHGFun_neg_natCast b c z (n + 1)).summable
    (hasSum_regularizedGaussHGFun_neg_natCast (b + 1) c z (n + 1)).summable hs₂
  rw [hshift] at h
  push_cast at h ⊢
  linear_combination h

/-- The coefficients `C(m + i, m) 𝐅ₘ₊ᵢ` of `regularizedGaussHGFunSeries a b c` are
`(a)ₘ (b)ₘ / m!` times the coefficients of `regularizedGaussHGFunSeries (a + m) (b + m) (c + m)`,
so that the `m`-th Taylor coefficient of `𝐅(a, b; c; ·)` at a point is a multiple of
`𝐅(a + m, b + m; c + m; ·)` there. -/
theorem choose_mul_coeff_regularizedGaussHGFunSeries (a b c : ℂ) (m i : ℕ) :
    ((m + i).choose m : ℂ) * (regularizedGaussHGFunSeries a b c).coeff (m + i) =
      (ascPochhammer ℂ m).eval a * (ascPochhammer ℂ m).eval b / m ! *
        (regularizedGaussHGFunSeries (a + m) (b + m) (c + m)).coeff i := by
  simp only [coeff_regularizedGaussHGFunSeries]
  rw [TauCeti.ascPochhammer_add_eval a m i, TauCeti.ascPochhammer_add_eval b m i,
    show c + ((m + i : ℕ) : ℂ) = c + m + i by push_cast; ring, Nat.cast_add_choose]
  field_simp [Nat.factorial_ne_zero]

/-- For `‖w‖ ≤ y < 1`, `‖𝐅(a, b; c; w)‖` is at most the majorant series
`∑ ‖𝐅ⱼ‖ yʲ` of the coefficients of `regularizedGaussHGFunSeries a b c`. -/
theorem norm_regularizedGaussHGFun_le_tsum (a b c : ℂ) {w : ℂ} {y : ℝ} (hw : ‖w‖ ≤ y)
    (hy : y < 1) :
    ‖regularizedGaussHGFun a b c w‖ ≤
      ∑' j, ‖(regularizedGaussHGFunSeries a b c).coeff j‖ * y ^ j := by
  have hy₀ : 0 ≤ y := (norm_nonneg w).trans hw
  have hs := (summable_coeff_regularizedGaussHGFunSeries_mul_pow a b c
    (z := (y : ℂ)) (by rwa [norm_real, Real.norm_of_nonneg hy₀])).norm
  simp only [norm_mul, norm_pow, norm_real, Real.norm_of_nonneg hy₀] at hs
  have hle (j : ℕ) : ‖(regularizedGaussHGFunSeries a b c).coeff j * w ^ j‖ ≤
      ‖(regularizedGaussHGFunSeries a b c).coeff j‖ * y ^ j := by
    rw [norm_mul, norm_pow]; gcongr
  have hs' := hs.of_nonneg_of_le (fun _ => norm_nonneg _) hle
  rw [regularizedGaussHGFun_eq_tsum_coeff_mul_pow]
  exact (norm_tsum_le_tsum_norm hs').trans (Summable.tsum_le_tsum hle hs' hs)

open Finset in
/-- For `‖u‖ + ‖z‖ < 1`, the norms of the terms `C(i + j, i) 𝐅ᵢ₊ⱼ uⁱ zʲ` of the binomial double
series of `𝐅(a, b; c; u + z)` sum to the majorant series `∑ ‖𝐅ₙ‖ (‖u‖ + ‖z‖)ⁿ`. -/
theorem hasSum_norm_choose_mul_coeff_regularizedGaussHGFunSeries (a b c : ℂ) {u z : ℂ}
    (h : ‖u‖ + ‖z‖ < 1) :
    HasSum (fun q : ℕ × ℕ => ‖((q.1 + q.2).choose q.1 : ℂ) *
        (regularizedGaussHGFunSeries a b c).coeff (q.1 + q.2) * (u ^ q.1 * z ^ q.2)‖)
      (∑' n, ‖(regularizedGaussHGFunSeries a b c).coeff n‖ * (‖u‖ + ‖z‖) ^ n) := by
  set g : ℕ × ℕ → ℝ := fun q => ‖((q.1 + q.2).choose q.1 : ℂ) *
    (regularizedGaussHGFunSeries a b c).coeff (q.1 + q.2) * (u ^ q.1 * z ^ q.2)‖
  have hfib (n : ℕ) : ∑ q ∈ antidiagonal n, g q =
      ‖(regularizedGaussHGFunSeries a b c).coeff n‖ * (‖u‖ + ‖z‖) ^ n := by
    rw [(Commute.all _ _).add_pow', mul_sum]
    refine sum_congr rfl fun q hq => ?_
    rw [mem_antidiagonal] at hq
    simp only [g, norm_mul, norm_pow, Complex.norm_natCast, hq, nsmul_eq_mul]
    ring
  have h₀ : 0 ≤ ‖u‖ + ‖z‖ := by positivity
  have hy : Summable fun n =>
      ‖(regularizedGaussHGFunSeries a b c).coeff n‖ * (‖u‖ + ‖z‖) ^ n := by
    have := (summable_coeff_regularizedGaussHGFunSeries_mul_pow a b c
      (z := ((‖u‖ + ‖z‖ : ℝ) : ℂ)) (by rwa [norm_real, Real.norm_of_nonneg h₀])).norm
    simpa only [norm_mul, norm_pow, norm_real, Real.norm_of_nonneg h₀] using this
  have hgs : Summable g := by
    rw [← HasAntidiagonal.sigmaAntidiagonalEquivProd.summable_iff]
    refine (summable_sigma_of_nonneg fun _ => norm_nonneg _).2
      ⟨fun n => Summable.of_finite, hy.congr fun n => ?_⟩
    rw [tsum_fintype]
    exact ((sum_coe_sort (antidiagonal n) g).trans (hfib n)).symm
  have hgrp := hgs.hasSum.sum_antidiagonal
  rw [show (fun n => ∑ q ∈ antidiagonal n, g q) = _ from funext hfib] at hgrp
  have hg := hgs.hasSum
  rwa [← hgrp.tsum_eq] at hg

open Finset in
/-- For `‖u‖ + ‖z‖ < 1`, `𝐅(a, b; c; u + z)` is the sum of the binomial double series
`∑ C(i + j, i) 𝐅ᵢ₊ⱼ uⁱ zʲ` in powers of `u` and `z`. -/
theorem hasSum_choose_mul_coeff_regularizedGaussHGFunSeries (a b c : ℂ) {u z : ℂ}
    (h : ‖u‖ + ‖z‖ < 1) :
    HasSum (fun q : ℕ × ℕ => ((q.1 + q.2).choose q.1 : ℂ) *
        (regularizedGaussHGFunSeries a b c).coeff (q.1 + q.2) * (u ^ q.1 * z ^ q.2))
      (regularizedGaussHGFun a b c (u + z)) := by
  set f : ℕ × ℕ → ℂ := fun q => ((q.1 + q.2).choose q.1 : ℂ) *
    (regularizedGaussHGFunSeries a b c).coeff (q.1 + q.2) * (u ^ q.1 * z ^ q.2)
  have hs : Summable f :=
    (hasSum_norm_choose_mul_coeff_regularizedGaussHGFunSeries a b c h).summable.of_norm
  have hgrp := hs.hasSum.sum_antidiagonal
  have hfib (n : ℕ) : ∑ q ∈ antidiagonal n, f q =
      (regularizedGaussHGFunSeries a b c).coeff n * (u + z) ^ n := by
    rw [(Commute.all _ _).add_pow', mul_sum]
    refine sum_congr rfl fun q hq => ?_
    rw [mem_antidiagonal] at hq
    simp only [f, hq, nsmul_eq_mul]
    ring
  rw [show (fun n => ∑ q ∈ antidiagonal n, f q) = _ from funext hfib] at hgrp
  have hF := hs.hasSum
  rwa [← (hasSum_regularizedGaussHGFun a b c ((norm_add_le _ _).trans_lt h)).unique hgrp] at hF

private theorem succ_mul_coeff_regularizedGaussHGFunSeries_succ (a b c : ℂ) (n : ℕ) :
    ((n : ℂ) + 1) * (regularizedGaussHGFunSeries a b c).coeff (n + 1) =
      a * b * (regularizedGaussHGFunSeries (a + 1) (b + 1) (c + 1)).coeff n := by
  have ha := (ascPochhammer_succ_eval n a).trans (ascPochhammer_eval_succ n a).symm
  have hb := (ascPochhammer_succ_eval n b).trans (ascPochhammer_eval_succ n b).symm
  have hn : (n : ℂ) + 1 ≠ 0 := mod_cast Nat.succ_ne_zero n
  have hc : c + ((n : ℂ) + 1) = c + 1 + n := by ring
  rw [coeff_regularizedGaussHGFunSeries, coeff_regularizedGaussHGFunSeries, ha, hb,
    Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, hc]
  field_simp

/-- On the open unit disk, the derivative of `regularizedGaussHGFun a b c` is
`a * b * regularizedGaussHGFun (a + 1) (b + 1) (c + 1)` (DLMF 15.5.1 in regularized form). -/
theorem deriv_regularizedGaussHGFun (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    deriv (regularizedGaussHGFun a b c) z =
      a * b * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z := by
  have hz' : ‖z‖ₑ < 1 := by rwa [← ofReal_norm, ENNReal.ofReal_lt_one]
  have hp : HasFPowerSeriesOnBall (regularizedGaussHGFun a b c)
      (FormalMultilinearSeries.ofScalars ℂ (regularizedGaussHGFunSeries a b c).coeff) 0 1 := by
    simpa using hasFPowerSeriesOnBall_regularizedGaussHGFun a b c
  have hd := hp.iteratedDeriv_eq_tsum_descFactorial_mul_pow hz' 1
  rw [iteratedDeriv_one] at hd
  have hsum : Summable fun k : ℕ =>
      (k.descFactorial 1 : ℂ) * (regularizedGaussHGFunSeries a b c).coeff k * z ^ (k - 1) := by
    rw [← summable_nat_add_iff 1]
    refine ((summable_coeff_regularizedGaussHGFunSeries_mul_pow (a + 1) (b + 1) (c + 1) hz).mul_left
      (a * b)).congr fun n => ?_
    simp only [Nat.descFactorial_one, add_tsub_cancel_right, Nat.cast_add, Nat.cast_one,
      succ_mul_coeff_regularizedGaussHGFunSeries_succ, mul_assoc]
  rw [hd, hsum.tsum_eq_zero_add]
  simp only [Nat.descFactorial_one, Nat.cast_zero, zero_mul, zero_add, add_tsub_cancel_right,
    Nat.cast_add, Nat.cast_one, succ_mul_coeff_regularizedGaussHGFunSeries_succ, mul_assoc,
    regularizedGaussHGFun_eq_tsum_coeff_mul_pow, ← tsum_mul_left]

/-- `HasDerivAt` form of `Complex.deriv_regularizedGaussHGFun` on the open unit disk. -/
theorem hasDerivAt_regularizedGaussHGFun (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    HasDerivAt (regularizedGaussHGFun a b c)
      (a * b * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z) z := by
  rw [← deriv_regularizedGaussHGFun a b c hz]
  exact (analyticAt_regularizedGaussHGFun a b c hz).differentiableAt.hasDerivAt

/-- Regularized Gauss contiguous shift in `c` and `a` on the open unit disk (DLMF 15.5.15):
`𝐅(a, b; c; z) = (c - a) 𝐅(a, b; c + 1; z) + a 𝐅(a + 1, b; c + 1; z)`. -/
theorem regularizedGaussHGFun_eq_sub_mul_add_mul (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b c z =
      (c - a) * regularizedGaussHGFun a b (c + 1) z +
        a * regularizedGaussHGFun (a + 1) b (c + 1) z :=
  regularizedGaussHGFun_eq_sub_mul_add_mul_of_summable
    (summable_coeff_regularizedGaussHGFunSeries_mul_pow a b (c + 1) hz)
    (summable_coeff_regularizedGaussHGFunSeries_mul_pow (a + 1) b (c + 1) hz)

/-- Regularized Gauss contiguous shift in `b` on the open unit disk (DLMF 15.5.16_5):
`𝐅(a, b; c; z) = 𝐅(a, b + 1; c; z) - a z 𝐅(a + 1, b + 1; c + 1; z)`. -/
theorem regularizedGaussHGFun_eq_regularizedGaussHGFun_sub_mul_mul (a b c : ℂ) {z : ℂ}
    (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b c z =
      regularizedGaussHGFun a (b + 1) c z -
        a * z * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z :=
  regularizedGaussHGFun_eq_sub_mul_mul_of_summable
    (summable_coeff_regularizedGaussHGFunSeries_mul_pow a b c hz)
    (summable_coeff_regularizedGaussHGFunSeries_mul_pow a (b + 1) c hz)
    (summable_coeff_regularizedGaussHGFunSeries_mul_pow (a + 1) (b + 1) (c + 1) hz)

/-- Regularized differential-contiguous relation lowering `c` on the open unit disk (DLMF 15.5.4):
`z * deriv (𝐅(a, b; c + 1)) z + c * 𝐅(a, b; c + 1; z) = 𝐅(a, b; c; z)`. -/
theorem mul_deriv_regularizedGaussHGFun_add_mul_eq (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    z * deriv (regularizedGaussHGFun a b (c + 1)) z + c * regularizedGaussHGFun a b (c + 1) z =
      regularizedGaussHGFun a b c z := by
  have h₁ := regularizedGaussHGFun_eq_sub_mul_add_mul a b c hz
  have h₂ := regularizedGaussHGFun_eq_regularizedGaussHGFun_sub_mul_mul b a (c + 1) hz
  rw [regularizedGaussHGFun_symm b a, regularizedGaussHGFun_symm b (a + 1),
    regularizedGaussHGFun_symm (b + 1) (a + 1)] at h₂
  rw [deriv_regularizedGaussHGFun a b (c + 1) hz]
  linear_combination -h₁ + a * h₂

/-- Regularized differential-contiguous relation raising `b` on the open unit disk (DLMF 15.5.3):
`z * deriv (𝐅(a, b; c)) z + b * 𝐅(a, b; c; z) = b * 𝐅(a, b + 1; c; z)`. -/
theorem mul_deriv_regularizedGaussHGFun_add_mul_eq_mul (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    z * deriv (regularizedGaussHGFun a b c) z + b * regularizedGaussHGFun a b c z =
      b * regularizedGaussHGFun a (b + 1) c z := by
  rw [deriv_regularizedGaussHGFun a b c hz]
  linear_combination b * regularizedGaussHGFun_eq_regularizedGaussHGFun_sub_mul_mul a b c hz

/-- Regularized differential-contiguous relation lowering `b` on the open unit disk (DLMF 15.5.19):
`z * (1 - z) * deriv (𝐅(a, b; c)) z` equals
`(c - b) * 𝐅(a, b - 1; c; z) - (c - b - a * z) * 𝐅(a, b; c; z)`. -/
theorem mul_one_sub_mul_deriv_regularizedGaussHGFun (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    z * (1 - z) * deriv (regularizedGaussHGFun a b c) z =
      (c - b) * regularizedGaussHGFun a (b - 1) c z -
        (c - b - a * z) * regularizedGaussHGFun a b c z := by
  have h₁ := regularizedGaussHGFun_eq_sub_mul_add_mul b (a + 1) c hz
  rw [regularizedGaussHGFun_symm b (a + 1), regularizedGaussHGFun_symm b (a + 1),
    regularizedGaussHGFun_symm (b + 1) (a + 1)] at h₁
  have h₂ := regularizedGaussHGFun_eq_regularizedGaussHGFun_sub_mul_mul b a c hz
  rw [regularizedGaussHGFun_symm b a, regularizedGaussHGFun_symm b (a + 1),
    regularizedGaussHGFun_symm (b + 1) (a + 1)] at h₂
  have h₃ := regularizedGaussHGFun_eq_regularizedGaussHGFun_sub_mul_mul a (b - 1) c hz
  rw [sub_add_cancel] at h₃
  rw [deriv_regularizedGaussHGFun a b c hz]
  linear_combination -a * z * h₁ - a * z * h₂ - (c - b) * h₃

private theorem differentiable_coeff_regularizedGaussHGFunSeries_mul_pow
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {fa fb fc fz : E → ℂ}
    (ha : Differentiable ℂ fa) (hb : Differentiable ℂ fb)
    (hc : Differentiable ℂ fc) (hz : Differentiable ℂ fz) (n : ℕ) :
    Differentiable ℂ fun w =>
      (regularizedGaussHGFunSeries (fa w) (fb w) (fc w)).coeff n * fz w ^ n := by
  simp only [coeff_regularizedGaussHGFunSeries, div_eq_mul_inv, mul_inv]
  have _ : Differentiable ℂ fun w => (Gamma (fc w + n))⁻¹ :=
    differentiable_one_div_Gamma.comp (by fun_prop)
  fun_prop

private theorem norm_regularizedGaussHGFun_term_add_le {a b c z : ℂ} {M k : ℕ} {CΓ r : ℝ}
    (ha : ‖a‖ ≤ M) (hb : ‖b‖ ≤ M) (hc : 1 ≤ (c + ((M + 1 : ℕ) : ℂ)).re)
    (hCΓ : ‖(Gamma (c + ((M + 1 : ℕ) : ℂ)))⁻¹‖ ≤ CΓ) (hz : ‖z‖ ≤ r) :
    ‖(regularizedGaussHGFunSeries a b c).coeff (M + 1 + k) * z ^ (M + 1 + k)‖ ≤
      CΓ * (M.ascFactorial (M + 1) : ℝ) ^ 2 * r ^ (M + 1) *
        ‖(regularizedGaussHGFunSeries ((2 * M + 1 : ℕ) : ℂ) ((2 * M + 1 : ℕ) : ℂ) 1).coeff k *
          (r : ℂ) ^ k‖ := by
  have hr₀ : 0 ≤ r := (norm_nonneg z).trans hz
  have hCΓ₀ : 0 ≤ CΓ := (norm_nonneg _).trans hCΓ
  let P : ℝ := M.ascFactorial (M + 1)
  have hΓk : ‖Gamma (c + ((M + 1 + k : ℕ) : ℂ))‖⁻¹ ≤ CΓ / k ! := by
    rw [← norm_inv, Nat.cast_add, ← add_assoc]
    exact (norm_inv_Gamma_add_natCast_le hc k).trans
      (div_le_div_of_nonneg_right hCΓ (Nat.cast_nonneg _))
  have hM2 : M + (M + 1) = 2 * M + 1 := by omega
  have hpM : (M.ascFactorial (M + 1 + k) : ℝ) = P * ((2 * M + 1).ascFactorial k : ℝ) := by
    rw [← Nat.ascFactorial_mul_ascFactorial M (M + 1) k, hM2, Nat.cast_mul]
  -- Compare with the positive majorant series `𝐅(2M + 1, 2M + 1; 1; r)`.
  have hk_coeff :
      ‖(regularizedGaussHGFunSeries ((2 * M + 1 : ℕ) : ℂ) ((2 * M + 1 : ℕ) : ℂ) 1).coeff k *
          (r : ℂ) ^ k‖ =
        ((2 * M + 1).ascFactorial k : ℝ) ^ 2 / (k ! * k !) * r ^ k := by
    rw [coeff_regularizedGaussHGFunSeries, add_comm (1 : ℂ) k, Gamma_nat_eq_factorial,
      ascPochhammer_nat_eq_natCast_ascFactorial]
    simp [abs_of_nonneg hr₀, sq]
  rw [hk_coeff, coeff_regularizedGaussHGFunSeries, pow_add z (M + 1) k, div_eq_mul_inv, mul_inv]
  simp only [norm_mul, norm_inv, Complex.norm_natCast, norm_pow]
  have ha_le := (TauCeti.norm_ascPochhammer_eval_le_ascFactorial (M + 1 + k) ha).trans_eq hpM
  have hb_le := (TauCeti.norm_ascPochhammer_eval_le_ascFactorial (M + 1 + k) hb).trans_eq hpM
  have hinv_fac : ((((M + 1 + k)! : ℕ) : ℝ))⁻¹ ≤ ((k ! : ℝ))⁻¹ :=
    inv_anti₀ (mod_cast Nat.factorial_pos k) (mod_cast Nat.factorial_le (Nat.le_add_left k (M + 1)))
  calc ‖(ascPochhammer ℂ (M + 1 + k)).eval a‖ *
          ‖(ascPochhammer ℂ (M + 1 + k)).eval b‖ *
          (((((M + 1 + k)! : ℕ) : ℝ))⁻¹ * ‖Gamma (c + ↑(M + 1 + k))‖⁻¹) *
          (‖z‖ ^ (M + 1) * ‖z‖ ^ k)
      ≤ (P * ((2 * M + 1).ascFactorial k : ℝ)) * (P * ((2 * M + 1).ascFactorial k : ℝ)) *
          (((k ! : ℝ))⁻¹ * (CΓ / k !)) * (r ^ (M + 1) * r ^ k) := by gcongr
    _ = CΓ * P ^ 2 * r ^ (M + 1) *
          (((2 * M + 1).ascFactorial k : ℝ) ^ 2 / (k ! * k !) * r ^ k) := by ring

private theorem exists_summable_bound_regularizedGaussHGFun_polydisc {v₀ : Fin 4 → ℂ}
    (hv₀ : ‖v₀ 3‖ < 1) :
    ∃ δ > 0, ∃ u : ℕ → ℝ, Summable u ∧ ∀ n : ℕ, ∀ w ∈ Metric.ball v₀ δ,
      ‖(regularizedGaussHGFunSeries (w 0) (w 1) (w 2)).coeff n * w 3 ^ n‖ ≤ u n := by
  let δ : ℝ := (1 - ‖v₀ 3‖) / 2
  let r : ℝ := (1 + ‖v₀ 3‖) / 2
  have hδ : 0 < δ := by dsimp [δ]; linarith
  have hr₀ : 0 ≤ r := by dsimp [r]; linarith [norm_nonneg (v₀ 3)]
  have hr_norm : ‖(r : ℂ)‖ < 1 := by rw [Complex.norm_of_nonneg hr₀]; dsimp [r]; linarith
  -- On the compact closed ball `K` around `v₀`, all parameters are bounded and `‖w 3‖ ≤ r < 1`.
  let K : Set (Fin 4 → ℂ) := Metric.closedBall v₀ δ
  have hK : IsCompact K := isCompact_closedBall v₀ δ
  obtain ⟨M, hM⟩ := exists_nat_gt (‖v₀‖ + δ + 1)
  have hΓ_cont : Continuous fun w : Fin 4 → ℂ => (Gamma (w 2 + ((M + 1 : ℕ) : ℂ)))⁻¹ :=
    (differentiable_one_div_Gamma.comp (by fun_prop)).continuous
  obtain ⟨CΓ, hCΓ⟩ := hK.exists_bound_of_continuousOn hΓ_cont.continuousOn
  have hfin (n : ℕ) : ∃ B : ℝ, ∀ w ∈ K,
      ‖(regularizedGaussHGFunSeries (w 0) (w 1) (w 2)).coeff n * w 3 ^ n‖ ≤ B :=
    hK.exists_bound_of_continuousOn
      (differentiable_coeff_regularizedGaussHGFunSeries_mul_pow
        (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) n).continuous.continuousOn
  choose Bf hBf using hfin
  -- Bound the first `M + 1` terms by compactness and the tail by `𝐅(2M + 1, 2M + 1; 1; r)`.
  let C : ℝ := CΓ * (M.ascFactorial (M + 1) : ℝ) ^ 2 * r ^ (M + 1)
  let u : ℕ → ℝ := fun n => if n < M + 1 then Bf n else
    C * ‖(regularizedGaussHGFunSeries ((2 * M + 1 : ℕ) : ℂ) ((2 * M + 1 : ℕ) : ℂ) 1).coeff
      (n - (M + 1)) * (r : ℂ) ^ (n - (M + 1))‖
  refine ⟨δ, hδ, u, ?_, fun n w hw => ?_⟩
  · rw [← summable_nat_add_iff (M + 1)]
    refine ((summable_coeff_regularizedGaussHGFunSeries_mul_pow
      ((2 * M + 1 : ℕ) : ℂ) ((2 * M + 1 : ℕ) : ℂ) 1 hr_norm).norm.mul_left C).congr fun k => ?_
    dsimp only [u]
    split_ifs with h
    · omega
    · rw [Nat.add_sub_cancel]
  · have hwK : w ∈ K := Metric.ball_subset_closedBall hw
    have hw_sub : ‖w - v₀‖ ≤ δ := mem_closedBall_iff_norm.mp hwK
    have hw_coord (i : Fin 4) : ‖w i‖ ≤ ‖v₀ i‖ + δ := by
      have hi : ‖w i - v₀ i‖ ≤ δ := (norm_le_pi_norm (w - v₀) i).trans hw_sub
      linarith [norm_le_norm_add_norm_sub' (w i) (v₀ i)]
    dsimp only [u]
    split_ifs with hlt
    · exact hBf n w hwK
    · obtain ⟨k, rfl⟩ : ∃ k, n = M + 1 + k :=
        ⟨n - (M + 1), (Nat.add_sub_of_le (not_lt.mp hlt)).symm⟩
      rw [Nat.add_sub_cancel_left]
      have hM_coord (i : Fin 4) : ‖w i‖ ≤ M - 1 := by
        linarith [hw_coord i, norm_le_pi_norm v₀ i]
      refine norm_regularizedGaussHGFun_term_add_le
        ((hM_coord 0).trans (by linarith)) ((hM_coord 1).trans (by linarith)) ?_
        (hCΓ w hwK) ((hw_coord 3).trans_eq (by dsimp [δ, r]; ring))
      have hre := neg_le_of_abs_le ((Complex.abs_re_le_norm (w 2)).trans (hM_coord 2))
      simp only [add_re, natCast_re, Nat.cast_add, Nat.cast_one, one_re]
      linarith

/-- The regularized Gaussian hypergeometric function is jointly analytic in `(a, b, c, z)` at every
point where `‖z‖ < 1`. -/
theorem analyticAt_uncurry_regularizedGaussHGFun {p : ℂ × ℂ × ℂ × ℂ} (hp : ‖p.2.2.2‖ < 1) :
    AnalyticAt ℂ (fun q : ℂ × ℂ × ℂ × ℂ =>
      regularizedGaussHGFun q.1 q.2.1 q.2.2.1 q.2.2.2) p := by
  let e : ℂ × ℂ × ℂ × ℂ → Fin 4 → ℂ := fun q => ![q.1, q.2.1, q.2.2.1, q.2.2.2]
  have he : AnalyticAt ℂ e p := AnalyticAt.pi fun i => by
    fin_cases i
    · exact analyticAt_fst
    · exact analyticAt_fst.comp analyticAt_snd
    · exact analyticAt_fst.comp (analyticAt_snd.comp analyticAt_snd)
    · exact analyticAt_snd.comp (analyticAt_snd.comp analyticAt_snd)
  obtain ⟨δ, hδ, u, hu, hbound⟩ := exists_summable_bound_regularizedGaussHGFun_polydisc
    (v₀ := e p) hp
  -- Uniform convergence of the holomorphic partial sums on `ball (e p) δ` yields holomorphy, hence
  -- analyticity.
  let F : ℕ → (Fin 4 → ℂ) → ℂ := fun n w =>
    (regularizedGaussHGFunSeries (w 0) (w 1) (w 2)).coeff n * w 3 ^ n
  let g : (Fin 4 → ℂ) → ℂ := fun w => ∑' n, F n w
  have hF_diff (n : ℕ) : Differentiable ℂ (F n) :=
    differentiable_coeff_regularizedGaussHGFunSeries_mul_pow
      (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop) n
  have hg_anal : AnalyticAt ℂ g (e p) :=
    ((tendstoUniformlyOn_tsum hu hbound).differentiableOn
      (Eventually.of_forall fun s => DifferentiableOn.fun_sum fun n _ =>
        (hF_diff n).differentiableOn)
      Metric.isOpen_ball).analyticAt_of_finiteDimensional
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hδ))
  have hgf : g ∘ e = fun q : ℂ × ℂ × ℂ × ℂ =>
      regularizedGaussHGFun q.1 q.2.1 q.2.2.1 q.2.2.2 := by
    ext q
    simp [g, F, e, regularizedGaussHGFun_eq_tsum_coeff_mul_pow]
  exact hgf ▸ hg_anal.comp he

/-- `Complex.regularizedGaussHGFun` composed with four analytic functions is analytic wherever the
fourth function takes values in the open unit disk. -/
theorem _root_.AnalyticAt.regularizedGaussHGFun {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {fa fb fc fz : E → ℂ} {x : E}
    (ha : AnalyticAt ℂ fa x) (hb : AnalyticAt ℂ fb x)
    (hc : AnalyticAt ℂ fc x) (hz : AnalyticAt ℂ fz x) (hz_lt : ‖fz x‖ < 1) :
    AnalyticAt ℂ (fun w => Complex.regularizedGaussHGFun (fa w) (fb w) (fc w) (fz w)) x :=
  (analyticAt_uncurry_regularizedGaussHGFun hz_lt).comp (ha.prod (hb.prod (hc.prod hz)))

/-- `Complex.regularizedGaussHGFun` composed with four complex-differentiable functions at `x` is
complex-differentiable at `x` when `‖fz x‖ < 1`. -/
theorem _root_.DifferentiableAt.regularizedGaussHGFun {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {fa fb fc fz : E → ℂ} {x : E}
    (ha : DifferentiableAt ℂ fa x) (hb : DifferentiableAt ℂ fb x)
    (hc : DifferentiableAt ℂ fc x) (hz : DifferentiableAt ℂ fz x) (hz_lt : ‖fz x‖ < 1) :
    DifferentiableAt ℂ (fun w => Complex.regularizedGaussHGFun (fa w) (fb w) (fc w) (fz w)) x :=
  (analyticAt_uncurry_regularizedGaussHGFun hz_lt).differentiableAt.comp x
    (ha.prodMk (hb.prodMk (hc.prodMk hz)))

/-- `Complex.regularizedGaussHGFun` composed with four functions complex-differentiable within `s`
at `x` is complex-differentiable within `s` at `x` when `‖fz x‖ < 1`. -/
theorem _root_.DifferentiableWithinAt.regularizedGaussHGFun {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {fa fb fc fz : E → ℂ} {s : Set E} {x : E}
    (ha : DifferentiableWithinAt ℂ fa s x) (hb : DifferentiableWithinAt ℂ fb s x)
    (hc : DifferentiableWithinAt ℂ fc s x) (hz : DifferentiableWithinAt ℂ fz s x)
    (hz_lt : ‖fz x‖ < 1) :
    DifferentiableWithinAt ℂ
      (fun w => Complex.regularizedGaussHGFun (fa w) (fb w) (fc w) (fz w)) s x :=
  (analyticAt_uncurry_regularizedGaussHGFun hz_lt).differentiableAt.comp_differentiableWithinAt x
    (ha.prodMk (hb.prodMk (hc.prodMk hz)))

/-- `Complex.regularizedGaussHGFun` composed with four functions complex-differentiable on `s` is
complex-differentiable on `s` when `‖fz x‖ < 1` on `s`. -/
theorem _root_.DifferentiableOn.regularizedGaussHGFun {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {fa fb fc fz : E → ℂ} {s : Set E}
    (ha : DifferentiableOn ℂ fa s) (hb : DifferentiableOn ℂ fb s)
    (hc : DifferentiableOn ℂ fc s) (hz : DifferentiableOn ℂ fz s)
    (hz_lt : ∀ x ∈ s, ‖fz x‖ < 1) :
    DifferentiableOn ℂ (fun w => Complex.regularizedGaussHGFun (fa w) (fb w) (fc w) (fz w)) s :=
  fun x hx => (ha x hx).regularizedGaussHGFun (hb x hx) (hc x hx) (hz x hx) (hz_lt x hx)

/-- `Complex.regularizedGaussHGFun` composed with four complex-differentiable functions is
complex-differentiable everywhere when `‖fz x‖ < 1` everywhere. -/
theorem _root_.Differentiable.regularizedGaussHGFun {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {fa fb fc fz : E → ℂ}
    (ha : Differentiable ℂ fa) (hb : Differentiable ℂ fb)
    (hc : Differentiable ℂ fc) (hz : Differentiable ℂ fz) (hz_lt : ∀ x, ‖fz x‖ < 1) :
    Differentiable ℂ fun w => Complex.regularizedGaussHGFun (fa w) (fb w) (fc w) (fz w) :=
  fun x => (ha x).regularizedGaussHGFun (hb x) (hc x) (hz x) (hz_lt x)

/-- Regularized three-term contiguous relation raising `a`, `b` and `c` on the open unit disk:
`𝐅(a, b; c; z) = c (1 - z) 𝐅(a + 1, b + 1; c + 1; z) + (c - a)(c - b) z 𝐅(a + 1, b + 1; c + 2; z)`,
for all complex `a`, `b`, `c`. -/
theorem regularizedGaussHGFun_eq_mul_one_sub_mul_add_mul (a b c : ℂ) {z : ℂ} (hz : ‖z‖ < 1) :
    regularizedGaussHGFun a b c z =
      c * (1 - z) * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z +
        (c - a) * (c - b) * z * regularizedGaussHGFun (a + 1) (b + 1) (c + 2) z := by
  -- Multiplied by `a`, the relation is a combination of the shifts in `a`, `b` and `c`.
  have hmul (a : ℂ) : a * regularizedGaussHGFun a b c z =
      a * (c * (1 - z) * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z +
        (c - a) * (c - b) * z * regularizedGaussHGFun (a + 1) (b + 1) (c + 2) z) := by
    have h₂ := regularizedGaussHGFun_eq_sub_mul_add_mul b a c hz
    rw [regularizedGaussHGFun_symm b a, regularizedGaussHGFun_symm b a,
      regularizedGaussHGFun_symm (b + 1) a] at h₂
    have h₅ := regularizedGaussHGFun_eq_regularizedGaussHGFun_sub_mul_mul a b c hz
    have h₇ := regularizedGaussHGFun_eq_regularizedGaussHGFun_sub_mul_mul a b (c + 1) hz
    rw [show c + 1 + 1 = c + 2 by ring] at h₇
    have h₉ := regularizedGaussHGFun_eq_sub_mul_add_mul a (b + 1) c hz
    linear_combination -(c - a) * h₂ - (c - a) * (c - b) * h₇ + c * h₅ + c * h₉
  -- Both sides are continuous in `a`, so the relation extends from `a ≠ 0` to `a = 0`.
  have hd (k : ℂ) : Differentiable ℂ fun a => regularizedGaussHGFun (a + 1) (b + 1) (c + k) z :=
    Differentiable.regularizedGaussHGFun (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop)
      fun _ => hz
  have hL : Continuous fun a => regularizedGaussHGFun a b c z :=
    (Differentiable.regularizedGaussHGFun differentiable_id (differentiable_const _)
      (differentiable_const _) (differentiable_const _) fun _ => hz).continuous
  have hR : Continuous fun a => c * (1 - z) * regularizedGaussHGFun (a + 1) (b + 1) (c + 1) z +
      (c - a) * (c - b) * z * regularizedGaussHGFun (a + 1) (b + 1) (c + 2) z :=
    (continuous_const.mul (hd 1).continuous).add
      ((((continuous_const.sub continuous_id).mul continuous_const).mul continuous_const).mul
        (hd 2).continuous)
  have hext := hL.ext_on (dense_compl_singleton 0) hR fun a' ha' =>
    mul_left_cancel₀ (Set.mem_compl_singleton_iff.mp ha') (hmul a')
  exact congrFun hext a

end Gaussian

end Complex
