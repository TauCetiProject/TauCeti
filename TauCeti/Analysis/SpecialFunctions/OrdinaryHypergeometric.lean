/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import Mathlib.RingTheory.PowerSeries.Derivative
public import TauCeti.Analysis.Analytic.OfScalars
public import TauCeti.RingTheory.Binomial
import Mathlib.Analysis.Analytic.ChangeOrigin
import TauCeti.RingTheory.PowerSeries.Derivative

/-!
# The ordinary hypergeometric function on the unit ball

Mathlib computes the radius of convergence of the series of `₂F₁(a, b; c; ·)`: it is `1`, unless
one of the parameters is a nonpositive integer, in which case the series is finite or its
coefficients take the junk value `0`, and the radius is `⊤`. This file records the uniform
consequence that the radius is always at least `1`, so `₂F₁(a, b; c; ·)` is analytic on the open
unit ball for all parameters.

Over a complete nontrivially normed field of characteristic zero, the series can be
differentiated termwise inside its disc of convergence. This shows that, when `c` is not a
nonpositive integer, `y = ₂F₁(a, b; c; ·)` solves **Gauss's hypergeometric equation**
`x (1 - x) y'' + (c - (a + b + 1) x) y' - a b y = 0` (DLMF 15.10.1) inside that disc. Over `ℝ` or
`ℂ`, this gives the iterated derivatives `(a)ₙ (b)ₙ / (c)ₙ` of `₂F₁(a, b; c; ·)` at `0`, and the
equation on the open unit disc, and on the whole field when the series terminates. The equation
is equivalent to the recurrence `(n + 1) (c + n) cₙ₊₁ = (a + n) (b + n) cₙ` for the coefficients
`cₙ` of the series.

## Main statements

* `TauCeti.one_le_radius_ordinaryHypergeometricSeries`: the radius of convergence of
  `ordinaryHypergeometricSeries 𝔸 a b c` is at least `1`.
* `TauCeti.analyticOnNhd_ordinaryHypergeometric`: `₂F₁ a b c` is analytic on the open unit ball.
* `TauCeti.mem_eball_ordinaryHypergeometricSeries_radius`: the open unit ball lies inside the
  ball of convergence of the series.
* `TauCeti.hasSum_ordinaryHypergeometric`: on the open unit ball, `₂F₁ a b c` is the sum of its
  series, and `TauCeti.summable_norm_ordinaryHypergeometricCoefficient_smul_pow`: the series
  converges absolutely there.
* `TauCeti.hasSum_multichoose_mul_multichoose_mul_pow`: with lower parameter `1`, the coefficients
  are products of generalized multichoose numbers, so `∑ (a)ₙ (b)ₙ / (n!)² xⁿ = ₂F₁(a, b; 1; x)`.
  For `a = b` over `𝕂` this is `TauCeti.hasSum_multichoose_sq_mul_pow`.
* `TauCeti.ordinaryHypergeometric_eq_one_add_sq_mul_add_tsum`,
  `TauCeti.one_add_sq_mul_le_ordinaryHypergeometric`, `TauCeti.exists_ordinaryHypergeometric_le`:
  `₂F₁(a, a; 1; x) = 1 + a² x + O(x²)`, with the explicit tail on the open unit disc and two-sided
  bounds for real `0 ≤ x ≤ r < 1`.
* `TauCeti.ordinaryHypergeometric_neg_nat_eq_sum`: a terminating `₂F₁(−n, b; c; z)` is the sum of
  its first `n + 1` terms.
* `TauCeti.ordinaryHypergeometricCoefficient_eq_div`: the coefficient as `(a)ₙ (b)ₙ / ((c)ₙ n!)`.
* `TauCeti.ordinaryHypergeometricCoefficient_add_one`: the coefficient recurrence.
* `TauCeti.iteratedDeriv_ordinaryHypergeometric_zero`: the iterated derivatives at `0`; in
  particular `TauCeti.deriv_ordinaryHypergeometric_zero` gives `(₂F₁ a b c)' 0 = a b / c`.
* `TauCeti.ordinaryHypergeometric_gaussEquation`: Gauss's hypergeometric equation inside the disc
  of convergence, with the special cases
  `TauCeti.ordinaryHypergeometric_gaussEquation_of_norm_lt_one` (the open unit disc) and
  `TauCeti.ordinaryHypergeometric_gaussEquation_of_neg_nat` (terminating series, everywhere).
* `TauCeti.mk_ordinaryHypergeometricCoefficient_gaussEquation`: Gauss's hypergeometric equation
  for the series as a formal power series, over any field of characteristic zero.

## References

* NIST Digital Library of Mathematical Functions, §15.2 and equation 15.10.1.
-/

public section

namespace TauCeti

/-- The ordinary hypergeometric function is the sum of the scalar power series with the
hypergeometric coefficients. -/
theorem ordinaryHypergeometric_eq_ofScalarsSum {𝕂 𝔸 : Type*} [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸]
    [TopologicalSpace 𝔸] [IsTopologicalRing 𝔸] (a b c : 𝕂) :
    (₂F₁ a b c : 𝔸 → 𝔸) =
      FormalMultilinearSeries.ofScalarsSum (ordinaryHypergeometricCoefficient a b c) :=
  rfl

/-- The coefficient `cₙ` of `₂F₁(a, b; c; ·)` written as the quotient
`(a)ₙ (b)ₙ / ((c)ₙ n!)`, the form in which DLMF 15.2.1 prints the terms of the series. -/
theorem ordinaryHypergeometricCoefficient_eq_div {K : Type*} [Field K] (a b c : K) (n : ℕ) :
    ordinaryHypergeometricCoefficient a b c n =
      (ascPochhammer K n).eval a * (ascPochhammer K n).eval b /
        ((ascPochhammer K n).eval c * n.factorial) := by
  simp only [ordinaryHypergeometricCoefficient, div_eq_mul_inv, mul_inv]
  ring

/-- **The hypergeometric coefficient recurrence.** The coefficients `cₙ = (a)ₙ (b)ₙ / ((c)ₙ n!)`
of `₂F₁(a, b; c; ·)` satisfy `cₙ₊₁ = (a + n) (b + n) / ((n + 1) (c + n)) cₙ`. With the convention
`x / 0 = 0` this holds for all parameters; when `c + n = 0` both sides vanish. -/
theorem ordinaryHypergeometricCoefficient_add_one {K : Type*} [Field K] (a b c : K) (n : ℕ) :
    ordinaryHypergeometricCoefficient a b c (n + 1) =
      (a + n) * (b + n) / ((n + 1) * (c + n)) * ordinaryHypergeometricCoefficient a b c n := by
  simp only [ordinaryHypergeometricCoefficient, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, ascPochhammer_succ_eval, div_eq_mul_inv, mul_inv]
  ring

/-- With lower parameter `1`, the hypergeometric coefficient `(a)ₙ (b)ₙ / ((1)ₙ n!)` is the product
of the generalized multichoose numbers `(a)ₙ / n!` and `(b)ₙ / n!`. -/
theorem ordinaryHypergeometricCoefficient_one_eq_multichoose_mul {K : Type*} [Field K] [CharZero K]
    (a b : K) (n : ℕ) :
    ordinaryHypergeometricCoefficient a b 1 n = Ring.multichoose a n * Ring.multichoose b n := by
  rw [ordinaryHypergeometricCoefficient, Ring.multichoose_eq_inv_factorial_mul_eval_ascPochhammer,
    Ring.multichoose_eq_inv_factorial_mul_eval_ascPochhammer, ascPochhammer_eval_one]
  ring

variable {𝕂 : Type*} (𝔸 : Type*) [RCLike 𝕂] [NormedDivisionRing 𝔸] [NormedAlgebra 𝕂 𝔸]

/-- The radius of convergence of the hypergeometric series `₂F₁(a, b; c; ·)` is at least `1`, for
all parameters. -/
theorem one_le_radius_ordinaryHypergeometricSeries (a b c : 𝕂) :
    1 ≤ (ordinaryHypergeometricSeries 𝔸 a b c).radius := by
  by_cases h : ∀ k : ℕ, (k : 𝕂) ≠ -a ∧ (k : 𝕂) ≠ -b ∧ (k : 𝕂) ≠ -c
  · exact (ordinaryHypergeometricSeries_radius_eq_one 𝔸 a b c h).ge
  · push Not at h
    obtain ⟨k, hk⟩ := h
    by_cases ha : (k : 𝕂) = -a
    · have ha' : a = -(k : 𝕂) := by rw [ha, neg_neg]
      rw [ha', ordinaryHypergeometric_radius_top_of_neg_nat₁]
      exact le_top
    by_cases hb : (k : 𝕂) = -b
    · have hb' : b = -(k : 𝕂) := by rw [hb, neg_neg]
      rw [hb', ordinaryHypergeometric_radius_top_of_neg_nat₂]
      exact le_top
    · have hc : c = -(k : 𝕂) := by rw [hk ha hb, neg_neg]
      rw [hc, ordinaryHypergeometric_radius_top_of_neg_nat₃]
      exact le_top

/-- The ordinary hypergeometric function `₂F₁(a, b; c; ·)` is analytic on the open unit ball, for
all parameters. -/
theorem analyticOnNhd_ordinaryHypergeometric [CompleteSpace 𝔸] (a b c : 𝕂) :
    AnalyticOnNhd 𝕂 (₂F₁ a b c : 𝔸 → 𝔸) (Metric.ball 0 1) := by
  intro x hx
  have h1 := one_le_radius_ordinaryHypergeometricSeries 𝔸 a b c
  exact ((ordinaryHypergeometricSeries 𝔸 a b c).hasFPowerSeriesOnBall
    (zero_lt_one.trans_le h1)).analyticAt_of_mem
      (Metric.eball_subset_eball h1 (by
        simpa only [Metric.mem_eball, edist_dist, ENNReal.ofReal_lt_one, Metric.mem_ball] using hx))

variable {𝔸} in
/-- The open unit ball lies inside the ball of convergence of the hypergeometric series, for all
parameters. -/
theorem mem_eball_ordinaryHypergeometricSeries_radius (a b c : 𝕂) {x : 𝔸} (hx : ‖x‖ < 1) :
    x ∈ Metric.eball (0 : 𝔸) (ordinaryHypergeometricSeries 𝔸 a b c).radius :=
  Metric.eball_subset_eball (one_le_radius_ordinaryHypergeometricSeries 𝔸 a b c) (by
    simpa only [Metric.mem_eball, edist_zero_right, ← ofReal_norm, ENNReal.ofReal_lt_one]
      using hx)

variable {𝔸} in
/-- Inside the open unit ball, `₂F₁(a, b; c; x)` is the sum of its hypergeometric series
`∑ (a)ₙ (b)ₙ / ((c)ₙ n!) xⁿ`, for all parameters. -/
theorem hasSum_ordinaryHypergeometric [CompleteSpace 𝔸] (a b c : 𝕂) {x : 𝔸} (hx : ‖x‖ < 1) :
    HasSum (fun n ↦ ordinaryHypergeometricCoefficient a b c n • x ^ n) (₂F₁ a b c x) := by
  have h := (ordinaryHypergeometricSeries 𝔸 a b c).hasSum
    (mem_eball_ordinaryHypergeometricSeries_radius a b c hx)
  rw [ordinaryHypergeometricSeries_apply_eq'] at h
  exact h

variable {𝔸} in
/-- Inside the open unit ball, the hypergeometric series `∑ (a)ₙ (b)ₙ / ((c)ₙ n!) xⁿ` converges
absolutely, for all parameters. -/
theorem summable_norm_ordinaryHypergeometricCoefficient_smul_pow (a b c : 𝕂) {x : 𝔸}
    (hx : ‖x‖ < 1) :
    Summable fun n ↦ ‖ordinaryHypergeometricCoefficient a b c n • x ^ n‖ := by
  simpa only [ordinaryHypergeometricSeries_apply_eq] using
    (ordinaryHypergeometricSeries 𝔸 a b c).summable_norm_apply
      (mem_eball_ordinaryHypergeometricSeries_radius a b c hx)

variable {𝔸} in
/-- Inside the open unit ball, the series `∑ (a)ₙ (b)ₙ / (n!)² xⁿ` of products of generalized
multichoose numbers sums to `₂F₁(a, b; 1; x)`. For `a = b` this is the series of squared
coefficients of `(1 - x)⁻ᵃ`. -/
theorem hasSum_multichoose_mul_multichoose_mul_pow [CompleteSpace 𝔸] (a b : 𝕂) {x : 𝔸}
    (hx : ‖x‖ < 1) :
    HasSum (fun n ↦ (Ring.multichoose a n * Ring.multichoose b n) • x ^ n) (₂F₁ a b 1 x) := by
  simpa only [ordinaryHypergeometricCoefficient_one_eq_multichoose_mul] using
    hasSum_ordinaryHypergeometric a b 1 hx

/-- Inside the open unit disc, the series `∑ c_a(n)² xⁿ` of squared coefficients
`c_a(n) = (a)ₙ / n!` of `(1 - x)⁻ᵃ` sums to `₂F₁(a, a; 1; x)`. -/
theorem hasSum_multichoose_sq_mul_pow (a : 𝕂) {x : 𝕂} (hx : ‖x‖ < 1) :
    HasSum (fun n ↦ Ring.multichoose a n ^ 2 * x ^ n) (₂F₁ a a 1 x) := by
  simpa only [sq, smul_eq_mul] using hasSum_multichoose_mul_multichoose_mul_pow (𝔸 := 𝕂) a a hx

/-- Inside the open unit disc, `₂F₁(a, a; 1; x)` is `1 + a² x` plus the tail
`∑ c_a(n + 2)² x^(n + 2)` of its series, where `c_a(n) = (a)ₙ / n!`. -/
theorem ordinaryHypergeometric_eq_one_add_sq_mul_add_tsum (a : 𝕂) {x : 𝕂} (hx : ‖x‖ < 1) :
    ₂F₁ a a 1 x = 1 + a ^ 2 * x + ∑' n : ℕ, Ring.multichoose a (n + 2) ^ 2 * x ^ (n + 2) := by
  have h := hasSum_multichoose_sq_mul_pow a hx
  rw [← h.tsum_eq, ← h.summable.sum_add_tsum_nat_add 2]
  simp [Finset.sum_range_succ]

/-- For `0 ≤ x < 1`, `₂F₁(a, a; 1; x)` is at least `1 + a² x`. -/
theorem one_add_sq_mul_le_ordinaryHypergeometric (a : ℝ) {x : ℝ} (hx₀ : 0 ≤ x) (hx₁ : x < 1) :
    1 + a ^ 2 * x ≤ ₂F₁ a a 1 x := by
  rw [ordinaryHypergeometric_eq_one_add_sq_mul_add_tsum a
    (by rw [Real.norm_eq_abs, abs_of_nonneg hx₀]; exact hx₁)]
  exact le_add_of_nonneg_right (tsum_nonneg fun n ↦ by positivity)

/-- On `[0, r]` with `0 < r < 1`, `₂F₁(a, a; 1; x)` is `1 + a² x + O(x²)`: it is at most
`1 + a² x + C x²` for some constant `C ≥ 0`. -/
theorem exists_ordinaryHypergeometric_le (a : ℝ) {r : ℝ} (hr₀ : 0 < r) (hr₁ : r < 1) :
    ∃ C, 0 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → x ≤ r → ₂F₁ a a 1 x ≤ 1 + a ^ 2 * x + C * x ^ 2 := by
  -- The tail at `x` is dominated termwise by `x²` times the shifted series at `r`.
  set g : ℕ → ℝ := fun n ↦ Ring.multichoose a (n + 2) ^ 2 * r ^ n
  have hg : Summable g := by
    have h := (summable_nat_add_iff 2).2 (hasSum_multichoose_sq_mul_pow a
      (by rwa [Real.norm_eq_abs, abs_of_pos hr₀])).summable
    convert h.mul_left (r ^ 2)⁻¹ using 2 with n
    simp only [g, pow_add]
    field_simp
  refine ⟨∑' n, g n, tsum_nonneg fun n ↦ by positivity, fun x hx₀ hxr ↦ ?_⟩
  rw [ordinaryHypergeometric_eq_one_add_sq_mul_add_tsum a
    (by rw [Real.norm_eq_abs, abs_of_nonneg hx₀]; linarith), mul_comm (∑' n, g n),
    ← tsum_mul_left]
  have hterm (n : ℕ) : Ring.multichoose a (n + 2) ^ 2 * x ^ (n + 2) ≤ x ^ 2 * g n := by
    have hxn : x ^ n ≤ r ^ n := pow_le_pow_left₀ hx₀ hxr n
    calc Ring.multichoose a (n + 2) ^ 2 * x ^ (n + 2)
        = x ^ 2 * (Ring.multichoose a (n + 2) ^ 2 * x ^ n) := by ring
      _ ≤ x ^ 2 * g n :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hxn (by positivity)) (by positivity)
  have hsum : Summable fun n ↦ Ring.multichoose a (n + 2) ^ 2 * x ^ (n + 2) :=
    (hg.mul_left (x ^ 2)).of_nonneg_of_le (fun n ↦ by positivity) hterm
  exact (add_le_add_iff_left _).2 (hsum.tsum_le_tsum hterm (hg.mul_left _))

section Terminating

open scoped Nat

variable {𝕂 𝔸 : Type*} [Field 𝕂] [Ring 𝔸] [Algebra 𝕂 𝔸] [TopologicalSpace 𝔸]
  [IsTopologicalRing 𝔸]

/-- A terminating `₂F₁(−n, b; c; z)` is the sum of its first `n + 1` terms, for all `b`, `c`. -/
theorem ordinaryHypergeometric_neg_nat_eq_sum (n : ℕ) (b c : 𝕂) (z : 𝔸) :
    ordinaryHypergeometric (-n : 𝕂) b c z =
      ∑ k ∈ Finset.range (n + 1), ((k ! : 𝕂)⁻¹ * (ascPochhammer 𝕂 k).eval (-n : 𝕂) *
        (ascPochhammer 𝕂 k).eval b * ((ascPochhammer 𝕂 k).eval c)⁻¹) • z ^ k := by
  rw [ordinaryHypergeometric_eq_tsum]
  refine tsum_eq_sum fun k hk => ?_
  rw [ascPochhammer_eval_neg_natCast_of_lt (by simpa using hk)]
  simp

end Terminating

section Scalar

variable {𝕂 : Type*} [RCLike 𝕂]

/-- The iterated derivatives of `₂F₁(a, b; c; ·)` at `0` are `(a)ₙ (b)ₙ / (c)ₙ`, for all
parameters. -/
@[simp]
theorem iteratedDeriv_ordinaryHypergeometric_zero (a b c : 𝕂) (n : ℕ) :
    iteratedDeriv n (₂F₁ a b c : 𝕂 → 𝕂) 0 =
      (ascPochhammer 𝕂 n).eval a * (ascPochhammer 𝕂 n).eval b / (ascPochhammer 𝕂 n).eval c := by
  have hr := zero_lt_one.trans_le (one_le_radius_ordinaryHypergeometricSeries 𝕂 a b c)
  rw [ordinaryHypergeometric_eq_ofScalarsSum,
    FormalMultilinearSeries.iteratedDeriv_ofScalarsSum_zero _ hr, ordinaryHypergeometricCoefficient]
  simp only [mul_assoc]
  rw [mul_inv_cancel_left₀ (Nat.cast_ne_zero.mpr n.factorial_ne_zero), div_eq_mul_inv, mul_assoc]

/-- The derivative of `₂F₁(a, b; c; ·)` at `0` is `a b / c`, for all parameters. -/
@[simp]
theorem deriv_ordinaryHypergeometric_zero (a b c : 𝕂) :
    deriv (₂F₁ a b c : 𝕂 → 𝕂) 0 = a * b / c := by
  rw [← iteratedDeriv_one, iteratedDeriv_ordinaryHypergeometric_zero]
  simp

end Scalar

section GaussEquation

variable {𝕂 : Type*} [NontriviallyNormedField 𝕂] [CompleteSpace 𝕂] [CharZero 𝕂]

/-- **Gauss's hypergeometric differential equation.** If the lower parameter `c` is not a
nonpositive integer, then `y = ₂F₁(a, b; c; ·)` satisfies
`x (1 - x) y'' + (c - (a + b + 1) x) y' - a b y = 0` at every `x` inside the disc of convergence of
its series. -/
theorem ordinaryHypergeometric_gaussEquation (a b c : 𝕂) (hc : ∀ k : ℕ, (k : 𝕂) ≠ -c) {x : 𝕂}
    (hx : ‖x‖ₑ < (ordinaryHypergeometricSeries 𝕂 a b c).radius) :
    x * (1 - x) * deriv (deriv (₂F₁ a b c)) x + (c - (a + b + 1) * x) * deriv (₂F₁ a b c) x -
      a * b * ₂F₁ a b c x = 0 := by
  set C := ordinaryHypergeometricCoefficient a b c with hC
  set f : 𝕂 → 𝕂 := ₂F₁ a b c
  -- by definition, `₂F₁ a b c` is the sum of `ordinaryHypergeometricSeries 𝕂 a b c`, which is the
  -- scalar series `ofScalars 𝕂 C`
  have hf : HasFPowerSeriesOnBall f (FormalMultilinearSeries.ofScalars 𝕂 C) 0
      (ordinaryHypergeometricSeries 𝕂 a b c).radius :=
    (ordinaryHypergeometricSeries 𝕂 a b c).hasFPowerSeriesOnBall (pos_of_gt hx)
  have hf' := hf.deriv_ofScalars
  have hxb : x ∈ Metric.eball (0 : 𝕂) (ordinaryHypergeometricSeries 𝕂 a b c).radius :=
    mem_eball_zero_iff.mpr hx
  -- the series of `f`, `f'`, `x f'`, `x f''` and `x² f''` at `x`, all indexed by powers `x ^ n`
  have h0 : HasSum (fun n : ℕ ↦ C n * x ^ n) (f x) := by
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hf.hasSum hxb
  have h1 : HasSum (fun n : ℕ ↦ (n + 1) * C (n + 1) * x ^ n) (deriv f x) := by
    simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hf'.hasSum hxb
  have h2 := hf.hasSum_mul_deriv_ofScalars hx
  have h3 := hf'.hasSum_mul_deriv_ofScalars hx
  have h4 : HasSum (fun n : ℕ ↦ ((n : 𝕂) - 1) * n * C n * x ^ n) (x * (x * deriv (deriv f) x)) := by
    simpa [sq, mul_assoc, mul_comm, mul_left_comm] using hf.hasSum_sq_mul_deriv_deriv_ofScalars hx
  have hsum := (h3.add (h1.mul_left c)).sub ((h4.add (h2.mul_left (a + b + 1))).add
    (h0.mul_left (a * b)))
  -- by the coefficient recurrence, every term of the combined series vanishes
  have hzero : (fun n : ℕ ↦ n * ((n + 1) * C (n + 1)) * x ^ n + c * ((n + 1) * C (n + 1) * x ^ n) -
      (((n : 𝕂) - 1) * n * C n * x ^ n + (a + b + 1) * (n * C n * x ^ n) + a * b * (C n * x ^ n))) =
      0 := by
    funext n
    have hcn : c + n ≠ 0 := fun h ↦ hc n (eq_neg_of_add_eq_zero_right h)
    have hrec : (n + 1) * (c + n) * C (n + 1) = (a + n) * (b + n) * C n := by
      rw [hC, ordinaryHypergeometricCoefficient_add_one a b c n]
      field_simp
    rw [Pi.zero_apply]
    linear_combination x ^ n * hrec
  rw [hzero] at hsum
  linear_combination hsum.unique hasSum_zero

end GaussEquation

section Scalar

variable {𝕂 : Type*} [RCLike 𝕂]

/-- **Gauss's hypergeometric differential equation** on the open unit disc. -/
theorem ordinaryHypergeometric_gaussEquation_of_norm_lt_one (a b c : 𝕂)
    (hc : ∀ k : ℕ, (k : 𝕂) ≠ -c) {x : 𝕂} (hx : ‖x‖ < 1) :
    x * (1 - x) * deriv (deriv (₂F₁ a b c)) x + (c - (a + b + 1) * x) * deriv (₂F₁ a b c) x -
      a * b * ₂F₁ a b c x = 0 :=
  ordinaryHypergeometric_gaussEquation a b c hc <|
    (by rw [← ofReal_norm]; exact ENNReal.ofReal_lt_one.mpr hx : ‖x‖ₑ < 1).trans_le
      (one_le_radius_ordinaryHypergeometricSeries 𝕂 a b c)

/-- **Gauss's hypergeometric differential equation for a terminating series.** If `a` or `b` is a
nonpositive integer, `₂F₁(a, b; c; ·)` is a polynomial, and it satisfies Gauss's equation at every
point, provided `c` is not a nonpositive integer. -/
theorem ordinaryHypergeometric_gaussEquation_of_neg_nat (a b c : 𝕂) {k : ℕ}
    (hab : (k : 𝕂) = -a ∨ (k : 𝕂) = -b) (hc : ∀ k : ℕ, (k : 𝕂) ≠ -c) (x : 𝕂) :
    x * (1 - x) * deriv (deriv (₂F₁ a b c)) x + (c - (a + b + 1) * x) * deriv (₂F₁ a b c) x -
      a * b * ₂F₁ a b c x = 0 := by
  refine ordinaryHypergeometric_gaussEquation a b c hc ?_
  rcases hab with ha | hb
  · rw [← neg_neg a, ← ha, ordinaryHypergeometric_radius_top_of_neg_nat₁]
    exact eNorm_lt_top
  · rw [← neg_neg b, ← hb, ordinaryHypergeometric_radius_top_of_neg_nat₂]
    exact eNorm_lt_top

end Scalar

section FormalGaussEquation

open PowerSeries

variable {K : Type*} [Field K] [CharZero K]

/-- The Gauss series `∑ (a)ₙ (b)ₙ / ((c)ₙ n!) Xⁿ` satisfies the hypergeometric equation
`X (1 - X) F'' + (c - (a + b + 1) X) F' = a b F` (DLMF 15.10.1) as a formal power series, when `c`
is not a nonpositive integer. -/
theorem mk_ordinaryHypergeometricCoefficient_gaussEquation (a b c : K)
    (hc : ∀ k : ℕ, (k : K) ≠ -c) :
    X * (1 - X) * d⁄dX (d⁄dX (mk (ordinaryHypergeometricCoefficient a b c))) +
        (C c - C (a + b + 1) * X) * d⁄dX (mk (ordinaryHypergeometricCoefficient a b c)) =
      C (a * b) * mk (ordinaryHypergeometricCoefficient a b c) := by
  set F := mk (ordinaryHypergeometricCoefficient a b c)
  -- The equation multiplied by `X`, written with the Euler operator `X * d⁄dX`, is the
  -- coefficient recurrence `(n + 1) (c + n) fₙ₊₁ = (a + n) (b + n) fₙ`.
  have hθ : X * d⁄dX (X * d⁄dX F) + (c - 1) • (X * d⁄dX F) =
      X * (X * d⁄dX (X * d⁄dX F) + (a + b) • (X * d⁄dX F) + (a * b) • F) := by
    ext n
    cases n with
    | zero => simp
    | succ m =>
      have hm₁ : (m : K) + 1 ≠ 0 := Nat.cast_add_one_ne_zero m
      have hm₂ : c + (m : K) ≠ 0 := fun h ↦ hc m (by linear_combination h)
      simp only [map_add, coeff_smul, smul_eq_mul, coeff_X_mul_derivative]
      rw [coeff_succ_X_mul]
      simp only [map_add, coeff_smul, smul_eq_mul, coeff_X_mul_derivative, F, coeff_mk]
      rw [ordinaryHypergeometricCoefficient_add_one]
      generalize ordinaryHypergeometricCoefficient a b c m = t
      have hr : ((m : K) + 1) * (c + m) * ((a + m) * (b + m) / ((m + 1) * (c + m))) =
          (a + m) * (b + m) := mul_div_cancel₀ _ (mul_ne_zero hm₁ hm₂)
      push_cast
      linear_combination t * hr
  refine mul_left_cancel₀ (X_ne_zero (R := K)) ?_
  simp only [smul_eq_C_mul, Derivation.leibniz, derivative_X, smul_eq_mul, map_add, map_sub,
    map_mul, map_one] at hθ ⊢
  linear_combination hθ

end FormalGaussEquation

end TauCeti
