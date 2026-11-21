/-
Copyright (c) 2026 Tau Ceti. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tau Ceti
-/
module

public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.SpecialFunctions.OrdinaryHypergeometric
public import TauCeti.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Analytic.ChangeOrigin
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Complex.LocallyUniformLimit
import Mathlib.Topology.Algebra.InfiniteSum.TsumUniformlyOn

/-!
# The ordinary hypergeometric function on the unit ball

Mathlib computes the radius of convergence of the series of `₂F₁(a, b; c; ·)`: it is `1`, unless
one of the parameters is a nonpositive integer, in which case the series is finite or its
coefficients take the junk value `0`, and the radius is `⊤`. This file records the uniform
consequence that the radius is always at least `1`, so `₂F₁(a, b; c; ·)` is analytic on the open
unit ball for all parameters. It also proves complex analyticity in all four arguments
`(a, b, c, z)` simultaneously along analytic curves away from the poles `c ∈ -ℕ` and inside the
open unit disc `‖z‖ < 1`.

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
* `TauCeti.ofReal_ordinaryHypergeometric`: coercing `₂F₁ a b c z` from `ℝ` to `ℂ` yields
  `₂F₁ (a : ℂ) (b : ℂ) (c : ℂ) (z : ℂ)`.
* `AnalyticAt.ordinaryHypergeometric`: composition of `₂F₁` with four complex-analytic maps is
  analytic wherever `c ∉ -ℕ` and `‖z‖ < 1`.
* `TauCeti.ordinaryHypergeometric_neg_nat_eq_sum`: a terminating `₂F₁(−n, b; c; z)` is the sum of
  its first `n + 1` terms.
* `TauCeti.ordinaryHypergeometricCoefficient_add_one`: the coefficient recurrence.
* `TauCeti.iteratedDeriv_ordinaryHypergeometric_zero`: the iterated derivatives at `0`; in
  particular `TauCeti.deriv_ordinaryHypergeometric_zero` gives `(₂F₁ a b c)' 0 = a b / c`.
* `TauCeti.ordinaryHypergeometric_gaussEquation`: Gauss's hypergeometric equation inside the disc
  of convergence, with the special cases
  `TauCeti.ordinaryHypergeometric_gaussEquation_of_norm_lt_one` (the open unit disc) and
  `TauCeti.ordinaryHypergeometric_gaussEquation_of_neg_nat` (terminating series, everywhere).

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

/-- **The hypergeometric coefficient recurrence.** The coefficients `cₙ = (a)ₙ (b)ₙ / ((c)ₙ n!)`
of `₂F₁(a, b; c; ·)` satisfy `cₙ₊₁ = (a + n) (b + n) / ((n + 1) (c + n)) cₙ`. With the convention
`x / 0 = 0` this holds for all parameters; when `c + n = 0` both sides vanish. -/
theorem ordinaryHypergeometricCoefficient_add_one {K : Type*} [Field K] (a b c : K) (n : ℕ) :
    ordinaryHypergeometricCoefficient a b c (n + 1) =
      (a + n) * (b + n) / ((n + 1) * (c + n)) * ordinaryHypergeometricCoefficient a b c n := by
  simp only [ordinaryHypergeometricCoefficient, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add,
    Nat.cast_one, ascPochhammer_succ_eval, div_eq_mul_inv, mul_inv]
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

/-- Coercing the real hypergeometric function `₂F₁ a b c z` to `ℂ` agrees with complex `₂F₁`. -/
theorem ofReal_ordinaryHypergeometric (a b c z : ℝ) :
    ((₂F₁ a b c z : ℝ) : ℂ) = ₂F₁ (a : ℂ) (b : ℂ) (c : ℂ) (z : ℂ) := by
  simp only [ordinaryHypergeometric, ordinaryHypergeometric_sum_eq, smul_eq_mul,
    Complex.ofReal_tsum]
  refine tsum_congr fun n ↦ ?_
  have hp (x : ℝ) : (((ascPochhammer ℝ n).eval x : ℝ) : ℂ) = (ascPochhammer ℂ n).eval (x : ℂ) := by
    have h := Polynomial.eval_map_apply (p := ascPochhammer ℝ n) (f := Complex.ofRealHom) x
    rw [ascPochhammer_map] at h
    exact h.symm
  simp only [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_pow, Complex.ofReal_natCast, hp]

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
    refine (hasSum_nat_add_iff' 1).mp ?_
    simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using h3.mul_left x
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

end TauCeti

section ComplexAnalytic

open Complex Filter Metric Set
open scoped Nat Topology

private noncomputable def hyperTerm (a b c z : ℂ) (n : ℕ) : ℂ :=
  ((n !⁻¹ : ℂ) * (ascPochhammer ℂ n).eval a * (ascPochhammer ℂ n).eval b *
    ((ascPochhammer ℂ n).eval c)⁻¹) * z ^ n

private theorem hyperTerm_succ (a b c z : ℂ) (k : ℕ) :
    hyperTerm a b c z (k + 1) =
      hyperTerm a b c z k * (((a + k) / (k + 1)) * ((b + k) / (c + k)) * z) := by
  simp only [hyperTerm, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
    ascPochhammer_succ_eval, mul_inv, pow_succ, div_eq_mul_inv]
  ring

private theorem norm_hyperTerm_ratio_le {a b c z : ℂ} {R ρ : ℝ} {k : ℕ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hz : ‖z‖ ≤ ρ)
    (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) (hc : ‖c‖ ≤ R) (hR : 1 ≤ R)
    (hk : 16 * R / (1 - ρ) ≤ k) :
    c + k ≠ 0 ∧ ‖((a + k) / (k + 1)) * ((b + k) / (c + k)) * z‖ ≤ (1 + ρ) / 2 := by
  set d := 1 - ρ
  have hdk : 16 * R ≤ k * d := (div_le_iff₀ (sub_pos.mpr hρ1)).mp hk
  have hkR : 16 * R ≤ k := hdk.trans (mul_le_of_le_one_right k.cast_nonneg (sub_le_self 1 hρ0))
  have hcre : -R ≤ c.re := (neg_le_neg hc).trans (abs_le.mp (abs_re_le_norm c)).1
  have hck_re : (k : ℝ) - R ≤ ‖c + k‖ := by
    have h := Complex.re_le_norm (c + k); simp only [add_re, natCast_re] at h; linarith
  have hck_pos : 0 < ‖c + k‖ := by linarith
  have hadd {u : ℂ} (hu : ‖u‖ ≤ R) : ‖u + k‖ ≤ R + k :=
    (norm_add_le u k).trans (by simpa [Complex.norm_natCast] using add_le_add_right hu (k : ℝ))
  have hf1 : ‖(a + k) / ((k : ℂ) + 1)‖ ≤ 1 + d / 4 := by
    have hc1 : ((k : ℂ) + 1) = ((k + 1 : ℕ) : ℂ) := by push_cast; rfl
    rw [norm_div, hc1, Complex.norm_natCast, Nat.cast_add, Nat.cast_one,
      div_le_iff₀ (by positivity)]
    nlinarith [hadd ha]
  have hf2 : ‖(b + k) / (c + k)‖ ≤ 1 + d / 4 := by
    rw [norm_div, div_le_iff₀ hck_pos]; nlinarith [hadd hb]
  have hprod : (1 + d / 4) * (1 + d / 4) * ρ ≤ (1 + ρ) / 2 := by
    have : 0 ≤ d ^ 2 * (7 + d) / 16 := by positivity
    nlinarith [sq d]
  refine ⟨norm_pos_iff.mp hck_pos, ?_⟩
  rw [norm_mul, norm_mul]
  exact (mul_le_mul (mul_le_mul hf1 hf2 (norm_nonneg _) (by positivity)) hz (norm_nonneg z)
    (by positivity)).trans hprod

private theorem norm_hyperTerm_add_le {a b c z : ℂ} {R ρ : ℝ} {M : ℕ}
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hz : ‖z‖ ≤ ρ)
    (ha : ‖a‖ ≤ R) (hb : ‖b‖ ≤ R) (hc : ‖c‖ ≤ R) (hR : 1 ≤ R)
    (hM : 16 * R / (1 - ρ) ≤ M) (m : ℕ) :
    ‖hyperTerm a b c z (M + m)‖ ≤ ‖hyperTerm a b c z M‖ * ((1 + ρ) / 2) ^ m := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.add_succ, hyperTerm_succ, norm_mul, pow_succ]
    have hrat := (norm_hyperTerm_ratio_le hρ0 hρ1 hz ha hb hc hR
      (hM.trans (Nat.cast_le.mpr (Nat.le_add_right M m)))).2
    exact (mul_le_mul ih hrat (norm_nonneg _) (by positivity)).trans_eq (by ring)

private theorem exists_closedBall_hyperTerm {f g h w : ℂ → ℂ} {t₀ : ℂ} {R ρ : ℝ} {M : ℕ}
    (hf : AnalyticAt ℂ f t₀) (hg : AnalyticAt ℂ g t₀) (hh : AnalyticAt ℂ h t₀)
    (hw : AnalyticAt ℂ w t₀) (hh₀ : ∀ n : ℕ, h t₀ ≠ -(n : ℂ)) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hwρ : ‖w t₀‖ < ρ) (hfR : ‖f t₀‖ < R) (hgR : ‖g t₀‖ < R) (hhR : ‖h t₀‖ < R) (hR : 1 ≤ R)
    (hM : 16 * R / (1 - ρ) ≤ M) :
    ∃ r > 0, (∀ t ∈ closedBall t₀ r, ‖f t‖ ≤ R ∧ ‖g t‖ ≤ R ∧ ‖h t‖ ≤ R ∧ ‖w t‖ ≤ ρ) ∧
      ∀ n : ℕ, DifferentiableOn ℂ (fun t ↦ hyperTerm (f t) (g t) (h t) (w t) n)
        (closedBall t₀ r) := by
  have hP0 : (ascPochhammer ℂ M).eval (h t₀) ≠ 0 := fun h0 ↦ by
    obtain ⟨k, _, hk⟩ := (ascPochhammer_eval_eq_zero_iff M (h t₀)).mp h0
    exact hh₀ k (neg_eq_iff_eq_neg.mp hk.symm)
  have hev : ∀ᶠ t in 𝓝 t₀,
      (DifferentiableAt ℂ f t ∧ DifferentiableAt ℂ g t ∧ DifferentiableAt ℂ h t ∧
        DifferentiableAt ℂ w t) ∧ (‖f t‖ < R ∧ ‖g t‖ < R ∧ ‖h t‖ < R ∧ ‖w t‖ < ρ) ∧
        (ascPochhammer ℂ M).eval (h t) ≠ 0 := by
    have hnorm {u : ℂ → ℂ} {B : ℝ} (hu : AnalyticAt ℂ u t₀) (hB : ‖u t₀‖ < B) :=
      (continuous_norm.continuousAt.comp hu.continuousAt).eventually (Iio_mem_nhds hB)
    filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt, hh.eventually_analyticAt,
      hw.eventually_analyticAt, hnorm hf hfR, hnorm hg hgR, hnorm hh hhR, hnorm hw hwρ,
      ((Polynomial.differentiable (ascPochhammer ℂ M)).continuous.continuousAt.comp
        hh.continuousAt).eventually_ne hP0] with t df dg dh dw bf bg bh bw hne
    exact ⟨⟨df.differentiableAt, dg.differentiableAt, dh.differentiableAt, dw.differentiableAt⟩,
      ⟨bf, bg, bh, bw⟩, hne⟩
  obtain ⟨r₀, hr₀, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hmem {t : ℂ} (ht : t ∈ closedBall t₀ (r₀ / 2)) :=
    hball t (mem_ball_iff_norm.mpr ((mem_closedBall_iff_norm.mp ht).trans_lt (half_lt_self hr₀)))
  refine ⟨r₀ / 2, half_pos hr₀, fun t ht ↦ ?_, fun n t ht ↦ ?_⟩
  · obtain ⟨_, ⟨bf, bg, bh, bw⟩, _⟩ := hmem ht
    exact ⟨bf.le, bg.le, bh.le, bw.le⟩
  · obtain ⟨⟨df, dg, dh, dw⟩, ⟨bf, bg, bh, bw⟩, hPM⟩ := hmem ht
    have hne : (ascPochhammer ℂ n).eval (h t) ≠ 0 := fun h0 ↦ by
      obtain ⟨k, _, hk⟩ := (ascPochhammer_eval_eq_zero_iff n (h t)).mp h0
      rcases lt_or_ge k M with hkM | hkM
      · exact hPM ((ascPochhammer_eval_eq_zero_iff M (h t)).mpr ⟨k, hkM, hk⟩)
      · exact (norm_hyperTerm_ratio_le hρ0 hρ1 bw.le bf.le bg.le bh.le hR
          (hM.trans (Nat.cast_le.mpr hkM))).1 (by linear_combination hk)
    exact (((((differentiableAt_const _).mul
      ((Polynomial.differentiableAt (ascPochhammer ℂ n)).comp t df)).mul
      ((Polynomial.differentiableAt (ascPochhammer ℂ n)).comp t dg)).mul
      (((Polynomial.differentiableAt (ascPochhammer ℂ n)).comp t dh).inv hne)).mul
      (dw.pow n)).differentiableWithinAt

namespace AnalyticAt

/-- Composition of the ordinary hypergeometric function `₂F₁` with four complex-analytic functions
is complex analytic wherever the denominator parameter avoids the nonpositive integers and the
argument lies in the open unit disc. -/
theorem ordinaryHypergeometric {f g h w : ℂ → ℂ} {t₀ : ℂ}
    (hf : AnalyticAt ℂ f t₀) (hg : AnalyticAt ℂ g t₀)
    (hh : AnalyticAt ℂ h t₀) (hw : AnalyticAt ℂ w t₀)
    (hh₀ : ∀ n : ℕ, h t₀ ≠ -(n : ℂ)) (hw₀ : ‖w t₀‖ < 1) :
    AnalyticAt ℂ (fun t : ℂ ↦ ₂F₁ (f t) (g t) (h t) (w t)) t₀ := by
  let ρ : ℝ := (‖w t₀‖ + 1) / 2
  let R : ℝ := max (max ‖f t₀‖ ‖g t₀‖) ‖h t₀‖ + 1
  let M : ℕ := ⌈16 * R / (1 - ρ)⌉₊ + 1
  have hρ0 : 0 ≤ ρ := by dsimp [ρ]; positivity
  have hρ1 : ρ < 1 := by dsimp [ρ]; linarith
  have hR : 1 ≤ R := by
    dsimp [R]; linarith [norm_nonneg (h t₀), le_max_right (max ‖f t₀‖ ‖g t₀‖) ‖h t₀‖]
  have hM : 16 * R / (1 - ρ) ≤ M := by
    dsimp [M]; push_cast; linarith [Nat.le_ceil (16 * R / (1 - ρ))]
  obtain ⟨r, hr, hcb_bd, hterm_diff⟩ := exists_closedBall_hyperTerm hf hg hh hw hh₀ hρ0 hρ1
    (by dsimp [ρ]; linarith)
    (by dsimp [R]; linarith [(le_max_left ‖f t₀‖ ‖g t₀‖).trans (le_max_left _ ‖h t₀‖)])
    (by dsimp [R]; linarith [(le_max_right ‖f t₀‖ ‖g t₀‖).trans (le_max_left _ ‖h t₀‖)])
    (by dsimp [R]; linarith [le_max_right (max ‖f t₀‖ ‖g t₀‖) ‖h t₀‖]) hR hM
  obtain ⟨C, hC⟩ := (isCompact_closedBall t₀ r).exists_bound_of_continuousOn
    (hterm_diff M).continuousOn
  have hu : Summable fun n : ℕ ↦ max C 0 * ((1 + ρ) / 2) ^ (n - M) :=
    (summable_nat_add_iff M).mp <| by
      simpa using (summable_geometric_of_lt_one (by positivity) (by linarith)).mul_left (max C 0)
  have huni : HasSumUniformlyOn (fun n t ↦ hyperTerm (f t) (g t) (h t) (w t) n)
      (fun t ↦ ₂F₁ (f t) (g t) (h t) (w t)) (ball t₀ r) := by
    have heq (t : ℂ) : ₂F₁ (f t) (g t) (h t) (w t) =
        ∑' n : ℕ, hyperTerm (f t) (g t) (h t) (w t) n := by
      simpa [_root_.ordinaryHypergeometric, hyperTerm] using
        ordinaryHypergeometric_sum_eq (f t) (g t) (h t) (w t)
    simp_rw [heq]
    apply HasSumUniformlyOn.of_norm_le_summable_eventually hu
    rw [Nat.cofinite_eq_atTop]
    filter_upwards [eventually_ge_atTop M] with n hn t ht
    obtain ⟨bf, bg, bh, bw⟩ := hcb_bd t (ball_subset_closedBall ht)
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
    simpa using (norm_hyperTerm_add_le hρ0 hρ1 bw bf bg bh hR hM m).trans
      (mul_le_mul_of_nonneg_right ((hC t (ball_subset_closedBall ht)).trans (le_max_left C 0))
        (by positivity))
  exact ((hasSumUniformlyOn_iff_tendstoUniformlyOn.mp
    huni).tendstoLocallyUniformlyOn.differentiableOn
    (Eventually.of_forall fun _ ↦ DifferentiableOn.fun_sum fun n _ ↦
      (hterm_diff n).mono ball_subset_closedBall) Metric.isOpen_ball).analyticOnNhd
    Metric.isOpen_ball t₀ (mem_ball_self hr)

end AnalyticAt

end ComplexAnalytic
