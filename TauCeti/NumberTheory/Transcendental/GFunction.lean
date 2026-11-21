/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Transcendental.EFunction.Basic
import Mathlib.NumberTheory.Chebyshev

/-!
# Siegel's G-functions

Siegel introduced G-functions alongside E-functions in 1929 to study Diophantine approximation and
linear/algebraic relations among values at algebraic points of locally analytic solutions to linear
differential equations with rational function coefficients over `algebraicClosure ℚ ℂ` — including
algebraic functions, logarithms, polylogarithms, Gauss hypergeometric series, and periods of
algebraic families of varieties (later developed by Galochkin, Bombieri, Chudnovsky, and André).

A formal power series `∑ aₙ Xⁿ` defines a *G-function* (`TauCeti.IsGFunction a`) when its
coefficient sequence `a : ℕ → ℂ` satisfies the same arithmetic growth conditions as an E-function
together with D-finiteness of the ordinary generating series `PowerSeries.mk a` over
`algebraicClosure ℚ ℂ`:

1. Every `aₙ` is algebraic over `ℚ`.
2. `PowerSeries.mk a` is D-finite over `algebraicClosure ℚ ℂ`.
3. Every Galois conjugate of `aₙ` has modulus at most `C ^ (n + 1)` for some `C > 0`.
4. Positive integers `dₙ ≤ D ^ (n + 1)` clear the denominators of `a₀, …, aₙ` simultaneously.

Because formal Borel division `aₙ ↦ aₙ / n!` preserves and reflects D-finiteness
(`TauCeti.isDFinite_ePowerSeries_iff`), a sequence `a` defines a G-function if and only if it
defines an E-function (`TauCeti.isGFunction_iff_isEFunction`). Consequently all coefficients of a
G-function lie in a common number field, while the geometric modulus bound `‖aₙ‖ ≤ C ^ (n + 1)`
implies that `PowerSeries.mk a` has convergence radius at least `C⁻¹`
(`PowerSeries.inv_le_radius_of_norm_coeff_le_mul_pow`), hence positive radius
(`TauCeti.IsGFunction.radius_pos`), and represents an analytic function on a disc around `0`.
G-functions are closed under addition, scalar multiplication, shifts
(`TauCeti.IsGFunction.shift`, `TauCeti.IsGFunction.comp_add_right`), rescaling, Galois conjugation,
formal differentiation, and Cauchy convolution (`TauCeti.IsGFunction.sum_antidiagonal_mul`).

## Main definitions

* `TauCeti.IsGFunction a`: Siegel's G-function predicate on a coefficient sequence `a : ℕ → ℂ`.

## Main results

* `TauCeti.isGFunction_iff_isEFunction`: `IsGFunction a ↔ IsEFunction a` (Borel transform).
* `TauCeti.IsGFunction.exists_numberField`: all coefficients lie in a single number field.
* `TauCeti.IsGFunction.radius_pos`, `TauCeti.IsGFunction.hasFPowerSeriesOnBall`,
  `TauCeti.IsGFunction.exists_hasFPowerSeriesOnBall`, `TauCeti.IsGFunction.exists_summable`:
  positive convergence radius and analyticity around `0`.
* `TauCeti.IsGFunction.add`, `TauCeti.IsGFunction.comp_add_right`,
  `TauCeti.IsGFunction.sum_antidiagonal_mul`, `TauCeti.IsGFunction.derivative`: closure under sums,
  shifts, Cauchy products, and formal differentiation.
* `TauCeti.isGFunction_const_one`, `TauCeti.isGFunction_one_div_natCast`,
  `TauCeti.not_isGFunction_one_div_factorial`: `1 / (1 - z)` and `-log (1 - z)` are G-functions
  (the latter via Chebyshev's bound on `lcm {1, …, n}`), whereas `exp z = ∑ zⁿ / n!` is not.

## References

* C. L. Siegel, *Über einige Anwendungen diophantischer Approximationen*, Abh. Preuß. Akad. Wiss.,
  Phys.-Math. Kl. 1929, Nr. 1.
* F. Beukers, *E-functions and G-functions*, lecture notes, Arizona Winter School, 2008, §4.1.
* S. Fischler and T. Rivoal, *On Siegel's problem for E-functions*, Math. Z. **301** (2022),
  1429–1453 (arXiv:1910.06817), Definition 1.
-/

public section

open Filter Polynomial
open scoped ENNReal NNReal PowerSeries Topology

namespace TauCeti

/-! ### Siegel's G-functions and the Borel transform equivalence -/

/-- A sequence `a : ℕ → ℂ` defines a *G-function* `∑ aₙ zⁿ` when its terms are algebraic over `ℚ`,
`PowerSeries.mk a` is D-finite over `algebraicClosure ℚ ℂ`, the Galois conjugates of `aₙ` are
bounded by `C ^ (n + 1)`, and positive integers `dₙ ≤ D ^ (n + 1)` clear the denominators of
`a₀, …, aₙ` simultaneously. -/
structure IsGFunction (a : ℕ → ℂ) : Prop where
  /-- Every Taylor coefficient `aₙ` is algebraic over `ℚ`. -/
  isAlgebraic : ∀ n, IsAlgebraic ℚ (a n)
  /-- The ordinary generating series `PowerSeries.mk a = ∑ aₙ Xⁿ` satisfies a nonzero linear
  differential equation with polynomial coefficients over `algebraicClosure ℚ ℂ`. -/
  isDFinite : PowerSeries.IsDFinite (algebraicClosure ℚ ℂ) (PowerSeries.mk a)
  /-- Geometric house bound: every complex root of `minpoly ℚ (aₙ)` has modulus at most
  `C ^ (n + 1)` for a uniform constant `C > 0` (using exponent `n + 1` so `n = 0` is included
  without an extra multiplicative factor). -/
  size_le : ∃ C : ℝ, 0 < C ∧ ∀ n, ∀ z ∈ (minpoly ℚ (a n)).aroots ℂ, ‖z‖ ≤ C ^ (n + 1)
  /-- Geometric common-denominator bound: positive integers `dₙ ≤ D ^ (n + 1)` make `dₙ * aₘ`
  an algebraic integer simultaneously for all `m ≤ n`. -/
  den_le : ∃ D : ℝ, 0 < D ∧ ∃ d : ℕ → ℕ,
    ∀ n, 1 ≤ d n ∧ (d n : ℝ) ≤ D ^ (n + 1) ∧ ∀ m ≤ n, IsIntegral ℤ ((d n : ℂ) * a m)

/-- **Borel transform equivalence.** A sequence `a` defines a G-function `∑ aₙ zⁿ` if and only if
it defines an E-function `∑ aₙ zⁿ / n!`. -/
theorem isGFunction_iff_isEFunction {a : ℕ → ℂ} :
    IsGFunction a ↔ IsEFunction a :=
  ⟨fun ⟨h1, h2, h3, h4⟩ ↦ ⟨h1, (isDFinite_ePowerSeries_iff a).mpr h2, h3, h4⟩,
   fun ⟨h1, h2, h3, h4⟩ ↦ ⟨h1, (isDFinite_ePowerSeries_iff a).mp h2, h3, h4⟩⟩

/-- Convert a G-function into the corresponding Borel-transformed E-function. -/
theorem IsGFunction.isEFunction {a : ℕ → ℂ} (ha : IsGFunction a) : IsEFunction a :=
  isGFunction_iff_isEFunction.mp ha

/-- Convert an E-function into the corresponding inverse-Borel G-function. -/
theorem IsEFunction.isGFunction {a : ℕ → ℂ} (ha : IsEFunction a) : IsGFunction a :=
  isGFunction_iff_isEFunction.mpr ha

namespace IsGFunction

/-- The house of the coefficients of a G-function grows at most geometrically. -/
theorem exists_house_le {a : ℕ → ℂ} (ha : IsGFunction a) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, house (a n) ≤ C ^ (n + 1) :=
  ha.isEFunction.exists_house_le

/-- Construct `IsGFunction a` using a geometric bound on `TauCeti.house (a n)`. -/
theorem of_house_le {a : ℕ → ℂ} (halg : ∀ n, IsAlgebraic ℚ (a n))
    (hdf : PowerSeries.IsDFinite (algebraicClosure ℚ ℂ) (PowerSeries.mk a))
    (hhouse : ∃ C : ℝ, 0 < C ∧ ∀ n, house (a n) ≤ C ^ (n + 1))
    (hden : ∃ D : ℝ, 0 < D ∧ ∃ d : ℕ → ℕ,
      ∀ n, 1 ≤ d n ∧ (d n : ℝ) ≤ D ^ (n + 1) ∧ ∀ m ≤ n, IsIntegral ℤ ((d n : ℂ) * a m)) :
    IsGFunction a :=
  (IsEFunction.of_house_le halg ((isDFinite_ePowerSeries_iff a).mpr hdf) hhouse hden).isGFunction

/-- The complex moduli `‖a n‖` of a G-function grow at most geometrically. -/
theorem exists_norm_le {a : ℕ → ℂ} (ha : IsGFunction a) :
    ∃ C : ℝ, 0 < C ∧ ∀ n, ‖a n‖ ≤ C ^ (n + 1) :=
  ha.isEFunction.exists_norm_le

/-- All coefficients of a G-function lie in a single number field inside `ℂ`. -/
theorem exists_numberField {a : ℕ → ℂ} (ha : IsGFunction a) :
    ∃ (K : IntermediateField ℚ ℂ) (_ : NumberField K), ∀ n, a n ∈ K :=
  ha.isEFunction.exists_numberField

/-! ### Convergence on a disc of positive radius -/

/-- A G-function has positive formal radius of convergence. -/
theorem radius_pos {a : ℕ → ℂ} (ha : IsGFunction a) :
    0 < (PowerSeries.mk a).radius := by
  obtain ⟨C, hC, hnorm⟩ := ha.exists_norm_le
  exact (ENNReal.inv_pos.mpr ENNReal.coe_ne_top).trans_le <|
    PowerSeries.inv_le_radius_of_norm_coeff_le_mul_pow (B := C) (C := Real.toNNReal C) fun n ↦ by
      simpa [Real.coe_toNNReal C hC.le, pow_succ'] using hnorm n

/-- A G-function represents the analytic sum `z ↦ ∑' n, a n * z ^ n` on the open ball of radius
`(PowerSeries.mk a).radius` around `0`. -/
theorem hasFPowerSeriesOnBall {a : ℕ → ℂ} (ha : IsGFunction a) :
    HasFPowerSeriesOnBall (fun z ↦ ∑' n, a n * z ^ n)
      (FormalMultilinearSeries.ofScalars ℂ a) 0 (PowerSeries.mk a).radius := by
  set p := FormalMultilinearSeries.ofScalars ℂ a
  have hrad : p.radius = (PowerSeries.mk a).radius := by
    simpa [p] using (PowerSeries.radius_eq_radius_ofScalars ℂ (PowerSeries.mk a)).symm
  have hp := p.hasFPowerSeriesOnBall (hrad ▸ ha.radius_pos)
  rw [hrad] at hp
  have hsum : p.sum = fun z ↦ ∑' n, a n * z ^ n := by
    ext z
    rw [FormalMultilinearSeries.sum]
    refine tsum_congr fun n ↦ ?_
    simp [p, mul_comm]
  rwa [hsum] at hp

/-- Every G-function has a finite positive radius `r : ℝ≥0` on which `∑ aₙ zⁿ` is its convergent
power series around `0`. -/
theorem exists_hasFPowerSeriesOnBall {a : ℕ → ℂ} (ha : IsGFunction a) :
    ∃ r : ℝ≥0, 0 < r ∧ HasFPowerSeriesOnBall (fun z ↦ ∑' n, a n * z ^ n)
      (FormalMultilinearSeries.ofScalars ℂ a) 0 r := by
  obtain ⟨r, hr, hrad⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp ha.radius_pos
  exact ⟨r, by simpa using hr, ha.hasFPowerSeriesOnBall.mono hr hrad.le⟩

/-- The series `∑ aₙ zⁿ` of a G-function is summable on a disc `{z : ℂ | ‖z‖ < r}` of positive
radius `r > 0`. -/
theorem exists_summable {a : ℕ → ℂ} (ha : IsGFunction a) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, ‖z‖ < r → Summable fun n : ℕ ↦ a n * z ^ n := by
  obtain ⟨r, hr, hp⟩ := ha.exists_hasFPowerSeriesOnBall
  refine ⟨r, hr, fun z hz ↦ ?_⟩
  have hmem : z ∈ Metric.eball (0 : ℂ) r := by
    rw [mem_eball_zero_iff, eNorm_eq_nnNorm, ENNReal.coe_lt_coe, ← NNReal.coe_lt_coe, coe_nnNorm]
    exact hz
  simpa [FormalMultilinearSeries.ofScalars_apply_eq, smul_eq_mul, mul_comm] using
    (hp.hasSum hmem).summable

/-- The analytic sum `z ↦ ∑' n, a n * z ^ n` of a G-function is analytic at `0`. -/
theorem analyticAt_zero {a : ℕ → ℂ} (ha : IsGFunction a) :
    AnalyticAt ℂ (fun z ↦ ∑' n, a n * z ^ n) 0 :=
  ha.hasFPowerSeriesOnBall.analyticAt

end IsGFunction

/-! ### Closure properties of G-functions -/

/-- The zero sequence is a G-function. -/
@[simp]
theorem isGFunction_zero : IsGFunction 0 :=
  isEFunction_zero.isGFunction

/-- Any sequence supported at a single index `k` with an algebraic value `c` is a G-function. -/
theorem isGFunction_single (k : ℕ) {c : ℂ} (hc : IsAlgebraic ℚ c) :
    IsGFunction (Pi.single k c) :=
  (isEFunction_single k hc).isGFunction

/-- The constant-one sequence `aₙ = 1` (representing `1 / (1 - z)`) is a G-function. -/
@[simp]
theorem isGFunction_const_one : IsGFunction (fun _ ↦ 1) :=
  isEFunction_const_one.isGFunction

/-- The geometric sequence `n ↦ α ^ n` is a G-function for algebraic `α`. -/
theorem isGFunction_pow {α : ℂ} (hα : IsAlgebraic ℚ α) : IsGFunction (α ^ ·) :=
  (isEFunction_pow hα).isGFunction

namespace IsGFunction

/-- Negation preserves G-functions. -/
protected theorem neg {a : ℕ → ℂ} (ha : IsGFunction a) : IsGFunction (-a) :=
  ha.isEFunction.neg.isGFunction

/-- Sums of G-functions are G-functions. -/
protected theorem add {a b : ℕ → ℂ} (ha : IsGFunction a) (hb : IsGFunction b) :
    IsGFunction (a + b) :=
  (ha.isEFunction.add hb.isEFunction).isGFunction

/-- Differences of G-functions are G-functions. -/
protected theorem sub {a b : ℕ → ℂ} (ha : IsGFunction a) (hb : IsGFunction b) :
    IsGFunction (a - b) :=
  (ha.isEFunction.sub hb.isEFunction).isGFunction

/-- Scalar multiplication by an algebraic number preserves G-functions. -/
protected theorem smul {c : ℂ} (hc : IsAlgebraic ℚ c) {a : ℕ → ℂ} (ha : IsGFunction a) :
    IsGFunction (c • a) :=
  (ha.isEFunction.smul hc).isGFunction

/-- Shifting the coefficient sequence (`aₙ ↦ a_{n + 1}`) preserves G-functions. -/
protected theorem shift {a : ℕ → ℂ} (ha : IsGFunction a) :
    IsGFunction fun n ↦ a (n + 1) :=
  ha.isEFunction.shift.isGFunction

/-- Shifting the coefficient sequence by `m` (`aₙ ↦ a_{n + m}`) preserves G-functions. -/
protected theorem comp_add_right {a : ℕ → ℂ} (ha : IsGFunction a) (m : ℕ) :
    IsGFunction fun n ↦ a (n + m) :=
  (ha.isEFunction.comp_add_right m).isGFunction

/-- Rescaling by an algebraic number `α` (`aₙ ↦ αⁿ aₙ`) preserves G-functions. -/
protected theorem rescale {α : ℂ} (hα : IsAlgebraic ℚ α) {a : ℕ → ℂ} (ha : IsGFunction a) :
    IsGFunction fun n ↦ α ^ n * a n :=
  (ha.isEFunction.rescale hα).isGFunction

/-- Applying a ring endomorphism of `ℂ` coefficientwise preserves G-functions. -/
protected theorem comp_ringHom {a : ℕ → ℂ} (ha : IsGFunction a) (σ : ℂ →+* ℂ) :
    IsGFunction (σ ∘ a) :=
  (ha.isEFunction.comp_ringHom σ).isGFunction

private theorem house_sum_antidiagonal_mul_le {a b : ℕ → ℂ} {C₁ C₂ : ℝ} (hC₁ : 0 < C₁)
    (hC₂ : 0 < C₂) (halg_a : ∀ n, IsAlgebraic ℚ (a n)) (halg_b : ∀ n, IsAlgebraic ℚ (b n))
    (hha : ∀ n, house (a n) ≤ C₁ ^ (n + 1)) (hhb : ∀ n, house (b n) ≤ C₂ ^ (n + 1)) (n : ℕ) :
    house (∑ ij ∈ Finset.antidiagonal n, a ij.1 * b ij.2) ≤
      (2 * max 1 (max C₁ C₂) ^ 2) ^ (n + 1) := by
  set B := max 1 (max C₁ C₂)
  have hB1 : 1 ≤ B := le_max_left _ _
  have hC₁B : C₁ ≤ B := (le_max_left C₁ C₂).trans (le_max_right _ _)
  have hC₂B : C₂ ≤ B := (le_max_right C₁ C₂).trans (le_max_right _ _)
  have hterm_alg (i j : ℕ) : IsAlgebraic ℚ (a i * b j) := (halg_a i).mul (halg_b j)
  calc house (∑ ij ∈ Finset.antidiagonal n, a ij.1 * b ij.2)
      ≤ ∑ ij ∈ Finset.antidiagonal n, house (a ij.1 * b ij.2) :=
        house_sum_le _ fun ij _ ↦ hterm_alg ij.1 ij.2
    _ ≤ ∑ _ij ∈ Finset.antidiagonal n, B ^ (n + 2) := by
        refine Finset.sum_le_sum fun ij hij ↦ ?_
        have hsum := Finset.mem_antidiagonal.mp hij
        have hexp : ij.1 + 1 + (ij.2 + 1) = n + 2 := by omega
        have hai : house (a ij.1) ≤ B ^ (ij.1 + 1) :=
          (hha ij.1).trans (pow_le_pow_left₀ hC₁.le hC₁B _)
        have hbj : house (b ij.2) ≤ B ^ (ij.2 + 1) :=
          (hhb ij.2).trans (pow_le_pow_left₀ hC₂.le hC₂B _)
        calc house (a ij.1 * b ij.2)
            ≤ house (a ij.1) * house (b ij.2) := house_mul_le (halg_a ij.1) (halg_b ij.2)
          _ ≤ B ^ (ij.1 + 1) * B ^ (ij.2 + 1) :=
              mul_le_mul hai hbj (house_nonneg _) (by positivity)
          _ = B ^ (n + 2) := by rw [← pow_add, hexp]
    _ = (n + 1 : ℝ) * B ^ (n + 2) := by simp [Finset.Nat.card_antidiagonal]
    _ ≤ (2 * B ^ 2) ^ (n + 1) := by
        have hn2 : (n + 1 : ℝ) ≤ 2 ^ (n + 1) := by exact_mod_cast Nat.lt_two_pow_self.le
        rw [mul_pow, ← pow_mul]
        exact mul_le_mul hn2 (pow_le_pow_right₀ hB1 (by omega))
          (by positivity) (by positivity)

/-- **Cauchy products of G-functions are G-functions.** -/
protected theorem sum_antidiagonal_mul {a b : ℕ → ℂ} (ha : IsGFunction a) (hb : IsGFunction b) :
    IsGFunction fun n ↦ ∑ ij ∈ Finset.antidiagonal n, a ij.1 * b ij.2 := by
  obtain ⟨C₁, hC₁, hha⟩ := ha.exists_house_le
  obtain ⟨C₂, hC₂, hhb⟩ := hb.exists_house_le
  obtain ⟨D₁, hD₁, d₁, hd₁⟩ := ha.den_le
  obtain ⟨D₂, hD₂, d₂, hd₂⟩ := hb.den_le
  have halg (n : ℕ) : IsAlgebraic ℚ (∑ ij ∈ Finset.antidiagonal n, a ij.1 * b ij.2) := by
    rw [← mem_algebraicClosure_iff]
    exact sum_mem fun ij _ ↦
      mem_algebraicClosure_iff.mpr ((ha.isAlgebraic ij.1).mul (hb.isAlgebraic ij.2))
  have hmk : (PowerSeries.mk fun n ↦ ∑ ij ∈ Finset.antidiagonal n, a ij.1 * b ij.2) =
      PowerSeries.mk a * PowerSeries.mk b := by
    ext n
    simp [PowerSeries.coeff_mul]
  refine of_house_le halg (by rw [hmk]; exact ha.isDFinite.mul hb.isDFinite)
    ⟨2 * max 1 (max C₁ C₂) ^ 2, by positivity,
      house_sum_antidiagonal_mul_le hC₁ hC₂ ha.isAlgebraic hb.isAlgebraic hha hhb⟩ ?_
  refine ⟨D₁ * D₂, mul_pos hD₁ hD₂, fun n ↦ d₁ n * d₂ n, fun n ↦ ?_⟩
  refine ⟨Nat.mul_le_mul (hd₁ n).1 (hd₂ n).1, ?_, fun m hm ↦ ?_⟩
  · rw [Nat.cast_mul, mul_pow]
    exact mul_le_mul (hd₁ n).2.1 (hd₂ n).2.1 (Nat.cast_nonneg _) (by positivity)
  · rw [Finset.mul_sum, ← mem_integralClosure_iff]
    refine sum_mem fun ij hij ↦ ?_
    rw [mem_integralClosure_iff]
    have hsum := Finset.mem_antidiagonal.mp hij
    have h1 : ((d₁ n * d₂ n : ℕ) : ℂ) * (a ij.1 * b ij.2) =
        ((d₁ n : ℂ) * a ij.1) * ((d₂ n : ℂ) * b ij.2) := by
      push_cast; ring
    rw [h1]
    exact ((hd₁ n).2.2 ij.1 (by omega)).mul ((hd₂ n).2.2 ij.2 (by omega))

/-- Formal differentiation (`aₙ ↦ (n + 1) a_{n + 1}`) preserves G-functions. -/
protected theorem derivative {a : ℕ → ℂ} (ha : IsGFunction a) :
    IsGFunction fun n ↦ (n + 1 : ℂ) * a (n + 1) := by
  have hb : IsGFunction fun n ↦ a (n + 1) := ha.shift
  obtain ⟨C, hC, hhb⟩ := hb.exists_house_le
  obtain ⟨D, hD, d, hd⟩ := hb.den_le
  have halg (n : ℕ) : IsAlgebraic ℚ ((n + 1 : ℂ) * a (n + 1)) :=
    ((isAlgebraic_natCast n).add isAlgebraic_one).mul (hb.isAlgebraic n)
  have hmk : (PowerSeries.mk fun n ↦ (n + 1 : ℂ) * a (n + 1)) = d⁄dX (PowerSeries.mk a) := by
    ext n
    simp [PowerSeries.coeff_derivative, mul_comm]
  refine of_house_le halg (by rw [hmk]; exact ha.isDFinite.derivative) ?_ ?_
  · refine ⟨2 * C, by positivity, fun n ↦ ?_⟩
    have hn1 : ((n + 1 : ℕ) : ℂ) = (n + 1 : ℂ) := by push_cast; rfl
    have hn2 : (n + 1 : ℝ) ≤ 2 ^ (n + 1) := by exact_mod_cast Nat.lt_two_pow_self.le
    rw [← hn1, mul_pow]
    calc house (((n + 1 : ℕ) : ℂ) * a (n + 1))
        ≤ house ((n + 1 : ℕ) : ℂ) * house (a (n + 1)) :=
          house_mul_le (isAlgebraic_natCast _) (hb.isAlgebraic n)
      _ = (n + 1 : ℝ) * house (a (n + 1)) := by rw [house_natCast, Nat.cast_add, Nat.cast_one]
      _ ≤ 2 ^ (n + 1) * C ^ (n + 1) :=
          mul_le_mul hn2 (hhb n) (house_nonneg _) (by positivity)
  · refine ⟨D, hD, d, fun n ↦ ⟨(hd n).1, (hd n).2.1, fun m hm ↦ ?_⟩⟩
    have hmul : (d n : ℂ) * ((m + 1 : ℂ) * a (m + 1)) =
        ((m + 1 : ℕ) : ℂ) * ((d n : ℂ) * a (m + 1)) := by
      push_cast; ring
    rw [hmul]
    exact (isIntegral_natCast (m + 1)).mul ((hd n).2.2 m hm)

end IsGFunction

/-! ### Concrete examples and non-examples of G-functions -/

/-- The logarithmic coefficient sequence `n ↦ 1 / (n : ℂ)` (representing
`-log (1 - z) = ∑_{n ≥ 1} zⁿ / n`, with `0` at `n = 0`) is a G-function. -/
theorem isGFunction_one_div_natCast : IsGFunction fun n : ℕ ↦ 1 / (n : ℂ) := by
  have hrat (n : ℕ) : (1 / (n : ℂ)) = ((1 / (n : ℚ) : ℚ) : ℂ) := by push_cast; rfl
  have halg (n : ℕ) : IsAlgebraic ℚ (1 / (n : ℂ)) := by
    rw [hrat n, ← eq_ratCast (algebraMap ℚ ℂ)]
    exact isAlgebraic_algebraMap _
  have hdf : PowerSeries.IsDFinite (algebraicClosure ℚ ℂ)
      (PowerSeries.mk fun n : ℕ ↦ 1 / (n : ℂ)) := by
    rw [← PowerSeries.isDFinite_derivative_iff]
    have hderiv : d⁄dX (PowerSeries.mk fun n : ℕ ↦ 1 / (n : ℂ)) = PowerSeries.mk fun _ ↦ 1 := by
      ext n
      have hne : ((n + 1 : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.succ_ne_zero n)
      rw [PowerSeries.coeff_derivative, PowerSeries.coeff_mk, PowerSeries.coeff_mk, one_div]
      exact_mod_cast inv_mul_cancel₀ hne
    rw [hderiv]
    exact isGFunction_const_one.isDFinite
  refine IsGFunction.of_house_le halg hdf ⟨1, one_pos, fun n ↦ ?_⟩ ?_
  · rw [hrat n, house_ratCast, one_pow]
    rcases n.eq_zero_or_pos with rfl | hn
    · simp
    · simp only [one_div, Rat.cast_inv, Rat.cast_natCast, abs_inv, Nat.abs_cast]
      exact inv_le_one_of_one_le₀ (by exact_mod_cast hn)
  · refine ⟨Real.exp (Real.log 4 + 4), Real.exp_pos _, Nat.lcmUpto, fun n ↦ ?_⟩
    refine ⟨Nat.succ_le_of_lt (Nat.lcmUpto_pos n), ?_, fun m hm ↦ ?_⟩
    · calc (Nat.lcmUpto n : ℝ)
          = Real.exp (Real.log (Nat.lcmUpto n)) :=
            (Real.exp_log (Nat.cast_pos.mpr (Nat.lcmUpto_pos n))).symm
        _ = Real.exp (Chebyshev.psi n) := by rw [Chebyshev.psi_eq_log_lcmUpto]
        _ ≤ Real.exp ((Real.log 4 + 4) * n) :=
            Real.exp_le_exp.mpr (Chebyshev.psi_le_const_mul_self (Nat.cast_nonneg n))
        _ ≤ Real.exp ((Real.log 4 + 4) * (n + 1 : ℕ)) := by
            gcongr
            exact_mod_cast Nat.le_succ n
        _ = Real.exp (Real.log 4 + 4) ^ (n + 1) := by rw [mul_comm, Real.exp_natCast_mul]
    · rcases m.eq_zero_or_pos with rfl | hm0
      · simp [isIntegral_zero]
      · have hdvd : m ∣ Nat.lcmUpto n :=
          Finset.dvd_lcm (Finset.mem_Icc.mpr ⟨hm0, hm⟩)
        obtain ⟨q, hq⟩ := hdvd
        have hval : (Nat.lcmUpto n : ℂ) * (1 / (m : ℂ)) = (q : ℂ) := by
          have hm_ne : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm0.ne'
          rw [hq, Nat.cast_mul, mul_one_div, mul_div_cancel_left₀ _ hm_ne]
        rw [hval]
        exact isIntegral_natCast q

/-- The reciprocal-factorial sequence `n ↦ 1 / (n! : ℂ)` (the Taylor coefficients of `Complex.exp`)
is not a G-function. -/
theorem not_isGFunction_one_div_factorial : ¬IsGFunction fun n ↦ 1 / (n.factorial : ℂ) := by
  intro ha
  obtain ⟨D, _, d, hd⟩ := ha.den_le
  obtain ⟨n, hn⟩ := (FloorSemiring.eventually_mul_pow_lt_factorial_sub D D 0).exists
  let q : ℚ := (d n : ℚ) / n.factorial
  have hq : (q : ℂ) = (d n : ℂ) * (1 / (n.factorial : ℂ)) := by
    simp [q, div_eq_mul_inv]
  have hq0 : (q : ℂ) ≠ 0 := by
    rw [hq]
    exact mul_ne_zero (Nat.cast_ne_zero.mpr (Nat.one_le_iff_ne_zero.mp (hd n).1))
      (one_div_ne_zero (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n)))
  have h1 : 1 ≤ (d n : ℝ) / n.factorial := by
    have hh := one_le_house (hq ▸ (hd n).2.2 n le_rfl) hq0
    rwa [house_ratCast, Rat.cast_div, Rat.cast_natCast, Rat.cast_natCast,
      abs_of_nonneg (by positivity)] at hh
  have hfn : (n.factorial : ℝ) ≤ d n :=
    (one_le_div (Nat.cast_pos.mpr (Nat.factorial_pos n))).mp h1
  exact hn.not_ge ((hfn.trans (hd n).2.1).trans_eq (pow_succ' D n))

end TauCeti
