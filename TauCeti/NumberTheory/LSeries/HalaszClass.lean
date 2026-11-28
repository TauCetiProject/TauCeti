/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
public import Mathlib.NumberTheory.LSeries.Basic
import Mathlib.Analysis.PSeries
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.Injectivity

/-!
# The logarithmic-derivative coefficient class

For a multiplicative arithmetic function `f` with `L`-series `F(s) = ∑ f(n) n ^ (-s)`, the
coefficients `Λ_f` of the logarithmic derivative are defined by `-F'(s) / F(s) = ∑ Λ_f(n) n ^ (-s)`;
for `f = 1` they are the von Mangoldt function `Λ`. Granville, Harper and Soundararajan state
Halász's theorem for the class `C(κ)` of multiplicative functions with `|Λ_f(n)| ≤ κ Λ(n)` for all
`n`. For a completely multiplicative `f` one has `Λ_f = f Λ`, so the completely multiplicative
functions bounded by `1` in absolute value are the basic members of `C(1)`; of such memberships
this file proves only the case `f = 1`.

This file defines the class with its Euler logarithm made explicit. An arithmetic function `b` is a
*logarithmic-derivative coefficient* of `f` with constant `κ` (`TauCeti.IsHalaszCoefficient`) if
`‖b n‖ ≤ κ Λ(n)` for every `n`, and for every `s` with `1 < re s` the three series
`F(s) = LSeries f s`, `LSeries b s` and `H(s) = LSeries (n ↦ b n / log n) s` converge absolutely,
`F(s) = exp (H(s))`, and `-F'(s) / F(s) = LSeries b s`. The class
`TauCeti.HalaszCoefficientClass κ f` asks for `κ > 0`, for `f` to be multiplicative, and for such
a coefficient to exist. The quotient `b n / log n` is `0` at `n = 0` and `n = 1`, where `b`
vanishes.

The coefficient is determined by `f`: two coefficients have the same `L`-series on `1 < re s`, so
they agree at every positive index, and both vanish at `0`. `TauCeti.halaszCoeff f` is this
coefficient `Λ_f` when it exists, and `0` otherwise.

## Main definitions

* `TauCeti.IsHalaszCoefficient κ f b`: `b` is a logarithmic-derivative coefficient of `f` with
  constant `κ`.
* `TauCeti.HalaszCoefficientClass κ f`: the class `C(κ)`.
* `TauCeti.halaszCoeff f`: the coefficient `Λ_f`.

## Main results

* `TauCeti.IsHalaszCoefficient.eq_of_LSeries_eq`, `TauCeti.IsHalaszCoefficient.unique`: the
  coefficient is unique; any arithmetic function whose `L`-series converges absolutely on
  `1 < re s` and equals `-F' / F` there is the coefficient.
* `TauCeti.IsHalaszCoefficient.apply_eq_zero_of_not_isPrimePow`: the coefficient vanishes away
  from prime powers.
* `TauCeti.IsHalaszCoefficient.LSeries_ne_zero`: `F(s) ≠ 0` for `1 < re s`.
* `TauCeti.HalaszCoefficientClass.mono`: `C(κ) ⊆ C(κ')` for `κ ≤ κ'`.
* `TauCeti.halaszCoefficientClass_zeta`, `TauCeti.halaszCoeff_zeta`: the function `ζ` (equal to
  `1` at every `n ≥ 1`) belongs to `C(1)`, with `Λ_f = Λ`.
* `TauCeti.not_halaszCoefficientClass_id`: `n ↦ n` belongs to no class `C(κ)`.

## References

* A. Granville, A. J. Harper, K. Soundararajan, *A new proof of Halász's theorem, and its
  consequences*, Compos. Math. 155 (2019), 126–163, §1.
-/

public section

open ArithmeticFunction Complex Filter
open scoped ArithmeticFunction.zeta LSeries.notation

namespace TauCeti

/-- `b` is a *logarithmic-derivative coefficient* of `f` with constant `κ`: `‖b n‖ ≤ κ Λ(n)` for
every `n`, and for every `s` with `1 < re s` the `L`-series of `f`, of `b` and of `n ↦ b n / log n`
converge absolutely, `LSeries f s` is the exponential of the last one, and `-F' / F` is the
`L`-series of `b`. -/
structure IsHalaszCoefficient (κ : ℝ) (f b : ArithmeticFunction ℂ) : Prop where
  /-- The coefficient is bounded by `κ` times the von Mangoldt function, at every index. -/
  norm_le (n : ℕ) : ‖b n‖ ≤ κ * Λ n
  /-- The `L`-series of `f` converges absolutely on `1 < re s`. -/
  summable {s : ℂ} (hs : 1 < s.re) : LSeriesSummable f s
  /-- The `L`-series of the coefficient converges absolutely on `1 < re s`. -/
  summable_coeff {s : ℂ} (hs : 1 < s.re) : LSeriesSummable b s
  /-- The `L`-series of the Euler logarithm converges absolutely on `1 < re s`. -/
  summable_div_log {s : ℂ} (hs : 1 < s.re) :
    LSeriesSummable (fun n ↦ b n / (Real.log n : ℂ)) s
  /-- The `L`-series of `f` is the exponential of its Euler logarithm. -/
  eq_exp {s : ℂ} (hs : 1 < s.re) :
    LSeries f s = exp (LSeries (fun n ↦ b n / (Real.log n : ℂ)) s)
  /-- The negative logarithmic derivative of the `L`-series of `f` is the `L`-series of `b`. -/
  neg_deriv_div {s : ℂ} (hs : 1 < s.re) : -deriv (LSeries f) s / LSeries f s = LSeries b s

/-- The *logarithmic-derivative coefficient class* `C(κ)` of Granville, Harper and Soundararajan:
`κ > 0`, `f` is multiplicative, and `f` has a logarithmic-derivative coefficient with constant
`κ`. -/
def HalaszCoefficientClass (κ : ℝ) (f : ArithmeticFunction ℂ) : Prop :=
  0 < κ ∧ f.IsMultiplicative ∧ ∃ b : ArithmeticFunction ℂ, IsHalaszCoefficient κ f b

variable {κ κ' : ℝ} {f b b' : ArithmeticFunction ℂ}

/-- The class `C(κ)` written out: the coefficient bound, the three summability conditions, the
exponential identity and the logarithmic-derivative identity. -/
theorem halaszCoefficientClass_iff :
    HalaszCoefficientClass κ f ↔ 0 < κ ∧ f.IsMultiplicative ∧ ∃ b : ArithmeticFunction ℂ,
      (∀ n, ‖b n‖ ≤ κ * Λ n) ∧ ∀ s : ℂ, 1 < s.re →
        LSeriesSummable f s ∧ LSeriesSummable b s ∧
        LSeriesSummable (fun n ↦ b n / (Real.log n : ℂ)) s ∧
        LSeries f s = exp (LSeries (fun n ↦ b n / (Real.log n : ℂ)) s) ∧
        -deriv (LSeries f) s / LSeries f s = LSeries b s := by
  refine and_congr_right fun _ ↦ and_congr_right fun _ ↦ exists_congr fun b ↦ ⟨fun hb ↦ ?_, ?_⟩
  · exact ⟨hb.norm_le, fun s hs ↦ ⟨hb.summable hs, hb.summable_coeff hs, hb.summable_div_log hs,
      hb.eq_exp hs, hb.neg_deriv_div hs⟩⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun hs ↦ (h2 _ hs).1, fun hs ↦ (h2 _ hs).2.1, fun hs ↦ (h2 _ hs).2.2.1,
      fun hs ↦ (h2 _ hs).2.2.2.1, fun hs ↦ (h2 _ hs).2.2.2.2⟩

namespace IsHalaszCoefficient

/-- A logarithmic-derivative coefficient vanishes where the von Mangoldt function does. -/
theorem apply_eq_zero (hb : IsHalaszCoefficient κ f b) {n : ℕ} (hn : Λ n = 0) : b n = 0 := by
  have h := hb.norm_le n
  rw [hn, mul_zero] at h
  exact norm_le_zero_iff.1 h

/-- A logarithmic-derivative coefficient vanishes away from prime powers. -/
theorem apply_eq_zero_of_not_isPrimePow (hb : IsHalaszCoefficient κ f b) {n : ℕ}
    (hn : ¬IsPrimePow n) : b n = 0 :=
  hb.apply_eq_zero (vonMangoldt_eq_zero_iff.2 hn)

/-- The exponential identity gives `LSeries f s ≠ 0` on `1 < re s`. -/
theorem LSeries_ne_zero (hb : IsHalaszCoefficient κ f b) {s : ℂ} (hs : 1 < s.re) :
    LSeries f s ≠ 0 := by
  rw [hb.eq_exp hs]
  exact exp_ne_zero _

/-- A coefficient with constant `κ` is a coefficient with every constant `κ' ≥ κ`. -/
theorem mono (hb : IsHalaszCoefficient κ f b) (h : κ ≤ κ') : IsHalaszCoefficient κ' f b :=
  { hb with
    norm_le := fun n ↦ (hb.norm_le n).trans (mul_le_mul_of_nonneg_right h vonMangoldt_nonneg) }

/-- **Uniqueness of the logarithmic-derivative coefficient.** If the `L`-series of an arithmetic
function `b'` converges absolutely on `1 < re s` and equals `-F' / F` there, then `b'` is the
logarithmic-derivative coefficient of `f`. The values at `0` agree because both are arithmetic
functions; the `L`-series does not see them. -/
theorem eq_of_LSeries_eq (hb : IsHalaszCoefficient κ f b)
    (hsum : ∀ s : ℂ, 1 < s.re → LSeriesSummable b' s)
    (heq : ∀ s : ℂ, 1 < s.re → LSeries b' s = -deriv (LSeries f) s / LSeries f s) : b' = b := by
  ext n
  rcases eq_or_ne n 0 with rfl | hn
  · rw [ArithmeticFunction.map_zero, ArithmeticFunction.map_zero]
  have h2 : (1 : ℝ) < (2 : ℂ).re := by norm_num
  refine LSeries.eq_of_LSeries_eventually_eq
    ((hsum 2 h2).abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _))
    ((hb.summable_coeff h2).abscissaOfAbsConv_le.trans_lt (EReal.coe_lt_top _)) ?_ hn
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
  have hx' : 1 < (x : ℂ).re := by rwa [ofReal_re]
  rw [heq _ hx', hb.neg_deriv_div hx']

/-- Two logarithmic-derivative coefficients of the same function are equal, whatever their
constants. -/
theorem unique (hb : IsHalaszCoefficient κ f b) (hb' : IsHalaszCoefficient κ' f b') : b' = b :=
  hb.eq_of_LSeries_eq (fun _ hs ↦ hb'.summable_coeff hs) fun _ hs ↦ (hb'.neg_deriv_div hs).symm

end IsHalaszCoefficient

open Classical in
/-- The logarithmic-derivative coefficient `Λ_f` of `f`: the arithmetic function `b` with
`IsHalaszCoefficient κ f b` for some `κ`, which is unique, and `0` if there is none. -/
noncomputable def halaszCoeff (f : ArithmeticFunction ℂ) : ArithmeticFunction ℂ :=
  if h : ∃ κ b, IsHalaszCoefficient κ f b then h.choose_spec.choose else 0

/-- `halaszCoeff f` is `0` when `f` has no logarithmic-derivative coefficient. -/
theorem halaszCoeff_of_not_exists (h : ¬∃ κ b, IsHalaszCoefficient κ f b) : halaszCoeff f = 0 :=
  dite_eq_right h

/-- A logarithmic-derivative coefficient of `f` is `halaszCoeff f`. -/
theorem IsHalaszCoefficient.halaszCoeff_eq (hb : IsHalaszCoefficient κ f b) :
    halaszCoeff f = b := by
  have h : ∃ κ b, IsHalaszCoefficient κ f b := ⟨κ, b, hb⟩
  rw [halaszCoeff, dite_eq_left h]
  exact hb.unique h.choose_spec.choose_spec

/-- Membership in the class from a coefficient: the constructor of `C(κ)`. -/
theorem IsHalaszCoefficient.halaszCoefficientClass (hb : IsHalaszCoefficient κ f b) (hκ : 0 < κ)
    (hf : f.IsMultiplicative) : HalaszCoefficientClass κ f :=
  ⟨hκ, hf, b, hb⟩

namespace HalaszCoefficientClass

/-- The constant of a class is positive. -/
theorem pos (h : HalaszCoefficientClass κ f) : 0 < κ := h.1

/-- The members of a class are multiplicative. -/
theorem isMultiplicative (h : HalaszCoefficientClass κ f) : f.IsMultiplicative := h.2.1

/-- For `f` in `C(κ)`, the exposed coefficient `halaszCoeff f` is a logarithmic-derivative
coefficient of `f` with constant `κ`. -/
theorem isHalaszCoefficient_halaszCoeff (h : HalaszCoefficientClass κ f) :
    IsHalaszCoefficient κ f (halaszCoeff f) := by
  obtain ⟨b, hb⟩ := h.2.2
  rwa [hb.halaszCoeff_eq]

/-- For `f` in `C(κ)`, `‖Λ_f(n)‖ ≤ κ Λ(n)` at every `n`. -/
theorem norm_halaszCoeff_le (h : HalaszCoefficientClass κ f) (n : ℕ) :
    ‖halaszCoeff f n‖ ≤ κ * Λ n :=
  h.isHalaszCoefficient_halaszCoeff.norm_le n

/-- For `f` in `C(κ)`, the negative logarithmic derivative of the `L`-series of `f` on `1 < re s`
is the `L`-series of `Λ_f`. -/
theorem neg_deriv_div (h : HalaszCoefficientClass κ f) {s : ℂ} (hs : 1 < s.re) :
    -deriv (LSeries f) s / LSeries f s = LSeries (halaszCoeff f) s :=
  h.isHalaszCoefficient_halaszCoeff.neg_deriv_div hs

/-- For `f` in `C(κ)`, the `L`-series of `f` does not vanish on `1 < re s`. -/
theorem LSeries_ne_zero (h : HalaszCoefficientClass κ f) {s : ℂ} (hs : 1 < s.re) :
    LSeries f s ≠ 0 :=
  h.isHalaszCoefficient_halaszCoeff.LSeries_ne_zero hs

/-- The classes increase with the constant: `C(κ) ⊆ C(κ')` for `κ ≤ κ'`. -/
theorem mono (h : HalaszCoefficientClass κ f) (hκ : κ ≤ κ') : HalaszCoefficientClass κ' f :=
  ⟨h.pos.trans_le hκ, h.isMultiplicative, halaszCoeff f, h.isHalaszCoefficient_halaszCoeff.mono hκ⟩

end HalaszCoefficientClass

/-! ### The constant function one and the identity -/

/-- The von Mangoldt function is the logarithmic-derivative coefficient of `ζ`, the arithmetic
function equal to `1` at every `n ≥ 1`, with constant `1`. -/
theorem isHalaszCoefficient_zeta :
    IsHalaszCoefficient 1 (ζ : ArithmeticFunction ℂ) ⟨fun n ↦ (Λ n : ℂ), by simp⟩ where
  norm_le n := by
    rw [coe_mk, norm_real, Real.norm_of_nonneg vonMangoldt_nonneg, one_mul]
  summable hs := LSeriesSummable_zeta_iff.2 hs
  summable_coeff hs := LSeriesSummable_vonMangoldt hs
  summable_div_log hs := by
    refine LSeriesSummable_of_bounded_of_one_lt_re (m := 1) (fun n _ ↦ ?_) hs
    rw [coe_mk, norm_div, norm_real, norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
    exact div_le_one_of_le₀ (vonMangoldt_le_log.trans (le_abs_self _)) (abs_nonneg _)
  eq_exp hs := (LSeries_zeta_eq_riemannZeta hs).trans (riemannZeta_eq_exp_LSeries hs).symm
  neg_deriv_div hs := by
    have h := LSeries_vonMangoldt_eq hs
    rw [← LSeries_zeta_eq] at h
    exact h.symm

/-- **The constant function one is in `C(1)`.** The arithmetic function `ζ`, equal to `1` at
every `n ≥ 1` and to `0` at `0`, belongs to `C(1)`. -/
theorem halaszCoefficientClass_zeta : HalaszCoefficientClass 1 (ζ : ArithmeticFunction ℂ) :=
  isHalaszCoefficient_zeta.halaszCoefficientClass one_pos isMultiplicative_zeta.natCast

/-- The logarithmic-derivative coefficient of `ζ` is the von Mangoldt function. -/
theorem halaszCoeff_zeta (n : ℕ) : halaszCoeff (ζ : ArithmeticFunction ℂ) n = Λ n := by
  rw [isHalaszCoefficient_zeta.halaszCoeff_eq, coe_mk]

/-- **The identity is in no class.** The arithmetic function `n ↦ n` belongs to no `C(κ)`: its
`L`-series does not converge absolutely at `s = 3 / 2`. -/
theorem not_halaszCoefficientClass_id (κ : ℝ) :
    ¬HalaszCoefficientClass κ ((ArithmeticFunction.id : ArithmeticFunction ℕ) :
      ArithmeticFunction ℂ) := by
  rintro ⟨-, -, b, hb⟩
  have hs : (1 : ℝ) < ((3 / 2 : ℝ) : ℂ).re := by
    rw [ofReal_re]
    norm_num
  have h32 : (3 / 2 : ℝ) = 1 / 2 + 1 := by norm_num
  have hsum := (hb.summable hs).norm
  have hterm (n : ℕ) : ‖LSeries.term ((ArithmeticFunction.id : ArithmeticFunction ℕ) :
      ArithmeticFunction ℂ) ((3 / 2 : ℝ) : ℂ) n‖ = 1 / (n : ℝ) ^ (1 / 2 : ℝ) := by
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    have hn0 : (0 : ℝ) < n := Nat.cast_pos.2 (Nat.pos_of_ne_zero hn)
    rw [LSeries.norm_term_eq, ite_eq_right hn, ofReal_re, natCoe_apply, id_apply,
      Complex.norm_natCast, h32, Real.rpow_add_one hn0.ne']
    field_simp
  rw [funext hterm, Real.summable_one_div_nat_rpow] at hsum
  norm_num at hsum

end TauCeti
