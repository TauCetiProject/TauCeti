module

/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
public import TauCeti.Analysis.SpecialFunctions.HermiteFunction
public import TauCeti.Probability.Distributions.Gaussian.HermiteMemLp

/-!
# Integrability, `L²` membership, and parity of the Hermite functions

This file continues the object API for the Hermite functions
`ψₙ(x) = Hₙ(x√2) exp(-x²/2) / √(n!√π)` (`TauCeti.hermiteFunction`), adding the regularity facts
the `OrthogonalL2Bases` roadmap's **A2** milestone lists and its **A3** basis construction consumes:

* `TauCeti.integrable_hermiteFunction` — every `ψₙ` is integrable against Lebesgue measure;
* `TauCeti.memLp_two_hermiteFunction` — every `ψₙ` is in `L²(volume)`, the membership the
  `hermiteFunctionLp`/`hermiteHilbertBasis` layer needs to package `ψₙ` as an `Lp` element;
* `TauCeti.hermiteFunction_neg` — the parity relation `ψₙ(-x) = (-1)ⁿ ψₙ(x)`.

The analytic input is a single reusable engine, `TauCeti.integrable_eval_mul_gaussianEnvelope`: a
real polynomial evaluated pointwise, times a Gaussian envelope `exp(-x²/(2v))` of any positive
variance `v`, is Lebesgue-integrable. It is obtained by transporting the polynomial's integrability
against the Gaussian *measure* `gaussianReal 0 v` (all of whose moments are finite,
`TauCeti.integrable_pow_gaussianReal`, so `TauCeti.integrable_eval_of_forall_integrable_pow`
applies) across the change of variables `gaussianReal 0 v = volume.withDensity (gaussianPDF 0 v)`
with `integrable_withDensity_iff`. Applied to the polynomial `Hₙ(·√2)` with `v = 1` this gives the
`L¹` membership, and to its square with `v = ½` (whose envelope `exp(-x²)` is `ψₙ²` up to the
constant) the `L²` membership.

The parity of the functions rests on `TauCeti.aeval_neg_hermite`, the parity `Hₙ(-x) = (-1)ⁿ Hₙ(x)`
of the probabilists' Hermite polynomials, itself immediate from Mathlib's
`Polynomial.coeff_hermite_of_odd_add` (a nonzero coefficient forces `n` and its degree to share
parity).

Mathlib's Gaussian density API (`gaussianReal_of_var_ne_zero`, `measurable_gaussianPDF`,
`gaussianPDFReal_def`), `integrable_withDensity_iff`, `memLp_two_iff_integrable_sq`, and the
`Polynomial` evaluation API are consumed, not re-derived.
-/

public section

namespace TauCeti

open MeasureTheory ProbabilityTheory Polynomial

open scoped NNReal ENNReal

/-! ## Parity of the probabilists' Hermite polynomials -/

/-- **Parity of the Hermite polynomials.** `Hₙ(-x) = (-1)ⁿ Hₙ(x)` in any commutative ring: a
coefficient of `hermite n` in degree `k` can be nonzero only when `n + k` is even
(`Polynomial.coeff_hermite_of_odd_add`), so `k` and `n` share parity and `(-x)ᵏ = (-1)ⁿ xᵏ` on every
surviving monomial. -/
theorem aeval_neg_hermite {R : Type*} [CommRing R] (n : ℕ) (x : R) :
    aeval (-x) (hermite n) = (-1) ^ n * aeval x (hermite n) := by
  rw [aeval_eq_sum_range, aeval_eq_sum_range, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hodd : Odd (n + k)
  · rw [coeff_hermite_of_odd_add hodd]; simp
  · rw [Nat.not_odd_iff_even] at hodd
    rw [zsmul_eq_mul, zsmul_eq_mul]
    have hpow : (-x) ^ k = (-1) ^ n * x ^ k := by
      rcases Nat.even_or_odd n with hn | hn
      · rw [Even.neg_pow ((Nat.even_add.mp hodd).mp hn), Even.neg_one_pow hn, one_mul]
      · have hk : Odd k := Nat.not_even_iff_odd.mp fun hke =>
          (Nat.not_even_iff_odd.mpr hn) ((Nat.even_add.mp hodd).mpr hke)
        rw [Odd.neg_pow hk, Odd.neg_one_pow hn]; ring
    rw [hpow]; ring

/-! ## Integrability of a polynomial against a Gaussian envelope -/

/-- A real polynomial evaluated pointwise, times a Gaussian envelope `exp(-x²/(2v))` of positive
variance `v`, is Lebesgue-integrable. Transported from the polynomial's integrability against the
Gaussian measure `gaussianReal 0 v` (finite moments of all orders) across
`gaussianReal 0 v = volume.withDensity (gaussianPDF 0 v)`. -/
theorem integrable_eval_mul_gaussianEnvelope (q : ℝ[X]) {w : ℝ≥0} (hw : w ≠ 0) :
    Integrable (fun x : ℝ => q.eval x * Real.exp (-x ^ 2 / (2 * (w : ℝ)))) volume := by
  have hint : Integrable (fun x : ℝ => q.eval x) (gaussianReal 0 w) :=
    integrable_eval_of_forall_integrable_pow (fun k => integrable_pow_gaussianReal 0 w k) q
  rw [gaussianReal_of_var_ne_zero 0 hw,
    integrable_withDensity_iff (measurable_gaussianPDF 0 w)
      (ae_of_all _ fun _ => ENNReal.ofReal_lt_top)] at hint
  simp only [toReal_gaussianPDF] at hint
  have hw' : (0 : ℝ) < (w : ℝ) := NNReal.coe_pos.mpr (zero_lt_iff.mpr hw)
  have hsqrt : Real.sqrt (2 * Real.pi * (w : ℝ)) ≠ 0 :=
    (Real.sqrt_pos.mpr (by positivity)).ne'
  refine (hint.const_mul (Real.sqrt (2 * Real.pi * (w : ℝ)))).congr (ae_of_all _ fun x => ?_)
  simp only [gaussianPDFReal_def, sub_zero]
  field_simp

/-- A real polynomial times the envelope `exp(-x²)` is Lebesgue-integrable — the `v = ½` case of
`integrable_eval_mul_gaussianEnvelope`, the shape of `ψₙ²`. -/
theorem integrable_eval_mul_exp_neg_sq (q : ℝ[X]) :
    Integrable (fun x : ℝ => q.eval x * Real.exp (-x ^ 2)) volume := by
  have h := integrable_eval_mul_gaussianEnvelope q (w := 2⁻¹) (by norm_num)
  have he : (2 : ℝ) * ((2⁻¹ : ℝ≥0) : ℝ) = 1 := by push_cast; norm_num
  simpa only [he, div_one] using h

/-! ## `L¹` and `L²` membership of the Hermite functions -/

/-- The polynomial `Hₙ(·√2)`, real-evaluated, as a composition whose `eval` is `aeval (·√2)`. -/
private lemma eval_hermiteComp (n : ℕ) (x : ℝ) :
    (((hermite n).map (Int.castRingHom ℝ)).comp (X * Polynomial.C (Real.sqrt 2))).eval x
      = aeval (x * Real.sqrt 2) (hermite n) := by
  rw [eval_comp, eval_mul, eval_X, eval_C, aeval_def, algebraMap_int_eq, ← eval_map]

/-- **Target A2 (`L¹`).** Each Hermite function is integrable against Lebesgue measure: it is a
polynomial in `x` times the Gaussian envelope `exp(-x²/2)`, the `v = 1` case of
`integrable_eval_mul_gaussianEnvelope`. -/
theorem integrable_hermiteFunction (n : ℕ) : Integrable (hermiteFunction n) volume := by
  have h := integrable_eval_mul_gaussianEnvelope
    (((hermite n).map (Int.castRingHom ℝ)).comp (X * Polynomial.C (Real.sqrt 2))) (w := 1)
    one_ne_zero
  have hfun : hermiteFunction n = fun x =>
      (((hermite n).map (Int.castRingHom ℝ)).comp (X * Polynomial.C (Real.sqrt 2))).eval x
        * Real.exp (-x ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)))
        / Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) := by
    funext x
    rw [hermiteFunction_def, ← eval_hermiteComp,
      show (-(x ^ 2 / 2) : ℝ) = -x ^ 2 / (2 * ((1 : ℝ≥0) : ℝ)) by push_cast; ring]
  rw [hfun]
  exact h.div_const _

/-- **Target A2 (`L²`).** Each Hermite function lies in `L²(volume)`. Its square is
`(Hₙ(x√2))² exp(-x²)` up to the constant `(n!√π)`, integrable by `integrable_eval_mul_exp_neg_sq`,
and `L²` membership is integrability of the square (`memLp_two_iff_integrable_sq`). This is the
membership `hermiteFunctionLp` needs to realize `ψₙ` as an element of `Lp ℝ 2 volume`. -/
theorem memLp_two_hermiteFunction (n : ℕ) : MemLp (hermiteFunction n) 2 volume := by
  rw [memLp_two_iff_integrable_sq (continuous_hermiteFunction n).aestronglyMeasurable]
  have hfun : (fun x => hermiteFunction n x ^ 2) = fun x =>
      ((((hermite n).map (Int.castRingHom ℝ)).comp (X * Polynomial.C (Real.sqrt 2))) ^ 2).eval x
        * Real.exp (-x ^ 2)
        / Real.sqrt ((n.factorial : ℝ) * Real.sqrt Real.pi) ^ 2 := by
    funext x
    have henv : Real.exp (-(x ^ 2 / 2)) ^ 2 = Real.exp (-x ^ 2) := by
      rw [pow_two, ← Real.exp_add]; congr 1; ring
    rw [hermiteFunction_def, div_pow, mul_pow, henv, eval_pow, eval_hermiteComp]
  rw [hfun]
  exact (integrable_eval_mul_exp_neg_sq _).div_const _

/-! ## Parity of the Hermite functions -/

/-- **Target A2 (parity).** `ψₙ(-x) = (-1)ⁿ ψₙ(x)`: the Gaussian envelope `exp(-x²/2)` is even and
the polynomial factor `Hₙ(x√2)` carries the parity of `Hₙ` (`aeval_neg_hermite`). -/
theorem hermiteFunction_neg (n : ℕ) (x : ℝ) :
    hermiteFunction n (-x) = (-1) ^ n * hermiteFunction n x := by
  have h1 : (-x) * Real.sqrt 2 = -(x * Real.sqrt 2) := by ring
  have h2 : ((-x) ^ 2 / 2 : ℝ) = x ^ 2 / 2 := by ring
  rw [hermiteFunction_def, hermiteFunction_def, h1, aeval_neg_hermite, h2]
  ring

end TauCeti
