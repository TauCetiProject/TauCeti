/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Marcinkiewicz.General
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Interpolating an `L^q`-bounded operator of weak type `(p₀, p₀)`

Let `1 ≤ q < ∞` and let `T : L^q(μ) → L^q(ν)` be a bounded linear operator which is moreover of
**weak type `(p₀, p₀)`** on `L^q` for some `0 < p₀`: for every `f ∈ L^q(μ)` and every height `t`,

`t ^ p₀ · ν {‖T f‖ > t} ≤ A ∫ ‖f‖ ^ p₀ dμ`.

Then `T` is of **strong type `(p, p)`** on `L^q` for every `p₀ < p < q`:

`∫ ‖T f‖ ^ p dν ≤ (p / (p - p₀) · 2 ^ p₀ A + p / (q - p) · 2 ^ q ‖T‖ ^ q) ∫ ‖f‖ ^ p dμ`
(`ContinuousLinearMap.lintegral_rpow_enorm_le_of_rpow_mul_meas_lt_le`).

With `p₀ = 1` and `q = 2` this is the form in which Marcinkiewicz interpolation is used for
singular integral operators, which are given as bounded operators on `L²` and whose weak `(1, 1)`
estimate is proved on `L¹ ∩ L²`. Since `T` is only defined on `L^q`, the operator-level theorem
`TauCeti.lintegral_rpow_le_of_rpow_mul_meas_lt_le`, which needs `T` on all measurable functions,
does not apply directly. Instead `f ∈ L^q` is split at each height `t` into the part where
`‖f‖ > t`, which is again in `L^q` and is controlled by the weak `(p₀, p₀)` bound, and the part
where `‖f‖ ≤ t`, which is controlled by Chebyshev's inequality and the `L^q` bound. This is the
hypothesis of the distributional form `TauCeti.lintegral_rpow_le_of_meas_ofReal_lt_le` with
exponents `p₀` and `q`.

The theorem bounds `T` on the subspace `L^p ∩ L^q` of `L^p`; extending `T` to `L^p` is a
separate step.

## References

* L. Grafakos, *Classical Fourier Analysis*, Theorem 1.3.2 and Theorem 5.3.3.
* E. Stein, *Singular Integrals and Differentiability Properties of Functions*, Chapter I, §4,
  and Chapter II, §2.4.
-/

public section

namespace ContinuousLinearMap

open MeasureTheory Set TauCeti
open scoped ENNReal

variable {α β E F : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α}
  {ν : Measure β} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F] {q : ℝ≥0∞} [Fact (1 ≤ q)]

/-- **Chebyshev's inequality for a bounded operator on `L^q`**: such an operator is of weak type
`(q, q)` with constant `‖T‖ ^ q`. -/
private theorem rpow_mul_meas_lt_enorm_le (T : Lp E q μ →L[ℝ] Lp F q ν) (hq : q ≠ ∞)
    (g : Lp E q μ) (t : ℝ≥0∞) :
    t ^ q.toReal * ν {x | t < ‖T g x‖ₑ} ≤ ‖T‖ₑ ^ q.toReal * ∫⁻ x, ‖g x‖ₑ ^ q.toReal ∂μ := by
  have hq₀ : q ≠ 0 := (zero_lt_one.trans_le Fact.out).ne'
  have hqr : 0 < q.toReal := ENNReal.toReal_pos hq₀ hq
  rw [lintegral_rpow_enorm_eq_rpow_eLpNorm' hqr,
    ← eLpNorm_eq_eLpNorm' hq₀ hq (Lp.aestronglyMeasurable g), ← Lp.enorm_def,
    ← ENNReal.mul_rpow_of_nonneg _ _ hqr.le]
  calc t ^ q.toReal * ν {x | t < ‖T g x‖ₑ}
      ≤ t ^ q.toReal * ν {x | t ≤ ‖T g x‖ₑ} :=
        mul_le_mul_right (measure_mono (ofPred_subset_ofPred.2 fun _ hx => hx.le)) _
    _ ≤ ‖T g‖ₑ ^ q.toReal := by
        rw [Lp.enorm_def]
        exact mul_meas_ge_le_pow_eLpNorm' (μ := ν) hq₀ hq t
    _ ≤ (‖T‖ₑ * ‖g‖ₑ) ^ q.toReal := ENNReal.rpow_le_rpow (T.le_opENorm g) hqr.le

/-- **The splitting step of Marcinkiewicz interpolation** for an `L^q`-bounded operator of weak
type `(p₀, p₀)`. At the height `t`, the part of `f` above `t` is controlled in `L^{p₀}` and the
part below it in `L^q`. -/
private theorem meas_ofReal_lt_enorm_le (T : Lp E q μ →L[ℝ] Lp F q ν) (hq : q ≠ ∞) {A : ℝ≥0∞}
    {p₀ : ℝ} (hp₀ : 0 < p₀)
    (hT : ∀ (f : Lp E q μ) (t : ℝ≥0∞), t ^ p₀ * ν {x | t < ‖T f x‖ₑ} ≤
      A * ∫⁻ x, ‖f x‖ₑ ^ p₀ ∂μ)
    (f : Lp E q μ) {t : ℝ} (ht : 0 < t) :
    ν {x | ENNReal.ofReal t < ‖T f x‖ₑ} ≤
      2 ^ p₀ * A * ENNReal.ofReal (t ^ (-p₀)) *
          ∫⁻ x in {x | ENNReal.ofReal (1 * t) < ‖f x‖ₑ}, ‖f x‖ₑ ^ p₀ ∂μ +
        2 ^ q.toReal * ‖T‖ₑ ^ q.toReal * ENNReal.ofReal (t ^ (-q.toReal)) *
          ∫⁻ x in {x | ‖f x‖ₑ ≤ ENNReal.ofReal (1 * t)}, ‖f x‖ₑ ^ q.toReal ∂μ := by
  have hqr : 0 < q.toReal := ENNReal.toReal_pos (zero_lt_one.trans_le Fact.out).ne' hq
  set s := ENNReal.ofReal t with hs
  set S := {x | s < ‖f x‖ₑ} with hSdef
  have hS : MeasurableSet S :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable f).enorm
  -- Split `f` into its parts above and below the height `t`; both lie in `L^q`.
  have h₁ := (Lp.memLp f).indicator hS.nullMeasurableSet
  have h₂ := (Lp.memLp f).indicator hS.compl.nullMeasurableSet
  set f₁ := h₁.toLp _
  set f₂ := h₂.toLp _
  have hf : f = f₁ + f₂ := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add f₁ f₂, h₁.coeFn_toLp, h₂.coeFn_toLp] with x hx h₁x h₂x
    rw [hx, Pi.add_apply, h₁x, h₂x, indicator_self_add_compl_apply]
  -- Where `‖T f‖ > t`, either `‖T f₁‖ > t / 2` or `‖T f₂‖ > t / 2`.
  have hsub : {x | s < ‖T f x‖ₑ} ≤ᵐ[ν]
      {x | ENNReal.ofReal (t / 2) < ‖T f₁ x‖ₑ} ∪ {x | ENNReal.ofReal (t / 2) < ‖T f₂ x‖ₑ} := by
    filter_upwards [Lp.coeFn_add (T f₁) (T f₂)] with x hx hxt
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hnot hxt
    refine (hxt.trans_le ?_).false
    rw [hf, map_add, hx, Pi.add_apply, hs, ← add_halves t,
      ENNReal.ofReal_add (half_pos ht).le (half_pos ht).le]
    exact (enorm_add_le _ _).trans (add_le_add hnot.1 hnot.2)
  -- The high part by the weak `(p₀, p₀)` bound, the low part by Chebyshev's inequality.
  have hhigh := meas_le_ofReal_rpow_neg_mul_of_rpow_mul_le (half_pos ht) (hT f₁ _)
  have hlow := meas_le_ofReal_rpow_neg_mul_of_rpow_mul_le (half_pos ht)
    (rpow_mul_meas_lt_enorm_le T hq f₂ _)
  have hhalf (r : ℝ) : ENNReal.ofReal ((t / 2) ^ (-r)) = 2 ^ r * ENNReal.ofReal (t ^ (-r)) := by
    rw [Real.div_rpow ht.le zero_le_two, Real.rpow_neg zero_le_two, div_inv_eq_mul,
      ENNReal.ofReal_mul' (by positivity), ← ENNReal.ofReal_rpow_of_pos two_pos, mul_comm]
    simp
  rw [hhalf, lintegral_congr_ae (h₁.coeFn_toLp.mono fun _ hx => by rw [hx]),
    lintegral_enorm_indicator_rpow hS hp₀] at hhigh
  rw [hhalf, lintegral_congr_ae (h₂.coeFn_toLp.mono fun _ hx => by rw [hx]),
    lintegral_enorm_indicator_rpow hS.compl hqr] at hlow
  have hSc : {x | ‖f x‖ₑ ≤ s} = Sᶜ := by ext x; simp [hSdef]
  rw [one_mul, hSc]
  refine (measure_mono_ae hsub).trans ((measure_union_le _ _).trans ?_)
  convert add_le_add hhigh hlow using 2 <;> ring

/-- **Marcinkiewicz interpolation for an `L^q`-bounded operator of weak type `(p₀, p₀)`.** Let
`T : L^q(μ) → L^q(ν)` be a bounded linear operator, `1 ≤ q < ∞`, such that
`t ^ p₀ · ν {‖T f‖ > t} ≤ A ∫ ‖f‖ ^ p₀` for every `f ∈ L^q(μ)` and every `t`. Then for every
`p₀ < p < q` and every `f ∈ L^q(μ)`,

`∫ ‖T f‖ ^ p dν ≤ (p / (p - p₀) · 2 ^ p₀ A + p / (q - p) · 2 ^ q ‖T‖ ^ q) ∫ ‖f‖ ^ p dμ`. -/
theorem lintegral_rpow_enorm_le_of_rpow_mul_meas_lt_le (T : Lp E q μ →L[ℝ] Lp F q ν)
    {A : ℝ≥0∞} {p₀ : ℝ}
    (hT : ∀ (f : Lp E q μ) (t : ℝ≥0∞), t ^ p₀ * ν {x | t < ‖T f x‖ₑ} ≤
      A * ∫⁻ x, ‖f x‖ₑ ^ p₀ ∂μ)
    {p : ℝ} (hp₀ : 0 < p₀) (hlt₀ : p₀ < p) (hlt₁ : p < q.toReal) (f : Lp E q μ) :
    ∫⁻ x, ‖T f x‖ₑ ^ p ∂ν ≤
      (ENNReal.ofReal (p / (p - p₀)) * (2 ^ p₀ * A) +
          ENNReal.ofReal (p / (q.toReal - p)) * (2 ^ q.toReal * ‖T‖ₑ ^ q.toReal)) *
        ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  have hq : q ≠ ∞ := by
    rintro rfl
    simp only [ENNReal.toReal_top] at hlt₁
    linarith
  have h := lintegral_rpow_le_of_meas_ofReal_lt_le (Lp.aestronglyMeasurable f).enorm
    (Lp.aestronglyMeasurable (T f)).enorm hp₀ hlt₀ hlt₁ one_pos
    fun t ht => meas_ofReal_lt_enorm_le T hq hp₀ hT f ht
  simpa only [Real.one_rpow, mul_one] using h

end ContinuousLinearMap
