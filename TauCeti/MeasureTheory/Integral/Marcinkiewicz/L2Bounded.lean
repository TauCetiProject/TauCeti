/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.MeasureTheory.Integral.Marcinkiewicz.General
public import Mathlib.MeasureTheory.Function.LpSpace.Basic

/-!
# Interpolating an `L²`-bounded operator of weak type `(1, 1)`

Let `T : L²(μ) → L²(ν)` be a bounded linear operator which is moreover of **weak type `(1, 1)`**
on `L²`: for every `f ∈ L²(μ)` and every height `t`,

`t · ν {‖T f‖ > t} ≤ A ‖f‖₁`.

Then `T` is of **strong type `(p, p)`** on `L²` for every `1 < p < 2`:

`∫ ‖T f‖ ^ p dν ≤ (2 A p / (p - 1) + 4 ‖T‖² p / (2 - p)) ∫ ‖f‖ ^ p dμ`
(`ContinuousLinearMap.lintegral_rpow_enorm_le_of_mul_meas_lt_le`).

This is the form in which Marcinkiewicz interpolation is used for singular integral operators,
which are given as bounded operators on `L²` and whose weak `(1, 1)` estimate is proved on
`L¹ ∩ L²`. Since `T` is only defined on `L²`, the operator-level theorem
`TauCeti.lintegral_rpow_le_of_rpow_mul_meas_lt_le`, which needs `T` on all measurable functions,
does not apply directly. Instead `f ∈ L²` is split at each height `t` into the part where
`‖f‖ > t`, which is again in `L²` and is controlled by the weak `(1, 1)` bound, and the part where
`‖f‖ ≤ t`, which is controlled by Chebyshev's inequality and the `L²` bound. This is the
hypothesis of the distributional form `TauCeti.lintegral_rpow_le_of_meas_ofReal_lt_le` with
exponents `1` and `2`.

The theorem bounds `T` on the dense subspace `L^p ∩ L²` of `L^p`; extending `T` to `L^p` is a
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
  [NormedSpace ℝ F]

/-- **The splitting step of Marcinkiewicz interpolation** for an `L²`-bounded operator of weak
type `(1, 1)`. At the height `t`, the part of `f` above `t` is controlled in `L¹` and the part
below it in `L²`. -/
private theorem meas_ofReal_lt_enorm_le (T : Lp E 2 μ →L[ℝ] Lp F 2 ν) {A : ℝ≥0∞}
    (hT : ∀ (f : Lp E 2 μ) (t : ℝ≥0∞), t * ν {x | t < ‖T f x‖ₑ} ≤ A * ∫⁻ x, ‖f x‖ₑ ∂μ)
    (f : Lp E 2 μ) {t : ℝ} (ht : 0 < t) :
    ν {x | ENNReal.ofReal t < ‖T f x‖ₑ} ≤
      2 * A * ENNReal.ofReal (t ^ (-1 : ℝ)) *
          ∫⁻ x in {x | ENNReal.ofReal (1 * t) < ‖f x‖ₑ}, ‖f x‖ₑ ^ (1 : ℝ) ∂μ +
        4 * ‖T‖ₑ ^ 2 * ENNReal.ofReal (t ^ (-2 : ℝ)) *
          ∫⁻ x in {x | ‖f x‖ₑ ≤ ENNReal.ofReal (1 * t)}, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
  set s := ENNReal.ofReal t
  have hs0 : s ≠ 0 := (ENNReal.ofReal_pos.2 ht).ne'
  have hs2 : s / 2 ≠ 0 := ENNReal.div_ne_zero.2 ⟨hs0, ENNReal.ofNat_ne_top⟩
  have hs2' : s / 2 ≠ ∞ := ENNReal.div_ne_top ENNReal.ofReal_ne_top two_ne_zero
  set S := {x | s < ‖f x‖ₑ} with hSdef
  have hS : MeasurableSet S :=
    measurableSet_lt measurable_const (Lp.stronglyMeasurable f).enorm
  -- Split `f` into its parts above and below the height `t`; both lie in `L²`.
  have h₁ := (Lp.memLp f).indicator hS.nullMeasurableSet
  have h₂ := (Lp.memLp f).indicator hS.compl.nullMeasurableSet
  set f₁ := h₁.toLp _
  set f₂ := h₂.toLp _
  have hf : f = f₁ + f₂ := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add f₁ f₂, h₁.coeFn_toLp, h₂.coeFn_toLp] with x hx h₁x h₂x
    rw [hx, Pi.add_apply, h₁x, h₂x, indicator_self_add_compl_apply]
  have hint : ∀ (R : Set α), MeasurableSet R → ∀ (q : ℝ), 0 < q → ∀ (g : α → E),
      g =ᵐ[μ] R.indicator f → ∫⁻ x, ‖g x‖ₑ ^ q ∂μ = ∫⁻ x in R, ‖f x‖ₑ ^ q ∂μ := by
    intro R hR q hq g hg
    rw [lintegral_congr_ae (hg.mono fun x hx => by rw [hx]), ← lintegral_indicator hR]
    refine lintegral_congr fun x => ?_
    by_cases hx : x ∈ R <;> simp [hx, hq]
  -- Where `‖T f‖ > t`, either `‖T f₁‖ > t / 2` or `‖T f₂‖ > t / 2`.
  have hsub : {x | s < ‖T f x‖ₑ} ≤ᵐ[ν] {x | s / 2 < ‖T f₁ x‖ₑ} ∪ {x | s / 2 < ‖T f₂ x‖ₑ} := by
    filter_upwards [Lp.coeFn_add (T f₁) (T f₂)] with x hx hxt
    by_contra hnot
    simp only [mem_union, mem_ofPred_eq, not_or, not_lt] at hnot hxt
    refine (hxt.trans_le ?_).false
    rw [hf, map_add, hx, Pi.add_apply, ← ENNReal.add_halves s]
    exact (enorm_add_le _ _).trans (add_le_add hnot.1 hnot.2)
  -- The high part, by the weak `(1, 1)` bound.
  have hhigh : ν {x | s / 2 < ‖T f₁ x‖ₑ} ≤
      2 * A * ENNReal.ofReal (t ^ (-1 : ℝ)) * ∫⁻ x in S, ‖f x‖ₑ ^ (1 : ℝ) ∂μ := by
    have hI : ∫⁻ x, ‖f₁ x‖ₑ ∂μ = ∫⁻ x in S, ‖f x‖ₑ ^ (1 : ℝ) ∂μ := by
      simpa using hint S hS 1 one_pos f₁ h₁.coeFn_toLp
    have hinv : ENNReal.ofReal (t ^ (-1 : ℝ)) = s⁻¹ := by
      rw [Real.rpow_neg_one, ENNReal.ofReal_inv_of_pos ht]
    rw [← ENNReal.mul_le_mul_iff_right hs2 hs2', ← hI, hinv]
    calc s / 2 * ν {x | s / 2 < ‖T f₁ x‖ₑ} ≤ A * ∫⁻ x, ‖f₁ x‖ₑ ∂μ := hT f₁ (s / 2)
      _ = s / 2 * 2 * s⁻¹ * (A * ∫⁻ x, ‖f₁ x‖ₑ ∂μ) := by
        rw [ENNReal.div_mul_cancel two_ne_zero ENNReal.ofNat_ne_top,
          ENNReal.mul_inv_cancel hs0 ENNReal.ofReal_ne_top, one_mul]
      _ = s / 2 * (2 * A * s⁻¹ * ∫⁻ x, ‖f₁ x‖ₑ ∂μ) := by ring
  -- The low part, by Chebyshev's inequality and the `L²` bound.
  have hlow : ν {x | s / 2 < ‖T f₂ x‖ₑ} ≤
      4 * ‖T‖ₑ ^ 2 * ENNReal.ofReal (t ^ (-2 : ℝ)) * ∫⁻ x in Sᶜ, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
    have hI : ‖f₂‖ₑ ^ 2 = ∫⁻ x in Sᶜ, ‖f x‖ₑ ^ (2 : ℝ) ∂μ := by
      rw [← hint Sᶜ hS.compl 2 two_pos f₂ h₂.coeFn_toLp]
      simpa [Lp.enorm_def] using
        eLpNorm_nnreal_pow_eq_lintegral (p := 2) two_ne_zero (Lp.aestronglyMeasurable f₂)
    have hinv : ENNReal.ofReal (t ^ (-2 : ℝ)) = (s ^ 2)⁻¹ := by
      rw [Real.rpow_neg ht.le, Real.rpow_two, ENNReal.ofReal_inv_of_pos (pow_pos ht 2),
        ENNReal.ofReal_pow ht.le]
    have hcheb := mul_meas_ge_le_pow_eLpNorm' (μ := ν) two_ne_zero ENNReal.ofNat_ne_top
      (f := T f₂) (s / 2)
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_ofNat, ← Lp.enorm_def] at hcheb
    rw [← ENNReal.mul_le_mul_iff_right (pow_ne_zero 2 hs2) (ENNReal.pow_ne_top hs2'), ← hI, hinv]
    calc (s / 2) ^ 2 * ν {x | s / 2 < ‖T f₂ x‖ₑ}
        ≤ (s / 2) ^ 2 * ν {x | s / 2 ≤ ‖T f₂ x‖ₑ} :=
          mul_le_mul_right (measure_mono (ofPred_subset_ofPred.2 fun _ hx => hx.le)) _
      _ ≤ ‖T f₂‖ₑ ^ 2 := hcheb
      _ ≤ (‖T‖ₑ * ‖f₂‖ₑ) ^ 2 := pow_le_pow_left₀ zero_le (T.le_opENorm _) 2
      _ = (s / 2 * 2) ^ 2 * (s ^ 2)⁻¹ * (‖T‖ₑ ^ 2 * ‖f₂‖ₑ ^ 2) := by
        rw [ENNReal.div_mul_cancel two_ne_zero ENNReal.ofNat_ne_top,
          ENNReal.mul_inv_cancel (pow_ne_zero 2 hs0) (ENNReal.pow_ne_top ENNReal.ofReal_ne_top),
          one_mul, mul_pow]
      _ = (s / 2) ^ 2 * (4 * ‖T‖ₑ ^ 2 * (s ^ 2)⁻¹ * ‖f₂‖ₑ ^ 2) := by ring
  rw [one_mul]
  have hSc : {x | ‖f x‖ₑ ≤ s} = Sᶜ := by ext x; simp [hSdef]
  rw [hSc]
  exact (measure_mono_ae hsub).trans ((measure_union_le _ _).trans (add_le_add hhigh hlow))

/-- **Marcinkiewicz interpolation for an `L²`-bounded operator of weak type `(1, 1)`.** Let
`T : L²(μ) → L²(ν)` be a bounded linear operator such that `t · ν {‖T f‖ > t} ≤ A ‖f‖₁` for every
`f ∈ L²(μ)` and every `t`. Then for every `1 < p < 2` and every `f ∈ L²(μ)`,

`∫ ‖T f‖ ^ p dν ≤ (p / (p - 1) · 2 A + p / (2 - p) · 4 ‖T‖²) ∫ ‖f‖ ^ p dμ`. -/
theorem lintegral_rpow_enorm_le_of_mul_meas_lt_le (T : Lp E 2 μ →L[ℝ] Lp F 2 ν) {A : ℝ≥0∞}
    (hT : ∀ (f : Lp E 2 μ) (t : ℝ≥0∞), t * ν {x | t < ‖T f x‖ₑ} ≤ A * ∫⁻ x, ‖f x‖ₑ ∂μ)
    {p : ℝ} (hp : 1 < p) (hp' : p < 2) (f : Lp E 2 μ) :
    ∫⁻ x, ‖T f x‖ₑ ^ p ∂ν ≤
      (ENNReal.ofReal (p / (p - 1)) * (2 * A) + ENNReal.ofReal (p / (2 - p)) * (4 * ‖T‖ₑ ^ 2)) *
        ∫⁻ x, ‖f x‖ₑ ^ p ∂μ := by
  have h := lintegral_rpow_le_of_meas_ofReal_lt_le (Lp.aestronglyMeasurable f).enorm
    (Lp.aestronglyMeasurable (T f)).enorm one_pos hp hp' one_pos
    fun t ht => meas_ofReal_lt_enorm_le T hT f ht
  simpa only [Real.one_rpow, mul_one] using h

end ContinuousLinearMap
