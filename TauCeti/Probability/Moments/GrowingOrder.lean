/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.PSeries
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import TauCeti.Analysis.SpecialFunctions.Pow.Real
import TauCeti.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Almost sure upper bounds from moments of growing order

Let `Z n` be integrable and almost everywhere nonnegative with `c ^ k n ≤ Z n` almost everywhere on
`{c ≤ Y n}` for all large `n`, where the order `k n` may depend on `n`; this holds for every
`c ≥ 0` when `|Y n| ^ k n ≤ Z n`. At a threshold `c > 0`, Markov's inequality for `Z n` at the
level `c ^ k n` turns summability of the normalized moments `(∫ Z n) / c ^ k n` into a summable
eventual majorant for the exceedance measures `μ {Y n ≥ c}`. The summability holds when
`∫ Z n ≤ C (n + 1) ^ d t ^ k n` at a rate `0 < t < c`, provided the orders satisfy
`k n ≥ B log (n + 1)` with `d + 1 < B log (c / t)`; orders growing faster than `log n` satisfy
this for every `B`.

If for every `c > L ≥ 0` there are such orders and functions, which may depend on `c`, the first
Borel–Cantelli lemma shows that almost surely `Y n` is eventually below every `c > L`, that is,
`limsup Y n ≤ L`. This is how the trace method bounds largest eigenvalues of random matrices
almost surely: `Y n` is the norm or the largest eigenvalue, and `Z n` is the trace of the
`k n`-th power. The level form of the comparison covers zero orders on empty matrices, where
`|Y n| ^ 0 = 1` exceeds the trace `0`.

## Main statements

* `TauCeti.exists_tsum_lt_top_and_eventually_measure_ge_le_of_summable_integral_div_pow`: the
  summable exceedance majorant at one threshold from summable normalized moments.
* `TauCeti.exists_tsum_lt_top_and_eventually_measure_ge_le_of_integral_le_mul_rpow_mul_pow`: the
  same from a moment bound with a polynomial prefactor and logarithmic orders.
* `TauCeti.ae_forall_eventually_lt_of_summable_integral_div_pow`: the almost sure bound
  `limsup Y n ≤ L` with orders and functions chosen per threshold.

## References

* Z. Bai and J. W. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*,
  2nd ed., Springer (2010), Chapter 5.
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {Y Z : ℕ → Ω → ℝ} {k : ℕ → ℕ} {c L : ℝ}

/-- **Summable exceedance majorant from summable moments of growing order.** Let `0 < c`, and for
all large `n` let `Z n` be integrable and almost everywhere nonnegative with `c ^ k n ≤ Z n` almost
everywhere on `{c ≤ Y n}`. If the normalized moments `(∫ Z n) / c ^ k n` are summable, then the
measures of the sets `{ω | c ≤ Y n ω}` are eventually bounded by a series with finite sum. -/
theorem exists_tsum_lt_top_and_eventually_measure_ge_le_of_summable_integral_div_pow
    (hc : 0 < c) (hYZ : ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, c ≤ Y n ω → c ^ k n ≤ Z n ω)
    (hZ₀ : ∀ᶠ n in atTop, 0 ≤ᵐ[μ] Z n) (hZ : ∀ᶠ n in atTop, Integrable (Z n) μ)
    (hsum : Summable fun n ↦ (∫ ω, Z n ω ∂μ) / c ^ k n) :
    ∃ b : ℕ → ℝ≥0∞, (∑' n, b n) < ∞ ∧ ∀ᶠ n in atTop, μ {ω | c ≤ Y n ω} ≤ b n := by
  -- The summable majorant is `ofReal ((∫ Z n) / c ^ k n)`.
  refine ⟨fun n ↦ ENNReal.ofReal ((∫ ω, Z n ω ∂μ) / c ^ k n), hsum.tsum_ofReal_lt_top, ?_⟩
  -- Markov's inequality for `Z n` at the level `c ^ k n` bounds each exceedance probability.
  filter_upwards [hYZ, hZ₀, hZ] with n hYZn hZ₀n hZn
  have hsub : {ω | c ≤ Y n ω} ≤ᵐ[μ] {ω | c ^ k n ≤ Z n ω} := hYZn.mono fun _ h ↦ h
  refine (measure_mono_ae hsub).trans ?_
  rw [← integral_div]
  exact (hZn.div_const _).measure_le_integral
    (hZ₀n.mono fun _ h ↦ div_nonneg h (pow_nonneg hc.le _))
    fun _ hω ↦ (one_le_div (pow_pos hc _)).2 hω

/-- **Summable exceedance majorant from moments of logarithmic order.** Let `0 < t < c`, and for
all large `n` let `Z n` be integrable and almost everywhere nonnegative with `c ^ k n ≤ Z n` almost
everywhere on `{c ≤ Y n}`. Suppose that eventually `k n ≥ B * log (n + 1)` and
`∫ Z n ≤ C * (n + 1) ^ d * t ^ k n`, where `d + 1 < B * log (c / t)`. Then the measures of the
sets `{ω | c ≤ Y n ω}` are eventually bounded by a series with finite sum. -/
theorem exists_tsum_lt_top_and_eventually_measure_ge_le_of_integral_le_mul_rpow_mul_pow
    {t B C d : ℝ} (ht : 0 < t) (htc : t < c) (hB : d + 1 < B * Real.log (c / t))
    (hk : ∀ᶠ n : ℕ in atTop, B * Real.log (n + 1) ≤ k n)
    (hYZ : ∀ᶠ n in atTop, ∀ᵐ ω ∂μ, c ≤ Y n ω → c ^ k n ≤ Z n ω)
    (hZ₀ : ∀ᶠ n in atTop, 0 ≤ᵐ[μ] Z n) (hZ : ∀ᶠ n in atTop, Integrable (Z n) μ)
    (hbound : ∀ᶠ n : ℕ in atTop, ∫ ω, Z n ω ∂μ ≤ C * (n + 1 : ℝ) ^ d * t ^ k n) :
    ∃ b : ℕ → ℝ≥0∞, (∑' n, b n) < ∞ ∧ ∀ᶠ n in atTop, μ {ω | c ≤ Y n ω} ≤ b n := by
  have hc := ht.trans htc
  refine exists_tsum_lt_top_and_eventually_measure_ge_le_of_summable_integral_div_pow hc hYZ hZ₀
    hZ ?_
  -- The normalized moments are eventually at most `|C| * (n + 1) ^ e` with `e < -1`.
  let e := d + B * Real.log (t / c)
  have he : e < -1 := by
    dsimp only [e]
    rw [Real.log_div ht.ne' hc.ne']
    rw [Real.log_div hc.ne' ht.ne'] at hB
    linarith
  have hsum : Summable fun n : ℕ ↦ |C| * ((n : ℝ) + 1) ^ e := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      ((summable_nat_add_iff 1).2 (Real.summable_nat_rpow.2 he)).mul_left |C|
  refine hsum.of_norm_bounded_eventually_nat ?_
  filter_upwards [hbound, hk, hZ₀] with n hn hkn hZ₀n
  rw [Real.norm_of_nonneg (div_nonneg (integral_nonneg_of_ae hZ₀n) (pow_nonneg hc.le _))]
  calc (∫ ω, Z n ω ∂μ) / c ^ k n ≤ |C| * ((n + 1 : ℝ) ^ d * (t / c) ^ k n) := by
        have habs : C * (n + 1 : ℝ) ^ d * t ^ k n ≤ |C| * (n + 1 : ℝ) ^ d * t ^ k n :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)) (by positivity)
        refine (div_le_div_of_nonneg_right (hn.trans habs) (by positivity)).trans_eq ?_
        rw [div_pow]
        ring
    _ ≤ |C| * ((n : ℝ) + 1) ^ e :=
        mul_le_mul_of_nonneg_left (rpow_mul_pow_le_rpow_of_log_le
          (le_add_of_nonneg_left (Nat.cast_nonneg _)) (div_pos ht hc) ((div_le_one hc).2 htc.le)
          hkn le_rfl) (abs_nonneg C)

/-- **Almost sure upper bounds from summable moments of growing order.** Let `0 ≤ L`. Suppose
that for every `c > L` there are orders `k n` and functions `Z n`, which may depend on `c`, such
that for all large `n` the function `Z n` is integrable and almost everywhere nonnegative with
`c ^ k n ≤ Z n` almost everywhere on `{c ≤ Y n}`, and the normalized moments `(∫ Z n) / c ^ k n`
are summable. Then almost surely `Y n` is eventually below every `c > L`. -/
theorem ae_forall_eventually_lt_of_summable_integral_div_pow (hL : 0 ≤ L)
    (h : ∀ c > L, ∃ (k : ℕ → ℕ) (Z : ℕ → Ω → ℝ),
      (∀ᶠ n in atTop, ∀ᵐ ω ∂μ, c ≤ Y n ω → c ^ k n ≤ Z n ω) ∧ (∀ᶠ n in atTop, 0 ≤ᵐ[μ] Z n) ∧
      (∀ᶠ n in atTop, Integrable (Z n) μ) ∧ Summable fun n ↦ (∫ ω, Z n ω ∂μ) / c ^ k n) :
    ∀ᵐ ω ∂μ, ∀ c > L, ∀ᶠ n in atTop, Y n ω < c := by
  refine TauCeti.MeasureTheory.ae_forall_eventually_lt_of_eventually_measure_le fun c hc ↦ ?_
  obtain ⟨k, Z, hYZ, hZ₀, hZ, hsum⟩ := h c hc
  exact exists_tsum_lt_top_and_eventually_measure_ge_le_of_summable_integral_div_pow
    (hL.trans_lt hc) hYZ hZ₀ hZ hsum

end TauCeti
