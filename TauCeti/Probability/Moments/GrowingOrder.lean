/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import TauCeti.Analysis.SpecificLimits.SuperlogarithmicGeometric
import TauCeti.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Almost sure upper bounds from moments of growing order

Let `|Y n| ^ k n ≤ Z n` with `Z n` integrable, where the order `k n` may depend on `n`. Markov's
inequality at the level `c ^ k n` and the first Borel–Cantelli lemma show that if the normalized
moments `(∫ Z n) / c ^ k n` are summable for every `c > L ≥ 0`, then almost surely `Y n` is
eventually below every `c > L`, that is, `limsup Y n ≤ L`.

The summability holds whenever `∫ Z n ≤ C n ^ a c ^ k n` for every `c > L`, with constants `C` and
`a` that may depend on `c`, and the orders grow faster than `log n`. A moment bound with a
polynomial prefactor and an exponential rate `c` therefore bounds `limsup Y n` by the infimum of
the admissible rates. This is how the trace method bounds largest eigenvalues of random matrices
almost surely: `Y n` is the largest eigenvalue or the norm, and `Z n` is the trace of the
`k n`-th power.

## Main statements

* `TauCeti.ae_forall_eventually_lt_of_summable_integral_div_pow`: the summable form.
* `TauCeti.ae_forall_eventually_lt_of_integral_le_mul_pow`: the form with a polynomial prefactor
  and orders growing faster than `log n`.

## References

* Z. Bai and J. W. Silverstein, *Spectral Analysis of Large Dimensional Random Matrices*,
  2nd ed., Springer (2010), Chapter 5.
-/

public section

open Filter MeasureTheory
open scoped ENNReal Topology

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
  {Y Z : ℕ → Ω → ℝ} {k : ℕ → ℕ} {L : ℝ}

/-- **Almost sure upper bounds from summable moments of growing order.** Let
`|Y n| ^ k n ≤ Z n` almost everywhere with every `Z n` integrable, and `0 ≤ L`. If for every
`c > L` the normalized moments `(∫ Z n) / c ^ k n` are summable, then almost surely `Y n` is
eventually below every `c > L`. -/
theorem ae_forall_eventually_lt_of_summable_integral_div_pow (hL : 0 ≤ L)
    (hYZ : ∀ n, ∀ᵐ ω ∂μ, |Y n ω| ^ k n ≤ Z n ω) (hZ : ∀ n, Integrable (Z n) μ)
    (hsum : ∀ c > L, Summable fun n ↦ (∫ ω, Z n ω ∂μ) / c ^ k n) :
    ∀ᵐ ω ∂μ, ∀ c > L, ∀ᶠ n in atTop, Y n ω < c := by
  have hZ₀ (n : ℕ) : 0 ≤ᵐ[μ] Z n := by
    filter_upwards [hYZ n] with ω hω
    exact (by positivity : 0 ≤ |Y n ω| ^ k n).trans hω
  refine TauCeti.MeasureTheory.ae_forall_eventually_lt_of_tsum_ge_ne_top fun c hc ↦ ?_
  have hc₀ : 0 < c := hL.trans_lt hc
  -- Markov's inequality for `Z n` at the level `c ^ k n` bounds each exceedance probability.
  have hmarkov (n : ℕ) :
      μ {ω | c ≤ Y n ω} ≤ ENNReal.ofReal ((∫ ω, Z n ω ∂μ) / c ^ k n) := by
    have hck : 0 < c ^ k n := pow_pos hc₀ _
    calc μ {ω | c ≤ Y n ω}
        ≤ μ {ω | ENNReal.ofReal (c ^ k n) ≤ ENNReal.ofReal (Z n ω)} :=
          measure_mono_ae <| by
            filter_upwards [hYZ n] with ω hω (hcY : c ≤ Y n ω)
            exact ENNReal.ofReal_le_ofReal
              ((pow_le_pow_left₀ hc₀.le (hcY.trans (le_abs_self _)) _).trans hω)
      _ ≤ (∫⁻ ω, ENNReal.ofReal (Z n ω) ∂μ) / ENNReal.ofReal (c ^ k n) :=
          meas_ge_le_lintegral_div (hZ n).aemeasurable.ennreal_ofReal
            (ENNReal.ofReal_pos.2 hck).ne' ENNReal.ofReal_ne_top
      _ = ENNReal.ofReal ((∫ ω, Z n ω ∂μ) / c ^ k n) := by
          rw [← ofReal_integral_eq_lintegral_ofReal (hZ n) (hZ₀ n),
            ENNReal.ofReal_div_of_pos hck]
  have hnonneg (n : ℕ) : 0 ≤ (∫ ω, Z n ω ∂μ) / c ^ k n :=
    div_nonneg (integral_nonneg_of_ae (hZ₀ n)) (pow_nonneg hc₀.le _)
  refine ne_top_of_le_ne_top ?_ (tsum_le_tsum hmarkov)
  rw [← ENNReal.ofReal_tsum_of_nonneg hnonneg (hsum c hc)]
  exact ENNReal.ofReal_ne_top

/-- **Almost sure upper bounds from moments of growing order.** Let `|Y n| ^ k n ≤ Z n` almost
everywhere with every `Z n` integrable, and `0 ≤ L`. Suppose that the orders `k n` grow faster
than `log n`, and that for every `c > L` there are constants `C` and `a` with
`∫ Z n ≤ C n ^ a c ^ k n` for all large `n`. Then almost surely `Y n` is eventually below every
`c > L`. -/
theorem ae_forall_eventually_lt_of_integral_le_mul_pow (hL : 0 ≤ L)
    (hYZ : ∀ n, ∀ᵐ ω ∂μ, |Y n ω| ^ k n ≤ Z n ω) (hZ : ∀ n, Integrable (Z n) μ)
    (hk : Tendsto (fun n ↦ (k n : ℝ) / Real.log n) atTop atTop)
    (hmom : ∀ c > L, ∃ C : ℝ, ∃ a : ℕ, ∀ᶠ n : ℕ in atTop,
      ∫ ω, Z n ω ∂μ ≤ C * n ^ a * c ^ k n) :
    ∀ᵐ ω ∂μ, ∀ c > L, ∀ᶠ n in atTop, Y n ω < c := by
  refine ae_forall_eventually_lt_of_summable_integral_div_pow hL hYZ hZ fun c hc ↦ ?_
  -- Compare with an intermediate rate `L < c' < c`, at which the moments are controlled.
  obtain ⟨c', hLc', hc'c⟩ := exists_between hc
  have hc'₀ : 0 < c' := hL.trans_lt hLc'
  have hc₀ : 0 < c := hc'₀.trans hc'c
  obtain ⟨C, a, hC⟩ := hmom c' hLc'
  have hZ₀ (n : ℕ) : 0 ≤ ∫ ω, Z n ω ∂μ := integral_nonneg_of_ae <| by
    filter_upwards [hYZ n] with ω hω
    exact (by positivity : 0 ≤ |Y n ω| ^ k n).trans hω
  have hsum : Summable fun n : ℕ ↦ |C| * ((n : ℝ) ^ a * (c' / c) ^ k n) :=
    (summable_pow_mul_pow_of_tendsto_div_log_atTop hk a (div_pos hc'₀ hc₀).le
      ((div_lt_one hc₀).2 hc'c)).mul_left _
  refine hsum.of_norm_bounded_eventually_nat ?_
  filter_upwards [hC] with n hn
  rw [Real.norm_of_nonneg (div_nonneg (hZ₀ n) (pow_nonneg hc₀.le _)), div_le_iff₀ (pow_pos hc₀ _)]
  have hrate : (c' / c) ^ k n * c ^ k n = c' ^ k n := by
    rw [div_pow, div_mul_cancel₀ _ (pow_pos hc₀ _).ne']
  calc ∫ ω, Z n ω ∂μ ≤ C * n ^ a * c' ^ k n := hn
    _ ≤ |C| * ((n : ℝ) ^ a * c' ^ k n) := by
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right (le_abs_self C) (by positivity)
    _ = |C| * ((n : ℝ) ^ a * (c' / c) ^ k n) * c ^ k n := by
      rw [← hrate]
      ring

end TauCeti
