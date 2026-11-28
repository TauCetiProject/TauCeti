/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
public import Mathlib.MeasureTheory.Integral.MeanInequalities
import TauCeti.Analysis.SpecialFunctions.Pow.NNReal
import TauCeti.MeasureTheory.Integral.NormRpow

/-!
# A rank-one operator: off-diagonal interpolation needs `q₀ ≠ q₁`

The off-diagonal Marcinkiewicz theorem `TauCeti.lintegral_rpow_le_of_rpow_mul_meas_lt_le_rpow`
interpolates between a weak type `(p₀, q₀)` bound

`r ^ q₀ * ν {T g > r} ≤ A₀ * (∫⁻ ‖g‖ ^ p₀) ^ (q₀ / p₀)`

and a weak type `(p₁, q₁)` bound for a subadditive operator `T`, and it assumes `p₀ ≠ p₁` and
`q₀ ≠ q₁`. This file shows on the real line that the hypothesis `q₀ ≠ q₁` cannot be dropped.

Let `T` be the rank-one operator `T f (y) = (∫_0^1 f) |y|^{-1/2}`. Its modulus is dominated by
the sublinear operator `rankOneOperator g y = (∫_0^1 |g|) |y|^{-1/2}`, with values in `ℝ≥0∞`
(`eNorm_setIntegral_mul_abs_rpow_le_rankOneOperator`), which equals it for nonnegative `g`
integrable on `[0, 1]`, away from `y = 0`. Since `|y|^{-1/2}` lies in weak `L²` but not in `L²`:

* `rankOneOperator` is subadditive (`rankOneOperator_add_le`);
* it is of weak type `(1, 2)` (`rpow_two_mul_volume_lt_rankOneOperator_le_mul_lintegral_eNorm`)
  and of weak type `(2, 2)`
  (`rpow_two_mul_volume_lt_rankOneOperator_le_mul_lintegral_eNorm_rpow_two`), both with
  constant `2`, in exactly the form of the hypotheses of the off-diagonal theorem;
* it is not of strong type `(4/3, 2)` with any finite constant
  (`not_exists_lintegral_rankOneOperator_rpow_le`), since it maps the indicator of `[0, 1]`, which
  lies in every `Lᵖ`, to `|y|^{-1/2}`, which is not square integrable
  (`TauCeti.setLIntegral_enorm_sub_rpow_eq_top_of_mem_interior`).

The same holds for the linear operator `T` itself: its distribution function obeys the same
bound (`rpow_two_mul_volume_lt_eNorm_setIntegral_mul_abs_rpow_le`), and it is not of strong type
`(4/3, 2)` either (`not_exists_lintegral_eNorm_setIntegral_mul_abs_rpow_le`). The sublinear
operator is the one to which the off-diagonal theorem applies: the Bochner integral vanishes on
functions that are not integrable on `[0, 1]`, so `y ↦ |T f (y)|` is not subadditive on all
measurable functions, as the theorem's hypothesis asks.

With `p₀ = 1`, `p₁ = 2`, `q₀ = q₁ = 2` and `θ = 1/2`, the interpolated exponents are
`1/p = (1 - θ)/1 + θ/2 = 3/4` and `1/q = 1/2`, so `(p, q) = (4/3, 2)`. Every hypothesis of the
off-diagonal theorem except `q₀ ≠ q₁` holds, and its conclusion fails.

## References

* L. Grafakos, *Classical Fourier Analysis*, 3rd ed., Graduate Texts in Mathematics 249, Springer,
  2014, Theorem 1.4.19 (the off-diagonal Marcinkiewicz theorem).
-/

open MeasureTheory Set
open scoped ENNReal

public noncomputable section

namespace TauCeti.Examples.MarcinkiewiczRankOne

/-- The sublinear rank-one operator `g ↦ (∫_0^1 |g|) |y|^{-1/2}` on the real line, with values in
`ℝ≥0∞`. It dominates the modulus of the linear operator `f ↦ (∫_0^1 f) |y|^{-1/2}`, and equals
it for nonnegative functions integrable on `[0, 1]`, away from `y = 0`. -/
def rankOneOperator (g : ℝ → ℝ) (y : ℝ) : ℝ≥0∞ :=
  (∫⁻ x in Icc 0 1, ‖g x‖ₑ) * ‖y‖ₑ ^ (-(1 / 2 : ℝ))

/-- The defining formula of `rankOneOperator`. -/
theorem rankOneOperator_apply (g : ℝ → ℝ) (y : ℝ) :
    rankOneOperator g y = (∫⁻ x in Icc 0 1, ‖g x‖ₑ) * ‖y‖ₑ ^ (-(1 / 2 : ℝ)) :=
  (rfl)

/-- The rank-one operator dominates the modulus of the linear operator
`f ↦ (∫_0^1 f) |y|^{-1/2}`. -/
theorem eNorm_setIntegral_mul_abs_rpow_le_rankOneOperator (g : ℝ → ℝ) (y : ℝ) :
    ‖(∫ x in Icc 0 1, g x) * |y| ^ (-(1 / 2 : ℝ))‖ₑ ≤ rankOneOperator g y := by
  rw [rankOneOperator_apply, eNorm_mul]
  rcases eq_or_ne y 0 with rfl | hy
  · simp
  · gcongr
    · exact eNorm_integral_le_lintegral_eNorm _
    · rw [Real.eNorm_abs_rpow_of_ne_zero hy]

/-- The rank-one operator is subadditive. -/
theorem rankOneOperator_add_le {g : ℝ → ℝ} (hg : AEMeasurable g (volume.restrict (Icc 0 1)))
    (h : ℝ → ℝ) (y : ℝ) :
    rankOneOperator (g + h) y ≤ rankOneOperator g y + rankOneOperator h y := by
  simp only [rankOneOperator_apply, ← add_mul]
  gcongr
  calc ∫⁻ x in Icc 0 1, ‖(g + h) x‖ₑ ≤ ∫⁻ x in Icc 0 1, (‖g x‖ₑ + ‖h x‖ₑ) :=
        lintegral_mono fun x => eNorm_add_le _ _
    _ = _ := lintegral_add_left' hg.eNorm _

/-- For `0 < r < ∞`, the threshold `r < I a^{-1/2}` forces `a < (I / r)²`. -/
private theorem lt_div_rpow_two_of_lt_mul_rpow_neg_half {r I a : ℝ≥0∞} (hr : r ≠ 0)
    (hr' : r ≠ ⊤) (h : r < I * a ^ (-(1 / 2 : ℝ))) : a < (I / r) ^ (2 : ℝ) := by
  -- Multiplying through gives `r a^{1/2} < I`, so `a^{1/2} < I / r`; then square.
  have h₁ : a ^ (1 / 2 : ℝ) < I / r := by
    rw [ENNReal.rpow_neg, ← div_eq_mul_inv, ENNReal.lt_div_iff_mul_lt (Or.inr hr') (Or.inr hr),
      mul_comm] at h
    rwa [ENNReal.lt_div_iff_mul_lt (Or.inl hr) (Or.inl hr')]
  rwa [one_div, ENNReal.rpow_inv_lt_iff two_pos] at h₁

/-- The distribution function of the rank-one operator: `T g` lies in weak `L²`, with
`r² |{T g > r}| ≤ 2 (∫_0^1 |g|)²`. -/
theorem rpow_two_mul_volume_lt_rankOneOperator_le (g : ℝ → ℝ) (r : ℝ≥0∞) :
    r ^ (2 : ℝ) * volume {y | r < rankOneOperator g y} ≤
      2 * (∫⁻ x in Icc 0 1, ‖g x‖ₑ) ^ (2 : ℝ) := by
  simp only [rankOneOperator_apply]
  generalize ∫⁻ x in Icc 0 1, ‖g x‖ₑ = I
  -- The degenerate cases `r = 0` and `r = ∞` are immediate.
  rcases eq_or_ne r 0 with rfl | hr
  · simp [ENNReal.zero_rpow_of_pos two_pos]
  rcases eq_or_ne r ⊤ with rfl | hr'
  · simp
  -- Otherwise `r < I ‖y‖^{-1/2}` forces `‖y‖ < (I / r)²`.
  have hsub : {y : ℝ | r < I * ‖y‖ₑ ^ (-(1 / 2 : ℝ))} ⊆ Metric.eball 0 ((I / r) ^ (2 : ℝ)) :=
    fun y hy => by
      rw [Metric.mem_eball, edist_zero_right]
      exact lt_div_rpow_two_of_lt_mul_rpow_neg_half hr hr' hy
  calc r ^ (2 : ℝ) * volume {y : ℝ | r < I * ‖y‖ₑ ^ (-(1 / 2 : ℝ))}
      ≤ r ^ (2 : ℝ) * volume (Metric.eball (0 : ℝ) ((I / r) ^ (2 : ℝ))) := by
        gcongr
    _ = 2 * I ^ (2 : ℝ) := by
      rw [Real.volume_eball, ENNReal.div_rpow_of_nonneg _ _ zero_le_two, mul_left_comm,
        ENNReal.mul_div_cancel (by positivity) (by finiteness)]

/-- **Weak type `(1, 2)`.** The rank-one operator satisfies the weak type `(1, 2)` bound with
constant `2`, in the form of the hypotheses of the off-diagonal Marcinkiewicz theorem. -/
theorem rpow_two_mul_volume_lt_rankOneOperator_le_mul_lintegral_eNorm (g : ℝ → ℝ) (r : ℝ≥0∞) :
    r ^ (2 : ℝ) * volume {y | r < rankOneOperator g y} ≤
      2 * (∫⁻ x, ‖g x‖ₑ ^ (1 : ℝ)) ^ ((2 : ℝ) / 1) := by
  refine (rpow_two_mul_volume_lt_rankOneOperator_le g r).trans ?_
  simp only [ENNReal.rpow_one, div_one]
  gcongr
  exact Measure.restrict_le_self

/-- **Weak type `(2, 2)`.** The rank-one operator satisfies the weak type `(2, 2)` bound with
constant `2`, in the form of the hypotheses of the off-diagonal Marcinkiewicz theorem. By the
Cauchy–Schwarz inequality, `(∫_0^1 |g|)² ≤ ∫_0^1 |g|²`. -/
theorem rpow_two_mul_volume_lt_rankOneOperator_le_mul_lintegral_eNorm_rpow_two {g : ℝ → ℝ}
    (hg : AEMeasurable g (volume.restrict (Icc 0 1))) (r : ℝ≥0∞) :
    r ^ (2 : ℝ) * volume {y | r < rankOneOperator g y} ≤
      2 * (∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ)) ^ ((2 : ℝ) / 2) := by
  refine (rpow_two_mul_volume_lt_rankOneOperator_le g r).trans ?_
  have hcs : ∫⁻ x in Icc 0 1, ‖g x‖ₑ ≤ (∫⁻ x in Icc 0 1, ‖g x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
    have h := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (Icc (0 : ℝ) 1))
      (Real.HolderConjugate.two_two) hg.eNorm aemeasurable_const (f := fun x => ‖g x‖ₑ)
      (g := fun _ => 1)
    simpa [Real.volume_Icc] using h
  rw [div_self two_ne_zero, ENNReal.rpow_one]
  gcongr 2 * ?_
  calc (∫⁻ x in Icc 0 1, ‖g x‖ₑ) ^ (2 : ℝ)
      ≤ ((∫⁻ x in Icc 0 1, ‖g x‖ₑ ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by gcongr
    _ = ∫⁻ x in Icc 0 1, ‖g x‖ₑ ^ (2 : ℝ) := by rw [← ENNReal.rpow_mul]; norm_num
    _ ≤ ∫⁻ x, ‖g x‖ₑ ^ (2 : ℝ) := setLIntegral_le_lintegral _ _

/-- The function `|y|^{-1}` is not integrable near `0`: `∫ |y|^{-1} dy = ∞` on the real line. -/
private theorem lintegral_eNorm_rpow_neg_one_eq_top : ∫⁻ y : ℝ, ‖y‖ₑ ^ (-1 : ℝ) = ⊤ := by
  simpa using TauCeti.setLIntegral_enorm_sub_rpow_eq_top_of_mem_interior (mu := volume)
    (s := -1) (by simp) (Ω := univ) (x := (0 : ℝ)) (by simp)

/-- The rank-one operator maps the indicator of `[0, 1]` to `|y|^{-1/2}`. -/
theorem rankOneOperator_indicator (y : ℝ) :
    rankOneOperator ((Icc 0 1).indicator 1) y = ‖y‖ₑ ^ (-(1 / 2 : ℝ)) := by
  rw [rankOneOperator_apply, setLIntegral_congr_fun measurableSet_Icc fun x hx => by
    rw [indicator_of_mem hx, Pi.one_apply, eNorm_one]]
  simp [Real.volume_Icc]

/-- The indicator of `[0, 1]` has `∫ |v|^{4/3} = 1`. -/
private theorem lintegral_eNorm_indicator_rpow :
    ∫⁻ x, ‖(Icc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) x‖ₑ ^ (4 / 3 : ℝ) = 1 := by
  have hfun : (fun x => ‖(Icc (0 : ℝ) 1).indicator (1 : ℝ → ℝ) x‖ₑ ^ (4 / 3 : ℝ)) =
      (Icc 0 1).indicator 1 := by
    ext x
    by_cases hx : x ∈ Icc (0 : ℝ) 1 <;> simp [hx]
  rw [hfun, lintegral_indicator_one measurableSet_Icc, Real.volume_Icc]
  norm_num

/-- A bound `∫ (S v)² ≤ C (∫ |v|^{4/3})^{3/2}` for every `v` fails with every finite `C` as soon as
`∫ (S v)² = ∞` for the indicator `v` of `[0, 1]`. -/
private theorem not_exists_of_lintegral_indicator_eq_top {S : (ℝ → ℝ) → ℝ → ℝ≥0∞}
    (hS : ∫⁻ y, S ((Icc 0 1).indicator 1) y ^ (2 : ℝ) = ⊤) :
    ¬ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ v : ℝ → ℝ, AEMeasurable v →
      ∫⁻ y, S v y ^ (2 : ℝ) ≤ C * (∫⁻ x, ‖v x‖ₑ ^ (4 / 3 : ℝ)) ^ ((2 : ℝ) / (4 / 3)) := by
  rintro ⟨C, hC, h⟩
  have hv := h ((Icc 0 1).indicator 1)
    ((aemeasurable_const (b := (1 : ℝ))).indicator measurableSet_Icc)
  rw [hS, lintegral_eNorm_indicator_rpow, ENNReal.one_rpow, mul_one] at hv
  exact hC (top_unique hv)

/-- **Not of strong type `(4/3, 2)`.** No finite constant `C` bounds
`∫ (T v)²` by `C (∫ |v|^{4/3})^{3/2}`: the indicator of `[0, 1]` has `∫ |v|^{4/3} = 1`, and its
image `|y|^{-1/2}` is not square integrable. -/
theorem not_exists_lintegral_rankOneOperator_rpow_le :
    ¬ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ v : ℝ → ℝ, AEMeasurable v →
      ∫⁻ y, rankOneOperator v y ^ (2 : ℝ) ≤
        C * (∫⁻ x, ‖v x‖ₑ ^ (4 / 3 : ℝ)) ^ ((2 : ℝ) / (4 / 3)) := by
  refine not_exists_of_lintegral_indicator_eq_top ?_
  simp_rw [rankOneOperator_indicator, ← ENNReal.rpow_mul]
  norm_num [lintegral_eNorm_rpow_neg_one_eq_top]

/-! ### The linear rank-one operator -/

/-- The distribution function of the linear rank-one operator `f ↦ (∫_0^1 f) |y|^{-1/2}`:
`r² |{|T f| > r}| ≤ 2 (∫_0^1 |f|)²`. As for `rankOneOperator`, this bound gives the weak type
`(1, 2)` and, by the Cauchy–Schwarz inequality, the weak type `(2, 2)` bounds with constant `2`. -/
theorem rpow_two_mul_volume_lt_eNorm_setIntegral_mul_abs_rpow_le (f : ℝ → ℝ) (r : ℝ≥0∞) :
    r ^ (2 : ℝ) * volume {y | r < ‖(∫ x in Icc 0 1, f x) * |y| ^ (-(1 / 2 : ℝ))‖ₑ} ≤
      2 * (∫⁻ x in Icc 0 1, ‖f x‖ₑ) ^ (2 : ℝ) := by
  refine le_trans ?_ (rpow_two_mul_volume_lt_rankOneOperator_le f r)
  gcongr
  exact eNorm_setIntegral_mul_abs_rpow_le_rankOneOperator f _

/-- **The linear rank-one operator is not of strong type `(4/3, 2)`.** No finite constant `C`
bounds `∫ |T f|²` by `C (∫ |f|^{4/3})^{3/2}` for `T f (y) = (∫_0^1 f) |y|^{-1/2}`. -/
theorem not_exists_lintegral_eNorm_setIntegral_mul_abs_rpow_le :
    ¬ ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ f : ℝ → ℝ, AEMeasurable f →
      ∫⁻ y, ‖(∫ x in Icc 0 1, f x) * |y| ^ (-(1 / 2 : ℝ))‖ₑ ^ (2 : ℝ) ≤
        C * (∫⁻ x, ‖f x‖ₑ ^ (4 / 3 : ℝ)) ^ ((2 : ℝ) / (4 / 3)) := by
  refine not_exists_of_lintegral_indicator_eq_top
    (S := fun f y => ‖(∫ x in Icc 0 1, f x) * |y| ^ (-(1 / 2 : ℝ))‖ₑ) ?_
  have hint : ∫ x in Icc (0 : ℝ) 1, (Icc 0 1).indicator (1 : ℝ → ℝ) x = 1 := by
    rw [setIntegral_congr_fun measurableSet_Icc fun x hx => by
      rw [indicator_of_mem hx, Pi.one_apply]]
    simp
  rw [← lintegral_eNorm_rpow_neg_one_eq_top]
  refine lintegral_congr_ae ((Measure.ae_ne volume 0).mono fun y hy => ?_)
  simp only [hint, one_mul]
  rw [Real.eNorm_abs_rpow_of_ne_zero hy, ← ENNReal.rpow_mul]
  norm_num

end TauCeti.Examples.MarcinkiewiczRankOne
