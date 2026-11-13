/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.BetaGas.Basic
import Mathlib.MeasureTheory.Integral.Asymptotics

import TauCeti.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# Normalizability of the finite beta gas

For a continuous potential, `0 < β ≤ β'`, and `1 < β'`, the weight is integrable if
`2 * β' / β < liminf_{|x| → ∞} V x / log |x|`, where the liminf is in the extended reals.
The Vandermonde product contributes a coordinate power `β * (n - 1)`; the growth assumption
dominates it by a power with exponent below `-1`, uniformly in `n`. The partition function is
then positive and the beta-gas measure is a probability. The Gaussian case is a specialization.

## References

* G. W. Anderson, A. Guionnet, O. Zeitouni, *An Introduction to Random Matrices*, Cambridge
  University Press (2010), §2.6.1, (2.6.1)–(2.6.2). Their potential `V_AGZ` is `β V / 2`
  in our convention; their threshold `β'` therefore becomes `2 * β' / β`.
-/

public section
noncomputable section

open Asymptotics MeasureTheory Real Set

namespace TauCeti.Probability

/-- Bound the Vandermonde interaction by a product of one-coordinate powers. -/
theorem betaGasVandermonde_le_coord_prod (n : ℕ) {β : ℝ} (hβ : 0 ≤ β)
    (x : Fin n → ℝ) :
    (∏ z ∈ betaGasPairs n, |x z.1 - x z.2| ^ β) ≤
      ∏ i : Fin n, (1 + |x i|) ^ (β * ((n - 1 : ℕ) : ℝ)) := by
  classical
  let f : Fin n → ℝ := fun i => 1 + |x i|
  have hdiff (i j : Fin n) : |x i - x j| ≤ f i * f j := by
    dsimp [f]
    have h := abs_sub_le (x i) 0 (x j)
    simp only [sub_zero, zero_sub, abs_neg] at h
    nlinarith [abs_nonneg (x i), abs_nonneg (x j)]
  have hfst :
      (∏ z ∈ betaGasPairs n, f z.1 ^ β) =
        ∏ i : Fin n, f i ^ (β * ((n - 1 - i.val : ℕ) : ℝ)) := by
    rw [Finset.prod_finset_product (betaGasPairs n) Finset.univ
      (fun i => Finset.Ioi i) (by
        intro z
        simp)]
    simp only [Finset.prod_const, Fin.card_Ioi, f]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  have hsnd :
      (∏ z ∈ betaGasPairs n, f z.2 ^ β) =
        ∏ i : Fin n, f i ^ (β * (i.val : ℝ)) := by
    rw [Finset.prod_finset_product_right (betaGasPairs n) Finset.univ
      (fun i => Finset.Iio i) (by
        intro z
        simp)]
    simp only [Finset.prod_const, Fin.card_Iio, f]
    apply Finset.prod_congr rfl
    intro i _
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  calc
    _ ≤ ∏ z ∈ betaGasPairs n, (f z.1 ^ β * f z.2 ^ β) := by
      apply Finset.prod_le_prod₀
      · intro z _
        positivity
      intro z _
      calc
        |x z.1 - x z.2| ^ β ≤ (f z.1 * f z.2) ^ β :=
          Real.rpow_le_rpow (abs_nonneg _) (hdiff z.1 z.2) hβ
        _ = f z.1 ^ β * f z.2 ^ β :=
          Real.mul_rpow (by positivity) (by positivity)
    _ = (∏ z ∈ betaGasPairs n, f z.1 ^ β) *
        (∏ z ∈ betaGasPairs n, f z.2 ^ β) := Finset.prod_mul_distrib
    _ = ∏ i : Fin n, (f i ^ (β * ((n - 1 - i.val : ℕ) : ℝ)) *
        f i ^ (β * (i.val : ℝ))) := by rw [hfst, hsnd, Finset.prod_mul_distrib]
    _ = ∏ i : Fin n, f i ^ (β * ((n - 1 : ℕ) : ℝ)) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [← Real.rpow_add (by positivity)]
      have hpow : n - 1 - i.val + i.val = n - 1 := by omega
      have hpowR : ((n - 1 - i.val : ℕ) : ℝ) + (i.val : ℝ) =
          ((n - 1 : ℕ) : ℝ) := by exact_mod_cast hpow
      rw [← mul_add, hpowR]

/-- Bound the beta-gas weight by a product of one-coordinate functions. -/
theorem betaGasWeight_le_coord_prod (n : ℕ) {β : ℝ} (hβ : 0 ≤ β)
    (V : ℝ → ℝ)
    (x : Fin n → ℝ) :
    betaGasWeight n β V x ≤
      ∏ i : Fin n, ((1 + |x i|) ^ (β * ((n - 1 : ℕ) : ℝ)) *
        exp (-(β * (n : ℝ) / 2) * V (x i))) := by
  classical
  let pairs := betaGasPairs n
  let a : ℝ := β * (n : ℝ) / 2
  let p : ℝ := β * ((n - 1 : ℕ) : ℝ)
  have hvander : (∏ z ∈ pairs, |x z.1 - x z.2| ^ β) ≤
      ∏ i : Fin n, (1 + |x i|) ^ p :=
    betaGasVandermonde_le_coord_prod n hβ x
  have hexp : exp (-(β * (n : ℝ) / 2) * ∑ i : Fin n, V (x i)) =
      ∏ i : Fin n, exp (-a * V (x i)) := by
    have hdistrib : -(β * (n : ℝ) / 2) * ∑ i : Fin n, V (x i) =
        ∑ i : Fin n, (-a * V (x i)) := by simp [a, Finset.mul_sum]
    rw [hdistrib]
    exact Real.exp_sum _ _
  have hpoint : betaGasWeight n β V x ≤
      ∏ i : Fin n, ((1 + |x i|) ^ p * exp (-a * V (x i))) := by
    rw [betaGasWeight_def]
    rw [hexp]
    calc
      _ ≤ (∏ i : Fin n, exp (-a * V (x i))) *
          (∏ i : Fin n, (1 + |x i|) ^ p) := by
        exact mul_le_mul_of_nonneg_left hvander (by positivity)
      _ = ∏ i : Fin n, ((1 + |x i|) ^ p * exp (-a * V (x i))) := by
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro i _
        ring
  exact hpoint

/-- For a continuous potential and `0 < β ≤ β'` with `1 < β'`, the beta-gas weight is
integrable if eventually as `|x| → ∞`, `2 * β' / β < V x / log |x|`. -/
theorem integrable_betaGasWeight_of_eventually_lt_div_log (n : ℕ) {β β' : ℝ}
    (hβ : 0 < β)
    (hβ' : 1 < β') (hββ' : β ≤ β') {V : ℝ → ℝ} (hV : Continuous V)
    (hRatio : ∀ᶠ x in Filter.comap (fun x : ℝ => |x|) Filter.atTop,
      2 * β' / β < V x / log |x|) :
    Integrable (betaGasWeight n β V)
      (volume : Measure (Fin n → ℝ)) := by
  classical
  by_cases hn : n = 0
  · subst n
    simp
  · have hnle : 1 ≤ n := Nat.one_le_iff_ne_zero.mpr hn
    let a : ℝ := β * (n : ℝ) / 2
    let p : ℝ := β * ((n - 1 : ℕ) : ℝ)
    let c : ℝ := 2 * β' / β
    have ha : 0 < a := by
      dsimp [a]
      positivity
    have hq : p - a * c < -1 := by
      have hncast : (n : ℝ) = ((n - 1 : ℕ) : ℝ) + 1 := by
        exact_mod_cast (Nat.sub_add_cancel hnle).symm
      have hformula : p - a * c =
          -β' + ((n - 1 : ℕ) : ℝ) * (β - β') := by
        dsimp [p, a, c]
        rw [hncast]
        field_simp [hβ.ne']
        ring
      rw [hformula]
      have hdiff : β - β' ≤ 0 := sub_nonpos.mpr hββ'
      have hmul : ((n - 1 : ℕ) : ℝ) * (β - β') ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (by positivity) hdiff
      linarith
    have hlarge : ∀ᶠ x in Filter.comap (fun x : ℝ => |x|) Filter.atTop, 1 < |x| := by
      exact Filter.tendsto_comap.eventually (Filter.eventually_gt_atTop 1)
    have hGrowth :
        ∀ᶠ x in Filter.comap (fun x : ℝ => |x|) Filter.atTop, c * log |x| ≤ V x := by
      filter_upwards [hRatio, hlarge] with x hratio hx
      have hlog : 0 < log |x| := Real.log_pos hx
      exact le_of_lt ((lt_div_iff₀ hlog).mp hratio)
    have hmajor : Integrable
        (fun x : Fin n → ℝ =>
          ∏ i, ((1 + |x i|) ^ p * exp (-a * V (x i))))
        (volume : Measure (Fin n → ℝ)) :=
      Integrable.fintype_prod fun _ =>
        integrable_one_add_abs_rpow_mul_exp_neg_of_log_growth
          (by positivity) ha hq hV hGrowth
    apply Integrable.mono' hmajor
      ((continuous_betaGasWeight n hβ.le hV).aestronglyMeasurable)
    filter_upwards with x
    simpa only [Real.norm_eq_abs, abs_of_nonneg (betaGasWeight_nonneg n β V x),
      abs_of_nonneg (by positivity :
        0 ≤ ∏ i : Fin n, ((1 + |x i|) ^ p * exp (-a * V (x i))))] using
      betaGasWeight_le_coord_prod n hβ.le V x

/-- For a continuous potential and `0 < β ≤ β'` with `1 < β'`, the beta-gas weight is
integrable if the liminf of `V x / log |x|` as `|x| → ∞` exceeds `2 * β' / β`.
The liminf is taken in the extended reals. -/
theorem integrable_betaGasWeight_of_lt_liminf_div_log (n : ℕ) {β β' : ℝ} (hβ : 0 < β)
    (hβ' : 1 < β') (hββ' : β ≤ β') {V : ℝ → ℝ} (hV : Continuous V)
    (hliminf :
      ((2 * β' / β : ℝ) : EReal) <
        Filter.liminf (fun x : ℝ => ((V x / log |x| : ℝ) : EReal))
          (Filter.comap (fun x : ℝ => |x|) Filter.atTop)) :
    Integrable (betaGasWeight n β V)
      (volume : Measure (Fin n → ℝ)) := by
  have hratioE : ∀ᶠ x in Filter.comap (fun x : ℝ => |x|) Filter.atTop,
      ((2 * β' / β : ℝ) : EReal) < ((V x / log |x| : ℝ) : EReal) :=
    Filter.eventually_lt_of_lt_liminf hliminf
  have hRatio : ∀ᶠ x in Filter.comap (fun x : ℝ => |x|) Filter.atTop,
      2 * β' / β < V x / log |x| := by
    filter_upwards [hratioE] with x hx
    exact EReal.coe_lt_coe_iff.mp hx
  exact integrable_betaGasWeight_of_eventually_lt_div_log n hβ hβ' hββ' hV hRatio

/-- For `0 < β ≤ β'`, `1 < β'`, and continuous `V` with
`2 * β' / β < liminf_{|x| → ∞} V x / log |x|`, the partition function is positive. -/
theorem betaGasPartitionFunction_pos_of_lt_liminf_div_log (n : ℕ) {β β' : ℝ} (hβ : 0 < β)
    (hβ' : 1 < β') (hββ' : β ≤ β') {V : ℝ → ℝ} (hV : Continuous V)
    (hliminf :
      ((2 * β' / β : ℝ) : EReal) <
        Filter.liminf (fun x : ℝ => ((V x / log |x| : ℝ) : EReal))
          (Filter.comap (fun x : ℝ => |x|) Filter.atTop)) :
    0 < betaGasPartitionFunction n β V := by
  exact betaGasPartitionFunction_pos_of_integrable n β V
    (integrable_betaGasWeight_of_lt_liminf_div_log n hβ hβ' hββ' hV hliminf)

/-- The general-potential beta-gas measure is a probability under the logarithmic-growth
condition. -/
theorem isProbabilityMeasure_betaGasMeasure_of_lt_liminf_div_log (n : ℕ) {β β' : ℝ} (hβ : 0 < β)
    (hβ' : 1 < β') (hββ' : β ≤ β') {V : ℝ → ℝ} (hV : Continuous V)
    (hliminf :
      ((2 * β' / β : ℝ) : EReal) <
        Filter.liminf (fun x : ℝ => ((V x / log |x| : ℝ) : EReal))
          (Filter.comap (fun x : ℝ => |x|) Filter.atTop)) :
    IsProbabilityMeasure (betaGasMeasure n β V) :=
  isProbabilityMeasure_betaGasMeasure n β V
    (integrable_betaGasWeight_of_lt_liminf_div_log n hβ hβ' hββ' hV hliminf)

/-- The Gaussian beta-gas weight is integrable for every positive inverse temperature. -/
theorem integrable_gaussianBetaGasWeight (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    Integrable (gaussianBetaGasWeight n β)
      (volume : Measure (Fin n → ℝ)) := by
  let β' : ℝ := max β 2
  have hβ' : 1 < β' := by
    dsimp [β']
    exact lt_of_lt_of_le one_lt_two (le_max_right _ _)
  have hββ' : β ≤ β' := le_max_left _ _
  have hc : 0 < 2 * β' / β := by positivity
  have hRatio := eventually_quadratic_div_log_abs_gt (2 * β' / β) hc
  rw [gaussianBetaGasWeight_eq_betaGasWeight]
  exact integrable_betaGasWeight_of_eventually_lt_div_log n hβ hβ' hββ' (by fun_prop) (by
    simpa [β'] using hRatio)

/-- The Gaussian beta-gas partition function is strictly positive for positive
inverse temperature. -/
theorem gaussianBetaGasPartitionFunction_pos (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    0 < gaussianBetaGasPartitionFunction n β := by
  rw [gaussianBetaGasPartitionFunction_eq_betaGasPartitionFunction]
  apply betaGasPartitionFunction_pos_of_integrable n β _
  rw [← gaussianBetaGasWeight_eq_betaGasWeight]
  exact integrable_gaussianBetaGasWeight n hβ

/-- The Gaussian beta-gas density integrates to one for positive inverse temperature. -/
@[simp]
theorem integral_gaussianBetaGasPDFReal_eq_one (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    (∫ x, gaussianBetaGasPDFReal n β x
      ∂(volume : Measure (Fin n → ℝ))) = 1 := by
  rw [gaussianBetaGasPDFReal_eq_betaGasPDFReal]
  apply integral_betaGasPDFReal_eq_one
  rw [← gaussianBetaGasPartitionFunction_eq_betaGasPartitionFunction]
  exact gaussianBetaGasPartitionFunction_pos n hβ

/-- The normalized Gaussian beta-gas measure has total mass one for positive
inverse temperature. -/
theorem isProbabilityMeasure_gaussianBetaGasMeasure (n : ℕ) {β : ℝ} (hβ : 0 < β) :
    IsProbabilityMeasure (gaussianBetaGasMeasure n β) := by
  rw [gaussianBetaGasMeasure_eq_betaGasMeasure]
  apply isProbabilityMeasure_betaGasMeasure
  rw [← gaussianBetaGasWeight_eq_betaGasWeight]
  exact integrable_gaussianBetaGasWeight n hβ

end TauCeti.Probability
