/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
import Mathlib.Analysis.Convex.Integral
import TauCeti.Analysis.Bochner.CharFun.Basic
import TauCeti.MeasureTheory.Measure.CharacteristicFunction.Wiener

/-!
# The modulus of a characteristic function through the symmetrized law

For a probability measure `μ` on `ℝ`, let `ρ` be the symmetrized law: the law of `x - y` under
`μ ⊗ μ`. The squared modulus of the characteristic function of `μ` is the characteristic function
of `ρ`, which is real: `‖charFun μ t‖ ^ 2 = ∫ w, cos (t * w) ∂ρ`
(`TauCeti.norm_charFun_sq_eq_integral_cos_mul`).

With the elementary inequality `x ≤ exp (-(1 - x ^ 2) / 2)` for `x ≥ 0`, this bounds a product
of moduli `∏ k ∈ s, ‖charFun μ (c k)‖` by
`exp (-(1 / 2) * ∫ w, ∑ k ∈ s, (1 - cos (c k * w)) ∂ρ)`. Restricting the integral to a set `A` and
applying Jensen's inequality to the average over `A` gives the bound
`Finset.prod_norm_charFun_le_setAverage_exp` by the `ρ`-average over `A` of
`exp (-(ρ A / 2) * ∑ k ∈ s, (1 - cos (c k * w)))`. Take for `A` the set where `|w| ≥ 1`, which
has `ρ`-mass at least `b` when every open ball of radius `1` has `μ`-mass at most `1 - b`
(`TauCeti.le_measureReal_map_sub_prod_setOf_le_abs`). The integral of such a product over an
interval of frequencies is then bounded through the integrals of
`exp (-(ρ A / 2) * ∑ k ∈ s, (1 - cos (c k * w)))` at fixed `w` with `|w| ≥ 1`, which can be
estimated through the arithmetic structure of the `c k`. This is the conditioning argument by
which Rudelson and Vershynin bound the small-ball probabilities of weighted sums of independent
identically distributed variables.

## References

* M. Rudelson and R. Vershynin, *Smallest singular value of a random rectangular matrix*,
  Comm. Pure Appl. Math. 62 (2009), §3.1, proof of Theorem 3.3, where the argument is credited
  to O. Friedland and S. Sodin; see also their *Bounds on the concentration function in terms of
  Diophantine approximation*, C. R. Math. Acad. Sci. Paris 345 (2007), 513–518.
-/

public section

open MeasureTheory Complex
open scoped ComplexConjugate

namespace TauCeti

variable {μ : Measure ℝ}

/-- The squared modulus of the characteristic function of a finite measure `μ` on `ℝ` is the
integral of `cos (t * w)` against the law of `x - y` under `μ ⊗ μ`. -/
theorem norm_charFun_sq_eq_integral_cos_mul [IsFiniteMeasure μ] (t : ℝ) :
    ‖charFun μ t‖ ^ 2 = ∫ w, Real.cos (t * w) ∂((μ.prod μ).map fun p ↦ p.1 - p.2) := by
  rw [integral_cos_mul_eq_re_charFun, charFun_map_sub_prod, mul_conj, ← normSq_eq_norm_sq,
    ofReal_re]

/-- For `c ≥ 0`, `exp (-(c * ∑ k ∈ s, (1 - cos (x k))))` is at most `1`, as each `1 - cos (x k)` is
nonnegative. This bounds the integrand of the conditioning bound
`Finset.prod_norm_charFun_le_setAverage_exp`. -/
theorem _root_.Finset.exp_neg_mul_sum_one_sub_cos_le_one {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    {c : ℝ} (hc : 0 ≤ c) : Real.exp (-(c * ∑ k ∈ s, (1 - Real.cos (x k)))) ≤ 1 :=
  Real.exp_le_one_iff.2 <| neg_nonpos.2 <|
    mul_nonneg hc <| Finset.sum_nonneg fun _ _ ↦ sub_nonneg.2 (Real.cos_le_one _)

/-- If every open ball of radius `r` has `μ`-mass at most `1 - b`, then the law of `x - y` under
`μ ⊗ μ` gives mass at least `b` to the set where `r ≤ |w|`. -/
theorem le_measureReal_map_sub_prod_setOf_le_abs [IsProbabilityMeasure μ] {b r : ℝ}
    (hb : ∀ v, μ.real (Metric.ball v r) ≤ 1 - b) :
    b ≤ ((μ.prod μ).map fun p ↦ p.1 - p.2).real {w | r ≤ |w|} := by
  set ρ := (μ.prod μ).map fun p : ℝ × ℝ ↦ p.1 - p.2
  have hA : MeasurableSet {w : ℝ | r ≤ |w|} :=
    measurableSet_le measurable_const continuous_abs.measurable
  -- The slice of `{w | |w| < r}` over `x` is the open ball of radius `r` about `x`.
  have hAc : ρ.real {w : ℝ | r ≤ |w|}ᶜ ≤ 1 - b := by
    have hb1 : 0 ≤ 1 - b := measureReal_nonneg.trans (hb 0)
    refine ENNReal.toReal_le_of_le_ofReal hb1 ?_
    rw [Measure.map_apply measurable_sub hA.compl, Measure.prod_apply (measurable_sub hA.compl)]
    refine (lintegral_mono fun x ↦ ?_).trans_eq (by rw [lintegral_const, measure_univ, mul_one])
    refine (measure_mono fun y hy ↦ ?_).trans
      ((ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _) hb1).2 (hb x))
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_ofPred_eq, not_le] at hy
    rw [Metric.mem_ball, Real.dist_eq, abs_sub_comm]
    exact hy
  rw [probReal_compl_eq_one_sub hA] at hAc
  linarith

/-- **The conditioning bound.** Let `ρ` be the law of `x - y` under `μ ⊗ μ` for a probability
measure `μ` on `ℝ`. For real points `c k`, `k ∈ s`, and a set `A` of positive `ρ`-measure, the
product of the moduli of the characteristic function of `μ` at the points `c k` is at most the
`ρ`-average over `A` of `exp (-(ρ A / 2) * ∑ k ∈ s, (1 - cos (c k * w)))`. -/
theorem _root_.Finset.prod_norm_charFun_le_setAverage_exp {ι : Type*} [IsProbabilityMeasure μ]
    (s : Finset ι) (c : ι → ℝ) {A : Set ℝ} (hρA : (μ.prod μ).map (fun p ↦ p.1 - p.2) A ≠ 0) :
    ∏ k ∈ s, ‖charFun μ (c k)‖ ≤ ⨍ w in A, Real.exp (-(((μ.prod μ).map fun p ↦ p.1 - p.2).real A
      / 2 * ∑ k ∈ s, (1 - Real.cos (c k * w)))) ∂((μ.prod μ).map fun p ↦ p.1 - p.2) := by
  set ρ := (μ.prod μ).map fun p : ℝ × ℝ ↦ p.1 - p.2
  have hcos : ∀ u : ℝ, Integrable (fun w ↦ Real.cos (u * w)) ρ := fun u ↦
    Integrable.of_bound (by fun_prop) 1
      (ae_of_all _ fun w ↦ (Real.norm_eq_abs _).trans_le (Real.abs_cos_le_one _))
  have hcos₁ : ∀ u : ℝ, Integrable (fun w ↦ 1 - Real.cos (u * w)) ρ := fun u ↦
    (integrable_const 1).sub (hcos u)
  -- Each factor `x = ‖charFun μ u‖` satisfies `x ≤ exp (-(1 - x ^ 2) / 2)`, as
  -- `x ^ 2 ≤ exp (x ^ 2 - 1)`.
  have hfactor : ∀ u : ℝ,
      ‖charFun μ u‖ ≤ Real.exp (-(∫ w, (1 - Real.cos (u * w)) ∂ρ) / 2) := by
    intro u
    have hsq : ‖charFun μ u‖ ^ 2 = ∫ w, Real.cos (u * w) ∂ρ :=
      norm_charFun_sq_eq_integral_cos_mul u
    rw [integral_sub (integrable_const 1) (hcos u), integral_const, probReal_univ, smul_eq_mul,
      mul_one, ← hsq]
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (Real.exp_nonneg _) two_ne_zero).1 ?_
    have h2 : ((2 : ℕ) : ℝ) * (-(1 - ‖charFun μ u‖ ^ 2) / 2) = ‖charFun μ u‖ ^ 2 - 1 := by
      push_cast
      ring
    rw [← Real.exp_natCast_mul, h2]
    linarith [Real.add_one_le_exp (‖charFun μ u‖ ^ 2 - 1)]
  have hsum : Integrable (fun w ↦ ∑ k ∈ s, (1 - Real.cos (c k * w))) ρ :=
    integrable_finsetSum _ fun k _ ↦ hcos₁ (c k)
  have hnonneg : ∀ w, 0 ≤ ∑ k ∈ s, (1 - Real.cos (c k * w)) := fun w ↦
    Finset.sum_nonneg fun k _ ↦ sub_nonneg.2 (Real.cos_le_one _)
  have hρA' : ρ A ≠ ⊤ := measure_ne_top ρ A
  calc ∏ k ∈ s, ‖charFun μ (c k)‖ ≤
        ∏ k ∈ s, Real.exp (-(∫ w, (1 - Real.cos (c k * w)) ∂ρ) / 2) :=
        Finset.prod_le_prod₀ (fun k _ ↦ norm_nonneg _) fun k _ ↦ hfactor (c k)
    _ = Real.exp (-(∫ w, ∑ k ∈ s, (1 - Real.cos (c k * w)) ∂ρ) / 2) := by
        rw [← Real.exp_sum, integral_finsetSum _ fun k _ ↦ hcos₁ (c k), ← Finset.sum_div,
          Finset.sum_neg_distrib]
    _ ≤ Real.exp (-(∫ w in A, ∑ k ∈ s, (1 - Real.cos (c k * w)) ∂ρ) / 2) := by
        refine Real.exp_le_exp.2 (div_le_div_of_nonneg_right (neg_le_neg ?_) zero_le_two)
        exact setIntegral_le_integral hsum (ae_of_all _ hnonneg)
    _ = Real.exp (⨍ w in A, -(ρ.real A / 2 * ∑ k ∈ s, (1 - Real.cos (c k * w))) ∂ρ) := by
        rw [setAverage_eq, integral_neg, integral_const_mul, smul_eq_mul]
        congr 1
        have : ρ.real A ≠ 0 := (measureReal_ne_zero_iff hρA').2 hρA
        field_simp
    _ ≤ ⨍ w in A, Real.exp (-(ρ.real A / 2 * ∑ k ∈ s, (1 - Real.cos (c k * w)))) ∂ρ :=
        convexOn_exp.map_set_average_le Real.continuous_exp.continuousOn isClosed_univ hρA hρA'
          (ae_of_all _ fun _ ↦ Set.mem_univ _) (hsum.const_mul _).neg.integrableOn
          (Integrable.of_bound (by fun_prop) 1 (ae_of_all _ fun _ ↦
            (Real.norm_of_nonneg (Real.exp_pos _).le).trans_le
              (s.exp_neg_mul_sum_one_sub_cos_le_one _ (by positivity)))).integrableOn

end TauCeti
