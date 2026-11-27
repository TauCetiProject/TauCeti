/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Moments.IntegrableExpMul

import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
import Mathlib.Probability.Moments.Basic

/-!
# Exponential moments of a statistic that is bounded below, and from even moments

Mathlib's `ProbabilityTheory.integrable_exp_mul_of_le` makes `exp (t * X)` integrable against a
finite measure when `X` is bounded above and the rate `t` is nonnegative. A law carried by a
half-line `[b, ∞)` needs the mirror image: `X` bounded below and `t` nonpositive. Both bounds are
one-sided, so neither statement follows from the two-sided
`ProbabilityTheory.integrable_exp_mul_of_mem_Icc`.

For such a law the remaining question is which positive rates survive, and that is decided by the
tail: if `X` already has an infinite moment of some order, then no positive rate is integrable
either, because an exponential moment on both sides of the origin forces every moment to be
finite. Combining the two statements gives the exponential-moment domain of a heavy-tailed
half-line law, which is `Set.Iic 0`.

Exponential moments of a measure on `ℝ` are also controlled by its even moments: integrating
`cosh (a x) = ∑ₙ (a x)²ⁿ / (2n)!` termwise shows that `∫ e^{a|x|}` is finite as soon as the even
moments are dominated by those of a measure for which it is finite.

## Main results

* `TauCeti.integrable_exp_mul_of_ge` — every nonpositive rate is integrable when `X` is bounded
  below;
* `TauCeti.integrableExpSet_eq_univ_of_mem_Icc` — a bounded real statistic has exponential
  moments at every rate;
* `TauCeti.isFiniteMeasure_of_integrable_exp_mul` — a statistic bounded below with an integrable
  exponential at a nonnegative rate lives on a finite measure;
* `TauCeti.not_integrable_exp_mul_of_not_integrable_rpow` and
  `TauCeti.not_integrable_exp_mul_of_not_integrable_pow` — no positive rate is integrable once a
  real, respectively natural, moment of `X` fails to exist;
* `TauCeti.integrableExpSet_eq_Iic_of_not_integrable_pow` — a statistic bounded below with an
  infinite natural moment has exponential-integrability domain `Set.Iic 0`.
* `TauCeti.lintegral_ofReal_cosh_mul_eq_tsum` — the `cosh` series integrated termwise against any
  measure on `ℝ`.
* `TauCeti.integrable_exp_mul_abs_of_integral_pow_le` — a measure on `ℝ` whose even moments are
  finite and dominated by those of a measure with a finite exponential moment `∫ e^{a|x|}` has
  that exponential moment too. This is how the method of moments transfers exponential moments
  between measures with the same moments.
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X : Ω → ℝ}

/-- An a.e.-measurable real statistic bounded almost surely in a compact interval has exponential
moments at every real rate. -/
theorem integrableExpSet_eq_univ_of_mem_Icc [IsFiniteMeasure μ] {a b : ℝ}
    (hX : AEMeasurable X μ) (hX_mem : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) :
    integrableExpSet X μ = Set.univ := by
  apply Set.eq_univ_of_forall
  exact fun _ ↦ integrable_exp_mul_of_mem_Icc hX hX_mem

/-- **A nonpositive exponential rate is integrable when the statistic is bounded below.** On
`b ≤ X` the integrand `exp (t * X)` is at most `exp (t * b)` for `t ≤ 0`, which a finite measure
integrates. This is the mirror image of `ProbabilityTheory.integrable_exp_mul_of_le`, which bounds
`X` above and asks for a nonnegative rate. -/
theorem integrable_exp_mul_of_ge [IsFiniteMeasure μ] (t b : ℝ) (ht : t ≤ 0)
    (hX : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, b ≤ X ω) :
    Integrable (fun ω ↦ Real.exp (t * X ω)) μ := by
  have h := integrable_exp_mul_of_le (μ := μ) (X := fun ω ↦ -X ω) (-t) (-b)
    (neg_nonneg.mpr ht) hX.neg (hb.mono fun _ hω ↦ neg_le_neg hω)
  simpa only [neg_mul_neg] using h

/-- A statistic bounded below with an integrable exponential at a nonnegative rate lives on a
finite measure: the exponential is bounded below by a positive constant. -/
theorem isFiniteMeasure_of_integrable_exp_mul {b t : ℝ} (hb : ∀ᵐ ω ∂μ, b ≤ X ω)
    (ht : 0 ≤ t) (hexp : Integrable (fun ω ↦ Real.exp (t * X ω)) μ) : IsFiniteMeasure μ := by
  have hc : Integrable (fun _ : Ω ↦ Real.exp (t * b)) μ :=
    hexp.mono' aestronglyMeasurable_const (hb.mono fun ω hω ↦ by
      rw [Real.norm_of_nonneg (Real.exp_pos _).le]
      exact Real.exp_le_exp.mpr (by gcongr))
  exact (integrable_const_iff_isFiniteMeasure (Real.exp_pos _).ne').mp hc

/-- **A statistic bounded below whose moment of order `q` is infinite has no positive exponential
moment.** The nonpositive rates cost nothing here, so a positive rate would give exponential
integrability on both sides of the origin, and that makes every moment finite. -/
theorem not_integrable_exp_mul_of_not_integrable_rpow {b t : ℝ} (q : ℝ)
    (hb : ∀ᵐ ω ∂μ, b ≤ X ω) (hq : 0 ≤ q)
    (hmom : ¬ Integrable (fun ω ↦ X ω ^ q) μ) (ht : 0 < t) :
    ¬ Integrable (fun ω ↦ Real.exp (t * X ω)) μ := fun hexp ↦ by
  have := isFiniteMeasure_of_integrable_exp_mul hb ht.le hexp
  have hX : AEMeasurable X μ := Real.aemeasurable_of_aemeasurable_exp_mul ht.ne' hexp.aemeasurable
  exact hmom <| integrable_rpow_of_integrable_exp_mul ht.ne' hexp
    (integrable_exp_mul_of_ge (-t) b (neg_nonpos.mpr ht.le) hX hb) hq

/-- **A statistic bounded below whose `n`-th moment is infinite has no positive exponential
moment**, the natural-power form of
`TauCeti.not_integrable_exp_mul_of_not_integrable_rpow`. -/
theorem not_integrable_exp_mul_of_not_integrable_pow {b t : ℝ} (n : ℕ)
    (hb : ∀ᵐ ω ∂μ, b ≤ X ω) (hmom : ¬ Integrable (fun ω ↦ X ω ^ n) μ) (ht : 0 < t) :
    ¬ Integrable (fun ω ↦ Real.exp (t * X ω)) μ :=
  not_integrable_exp_mul_of_not_integrable_rpow (n : ℝ) hb (Nat.cast_nonneg n)
    (by simpa only [Real.rpow_natCast] using hmom) ht

/-- A statistic bounded below with a nonintegrable natural power has exponential moments
exactly at nonpositive rates. -/
theorem integrableExpSet_eq_Iic_of_not_integrable_pow [IsFiniteMeasure μ] {b : ℝ}
    (hX : AEMeasurable X μ) (hb : ∀ᵐ ω ∂μ, b ≤ X ω) (n : ℕ)
    (hn : ¬ Integrable (fun ω ↦ X ω ^ n) μ) : integrableExpSet X μ = Set.Iic 0 := by
  ext t
  simp only [integrableExpSet, Set.mem_ofPred_eq, Set.mem_Iic]
  refine ⟨fun h ↦ ?_, fun ht ↦ integrable_exp_mul_of_ge t b ht hX hb⟩
  by_contra ht
  exact not_integrable_exp_mul_of_not_integrable_pow n hb hn (lt_of_not_ge ht) h

/-! ### Exponential moments from even moments -/

/-- **The `cosh` series integrated termwise.** For every measure `ρ` on `ℝ` and every `a`,
`∫⁻ cosh (a x) dρ = ∑ₙ a²ⁿ / (2n)! · ∫⁻ x²ⁿ dρ`, expanding `cosh y = ∑ₙ y²ⁿ / (2n)!`. No
finiteness is needed: both sides may be `∞`. -/
theorem lintegral_ofReal_cosh_mul_eq_tsum (ρ : Measure ℝ) (a : ℝ) :
    ∫⁻ x, ENNReal.ofReal (Real.cosh (a * x)) ∂ρ =
      ∑' n : ℕ, ENNReal.ofReal (a ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) *
        ∫⁻ x, ENNReal.ofReal (x ^ (2 * n)) ∂ρ := by
  have hcoef (n : ℕ) : 0 ≤ a ^ (2 * n) / (Nat.factorial (2 * n) : ℝ) :=
    div_nonneg ((even_two_mul n).pow_nonneg a) (Nat.cast_nonneg _)
  calc ∫⁻ x, ENNReal.ofReal (Real.cosh (a * x)) ∂ρ
      = ∫⁻ x, ∑' n : ℕ, ENNReal.ofReal (a ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) *
          ENNReal.ofReal (x ^ (2 * n)) ∂ρ := by
        refine lintegral_congr fun x ↦ ?_
        rw [Real.cosh_eq_tsum, ENNReal.ofReal_tsum_of_nonneg
          (fun n ↦ div_nonneg ((even_two_mul n).pow_nonneg _) (Nat.cast_nonneg _))
          (Real.hasSum_cosh _).summable]
        refine tsum_congr fun n ↦ ?_
        rw [← ENNReal.ofReal_mul (hcoef n), mul_pow, div_mul_eq_mul_div, mul_comm (a ^ (2 * n))]
    _ = ∑' n : ℕ, ∫⁻ x, ENNReal.ofReal (a ^ (2 * n) / (Nat.factorial (2 * n) : ℝ)) *
          ENNReal.ofReal (x ^ (2 * n)) ∂ρ :=
        lintegral_tsum fun n ↦ by fun_prop
    _ = _ := tsum_congr fun n ↦ lintegral_const_mul _ (by fun_prop)

/-- **Exponential moments from dominated even moments.** If `e^{a|x|}` is integrable against `μ`,
it is integrable against every measure `ν` whose even moments are finite and at most those of
`μ`. -/
theorem integrable_exp_mul_abs_of_integral_pow_le {μ ν : Measure ℝ} {a : ℝ}
    (hμ : Integrable (fun x ↦ Real.exp (a * |x|)) μ)
    (hν : ∀ n : ℕ, Integrable (fun x : ℝ ↦ x ^ (2 * n)) ν)
    (hle : ∀ n : ℕ, ∫ x, x ^ (2 * n) ∂ν ≤ ∫ x, x ^ (2 * n) ∂μ) :
    Integrable (fun x ↦ Real.exp (a * |x|)) ν := by
  have : IsFiniteMeasure ν := by simpa [integrable_const_iff] using hν 0
  rcases lt_or_ge a 0 with ha | ha
  · -- For `a < 0` the integrand is at most `1`.
    refine (integrable_const (1 : ℝ)).mono' (by fun_prop) (ae_of_all _ fun x ↦ ?_)
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
    exact mul_nonpos_of_nonpos_of_nonneg ha.le (abs_nonneg x)
  have hpow (ρ : Measure ℝ) (n : ℕ) : 0 ≤ᵐ[ρ] fun x : ℝ ↦ x ^ (2 * n) :=
    ae_of_all _ fun x ↦ (even_two_mul n).pow_nonneg x
  -- Termwise comparison of the `cosh` series.
  have hcosh : ∫⁻ x, ENNReal.ofReal (Real.cosh (a * x)) ∂ν ≤
      ∫⁻ x, ENNReal.ofReal (Real.cosh (a * x)) ∂μ := by
    rw [lintegral_ofReal_cosh_mul_eq_tsum, lintegral_ofReal_cosh_mul_eq_tsum]
    refine tsum_le_tsum fun n ↦ mul_le_mul_right ?_ _
    rw [← ofReal_integral_eq_lintegral_ofReal (hν n) (hpow ν n)]
    refine (ENNReal.ofReal_le_ofReal (hle n)).trans ?_
    rw [integral_eq_lintegral_of_nonneg_ae (hpow μ n) (by fun_prop)]
    exact ENNReal.ofReal_toReal_le
  -- `e^{a|x|} ≤ 2 cosh (a x)` and `cosh (a x) ≤ e^{a|x|}`, since `a |x| = |a x|`.
  have habs (x : ℝ) : a * |x| = |a * x| := by rw [abs_mul, abs_of_nonneg ha]
  have hexp (x : ℝ) : Real.exp (a * |x|) ≤ 2 * Real.cosh (a * x) := by
    rw [Real.cosh_eq, mul_div_cancel₀ _ two_ne_zero, habs]
    exact Real.exp_abs_le _
  have hcosh_le (x : ℝ) : Real.cosh (a * x) ≤ Real.exp (a * |x|) := by
    rw [← Real.cosh_abs, ← habs, Real.cosh_eq]
    linarith [Real.exp_le_exp.2 (neg_le_self (mul_nonneg ha (abs_nonneg x)))]
  refine ⟨by fun_prop, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (ae_of_all _ fun x ↦ (Real.exp_pos _).le)]
  calc ∫⁻ x, ENNReal.ofReal (Real.exp (a * |x|)) ∂ν
      ≤ ∫⁻ x, 2 * ENNReal.ofReal (Real.cosh (a * x)) ∂ν := by
        refine lintegral_mono fun x ↦ ?_
        rw [← ENNReal.ofReal_ofNat 2, ← ENNReal.ofReal_mul zero_le_two]
        exact ENNReal.ofReal_le_ofReal (hexp x)
    _ = 2 * ∫⁻ x, ENNReal.ofReal (Real.cosh (a * x)) ∂ν := lintegral_const_mul _ (by fun_prop)
    _ ≤ 2 * ∫⁻ x, ENNReal.ofReal (Real.exp (a * |x|)) ∂μ := by
        gcongr 2 * ?_
        exact hcosh.trans (lintegral_mono fun x ↦ ENNReal.ofReal_le_ofReal (hcosh_le x))
    _ < ⊤ := ENNReal.mul_lt_top ENNReal.ofNat_lt_top hμ.lintegral_lt_top

end TauCeti
