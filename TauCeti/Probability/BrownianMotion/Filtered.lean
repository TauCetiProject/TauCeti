/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.BrownianMotion.Basic
public import Mathlib.Probability.Process.Adapted
import TauCeti.Probability.Independence.Filtration
import TauCeti.Probability.Distributions.Gaussian.Moments
import TauCeti.Probability.Distributions.Gaussian.PolynomialMemLp

/-!
# Pre-Brownian motion relative to a filtration

Mathlib's `ProbabilityTheory.IsPreBrownianReal` prescribes only the finite-dimensional laws of
`W`. A martingale statement needs a filtration, and the law of `W` alone does not say how `W`
interacts with it: `TauCeti.Probability.IsFilteredPreBrownianReal ℱ W P` adds that `W` is adapted
to `ℱ` and that every increment `W_t - W_s`, `s ≤ t`, is independent of `ℱ_s`. A pre-Brownian
motion is a pre-Brownian motion relative to its own natural filtration
(`ProbabilityTheory.IsPreBrownianReal.isFilteredPreBrownianReal_natural`). Conversely, an adapted
process started at `0` whose increments `W_t - W_s` have law `N(0, t - s)` and are independent of
`ℱ_s` is a pre-Brownian motion relative to `ℱ`
(`MeasureTheory.Adapted.isFilteredPreBrownianReal`); this is how a change of measure is shown to
produce a new Brownian motion.

## Main declarations

* `TauCeti.Probability.IsFilteredPreBrownianReal`: a pre-Brownian motion relative to a
  filtration.
* `ProbabilityTheory.IsPreBrownianReal.isFilteredPreBrownianReal_natural`: the natural
  filtration.
* `ProbabilityTheory.IsPreBrownianReal.hasLaw_sub_of_le`: for `s ≤ t`, the increment
  `W_t - W_s` has law `N(0, t - s)`.
* `ProbabilityTheory.IsPreBrownianReal.integral_sq_increment` and
  `ProbabilityTheory.IsPreBrownianReal.integral_pow_four_increment`: second and fourth moments
  of increments; the centered square is square integrable with mean zero and second moment
  twice the squared interval length.
* `MeasureTheory.Adapted.isFilteredPreBrownianReal`: the characterization by Gaussian increments
  independent of the past.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991, §2.1.
-/

public section

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- `W` is a **pre-Brownian motion relative to the filtration `ℱ`** under `P`: its
finite-dimensional laws are those of Brownian motion, it is adapted to `ℱ`, and for `s ≤ t` the
increment `W t - W s` is independent of `ℱ s`. -/
structure IsFilteredPreBrownianReal (ℱ : Filtration ℝ≥0 mΩ) (W : ℝ≥0 → Ω → ℝ)
    (P : Measure Ω := by volume_tac) : Prop extends IsPreBrownianReal W P where
  /-- `W t` is `ℱ t`-measurable. -/
  adapted : Adapted ℱ W
  /-- The increment `W t - W s` is independent of `ℱ s`. -/
  indep_sub ⦃s t : ℝ≥0⦄ : s ≤ t → Indep (.comap (W t - W s) inferInstance) (ℱ s) P

end TauCeti.Probability

namespace ProbabilityTheory.IsPreBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- A pre-Brownian motion is a pre-Brownian motion relative to its natural filtration: by the weak
Markov property `ProbabilityTheory.IsPreBrownianReal.indepFun_shift`, the increments after time
`s` are independent of `(B u, u ≤ s)`. -/
theorem isFilteredPreBrownianReal_natural (hB : IsPreBrownianReal B P)
    (hmeas : ∀ t, StronglyMeasurable (B t)) :
    IsFilteredPreBrownianReal (Filtration.natural B hmeas) B P where
  toIsPreBrownianReal := hB
  adapted t := (Filtration.stronglyAdapted_natural hmeas t).measurable
  indep_sub s t hst := by
    rw [Filtration.natural_eq_comap]
    refine indep_of_indep_of_le_left ((IndepFun_iff_Indep _ _ _).mp (hB.indepFun_shift s)) ?_
    have : B t - B s = (fun x : ℝ≥0 → ℝ ↦ x (t - s)) ∘ fun ω u ↦ B (s + u) ω - B s ω := by
      ext ω
      simp [add_tsub_cancel_of_le hst]
    rw [this, ← MeasurableSpace.comap_comp]
    exact MeasurableSpace.comap_mono (measurable_pi_apply _).comap_le

/-- For `s ≤ t`, the increment `B t - B s` of a pre-Brownian motion has law `N(0, t - s)`. -/
theorem hasLaw_sub_of_le (hB : IsPreBrownianReal B P) {s t : ℝ≥0} (hst : s ≤ t) :
    HasLaw (B t - B s) (gaussianReal 0 (t - s)) P := by
  convert hB.hasLaw_sub t s using 2
  ext
  simp [Real.nndist_eq, hst]

/-- Every natural power of a pre-Brownian increment is integrable. -/
theorem integrable_pow_increment (hB : IsPreBrownianReal B P)
    {s t : ℝ≥0} (hst : s ≤ t) (n : ℕ) :
    Integrable (fun ω ↦ (B t ω - B s ω) ^ n) P := by
  simpa only [Function.comp_def, Pi.sub_apply] using
    (hB.hasLaw_sub_of_le hst).integrable_comp
      (TauCeti.integrable_pow_gaussianReal 0 (t - s) n)

/-- The second moment of a pre-Brownian increment is its interval length. -/
theorem integral_sq_increment (hB : IsPreBrownianReal B P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, (B t ω - B s ω) ^ 2 ∂P) = (t : ℝ) - s := by
  have h := (hB.hasLaw_sub_of_le hst).integral_comp
    (f := fun x : ℝ ↦ x ^ 2) (by fun_prop)
  simpa [Function.comp_def, Pi.sub_def, integral_sq_gaussianReal, NNReal.coe_sub hst] using h

/-- The fourth moment of a pre-Brownian increment is three times its squared interval length. -/
theorem integral_pow_four_increment (hB : IsPreBrownianReal B P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, (B t ω - B s ω) ^ 4 ∂P) = 3 * ((t : ℝ) - s) ^ 2 := by
  have h := (hB.hasLaw_sub_of_le hst).integral_comp
    (f := fun x : ℝ ↦ x ^ 4) (by fun_prop)
  have hm := integral_sub_pow_two_mul_gaussianReal 0 (t - s) 2
  norm_num [NNReal.coe_sub hst] at hm
  simpa only [Function.comp_def, Pi.sub_apply, hm, mul_comm] using h

/-- The centered square of a Brownian increment is square integrable. -/
theorem memLp_centered_sq_increment (hB : IsPreBrownianReal B P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    MemLp (fun ω ↦ (B t ω - B s ω) ^ 2 - ((t : ℝ) - s)) 2 P := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hlaw := hB.hasLaw_sub_of_le hst
  have h2 : MemLp (fun ω ↦ (B t ω - B s ω) ^ 2) 2 P :=
    (memLp_two_iff_integrable_sq
      ((hlaw.aemeasurable.pow_const 2).aestronglyMeasurable)).2
      (by simpa only [← pow_mul, Pi.sub_def] using hB.integrable_pow_increment hst 4)
  exact h2.sub (memLp_const _)

/-- The centered square of a Brownian increment has mean zero. -/
theorem integral_centered_sq_increment (hB : IsPreBrownianReal B P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, (B t ω - B s ω) ^ 2 - ((t : ℝ) - s) ∂P) = 0 := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  rw [integral_sub (hB.integrable_pow_increment hst 2) (integrable_const _),
    hB.integral_sq_increment hst, integral_const]
  simp

/-- The second moment of a centered squared Brownian increment is twice the squared
length of its time interval. -/
theorem integral_sq_centered_sq_increment (hB : IsPreBrownianReal B P)
    {s t : ℝ≥0} (hst : s ≤ t) :
    (∫ ω, ((B t ω - B s ω) ^ 2 - ((t : ℝ) - s)) ^ 2 ∂P) =
      2 * ((t : ℝ) - s) ^ 2 := by
  have := (hB.hasLaw_eval 0).isProbabilityMeasure
  have h4i := hB.integrable_pow_increment hst 4
  have h2i := hB.integrable_pow_increment hst 2
  have hexp : ∀ ω, ((B t ω - B s ω) ^ 2 - ((t : ℝ) - s)) ^ 2 =
      (B t ω - B s ω) ^ 4 - 2 * ((t : ℝ) - s) * (B t ω - B s ω) ^ 2 +
        ((t : ℝ) - s) ^ 2 := fun ω ↦ by ring
  simp_rw [hexp]
  have hsub : Integrable (fun ω ↦ (B t ω - B s ω) ^ 4 -
      2 * ((t : ℝ) - s) * (B t ω - B s ω) ^ 2) P := by
    simpa only [Pi.sub_def] using h4i.sub (h2i.const_mul (2 * ((t : ℝ) - s)))
  rw [integral_add hsub (integrable_const _),
    integral_sub h4i (h2i.const_mul _), integral_const_mul,
    hB.integral_pow_four_increment hst, hB.integral_sq_increment hst, integral_const]
  simp only [smul_eq_mul, probReal_univ, one_mul]
  ring

end ProbabilityTheory.IsPreBrownianReal

namespace MeasureTheory.Adapted

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {X : ℝ≥0 → Ω → ℝ}

/-- An adapted process that starts at `0` and whose increments `X t - X s`, `s ≤ t`, have law
`N(0, t - s)` and are independent of `ℱ s` is a pre-Brownian motion relative to `ℱ`. -/
theorem isFilteredPreBrownianReal (hX : Adapted ℱ X) (h0 : ∀ᵐ ω ∂P, X 0 ω = 0)
    (hlaw : ∀ ⦃s t : ℝ≥0⦄, s ≤ t → HasLaw (X t - X s) (gaussianReal 0 (t - s)) P)
    (hindep : ∀ ⦃s t : ℝ≥0⦄, s ≤ t → Indep (.comap (X t - X s) inferInstance) (ℱ s) P) :
    IsFilteredPreBrownianReal ℱ X P := by
  have := (hlaw (le_refl 0)).isProbabilityMeasure
  refine ⟨HasIndepIncrements.isPreBrownianReal_of_hasLaw (fun t ↦ ?_)
    (hX.hasIndepIncrements hindep), hX, hindep⟩
  refine (tsub_zero t ▸ hlaw (zero_le (a := t))).congr ?_
  filter_upwards [h0] with ω hω
  simp [hω]

end MeasureTheory.Adapted
