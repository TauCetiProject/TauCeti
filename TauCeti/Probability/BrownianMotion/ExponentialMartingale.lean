/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Probability.Martingale.Basic
public import TauCeti.Probability.BrownianMotion.Filtered
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Moments.Basic

/-!
# The exponential martingale of a Brownian motion

For a real parameter `θ` and a Brownian motion `W`, the process

`Z_t = exp (θ W_t - θ² t / 2)`

(`TauCeti.Probability.exponentialMartingale θ W`) is a strictly positive martingale with
`E[Z_t] = 1`, relative to every filtration for which `W` is a Brownian motion. It is the density
process of the change of measure in Girsanov's theorem: tilting the reference measure `P` by
`θ W_T`, that is `dQ = Z_T dP`, gives a probability measure equivalent to `P`, and on the events
known at time `t ≤ T` this measure has density `Z_t`. With `θ = -κ` for a market price of risk
`κ`, `Q` is the candidate for the risk-neutral measure of the Black–Scholes market; identifying it
as such requires Girsanov's theorem and the martingale property of discounted prices under `Q`,
which are not proved here.

Brownian motion relative to a filtration is
`TauCeti.Probability.IsFilteredPreBrownianReal`, from
`TauCeti.Probability.BrownianMotion.Filtered`.

## Main declarations

* `TauCeti.Probability.exponentialMartingale`: the process `exp (θ W_t - θ² t / 2)`.
* `ProbabilityTheory.IsPreBrownianReal.integral_exponentialMartingale`: `E[Z_t] = 1`.
* `TauCeti.Probability.IsFilteredPreBrownianReal.martingale_exponentialMartingale`: `Z` is a
  martingale.
* `ProbabilityTheory.IsPreBrownianReal.tilted_mul_eval_eq_withDensity`: tilting by `θ W_T` is
  the change of measure with density `Z_T`.
* `ProbabilityTheory.IsPreBrownianReal.integrable_exp_mul_eval`: `exp (θ W_T)` is integrable, so
  Mathlib's `MeasureTheory.isProbabilityMeasure_tilted`, `MeasureTheory.absolutelyContinuous_tilted`
  and `MeasureTheory.tilted_absolutelyContinuous` show that the tilted measure is a probability
  measure equivalent to `P`.
* `TauCeti.Probability.IsFilteredPreBrownianReal.tilted_mul_eval_apply`: on `ℱ_t`, `t ≤ T`, the
  tilted measure has density `Z_t`.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, Springer, 1991, §3.5.
* S. E. Shreve, *Stochastic Calculus for Finance II: Continuous-Time Models*, Springer, 2004,
  §5.2.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal ENNReal

namespace TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ}

/-- The **exponential martingale** `exp (θ W_t - θ² t / 2)` of a Brownian motion `W` with
parameter `θ`. -/
def exponentialMartingale (θ : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) : ℝ :=
  exp (θ * W t ω - θ ^ 2 * t / 2)

/-- Unfolding lemma for `exponentialMartingale`. -/
theorem exponentialMartingale_def (θ : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    exponentialMartingale θ W t ω = exp (θ * W t ω - θ ^ 2 * t / 2) :=
  (rfl)

/-- The exponential martingale is strictly positive. -/
theorem exponentialMartingale_pos (θ : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    0 < exponentialMartingale θ W t ω := by
  rw [exponentialMartingale_def]
  exact exp_pos _

/-- With parameter `0` the exponential martingale is constantly `1`. -/
@[simp]
theorem exponentialMartingale_zero_left (W : ℝ≥0 → Ω → ℝ) :
    exponentialMartingale 0 W = 1 := by
  ext t ω
  simp [exponentialMartingale_def]

/-- From time `s` to time `t ≥ s` the exponential martingale is multiplied by the exponential of
the increment `θ (W_t - W_s) - θ² (t - s) / 2`. -/
theorem exponentialMartingale_eq_mul (θ : ℝ) (W : ℝ≥0 → Ω → ℝ) (s t : ℝ≥0) (ω : Ω) :
    exponentialMartingale θ W t ω =
      exponentialMartingale θ W s ω * exp (θ * (W t ω - W s ω) - θ ^ 2 * (t - s) / 2) := by
  rw [exponentialMartingale_def, exponentialMartingale_def, ← exp_add]
  ring_nf

end TauCeti.Probability

namespace MeasureTheory.Adapted

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ} {W : ℝ≥0 → Ω → ℝ}

/-- The exponential martingale of a process adapted to `ℱ` is adapted to `ℱ`. -/
theorem stronglyAdapted_exponentialMartingale (hW : Adapted ℱ W) (θ : ℝ) :
    StronglyAdapted ℱ (exponentialMartingale θ W) := fun t ↦
  (measurable_exp.comp (((hW t).const_mul θ).sub_const _)).stronglyMeasurable

end MeasureTheory.Adapted

namespace ProbabilityTheory.IsPreBrownianReal

open TauCeti.Probability

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B : ℝ≥0 → Ω → ℝ}

/-- `exp (θ B_t)` is integrable. -/
theorem integrable_exp_mul_eval (hB : IsPreBrownianReal B P) (θ : ℝ) (t : ℝ≥0) :
    Integrable (fun ω ↦ exp (θ * B t ω)) P :=
  have := hB.isGaussianProcess.isProbabilityMeasure
  mgf_pos_iff.mp (mgf_gaussianReal (hB.hasLaw_eval t) θ ▸ exp_pos _)

private theorem exponentialMartingale_eq_mul_exp (θ : ℝ) (t : ℝ≥0) :
    exponentialMartingale θ B t = fun ω ↦ exp (-(θ ^ 2 * t / 2)) * exp (θ * B t ω) := by
  ext ω
  rw [exponentialMartingale_def, ← exp_add]
  ring_nf

/-- The exponential martingale is integrable at every time. -/
theorem integrable_exponentialMartingale (hB : IsPreBrownianReal B P) (θ : ℝ) (t : ℝ≥0) :
    Integrable (exponentialMartingale θ B t) P := by
  rw [exponentialMartingale_eq_mul_exp]
  exact (hB.integrable_exp_mul_eval θ t).const_mul _

/-- The exponential martingale has expectation `1` at every time. -/
theorem integral_exponentialMartingale (hB : IsPreBrownianReal B P) (θ : ℝ) (t : ℝ≥0) :
    ∫ ω, exponentialMartingale θ B t ω ∂P = 1 := by
  rw [exponentialMartingale_eq_mul_exp, integral_const_mul, ← mgf,
    mgf_gaussianReal (hB.hasLaw_eval t), ← exp_add]
  ring_nf
  exact exp_zero

/-- Tilting `P` by `θ B_T` is the change of measure with density `exp (θ B_T - θ² T / 2)`. -/
theorem tilted_mul_eval_eq_withDensity (hB : IsPreBrownianReal B P) (θ : ℝ) (T : ℝ≥0) :
    P.tilted (fun ω ↦ θ * B T ω) =
      P.withDensity fun ω ↦ ENNReal.ofReal (exponentialMartingale θ B T ω) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  rw [Measure.tilted, ← mgf, mgf_gaussianReal (hB.hasLaw_eval T)]
  congr with ω
  rw [exponentialMartingale_def, ← exp_sub]
  ring_nf

end ProbabilityTheory.IsPreBrownianReal

namespace TauCeti.Probability.IsFilteredPreBrownianReal

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ}
  {W : ℝ≥0 → Ω → ℝ}

/-- The exponential martingale `exp (θ W_t - θ² t / 2)` of a Brownian motion relative to `ℱ` is a
martingale relative to `ℱ`. -/
theorem martingale_exponentialMartingale (hW : IsFilteredPreBrownianReal ℱ W P) (θ : ℝ) :
    Martingale (exponentialMartingale θ W) ℱ P := by
  have := hW.isGaussianProcess.isProbabilityMeasure
  refine ⟨hW.adapted.stronglyAdapted_exponentialMartingale θ, fun s t hst ↦ ?_⟩
  -- The factor carrying `Z` from time `s` to time `t` is the exponential martingale, at time
  -- `t - s`, of the Brownian motion `u ↦ W (s + u) - W s` restarted at time `s`.
  let Y := exponentialMartingale θ (fun u ω ↦ W (s + u) ω - W s ω) (t - s)
  have hY : Y = fun ω ↦ exp (θ * (W t - W s) ω - θ ^ 2 * ((t : ℝ) - s) / 2) := by
    ext ω
    simp only [Y, exponentialMartingale_def, add_tsub_cancel_of_le hst, Pi.sub_apply,
      NNReal.coe_sub hst]
  have hYm : StronglyMeasurable[.comap (W t - W s) inferInstance] Y := by
    rw [hY]
    exact (measurable_exp.comp (((comap_measurable (W t - W s)).const_mul θ).sub_const _))
      |>.stronglyMeasurable
  have hZ : exponentialMartingale θ W t = exponentialMartingale θ W s * Y := by
    rw [hY]
    ext ω
    exact exponentialMartingale_eq_mul θ W s t ω
  have hZint : Integrable (exponentialMartingale θ W s * Y) P := by
    rw [← hZ]
    exact hW.integrable_exponentialMartingale θ t
  have hpull := condExp_mul_of_stronglyMeasurable_left (m := ℱ s)
    (hW.adapted.stronglyAdapted_exponentialMartingale θ s) hZint
    ((hW.shift s).integrable_exponentialMartingale θ (t - s))
  have hindep : P[Y | ℱ s] =ᵐ[P] fun _ ↦ ∫ ω, Y ω ∂P :=
    condExp_indep_eq (m₂ := ℱ s) (hW.adapted.measurable.sub hW.adapted.measurable).comap_le
      (ℱ.le s) hYm (hW.indep_sub hst)
  rw [hZ]
  filter_upwards [hpull, hindep] with ω h₁ h₂
  rw [h₁, Pi.mul_apply, h₂, (hW.shift s).integral_exponentialMartingale, mul_one]

/-- On an event `A` known at time `t ≤ T`, the tilt of `P` by `θ W_T` has density `Z_t`:
`Q(A) = E[Z_t; A]`. -/
theorem tilted_mul_eval_apply (hW : IsFilteredPreBrownianReal ℱ W P) (θ : ℝ) {t T : ℝ≥0}
    (htT : t ≤ T) {A : Set Ω} (hA : MeasurableSet[ℱ t] A) :
    P.tilted (fun ω ↦ θ * W T ω) A =
      ENNReal.ofReal (∫ ω in A, exponentialMartingale θ W t ω ∂P) := by
  have := hW.isGaussianProcess.isProbabilityMeasure
  rw [hW.tilted_mul_eval_eq_withDensity, withDensity_apply _ (ℱ.le t A hA),
    ← ofReal_integral_eq_lintegral_ofReal (hW.integrable_exponentialMartingale θ T).integrableOn
      (Filter.Eventually.of_forall fun ω ↦ (exponentialMartingale_pos θ W T ω).le),
    (hW.martingale_exponentialMartingale θ).setIntegral_eq htT hA]

end TauCeti.Probability.IsFilteredPreBrownianReal
