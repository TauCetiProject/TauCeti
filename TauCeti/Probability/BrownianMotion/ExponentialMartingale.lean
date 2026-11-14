/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Tilted
public import Mathlib.Probability.CDF
public import Mathlib.Probability.Martingale.Basic
public import TauCeti.Probability.BrownianMotion.Filtered
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Distributions.Gaussian.IsGaussianProcess.Basic
import Mathlib.Probability.Moments.Basic
import TauCeti.Probability.Distributions.Gaussian.Cdf
import TauCeti.Probability.Distributions.Tilted

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
* `ProbabilityTheory.IsPreBrownianReal.setIntegral_exponentialMartingale_preimage`,
  `ProbabilityTheory.IsPreBrownianReal.setIntegral_exponentialMartingale_lt`,
  `ProbabilityTheory.IsPreBrownianReal.setIntegral_exponentialMartingale_ge`: truncated
  expectations of `Z_t` over Borel sets and half-line events in terms of `N(θ t, t)` and the
  standard Gaussian cumulative distribution function, together with the started-at-`x` versions
  `ProbabilityTheory.IsPreBrownianReal.setIntegral_exp_mul_add_lt` and
  `ProbabilityTheory.IsPreBrownianReal.setIntegral_exp_mul_add_ge`.
* `ProbabilityTheory.IsPreBrownianReal.memLp_exponentialMartingale`: `Z_t` has finite moments of
  every finite order, since each real power of `Z_t` is a multiple of another exponential
  martingale (`TauCeti.Probability.rpow_exponentialMartingale`).
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

/-- A real power of the exponential martingale is a deterministic multiple of the exponential
martingale with the scaled parameter: `Z^θ_t ^ q = exp (q (q - 1) θ² t / 2) * Z^{qθ}_t`. -/
theorem rpow_exponentialMartingale (θ q : ℝ) (W : ℝ≥0 → Ω → ℝ) (t : ℝ≥0) (ω : Ω) :
    exponentialMartingale θ W t ω ^ q =
      exp (q * (q - 1) * θ ^ 2 * t / 2) * exponentialMartingale (q * θ) W t ω := by
  rw [exponentialMartingale_def, exponentialMartingale_def, ← exp_mul, ← exp_add]
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

/-- The exponential martingale has finite moments of every finite order. -/
theorem memLp_exponentialMartingale (hB : IsPreBrownianReal B P) (θ : ℝ) (t : ℝ≥0) {p : ℝ≥0∞}
    (hp : p ≠ ∞) : MemLp (exponentialMartingale θ B t) p P := by
  have hm := (hB.integrable_exponentialMartingale θ t).aestronglyMeasurable
  rcases eq_or_ne p 0 with rfl | hp0
  · exact memLp_zero_iff_aestronglyMeasurable.2 hm
  refine (integrable_norm_rpow_iff hm hp0 hp).1 ?_
  simp_rw [Real.norm_eq_abs, abs_of_pos (exponentialMartingale_pos θ B t _),
    rpow_exponentialMartingale]
  exact (hB.integrable_exponentialMartingale _ t).const_mul _

/-- Tilting `P` by `θ B_T` is the change of measure with density `exp (θ B_T - θ² T / 2)`. -/
theorem tilted_mul_eval_eq_withDensity (hB : IsPreBrownianReal B P) (θ : ℝ) (T : ℝ≥0) :
    P.tilted (fun ω ↦ θ * B T ω) =
      P.withDensity fun ω ↦ ENNReal.ofReal (exponentialMartingale θ B T ω) := by
  have := hB.isGaussianProcess.isProbabilityMeasure
  rw [Measure.tilted, ← mgf, mgf_gaussianReal (hB.hasLaw_eval T)]
  congr with ω
  rw [exponentialMartingale_def, ← exp_sub]
  ring_nf

/-- Integrating the exponential martingale `exp (θ B_t - θ² t / 2)` over `B_t ∈ s` gives the mass
of `s` under the shifted Gaussian law `N(θ t, t)`, including at `t = 0`. -/
theorem setIntegral_exponentialMartingale_preimage (hB : IsPreBrownianReal B P) (θ : ℝ)
    (t : ℝ≥0) {s : Set ℝ} (hs : MeasurableSet s) :
    ∫ ω in B t ⁻¹' s, exponentialMartingale θ B t ω ∂P = (gaussianReal (θ * t) t).real s := by
  have hlaw := hB.hasLaw_eval t
  have hf : Continuous fun y : ℝ ↦ exp (-(θ ^ 2 * t / 2)) * exp (θ * y) := by fun_prop
  have hmap := setIntegral_map (μ := P) hs hf.aestronglyMeasurable hlaw.aemeasurable
  rw [hlaw.map_eq, integral_const_mul, setIntegral_exp_mul_gaussianReal] at hmap
  have heq : exponentialMartingale θ B t =
      fun ω ↦ exp (-(θ ^ 2 * t / 2)) * exp (θ * B t ω) := exponentialMartingale_eq_mul_exp θ t
  rw [heq, ← hmap]
  simp only [zero_mul, zero_add]
  rw [← mul_assoc, ← exp_add]
  have hexp : -(θ ^ 2 * (t : ℝ) / 2) + (t : ℝ) * θ ^ 2 / 2 = 0 := by ring
  rw [hexp, exp_zero, one_mul, mul_comm (t : ℝ) θ]

/-- At positive time `t`, integrating `exp (θ B_t - θ² t / 2)` over `{B_t ≤ a}` gives the standard
Gaussian cumulative distribution value `Φ ((a - θ t) / √t)`. -/
theorem setIntegral_exponentialMartingale_le (hB : IsPreBrownianReal B P) (θ a : ℝ) {t : ℝ≥0}
    (ht : t ≠ 0) :
    ∫ ω in {ω | B t ω ≤ a}, exponentialMartingale θ B t ω ∂P =
      cdf (gaussianReal 0 1) ((a - θ * t) / √(t : ℝ)) := by
  have hset : {ω | B t ω ≤ a} = B t ⁻¹' Set.Iic a := rfl
  rw [hset, hB.setIntegral_exponentialMartingale_preimage θ t measurableSet_Iic,
    ← cdf_eq_real, cdf_gaussianReal_eq_cdf_zero_one (θ * t) ht a]

/-- At positive time `t`, integrating `exp (θ B_t - θ² t / 2)` over `{B_t < a}` gives
`Φ ((a - θ t) / √t)`. -/
theorem setIntegral_exponentialMartingale_lt (hB : IsPreBrownianReal B P) (θ a : ℝ) {t : ℝ≥0}
    (ht : t ≠ 0) :
    ∫ ω in {ω | B t ω < a}, exponentialMartingale θ B t ω ∂P =
      cdf (gaussianReal 0 1) ((a - θ * t) / √(t : ℝ)) := by
  have := nullSingletonClass_gaussianReal (μ := θ * t) ht
  have hset : {ω | B t ω < a} = B t ⁻¹' Set.Iio a := rfl
  rw [hset, hB.setIntegral_exponentialMartingale_preimage θ t measurableSet_Iio,
    measureReal_congr Iio_ae_eq_Iic, ← cdf_eq_real,
    cdf_gaussianReal_eq_cdf_zero_one (θ * t) ht a]

/-- At positive time `t`, integrating `exp (θ B_t - θ² t / 2)` over `{a < B_t}` gives
`Φ ((θ t - a) / √t)`. -/
theorem setIntegral_exponentialMartingale_gt (hB : IsPreBrownianReal B P) (θ a : ℝ) {t : ℝ≥0}
    (ht : t ≠ 0) :
    ∫ ω in {ω | a < B t ω}, exponentialMartingale θ B t ω ∂P =
      cdf (gaussianReal 0 1) ((θ * t - a) / √(t : ℝ)) := by
  have hset : {ω | a < B t ω} = B t ⁻¹' Set.Ioi a := rfl
  rw [hset, hB.setIntegral_exponentialMartingale_preimage θ t measurableSet_Ioi,
    measureReal_Ioi_gaussianReal_eq_cdf (θ * t) ht a]

/-- At positive time `t`, integrating `exp (θ B_t - θ² t / 2)` over `{a ≤ B_t}` gives
`Φ ((θ t - a) / √t)`. -/
theorem setIntegral_exponentialMartingale_ge (hB : IsPreBrownianReal B P) (θ a : ℝ) {t : ℝ≥0}
    (ht : t ≠ 0) :
    ∫ ω in {ω | a ≤ B t ω}, exponentialMartingale θ B t ω ∂P =
      cdf (gaussianReal 0 1) ((θ * t - a) / √(t : ℝ)) := by
  have := nullSingletonClass_gaussianReal (μ := θ * t) ht
  have hset : {ω | a ≤ B t ω} = B t ⁻¹' Set.Ici a := rfl
  rw [hset, hB.setIntegral_exponentialMartingale_preimage θ t measurableSet_Ici,
    ← measureReal_congr Ioi_ae_eq_Ici,
    measureReal_Ioi_gaussianReal_eq_cdf (θ * t) ht a]

private theorem exp_mul_add_eq (θ x : ℝ) (t : ℝ≥0) (ω : Ω) :
    exp (θ * (x + B t ω) - θ ^ 2 * t / 2) = exp (θ * x) * exponentialMartingale θ B t ω := by
  rw [exponentialMartingale_def, ← exp_add]
  ring_nf

/-- For Brownian motion started at `x`, integrating `exp (θ (x + B_t) - θ² t / 2)` over
`{x + B_t ≤ a}` at positive time `t` gives `exp (θ x) * Φ ((a - x - θ t) / √t)`. -/
theorem setIntegral_exp_mul_add_le (hB : IsPreBrownianReal B P) (θ x a : ℝ) {t : ℝ≥0}
    (ht : t ≠ 0) :
    ∫ ω in {ω | x + B t ω ≤ a}, exp (θ * (x + B t ω) - θ ^ 2 * t / 2) ∂P =
      exp (θ * x) * cdf (gaussianReal 0 1) ((a - x - θ * t) / √(t : ℝ)) := by
  have hset : {ω | x + B t ω ≤ a} = {ω | B t ω ≤ a - x} := by
    ext ω; simp only [Set.mem_ofPred_eq]; constructor <;> intro h <;> linarith
  simp_rw [hset, exp_mul_add_eq, integral_const_mul,
    hB.setIntegral_exponentialMartingale_le θ (a - x) ht]

/-- For Brownian motion started at `x`, integrating `exp (θ (x + B_t) - θ² t / 2)` over
`{x + B_t < a}` at positive time `t` gives `exp (θ x) * Φ ((a - x - θ t) / √t)`. -/
theorem setIntegral_exp_mul_add_lt (hB : IsPreBrownianReal B P) (θ x a : ℝ) {t : ℝ≥0}
    (ht : t ≠ 0) :
    ∫ ω in {ω | x + B t ω < a}, exp (θ * (x + B t ω) - θ ^ 2 * t / 2) ∂P =
      exp (θ * x) * cdf (gaussianReal 0 1) ((a - x - θ * t) / √(t : ℝ)) := by
  have hset : {ω | x + B t ω < a} = {ω | B t ω < a - x} := by
    ext ω; simp only [Set.mem_ofPred_eq]; constructor <;> intro h <;> linarith
  simp_rw [hset, exp_mul_add_eq, integral_const_mul,
    hB.setIntegral_exponentialMartingale_lt θ (a - x) ht]

/-- For Brownian motion started at `x`, integrating `exp (θ (x + B_t) - θ² t / 2)` over
`{a < x + B_t}` at positive time `t` gives `exp (θ x) * Φ ((x + θ t - a) / √t)`. -/
theorem setIntegral_exp_mul_add_gt (hB : IsPreBrownianReal B P) (θ x a : ℝ) {t : ℝ≥0}
    (ht : t ≠ 0) :
    ∫ ω in {ω | a < x + B t ω}, exp (θ * (x + B t ω) - θ ^ 2 * t / 2) ∂P =
      exp (θ * x) * cdf (gaussianReal 0 1) ((x + θ * t - a) / √(t : ℝ)) := by
  have hset : {ω | a < x + B t ω} = {ω | a - x < B t ω} := by
    ext ω; simp only [Set.mem_ofPred_eq]; constructor <;> intro h <;> linarith
  have harg : θ * (t : ℝ) - (a - x) = x + θ * t - a := by ring
  simp_rw [hset, exp_mul_add_eq, integral_const_mul,
    hB.setIntegral_exponentialMartingale_gt θ (a - x) ht, harg]

/-- For Brownian motion started at `x`, integrating `exp (θ (x + B_t) - θ² t / 2)` over
`{a ≤ x + B_t}` at positive time `t` gives `exp (θ x) * Φ ((x + θ t - a) / √t)`. -/
theorem setIntegral_exp_mul_add_ge (hB : IsPreBrownianReal B P) (θ x a : ℝ) {t : ℝ≥0}
    (ht : t ≠ 0) :
    ∫ ω in {ω | a ≤ x + B t ω}, exp (θ * (x + B t ω) - θ ^ 2 * t / 2) ∂P =
      exp (θ * x) * cdf (gaussianReal 0 1) ((x + θ * t - a) / √(t : ℝ)) := by
  have hset : {ω | a ≤ x + B t ω} = {ω | a - x ≤ B t ω} := by
    ext ω; simp only [Set.mem_ofPred_eq]; constructor <;> intro h <;> linarith
  have harg : θ * (t : ℝ) - (a - x) = x + θ * t - a := by ring
  simp_rw [hset, exp_mul_add_eq, integral_const_mul,
    hB.setIntegral_exponentialMartingale_ge θ (a - x) ht, harg]

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
