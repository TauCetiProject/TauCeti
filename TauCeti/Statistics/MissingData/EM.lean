/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.WithDensity
public import Mathlib.Order.Filter.Extr
import TauCeti.Analysis.Calculus.Gradient.LocalExtr
import TauCeti.MeasureTheory.Integral.Bochner.WithDensity
import TauCeti.MeasureTheory.Measure.LogLikelihoodRatio

/-!
# The EM algorithm at fixed observed data

The observed data are fixed. The missing part `z` of one complete observation ranges over a
measurable space `Z` with a reference measure `ρ`, and `f θ z` is the complete-data density at
the fixed observed data and the missing part `z`, for the parameter `θ`.

The observed-data likelihood is `L(θ) = ∫ f θ dρ`, and the conditional law of the missing part
given the observed data is `ρ` weighted by the density `f θ / L(θ)`. The EM criterion
`Q(θ | θ')` is the integral of `log f θ` under the conditional law at `θ'`, and an EM step from
`θ'` over a parameter set `Θ` is a maximizer of `Q(· | θ')` over `Θ`.

There are two separate junk values. The integrals are Bochner integrals and so take the value `0`
off integrability: when `f θ` is not integrable `L(θ) = 0`, and then the conditional law at `θ` is
the zero measure. Independently, Lean's `Real.log` is totalized by `Real.log 0 = 0`, so `log f θ`
is `0`, not `-∞`, where `f θ` vanishes, and `log L(θ)` is `0` both when the likelihood is
genuinely zero and when it is the Bochner fallback. The definitions below are these totalized
quantities. They have their statistical meaning only under side conditions:

* `missingLaw ρ f θ'` is the conditional law of the missing part when `f θ'` is a density slice:
  almost everywhere nonnegative and integrable with positive integral `L(θ')` (for instance when
  `f θ'` is integrable, almost everywhere positive, and `ρ ≠ 0`); it is then a probability
  measure.
* `Q(θ | θ')` is the conditional expectation of the complete-data log-likelihood only when
  moreover `0 < f θ` almost everywhere under `missingLaw ρ f θ'` and `log f θ` is integrable
  under it. Integrability alone is not enough: if `f θ` vanishes on a set of positive
  conditional probability, the statistical criterion is `-∞`, while the totalized `Q(θ | θ')`
  may still be a finite integral of an integrable function.
* If these conditions hold for every candidate `θ ∈ Θ`, they guarantee that the totalized and
  the statistical criteria agree on `Θ`, so an EM step is the statistical EM step. Without them
  the two criteria, and hence their maximizers, may differ: an EM step maximizes the totalized
  criterion, junk values included.

## Main definitions

* `MeasureTheory.Measure.obsLikelihood ρ f θ`: the observed-data likelihood `∫ f θ dρ`.
* `MeasureTheory.Measure.obsLogLikelihood ρ f θ`: its logarithm, with `Real.log 0 = 0`.
* `MeasureTheory.Measure.missingLaw ρ f θ`: the conditional law `ρ.withDensity (f θ / L(θ))` of
  the missing part given the observed data.
* `MeasureTheory.Measure.emQ ρ f θ θ'`: the EM criterion `Q(θ | θ') = ∫ log f θ d(missingLaw θ')`.
* `MeasureTheory.Measure.IsEMStep ρ Θ f θ' θ''`: `θ'' ∈ Θ` maximizes `Q(· | θ')` over `Θ`.

## Main results

* `MeasureTheory.Measure.isProbabilityMeasure_missingLaw`: the conditional law is a probability
  measure when `f θ` is almost everywhere nonnegative and `L(θ) ≠ 0`; in particular
  (`isProbabilityMeasure_missingLaw_of_pos`) when `f θ` is integrable and almost everywhere
  positive and `ρ ≠ 0`.
* `MeasureTheory.Measure.integral_missingLaw`: `∫ g d(missingLaw θ) = L(θ)⁻¹ ∫ f θ • g dρ` when
  `f θ` is almost everywhere nonnegative.
* `MeasureTheory.Measure.emQ_eq_inv_mul_integral`:
  `Q(θ | θ') = L(θ')⁻¹ ∫ f θ' log f θ dρ` when `f θ'` is almost everywhere nonnegative.
* `MeasureTheory.Measure.isEMStep_iff_isMaxOn`: an EM step is a maximizer of the totalized
  criterion `Q(· | θ')` on `Θ`.
* `MeasureTheory.Measure.absolutelyContinuous_missingLaw`: every conditional law `k_θ'` is
  absolutely continuous with respect to `k_θ` when `f θ` is integrable and almost everywhere
  positive.
* `MeasureTheory.Measure.llr_missingLaw_ae_eq`: when `k_θ' ≪ k_θ`, the log-likelihood ratio of
  the conditional laws at `θ'` and `θ` is `log f θ' - log f θ + log L(θ) - log L(θ')`, almost
  everywhere under `k_θ'`.
* `MeasureTheory.Measure.emQ_sub_le_obsLogLikelihood_sub`: the EM identity
  `log L(θ) - log L(θ') = Q(θ | θ') - Q(θ' | θ') + KL(k_θ' ‖ k_θ)` and the resulting inequality,
  where `k_θ` is the conditional law at `θ`, when `f θ`, `f θ'` are almost everywhere
  nonnegative, `L(θ') ≠ 0` (unless `ρ = 0`), `k_θ' ≪ k_θ`, and `log f θ`, `log f θ'` are
  `k_θ'`-integrable.
* `MeasureTheory.Measure.obsLogLikelihood_le_of_isEMStep`: under the same conditions at the
  starting point `θ' ∈ Θ` and the EM step `θ''`, the step does not decrease the observed-data
  log-likelihood, and at equality the conditional laws and the criteria agree.
* `MeasureTheory.Measure.IsEMStep.hasFDerivAt_obsLogLikelihood_zero`,
  `MeasureTheory.Measure.IsEMStep.hasGradientAt_obsLogLikelihood_zero`: an interior fixed point
  of EM at which Fisher's identity `∇ log L(θ) = ∇₁Q(θ | θ)` holds is a stationary point of the
  observed-data log-likelihood, `∇ log L(θ) = 0`.

A closing example on a two-point missing part exhibits an EM step and rejects a competing
candidate.

## Implementation notes

The Kullback–Leibler step of the EM identity follows `CKSD/Bayes/Evidence/Bounds.lean` of the
lean-CKSD project (<https://github.com/bjbraams/lean-CKSD>): the log-likelihood ratio of the two
conditional laws is computed from their densities (`TauCeti.llr_withDensity_ofReal_ae_eq`) and
integrated against the first, which turns Mathlib's `toReal_klDiv_of_measure_eq` into the
identity. No σ-finiteness instance on `ρ` is assumed: the conditional laws are finite measures
(`isFiniteMeasure_missingLaw`), which is all the density step needs.

## References

* R. J. A. Little and D. B. Rubin, *Statistical Analysis with Missing Data*, 3rd ed., Wiley
  (2019), Section 8.4.1, (8.13)–(8.18), pp. 193–194, and Theorems 8.1–8.2, pp. 194–195.
-/

public section

noncomputable section

open MeasureTheory

open scoped ENNReal Topology

namespace MeasureTheory.Measure

variable {E Z F : Type*} [MeasurableSpace Z] [NormedAddCommGroup F] [NormedSpace ℝ F]
  (ρ : Measure Z)

section Definitions

variable (f : E → Z → ℝ)

/-- The **observed-data likelihood** `L(θ) = ∫ f θ dρ`: the complete-data density at the fixed
observed data, integrated over the missing part. -/
def obsLikelihood (θ : E) : ℝ := ∫ z, f θ z ∂ρ

/-- The **observed-data log-likelihood** `log L(θ)`. It is the statistical log-likelihood when
`f θ` is a density slice: almost everywhere nonnegative with `0 < L(θ)` (which forces `f θ` to be
integrable), as in `missingLaw`. For a signed slice a positive integral `L(θ)` need not be a
likelihood. When `L(θ) = 0`, whether the likelihood is genuinely zero (statistically `-∞`) or
`f θ` is not integrable (the Bochner fallback), it is the junk value `Real.log 0 = 0`. -/
def obsLogLikelihood (θ : E) : ℝ := Real.log (ρ.obsLikelihood f θ)

/-- The **conditional law of the missing part** given the observed data, at the parameter `θ`:
the reference measure weighted by the density `f θ / L(θ)`. It is the conditional law when `f θ`
is a density slice, almost everywhere nonnegative and integrable with `0 < L(θ)`; for other real
inputs it is only a totalized measure (the zero measure when `L(θ) = 0`). -/
def missingLaw (θ : E) : Measure Z :=
  ρ.withDensity fun z ↦ ENNReal.ofReal (f θ z / ρ.obsLikelihood f θ)

/-- The **EM criterion** `Q(θ | θ') = ∫ log f θ d(missingLaw θ')`, a totalized Bochner integral
of the totalized `Real.log`. When `f θ'` is a density slice (almost everywhere nonnegative and
integrable with `0 < L(θ')`), `0 < f θ` almost everywhere under `missingLaw ρ f θ'`, and `log f θ`
is integrable under it, this is the conditional expectation of the complete-data log-likelihood
at `θ` given the observed data, under the parameter `θ'`. Otherwise it need not be: it may be the
junk value `0`, or a finite value where the statistical criterion is `-∞`. -/
def emQ (θ θ' : E) : ℝ := ∫ z, Real.log (f θ z) ∂ρ.missingLaw f θ'

/-- `θ''` is an **EM step** from `θ'` over the parameter set `Θ`: `θ'' ∈ Θ` maximizes the
totalized criterion `Q(· | θ')` over `Θ`. It is the statistical EM step when `f θ'` is a density
slice (almost everywhere nonnegative and integrable with `0 < L(θ')`) and, for every `θ ∈ Θ`,
`0 < f θ` almost everywhere under `missingLaw ρ f θ'` and `log f θ` is integrable under it. -/
def IsEMStep (Θ : Set E) (f : E → Z → ℝ) (θ' θ'' : E) : Prop :=
  θ'' ∈ Θ ∧ ∀ θ ∈ Θ, ρ.emQ f θ θ' ≤ ρ.emQ f θ'' θ'

end Definitions

variable {ρ} {f : E → Z → ℝ} {θ θ' θ'' : E} {Θ : Set E}

theorem obsLikelihood_def (θ : E) : ρ.obsLikelihood f θ = ∫ z, f θ z ∂ρ := (rfl)

theorem obsLogLikelihood_def (θ : E) :
    ρ.obsLogLikelihood f θ = Real.log (ρ.obsLikelihood f θ) := (rfl)

theorem missingLaw_def (θ : E) :
    ρ.missingLaw f θ = ρ.withDensity fun z ↦ ENNReal.ofReal (f θ z / ρ.obsLikelihood f θ) :=
  (rfl)

theorem emQ_def (θ θ' : E) : ρ.emQ f θ θ' = ∫ z, Real.log (f θ z) ∂ρ.missingLaw f θ' := (rfl)

theorem isEMStep_iff :
    ρ.IsEMStep Θ f θ' θ'' ↔ θ'' ∈ Θ ∧ ∀ θ ∈ Θ, ρ.emQ f θ θ' ≤ ρ.emQ f θ'' θ' :=
  Iff.rfl

/-! ### The observed-data likelihood -/

@[simp]
theorem obsLikelihood_zero_measure (f : E → Z → ℝ) (θ : E) :
    (0 : Measure Z).obsLikelihood f θ = 0 :=
  integral_zero_measure _

@[simp]
theorem obsLogLikelihood_zero_measure (f : E → Z → ℝ) (θ : E) :
    (0 : Measure Z).obsLogLikelihood f θ = 0 := by
  simp [obsLogLikelihood_def]

/-- Off integrability the observed-data likelihood is the Bochner junk value `0`. -/
theorem obsLikelihood_of_not_integrable (hi : ¬Integrable (f θ) ρ) : ρ.obsLikelihood f θ = 0 := by
  rw [obsLikelihood_def, integral_undef hi]

theorem obsLikelihood_nonneg (h : 0 ≤ᵐ[ρ] f θ) : 0 ≤ ρ.obsLikelihood f θ :=
  integral_nonneg_of_ae h

/-- The observed-data likelihood is positive when the complete-data density is integrable and
almost everywhere positive, and the reference measure is nonzero. -/
theorem obsLikelihood_pos [NeZero ρ] (hi : Integrable (f θ) ρ) (hpos : ∀ᵐ z ∂ρ, 0 < f θ z) :
    0 < ρ.obsLikelihood f θ := by
  rw [obsLikelihood_def, integral_pos_iff_support_of_nonneg_ae
    (hpos.mono fun _ hz ↦ hz.le) hi]
  refine lt_of_lt_of_eq (measure_univ_pos.mpr (NeZero.ne ρ)) (measure_congr ?_).symm
  filter_upwards [hpos] with z hz
  simp [hz.ne']

/-! ### The conditional law of the missing part -/

theorem missingLaw_absolutelyContinuous (θ : E) : ρ.missingLaw f θ ≪ ρ :=
  withDensity_absolutelyContinuous _ _

/-- When the observed-data likelihood vanishes (in particular when `f θ` is not integrable), the
conditional law is the junk value `0`. -/
theorem missingLaw_of_obsLikelihood_eq_zero (h : ρ.obsLikelihood f θ = 0) :
    ρ.missingLaw f θ = 0 := by
  simp [missingLaw_def, h]

@[simp]
theorem missingLaw_zero_measure (f : E → Z → ℝ) (θ : E) :
    (0 : Measure Z).missingLaw f θ = 0 :=
  withDensity_zero_left _

/-- Integration under the conditional law is integration of the `f θ`-weighted integrand against
the reference measure, divided by the observed-data likelihood. No integrability or measurability
is needed: off integrability both sides are `0`. -/
theorem integral_missingLaw (h : 0 ≤ᵐ[ρ] f θ) (g : Z → F) :
    ∫ z, g z ∂ρ.missingLaw f θ = (ρ.obsLikelihood f θ)⁻¹ • ∫ z, f θ z • g z ∂ρ := by
  by_cases hi : Integrable (f θ) ρ
  · rw [missingLaw_def, TauCeti.MeasureTheory.integral_withDensity_ofReal
      (hi.aemeasurable.div_const _) (h.mono fun z hz ↦ div_nonneg hz (obsLikelihood_nonneg h)),
      ← integral_smul]
    simp_rw [div_eq_inv_mul, mul_smul]
  · have hL : ρ.obsLikelihood f θ = 0 := obsLikelihood_of_not_integrable hi
    simp [missingLaw_of_obsLikelihood_eq_zero hL, hL]

/-- Integrability under the conditional law is integrability of the `f θ`-weighted function
against the reference measure, for an integrable and almost everywhere nonnegative `f θ`. -/
theorem integrable_missingLaw_iff (h : 0 ≤ᵐ[ρ] f θ) (hi : Integrable (f θ) ρ) (g : Z → F) :
    Integrable g (ρ.missingLaw f θ) ↔ Integrable (fun z ↦ f θ z • g z) ρ := by
  by_cases hL : ρ.obsLikelihood f θ = 0
  · have hf : f θ =ᵐ[ρ] 0 := (integral_eq_zero_iff_of_nonneg_ae h hi).1 hL
    simp only [missingLaw_of_obsLikelihood_eq_zero hL, integrable_zero_measure, true_iff]
    exact (integrable_zero Z F ρ).congr (hf.mono fun z hz ↦ by simp [hz])
  · rw [missingLaw_def, TauCeti.MeasureTheory.integrable_withDensity_ofReal_iff
      (hi.aemeasurable.div_const _) (h.mono fun z hz ↦ div_nonneg hz (obsLikelihood_nonneg h))]
    simp_rw [div_eq_inv_mul, mul_smul]
    exact integrable_smul_iff (inv_ne_zero hL) _

/-- The conditional law of the missing part is a probability measure when the complete-data
density is almost everywhere nonnegative with nonzero observed-data likelihood (which forces it
to be integrable). -/
theorem isProbabilityMeasure_missingLaw (h : 0 ≤ᵐ[ρ] f θ) (hL : ρ.obsLikelihood f θ ≠ 0) :
    IsProbabilityMeasure (ρ.missingLaw f θ) := by
  have hi : Integrable (f θ) ρ := Integrable.of_integral_ne_zero hL
  constructor
  rw [missingLaw_def, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (hi.div_const _)
      (h.mono fun z hz ↦ div_nonneg hz (obsLikelihood_nonneg h)),
    integral_div, ← obsLikelihood_def, div_self hL, ENNReal.ofReal_one]

/-- The conditional law of the missing part is a probability measure when the complete-data
density is integrable and almost everywhere positive and the reference measure is nonzero. -/
theorem isProbabilityMeasure_missingLaw_of_pos [NeZero ρ] (hi : Integrable (f θ) ρ)
    (hpos : ∀ᵐ z ∂ρ, 0 < f θ z) : IsProbabilityMeasure (ρ.missingLaw f θ) :=
  isProbabilityMeasure_missingLaw (hpos.mono fun _ hz ↦ hz.le)
    (obsLikelihood_pos hi hpos).ne'

/-! ### The EM criterion and EM steps -/

/-- The EM criterion as an integral against the reference measure:
`Q(θ | θ') = L(θ')⁻¹ ∫ f θ' log f θ dρ` when `f θ'` is almost everywhere nonnegative. -/
theorem emQ_eq_inv_mul_integral (h : 0 ≤ᵐ[ρ] f θ') (θ : E) :
    ρ.emQ f θ θ' = (ρ.obsLikelihood f θ')⁻¹ * ∫ z, f θ' z * Real.log (f θ z) ∂ρ :=
  integral_missingLaw h _

@[simp]
theorem emQ_zero_measure (f : E → Z → ℝ) (θ θ' : E) : (0 : Measure Z).emQ f θ θ' = 0 := by
  simp [emQ_def]

/-- When the observed-data likelihood at `θ'` vanishes, the criterion `Q(θ | θ')` is the junk
value `0`. -/
theorem emQ_of_obsLikelihood_eq_zero (h : ρ.obsLikelihood f θ' = 0) (θ : E) :
    ρ.emQ f θ θ' = 0 := by
  simp [emQ_def, missingLaw_of_obsLikelihood_eq_zero h]

/-- An EM step is a maximizer over `Θ` of the totalized criterion `Q(· | θ')`. -/
theorem isEMStep_iff_isMaxOn :
    ρ.IsEMStep Θ f θ' θ'' ↔ θ'' ∈ Θ ∧ IsMaxOn (fun θ ↦ ρ.emQ f θ θ') Θ θ'' := by
  rw [isEMStep_iff, isMaxOn_iff]

namespace IsEMStep

theorem mem (h : ρ.IsEMStep Θ f θ' θ'') : θ'' ∈ Θ :=
  h.1

/-- An EM step does not decrease the totalized criterion `Q(· | θ')` relative to any candidate
in `Θ`. -/
theorem le (h : ρ.IsEMStep Θ f θ' θ'') (hθ : θ ∈ Θ) : ρ.emQ f θ θ' ≤ ρ.emQ f θ'' θ' :=
  h.2 θ hθ

theorem isMaxOn (h : ρ.IsEMStep Θ f θ' θ'') : IsMaxOn (fun θ ↦ ρ.emQ f θ θ') Θ θ'' :=
  isMaxOn_iff.2 h.2

end IsEMStep

/-! ### Monotonicity of EM -/

/-- The conditional law of the missing part is always a finite measure: when `f θ` is integrable
its density `f θ / L(θ)` is integrable, and otherwise it is the junk value `0`. -/
instance isFiniteMeasure_missingLaw : IsFiniteMeasure (ρ.missingLaw f θ) := by
  by_cases hi : Integrable (f θ) ρ
  · rw [missingLaw_def]
    exact isFiniteMeasure_withDensity_ofReal (hi.div_const _).2
  · rw [missingLaw_of_obsLikelihood_eq_zero (obsLikelihood_of_not_integrable hi)]
    infer_instance

/-- Every conditional law of the missing part is absolutely continuous with respect to the one at
a parameter `θ` where the complete-data density is integrable and almost everywhere positive. -/
theorem absolutelyContinuous_missingLaw (hi : Integrable (f θ) ρ)
    (hpos : ∀ᵐ z ∂ρ, 0 < f θ z) (θ' : E) : ρ.missingLaw f θ' ≪ ρ.missingLaw f θ := by
  rcases eq_zero_or_neZero ρ with rfl | _
  · simp
  have hL := obsLikelihood_pos hi hpos
  rw [missingLaw_def θ]
  refine (missingLaw_absolutelyContinuous θ').trans (withDensity_absolutelyContinuous'
    (hi.aemeasurable.div_const _).ennreal_ofReal ?_)
  filter_upwards [hpos] with z hz
  simpa using div_pos hz hL

/-- The log-likelihood ratio of the conditional laws `k_θ'`, `k_θ` of the missing part is,
`k_θ'`-almost everywhere, the difference of the complete-data log-likelihoods minus that of the
observed-data log-likelihoods: `log (dk_θ' / dk_θ) = log f θ' - log f θ + log L(θ) - log L(θ')`,
whenever `k_θ' ≪ k_θ` (for instance when `f θ` is integrable and almost everywhere positive,
`absolutelyContinuous_missingLaw`). -/
theorem llr_missingLaw_ae_eq (hac : ρ.missingLaw f θ' ≪ ρ.missingLaw f θ) :
    llr (ρ.missingLaw f θ') (ρ.missingLaw f θ) =ᵐ[ρ.missingLaw f θ'] fun z ↦
      Real.log (f θ' z) - Real.log (f θ z) +
        (ρ.obsLogLikelihood f θ - ρ.obsLogLikelihood f θ') := by
  by_cases hi' : Integrable (f θ') ρ
  swap
  · simp [missingLaw_of_obsLikelihood_eq_zero (obsLikelihood_of_not_integrable hi'),
      Filter.EventuallyEq]
  by_cases hi : Integrable (f θ) ρ
  swap
  · rw [missingLaw_of_obsLikelihood_eq_zero (obsLikelihood_of_not_integrable hi)] at hac
    simp [Measure.absolutelyContinuous_zero_iff.1 hac, Filter.EventuallyEq]
  -- Both normalized densities are positive `k_θ'`-almost everywhere.
  have hdens (θ₀ : E) (hi₀ : Integrable (f θ₀) ρ) :
      ∀ᵐ z ∂ρ.missingLaw f θ₀, 0 < f θ₀ z / ρ.obsLikelihood f θ₀ := by
    rw [missingLaw_def]
    exact TauCeti.ae_pos_withDensity_ofReal (hi₀.aemeasurable.div_const _)
  have : SigmaFinite (ρ.withDensity fun z ↦ ENNReal.ofReal (f θ z / ρ.obsLikelihood f θ)) := by
    rw [← missingLaw_def]
    infer_instance
  have hllr := TauCeti.llr_withDensity_ofReal_ae_eq (hi'.aemeasurable.div_const _)
    (hi.aemeasurable.div_const _) (by rwa [← missingLaw_def, ← missingLaw_def])
  rw [← missingLaw_def, ← missingLaw_def] at hllr
  filter_upwards [hllr, hac.ae_le (hdens θ hi), hdens θ' hi'] with z hz hz₁ hz₂
  obtain ⟨hf, hL⟩ := div_ne_zero_iff.1 hz₁.ne'
  obtain ⟨hf', hL'⟩ := div_ne_zero_iff.1 hz₂.ne'
  rw [hz, obsLogLikelihood_def, obsLogLikelihood_def, Real.log_div hf' hL', Real.log_div hf hL]
  ring

/-- The Kullback–Leibler divergence between two conditional laws `k_θ'`, `k_θ` of the missing
part is finite when `k_θ' ≪ k_θ` and the complete-data log-likelihoods at `θ` and `θ'` are
integrable under `k_θ'`. -/
theorem klDiv_missingLaw_ne_top (hac : ρ.missingLaw f θ' ≪ ρ.missingLaw f θ)
    (hQ : Integrable (fun z ↦ Real.log (f θ z)) (ρ.missingLaw f θ'))
    (hQ' : Integrable (fun z ↦ Real.log (f θ' z)) (ρ.missingLaw f θ')) :
    InformationTheory.klDiv (ρ.missingLaw f θ') (ρ.missingLaw f θ) ≠ ∞ :=
  InformationTheory.klDiv_ne_top hac
    (((hQ'.sub hQ).add (integrable_const _)).congr (llr_missingLaw_ae_eq hac).symm)

/-- **The EM identity and inequality**: the gain in observed-data log-likelihood is the gain in
the EM criterion plus a Kullback–Leibler divergence,
`log L(θ) - log L(θ') = Q(θ | θ') - Q(θ' | θ') + KL(k_θ' ‖ k_θ)` with `k_θ = missingLaw ρ f θ`,
so the gain in `Q` bounds it (Little–Rubin, (8.17)–(8.18), p. 194). The conditions: `f θ` and
`f θ'` are almost everywhere nonnegative, `L(θ') ≠ 0` unless `ρ = 0` (so `k_θ'` and, by
`k_θ' ≪ k_θ`, also `k_θ` are probability measures), and `log f θ`, `log f θ'` are
`k_θ'`-integrable. -/
theorem emQ_sub_le_obsLogLikelihood_sub (h : 0 ≤ᵐ[ρ] f θ) (h' : 0 ≤ᵐ[ρ] f θ')
    (hL' : ρ ≠ 0 → ρ.obsLikelihood f θ' ≠ 0) (hac : ρ.missingLaw f θ' ≪ ρ.missingLaw f θ)
    (hQ : Integrable (fun z ↦ Real.log (f θ z)) (ρ.missingLaw f θ'))
    (hQ' : Integrable (fun z ↦ Real.log (f θ' z)) (ρ.missingLaw f θ')) :
    ρ.obsLogLikelihood f θ - ρ.obsLogLikelihood f θ' =
        ρ.emQ f θ θ' - ρ.emQ f θ' θ' +
          (InformationTheory.klDiv (ρ.missingLaw f θ') (ρ.missingLaw f θ)).toReal ∧
      ρ.emQ f θ θ' - ρ.emQ f θ' θ' ≤ ρ.obsLogLikelihood f θ - ρ.obsLogLikelihood f θ' := by
  rcases eq_or_ne ρ 0 with rfl | hρ
  · simp
  have := isProbabilityMeasure_missingLaw h' (hL' hρ)
  -- `k_θ' ≪ k_θ` forces `k_θ ≠ 0`, hence `L(θ) ≠ 0`.
  have hL : ρ.obsLikelihood f θ ≠ 0 := fun hL ↦ IsProbabilityMeasure.ne_zero (ρ.missingLaw f θ') <|
    Measure.absolutelyContinuous_zero_iff.1 (missingLaw_of_obsLikelihood_eq_zero hL ▸ hac)
  have := isProbabilityMeasure_missingLaw h hL
  have hKL : (InformationTheory.klDiv (ρ.missingLaw f θ') (ρ.missingLaw f θ)).toReal =
      ρ.emQ f θ' θ' - ρ.emQ f θ θ' + (ρ.obsLogLikelihood f θ - ρ.obsLogLikelihood f θ') := by
    rw [InformationTheory.toReal_klDiv_of_measure_eq hac (by simp),
      integral_congr_ae (llr_missingLaw_ae_eq hac),
      integral_add (f := fun z ↦ Real.log (f θ' z) - Real.log (f θ z)) (hQ'.sub hQ)
        (integrable_const _), integral_sub hQ' hQ]
    simp [emQ_def]
  constructor <;> linarith [ENNReal.toReal_nonneg (a := InformationTheory.klDiv
    (ρ.missingLaw f θ') (ρ.missingLaw f θ))]

/-- **Monotonicity of EM** (Little–Rubin, Theorem 8.1, p. 194): an EM step `θ''` from a starting
point `θ' ∈ Θ` does not decrease the observed-data log-likelihood, and at equality the
conditional laws of the missing part and the values of the EM criterion agree. The conditions
are those of `emQ_sub_le_obsLogLikelihood_sub` at the two compared parameters: `f θ'` and
`f θ''` almost everywhere nonnegative, `L(θ') ≠ 0` unless `ρ = 0`, `k_θ' ≪ k_θ''`, and
`log f θ'`, `log f θ''` integrable under `k_θ'`. -/
theorem obsLogLikelihood_le_of_isEMStep (hθ' : θ' ∈ Θ) (h : ρ.IsEMStep Θ f θ' θ'')
    (h' : 0 ≤ᵐ[ρ] f θ') (hL' : ρ ≠ 0 → ρ.obsLikelihood f θ' ≠ 0) (h'' : 0 ≤ᵐ[ρ] f θ'')
    (hac : ρ.missingLaw f θ' ≪ ρ.missingLaw f θ'')
    (hQ'' : Integrable (fun z ↦ Real.log (f θ'' z)) (ρ.missingLaw f θ'))
    (hQ' : Integrable (fun z ↦ Real.log (f θ' z)) (ρ.missingLaw f θ')) :
    ρ.obsLogLikelihood f θ' ≤ ρ.obsLogLikelihood f θ'' ∧
      (ρ.obsLogLikelihood f θ' = ρ.obsLogLikelihood f θ'' →
        ρ.missingLaw f θ'' = ρ.missingLaw f θ' ∧ ρ.emQ f θ'' θ' = ρ.emQ f θ' θ') := by
  have hid := (emQ_sub_le_obsLogLikelihood_sub h'' h' hL' hac hQ'' hQ').1
  have hle := h.le hθ'
  have hK := ENNReal.toReal_nonneg
    (a := InformationTheory.klDiv (ρ.missingLaw f θ') (ρ.missingLaw f θ''))
  refine ⟨by linarith, fun heq ↦ ⟨?_, by linarith⟩⟩
  have hK0 : (InformationTheory.klDiv (ρ.missingLaw f θ') (ρ.missingLaw f θ'')).toReal = 0 := by
    linarith
  exact (InformationTheory.klDiv_eq_zero_iff.1 (((ENNReal.toReal_eq_zero_iff _).1 hK0).resolve_right
    (klDiv_missingLaw_ne_top hac hQ'' hQ'))).symm

/-! ### Stationarity -/

section Stationarity

/-- **Stationarity of EM**, Fréchet form (Little–Rubin, Theorem 8.2, p. 195, by the same
argument): at an interior fixed point `θ` of EM, if `Q(· | θ)` and the observed-data
log-likelihood `log L` have the same Fréchet derivative `D` at `θ` (Fisher's identity
`D log L(θ) = D₁Q(θ | θ)`, assumed), then `θ` is a stationary point of `log L`:
`D log L(θ) = 0`. -/
theorem IsEMStep.hasFDerivAt_obsLogLikelihood_zero [NormedAddCommGroup E] [NormedSpace ℝ E]
    (h : ρ.IsEMStep Θ f θ θ) (hΘ : Θ ∈ 𝓝 θ) {D : StrongDual ℝ E}
    (hQ : HasFDerivAt (fun θ'' ↦ ρ.emQ f θ'' θ) D θ)
    (hL : HasFDerivAt (ρ.obsLogLikelihood f) D θ) :
    HasFDerivAt (ρ.obsLogLikelihood f) (0 : StrongDual ℝ E) θ := by
  rwa [(h.isMaxOn.isLocalMax hΘ).hasFDerivAt_eq_zero hQ] at hL

/-- **Stationarity of EM**, gradient form (Little–Rubin, Theorem 8.2, p. 195, by the same
argument): at an interior fixed point `θ` of EM, if `Q(· | θ)` has gradient `g` at `θ` and the
observed-data log-likelihood `log L` has the same gradient there (Fisher's identity
`∇ log L(θ) = ∇₁Q(θ | θ)`, with `Q` differentiated in its first argument, assumed), then `θ` is a
stationary point of the observed-data log-likelihood: `∇ log L(θ) = 0`. -/
theorem IsEMStep.hasGradientAt_obsLogLikelihood_zero [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] (h : ρ.IsEMStep Θ f θ θ) (hΘ : Θ ∈ 𝓝 θ) {g : E}
    (hQ : HasGradientAt (fun θ'' ↦ ρ.emQ f θ'' θ) g θ)
    (hL : HasGradientAt (ρ.obsLogLikelihood f) g θ) :
    HasGradientAt (ρ.obsLogLikelihood f) 0 θ := by
  rwa [(h.isMaxOn.isLocalMax hΘ).hasGradientAt_eq_zero hQ] at hL

end Stationarity

/-! ### Example: a two-point missing part

The missing part is `z : Bool` under counting measure, with complete-data density `θ` at `true`
and `1 - θ` at `false`. Then `L ≡ 1`, the conditional law at `1/2` is uniform on `Bool`, and
`Q(θ | 1/2) = log (θ (1 - θ)) / 2` on `(0, 1)`. The EM step from `1/2` over `(0, 1)` is `1/2`,
and `1/4` is not an EM step. -/

example : (count : Measure Bool).IsEMStep (Set.Ioo 0 1)
      (fun θ b ↦ if b then θ else 1 - θ) (1 / 2) (1 / 2) ∧
    ¬(count : Measure Bool).IsEMStep (Set.Ioo 0 1)
      (fun θ b ↦ if b then θ else 1 - θ) (1 / 2) (1 / 4) := by
  have hQ {θ : ℝ} (h0 : 0 < θ) (h1 : θ < 1) :
      (count : Measure Bool).emQ (fun θ b ↦ if b then θ else 1 - θ) θ (1 / 2) =
        Real.log (θ * (1 - θ)) / 2 := by
    rw [emQ_eq_inv_mul_integral (.of_forall fun b ↦ by cases b <;> norm_num), obsLikelihood_def,
      Real.log_mul h0.ne' (by linarith)]
    simp [integral_fintype]
    ring
  refine ⟨⟨by norm_num, fun θ ⟨h0, h1⟩ ↦ ?_⟩, fun h ↦ ?_⟩
  · rw [hQ h0 h1, hQ (by norm_num) (by norm_num)]
    gcongr ?_ / 2
    exact Real.log_le_log (by nlinarith) (by nlinarith [sq_nonneg (θ - 1 / 2)])
  · have h' := h.le (θ := 1 / 2) (by norm_num)
    rw [hQ (by norm_num) (by norm_num), hQ (by norm_num) (by norm_num)] at h'
    have := Real.log_lt_log (by norm_num)
      (show (1 / 4 : ℝ) * (1 - 1 / 4) < 1 / 2 * (1 - 1 / 2) by norm_num)
    linarith

end MeasureTheory.Measure
