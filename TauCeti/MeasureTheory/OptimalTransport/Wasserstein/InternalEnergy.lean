/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.InformationTheory.KullbackLeibler.Basic
public import TauCeti.Analysis.Convex.RecessionConstant
public import TauCeti.MeasureTheory.OptimalTransport.Wasserstein.PotentialEnergy

/-!
# Internal energy and the signed Boltzmann entropy

The *internal energy* of a measure `μ` relative to a reference measure `m`, for a density function
`U : ℝ → ℝ`, is

`∫ U(ρ) dm + U'(∞) μˢ(X)`,

where `μ = ρ m + μˢ` is the Lebesgue decomposition of `μ` with respect to `m` and `U'(∞)` is the
recession constant of `U` (`TauCeti.recessionConstant`). It is the third basic energy on the
Wasserstein space, with the potential and interaction energies; its Wasserstein gradient flows are
the nonlinear diffusion equations.

Neither integrand need be integrable and `U'(∞)` may be infinite, so the energy takes values in
`EReal`, with the convention of `TauCeti.potentialEnergy`: the positive contributions
`∫ U(ρ)⁺ dm + (U'(∞))⁺ μˢ(X)` and the negative ones `∫ U(ρ)⁻ dm + (U'(∞))⁻ μˢ(X)` are summed
separately in `ℝ≥0∞`, and the energy is `⊤` when the positive sum is infinite and their difference
otherwise (`TauCeti.internalEnergy`). For an absolutely continuous measure it is the potential
energy of `U(ρ)` against `m` (`TauCeti.internalEnergy_of_absolutelyContinuous`), and it does not
depend on the chosen density (`TauCeti.internalEnergy_withDensity`).

The formula needs a Lebesgue decomposition of `μ` whose density `ρ` is finite `m`-almost
everywhere. Both hold when `μ` and `m` are σ-finite (`Measure.rnDeriv_ne_top`), in particular for
finite measures against a finite reference or against Lebesgue measure, and this is the intended
domain. For other measures Mathlib's `Measure.rnDeriv` and `Measure.singularPart` are junk values,
and so is the internal energy.

The *Boltzmann entropy* `Ent_m(μ)` is the internal energy for `U(r) = r log r`
(`TauCeti.boltzmannEntropy`). Its recession constant is `⊤`, so the entropy is `⊤` as soon as `μ`
is not absolutely continuous with respect to `m`, and otherwise it is `∫ ρ log ρ dm` with the
conventions above. The reference measure may be infinite, as Lebesgue measure is, and then the
entropy may be `⊥`. Against a finite reference measure it is never `⊥`, and for finite measures it
is Mathlib's Kullback–Leibler divergence up to the mass correction:
`klDiv μ m = Ent_m(μ) + m(X) - μ(X)` (`TauCeti.klDiv_eq_boltzmannEntropy_add_sub`).

Changing the reference measure to a Gibbs measure `m.tilted f = Z⁻¹ exp(f) m`, with
`Z = ∫ exp f dm` finite, shifts the entropy by a potential energy and a free energy:
`Ent_{m.tilted f}(μ) = Ent_m(μ) - ∫ f dμ + μ(X) log Z` (`TauCeti.boltzmannEntropy_tilted`). This
is how the entropy against an infinite reference is controlled: for `f x = -a d(x, x₀)²` with
`exp f` integrable against a nonzero `m`, the tilted reference is a probability measure, and the
entropy of a law with finite second moment is a relative entropy minus a moment and a constant, in
particular never `⊥`.

## Main definitions

* `TauCeti.internalEnergy U m μ`: the internal energy of `μ` relative to `m`, as an extended real.
* `TauCeti.boltzmannEntropy m μ`: the signed Boltzmann entropy `Ent_m(μ)`.

## Main results

* `TauCeti.internalEnergy_of_absolutelyContinuous`, `TauCeti.internalEnergy_withDensity`: the
  internal energy of an absolutely continuous measure is the potential energy of `U(ρ)`, for any
  density `ρ`.
* `TauCeti.internalEnergy_eq_potentialEnergy_add`: for a real recession constant and finite singular
  mass, the internal energy is `∫ U(ρ) dm + U'(∞) μˢ(X)`.
* `TauCeti.boltzmannEntropy_eq_top_iff`, `TauCeti.boltzmannEntropy_eq_bot_iff`,
  `TauCeti.integrable_mul_log_iff_boltzmannEntropy_ne_top_and_ne_bot`: when the entropy is `⊤`,
  `⊥`, or finite.
* `TauCeti.klDiv_eq_boltzmannEntropy_add_sub`: `klDiv μ m = Ent_m(μ) + m(X) - μ(X)` for finite
  measures.
* `TauCeti.boltzmannEntropy_eq_potentialEnergy_llr`: for `μ ≪ m`, the entropy is `∫ log ρ dμ`.
* `TauCeti.boltzmannEntropy_tilted`, `TauCeti.klDiv_tilted_eq_boltzmannEntropy`: change of
  reference to a Gibbs measure.
* `TauCeti.boltzmannEntropy_ne_bot_of_integrable_exp`: the entropy is not `⊥` when some `exp f`
  is integrable against `m` and `f` is integrable against `μ`.

## References

* L. Ambrosio, N. Gigli, G. Savaré, *Gradient Flows in Metric Spaces and in the Space of
  Probability Measures*, 2nd ed., Birkhäuser 2008, §9.3.
* C. Villani, *Optimal Transport: Old and New*, Springer 2009, Chapter 17.
-/

public section

noncomputable section

open MeasureTheory Set InformationTheory
open scoped ENNReal NNReal

namespace TauCeti

variable {X : Type*} [MeasurableSpace X] {U : ℝ → ℝ} {m μ : Measure X}

section InternalEnergy

/-- The *internal energy* `∫ U(ρ) dm + U'(∞) μˢ(X)` of a measure `μ` relative to a reference
measure `m`, where `μ = ρ m + μˢ` is the Lebesgue decomposition of `μ` with respect to `m` and
`U'(∞)` is the recession constant of `U`, as an extended real. The positive parts
`∫ U(ρ)⁺ dm + (U'(∞))⁺ μˢ(X)` and the negative parts `∫ U(ρ)⁻ dm + (U'(∞))⁻ μˢ(X)` are summed
separately; the energy is `⊤` when the positive sum is infinite, and otherwise the positive sum
minus the negative one, which is `⊥` when only the latter is infinite.

The intended domain is σ-finite `μ` and `m`, for which `ρ` is finite `m`-almost everywhere, so
taking `ρ` through `ENNReal.toReal` changes it only on an `m`-null set. -/
def internalEnergy (U : ℝ → ℝ) (m μ : Measure X) : EReal :=
  if ∫⁻ x, ENNReal.ofReal (U (μ.rnDeriv m x).toReal) ∂m
      + (recessionConstant U).toENNReal * μ.singularPart m univ = ∞ then ⊤
  else ((∫⁻ x, ENNReal.ofReal (U (μ.rnDeriv m x).toReal) ∂m
      + (recessionConstant U).toENNReal * μ.singularPart m univ : ℝ≥0∞) : EReal)
    - ((∫⁻ x, ENNReal.ofReal (-U (μ.rnDeriv m x).toReal) ∂m
      + (-recessionConstant U).toENNReal * μ.singularPart m univ : ℝ≥0∞) : EReal)

/-- The defining formula of the internal energy. -/
theorem internalEnergy_def (U : ℝ → ℝ) (m μ : Measure X) :
    internalEnergy U m μ =
      if ∫⁻ x, ENNReal.ofReal (U (μ.rnDeriv m x).toReal) ∂m
          + (recessionConstant U).toENNReal * μ.singularPart m univ = ∞ then ⊤
      else ((∫⁻ x, ENNReal.ofReal (U (μ.rnDeriv m x).toReal) ∂m
          + (recessionConstant U).toENNReal * μ.singularPart m univ : ℝ≥0∞) : EReal)
        - ((∫⁻ x, ENNReal.ofReal (-U (μ.rnDeriv m x).toReal) ∂m
          + (-recessionConstant U).toENNReal * μ.singularPart m univ : ℝ≥0∞) : EReal) := (rfl)

/-- Without singular part, the internal energy is the potential energy of `U(ρ)` against `m`. -/
theorem internalEnergy_of_singularPart_eq_zero (h : μ.singularPart m = 0) :
    internalEnergy U m μ = potentialEnergy (fun x ↦ U (μ.rnDeriv m x).toReal) m := by
  by_cases hA : ∫⁻ x, ENNReal.ofReal (U (μ.rnDeriv m x).toReal) ∂m = ∞
  · simp [internalEnergy, h, hA, potentialEnergy_eq_top_iff.2 hA]
  · simp [internalEnergy, h, hA, potentialEnergy_of_lintegral_ne_top hA]

/-- The internal energy of a measure absolutely continuous with respect to `m` is the potential
energy of `U(ρ)` against `m`, where `ρ` is the Radon–Nikodym derivative. -/
theorem internalEnergy_of_absolutelyContinuous (h : μ ≪ m) :
    internalEnergy U m μ = potentialEnergy (fun x ↦ U (μ.rnDeriv m x).toReal) m :=
  internalEnergy_of_singularPart_eq_zero (Measure.singularPart_eq_zero_of_ac h)

/-- The internal energy does not depend on the choice of density: for every almost everywhere
measurable finite density `f`, the internal energy of `f m` is the potential energy of `U ∘ f`
against `m`. -/
theorem internalEnergy_withDensity [SigmaFinite m] {f : X → ℝ≥0} (hf : AEMeasurable f m) :
    internalEnergy U m (m.withDensity fun x ↦ f x) = potentialEnergy (fun x ↦ U (f x)) m := by
  rw [internalEnergy_of_absolutelyContinuous (withDensity_absolutelyContinuous _ _)]
  exact potentialEnergy_congr_ae <|
    (Measure.rnDeriv_withDensity₀ m hf.coe_nnreal_ennreal).mono fun x hx ↦ by simp only [hx,
      ENNReal.coe_toReal]

/-- If the recession constant of `U` is `⊤`, every measure with a nonzero singular part has
internal energy `⊤`. -/
theorem internalEnergy_eq_top_of_recessionConstant_eq_top (hU : recessionConstant U = ⊤)
    (h : μ.singularPart m ≠ 0) : internalEnergy U m μ = ⊤ := by
  have h' : μ.singularPart m univ ≠ 0 := by simpa using h
  simp [internalEnergy, hU, ENNReal.top_mul h']

/-- For a real recession constant `r` and a finite singular part, the internal energy is
`∫ U(ρ) dm + r μˢ(X)`, with the first term the potential energy of `U(ρ)` against `m`. -/
theorem internalEnergy_eq_potentialEnergy_add {r : ℝ} (hU : recessionConstant U = r)
    (h : μ.singularPart m univ ≠ ∞) :
    internalEnergy U m μ = potentialEnergy (fun x ↦ U (μ.rnDeriv m x).toReal) m
      + ((r * (μ.singularPart m univ).toReal : ℝ) : EReal) := by
  -- The positive and negative parts of the singular contribution `r μˢ(X)`, as real numbers.
  have hsing (s : ℝ) : (s : EReal).toENNReal * μ.singularPart m univ =
      ENNReal.ofReal (max s 0 * (μ.singularPart m univ).toReal) := by
    rw [EReal.toENNReal_of_ne_top (EReal.coe_ne_top s), EReal.toReal_coe,
      ENNReal.ofReal_mul (le_max_right _ _), ENNReal.ofReal_toReal h]
    simp [ENNReal.ofReal_max]
  rw [internalEnergy, hU, ← EReal.coe_neg, hsing, hsing]
  by_cases hA : ∫⁻ x, ENNReal.ofReal (U (μ.rnDeriv m x).toReal) ∂m = ∞
  · rw [potentialEnergy_eq_top_iff.2 hA, EReal.top_add_coe]
    simp [hA]
  have hA' : ∫⁻ x, ENNReal.ofReal (U (μ.rnDeriv m x).toReal) ∂m
      + ENNReal.ofReal (max r 0 * (μ.singularPart m univ).toReal) ≠ ∞ :=
    ENNReal.add_ne_top.2 ⟨hA, ENNReal.ofReal_ne_top⟩
  rw [potentialEnergy_of_lintegral_ne_top hA]
  simp only [hA', ↓reduceIte]
  by_cases hB : ∫⁻ x, ENNReal.ofReal (-U (μ.rnDeriv m x).toReal) ∂m = ∞
  · simp [hB, EReal.sub_top]
  rw [EReal.coe_ennreal_add, EReal.coe_ennreal_add, ← EReal.coe_ennreal_toReal hA,
    ← EReal.coe_ennreal_toReal hB, EReal.coe_ennreal_ofReal, EReal.coe_ennreal_ofReal,
    max_eq_left (mul_nonneg (le_max_right _ _) ENNReal.toReal_nonneg),
    max_eq_left (mul_nonneg (le_max_right _ _) ENNReal.toReal_nonneg)]
  norm_cast
  linear_combination (μ.singularPart m univ).toReal * max_zero_sub_max_neg_zero_eq_self r

/-- The internal energy of the zero measure is `0` when `U 0 = 0`. -/
@[simp]
theorem internalEnergy_zero_measure (hU : U 0 = 0) (m : Measure X) :
    internalEnergy U m 0 = 0 := by
  rw [internalEnergy_of_absolutelyContinuous (Measure.AbsolutelyContinuous.zero m),
    potentialEnergy_congr_ae (W := 0) ((Measure.rnDeriv_zero m).mono fun x hx ↦ by simp [hx, hU]),
    potentialEnergy_of_integrable (integrable_zero _ _ _)]
  simp

end InternalEnergy

section BoltzmannEntropy

/-- The *signed Boltzmann entropy* `Ent_m(μ)` of a measure `μ` relative to a reference measure `m`:
the internal energy for `U(r) = r log r`. It is `⊤` when `μ` is not absolutely continuous with
respect to `m` (`TauCeti.boltzmannEntropy_of_not_absolutelyContinuous`), and otherwise
`∫ ρ log ρ dm` for the density `ρ` of `μ`, with the extended-real conventions of
`TauCeti.potentialEnergy` (`TauCeti.boltzmannEntropy_of_absolutelyContinuous`). -/
def boltzmannEntropy (m μ : Measure X) : EReal :=
  internalEnergy (fun r ↦ r * Real.log r) m μ

/-- The Boltzmann entropy is the internal energy for `U(r) = r log r`. -/
theorem boltzmannEntropy_def (m μ : Measure X) :
    boltzmannEntropy m μ = internalEnergy (fun r ↦ r * Real.log r) m μ := (rfl)

/-- The Boltzmann entropy of a measure absolutely continuous with respect to `m` is the potential
energy of `ρ log ρ` against `m`, where `ρ` is the Radon–Nikodym derivative. -/
theorem boltzmannEntropy_of_absolutelyContinuous (h : μ ≪ m) :
    boltzmannEntropy m μ = potentialEnergy
      (fun x ↦ (μ.rnDeriv m x).toReal * Real.log (μ.rnDeriv m x).toReal) m :=
  internalEnergy_of_absolutelyContinuous h

/-- A measure that is not absolutely continuous with respect to `m` has Boltzmann entropy `⊤`. -/
theorem boltzmannEntropy_of_not_absolutelyContinuous [μ.HaveLebesgueDecomposition m]
    (h : ¬ μ ≪ m) : boltzmannEntropy m μ = ⊤ :=
  internalEnergy_eq_top_of_recessionConstant_eq_top recessionConstant_mul_log
    (mt (Measure.singularPart_eq_zero μ m).1 h)

/-- The Boltzmann entropy does not depend on the choice of density: for every almost everywhere
measurable finite density `f`, the entropy of `f m` is the potential energy of `f log f` against
`m`. -/
theorem boltzmannEntropy_withDensity [SigmaFinite m] {f : X → ℝ≥0} (hf : AEMeasurable f m) :
    boltzmannEntropy m (m.withDensity fun x ↦ f x) =
      potentialEnergy (fun x ↦ (f x : ℝ) * Real.log (f x)) m :=
  internalEnergy_withDensity hf

/-- The Boltzmann entropy is `⊤` exactly when `μ` is not absolutely continuous with respect to `m`,
or the positive part of `ρ log ρ` has infinite integral. -/
theorem boltzmannEntropy_eq_top_iff [μ.HaveLebesgueDecomposition m] :
    boltzmannEntropy m μ = ⊤ ↔ (μ ≪ m → ∫⁻ x, ENNReal.ofReal
      ((μ.rnDeriv m x).toReal * Real.log (μ.rnDeriv m x).toReal) ∂m = ∞) := by
  by_cases h : μ ≪ m
  · simp [boltzmannEntropy_of_absolutelyContinuous h, potentialEnergy_eq_top_iff, h]
  · simp [boltzmannEntropy_of_not_absolutelyContinuous h, h]

/-- The Boltzmann entropy is `⊥` exactly when `μ` is absolutely continuous with respect to `m`, the
positive part of `ρ log ρ` has finite integral, and its negative part has infinite integral. -/
theorem boltzmannEntropy_eq_bot_iff [μ.HaveLebesgueDecomposition m] :
    boltzmannEntropy m μ = ⊥ ↔ μ ≪ m ∧
      ∫⁻ x, ENNReal.ofReal ((μ.rnDeriv m x).toReal * Real.log (μ.rnDeriv m x).toReal) ∂m ≠ ∞ ∧
      ∫⁻ x, ENNReal.ofReal (-((μ.rnDeriv m x).toReal * Real.log (μ.rnDeriv m x).toReal)) ∂m
        = ∞ := by
  by_cases h : μ ≪ m
  · simp [boltzmannEntropy_of_absolutelyContinuous h, potentialEnergy_eq_bot_iff, h]
  · simp [boltzmannEntropy_of_not_absolutelyContinuous h, h]

/-- For `μ` absolutely continuous with respect to `m`, the Boltzmann entropy is finite exactly when
`ρ log ρ` is integrable against `m`. -/
theorem integrable_mul_log_iff_boltzmannEntropy_ne_top_and_ne_bot (h : μ ≪ m) :
    Integrable (fun x ↦ (μ.rnDeriv m x).toReal * Real.log (μ.rnDeriv m x).toReal) m ↔
      boltzmannEntropy m μ ≠ ⊤ ∧ boltzmannEntropy m μ ≠ ⊥ := by
  rw [boltzmannEntropy_of_absolutelyContinuous h]
  exact integrable_iff_potentialEnergy_ne_top_and_ne_bot (by fun_prop)

/-- If `ρ log ρ` is integrable against `m`, the Boltzmann entropy is its integral. -/
theorem boltzmannEntropy_of_integrable (h : μ ≪ m)
    (hi : Integrable (fun x ↦ (μ.rnDeriv m x).toReal * Real.log (μ.rnDeriv m x).toReal) m) :
    boltzmannEntropy m μ =
      ((∫ x, (μ.rnDeriv m x).toReal * Real.log (μ.rnDeriv m x).toReal ∂m : ℝ) : EReal) := by
  rw [boltzmannEntropy_of_absolutelyContinuous h, potentialEnergy_of_integrable hi]

/-- Against a finite reference measure, the Boltzmann entropy is never `⊥`. -/
theorem boltzmannEntropy_ne_bot [IsFiniteMeasure m] : boltzmannEntropy m μ ≠ ⊥ := by
  by_cases h : μ.singularPart m = 0
  · rw [boltzmannEntropy_def, internalEnergy_of_singularPart_eq_zero h]
    refine potentialEnergy_ne_bot_of_le (integrable_const (-1)) (ae_of_all _ fun x ↦ ?_)
    have hρ : 0 ≤ (μ.rnDeriv m x).toReal := ENNReal.toReal_nonneg
    linarith [Real.self_sub_one_le_mul_log hρ]
  · simp [boltzmannEntropy_def,
      internalEnergy_eq_top_of_recessionConstant_eq_top recessionConstant_mul_log h]

/-- The Boltzmann entropy of the zero measure is `0`. -/
@[simp]
theorem boltzmannEntropy_zero_measure (m : Measure X) : boltzmannEntropy m 0 = 0 :=
  internalEnergy_zero_measure (by simp) m

/-- The Boltzmann entropy of a σ-finite measure relative to itself is `0`. -/
@[simp]
theorem boltzmannEntropy_self (m : Measure X) [SigmaFinite m] : boltzmannEntropy m m = 0 := by
  rw [boltzmannEntropy_of_absolutelyContinuous Measure.AbsolutelyContinuous.rfl]
  have h : (fun x ↦ (m.rnDeriv m x).toReal * Real.log (m.rnDeriv m x).toReal) =ᵐ[m] 0 :=
    m.rnDeriv_self.mono fun x hx ↦ by simp [hx]
  rw [potentialEnergy_congr_ae h, potentialEnergy_of_integrable (integrable_zero _ _ _)]
  simp

/-- For finite measures, the Kullback–Leibler divergence is the Boltzmann entropy up to the mass
correction: `klDiv μ m = Ent_m(μ) + m(X) - μ(X)`. -/
theorem klDiv_eq_boltzmannEntropy_add_sub [IsFiniteMeasure μ] [IsFiniteMeasure m] :
    (klDiv μ m : EReal) = boltzmannEntropy m μ + m.real univ - μ.real univ := by
  by_cases hac : μ ≪ m
  swap
  · simp [hac, boltzmannEntropy_of_not_absolutelyContinuous hac]
  by_cases hint : Integrable (llr μ m) μ
  · have hi := (integrable_rnDeriv_mul_log_iff hac).2 hint
    rw [boltzmannEntropy_of_integrable hac hi, klDiv_of_ac_of_integrable hac hint,
      EReal.coe_ennreal_ofReal, max_eq_left (integral_llr_add_sub_measure_univ_nonneg hac hint)]
    have h : ∫ x, (μ.rnDeriv m x).toReal * Real.log (μ.rnDeriv m x).toReal ∂m
        = ∫ x, llr μ m x ∂μ := integral_rnDeriv_smul hac
    rw [h]
    norm_cast
  · have hi : ¬ Integrable
        (fun x ↦ (μ.rnDeriv m x).toReal * Real.log (μ.rnDeriv m x).toReal) m :=
      mt (integrable_rnDeriv_mul_log_iff hac).1 hint
    have htop : boltzmannEntropy m μ = ⊤ := by
      by_contra hne
      exact hi ((integrable_mul_log_iff_boltzmannEntropy_ne_top_and_ne_bot hac).2
        ⟨hne, boltzmannEntropy_ne_bot⟩)
    simp [klDiv_of_not_integrable hint, htop]

/-- For finite measures of equal mass, in particular for probability measures, the
Kullback–Leibler divergence is the Boltzmann entropy. -/
theorem klDiv_eq_boltzmannEntropy_of_measure_univ_eq [IsFiniteMeasure μ] [IsFiniteMeasure m]
    (h : μ univ = m univ) : (klDiv μ m : EReal) = boltzmannEntropy m μ := by
  rw [klDiv_eq_boltzmannEntropy_add_sub, measureReal_def, measureReal_def, h,
    EReal.add_sub_cancel_right]

/-- For `μ ≪ m`, the Boltzmann entropy `∫ ρ log ρ dm` is the potential energy `∫ log ρ dμ` of the
log-likelihood ratio `log ρ = llr μ m` against `μ` itself. -/
theorem boltzmannEntropy_eq_potentialEnergy_llr [SigmaFinite μ] [SigmaFinite m] (h : μ ≪ m) :
    boltzmannEntropy m μ = potentialEnergy (llr μ m) μ := by
  have key : ∀ F : ℝ → ℝ, Measurable F →
      ∫⁻ x, ENNReal.ofReal ((μ.rnDeriv m x).toReal * F (μ.rnDeriv m x).toReal) ∂m =
        ∫⁻ x, ENNReal.ofReal (F (μ.rnDeriv m x).toReal) ∂μ := fun F hF ↦ by
    rw [← lintegral_rnDeriv_mul h (by fun_prop)]
    refine lintegral_congr_ae ?_
    filter_upwards [Measure.rnDeriv_lt_top μ m] with x hx
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hx.ne]
  have hpos : ∫⁻ x, ENNReal.ofReal
      ((μ.rnDeriv m x).toReal * Real.log (μ.rnDeriv m x).toReal) ∂m =
        ∫⁻ x, ENNReal.ofReal (llr μ m x) ∂μ :=
    key Real.log Real.measurable_log
  have hneg : ∫⁻ x, ENNReal.ofReal
      (-((μ.rnDeriv m x).toReal * Real.log (μ.rnDeriv m x).toReal)) ∂m =
        ∫⁻ x, ENNReal.ofReal (-llr μ m x) ∂μ := by
    simp_rw [← mul_neg]
    exact key (fun t ↦ -Real.log t) Real.measurable_log.neg
  rw [boltzmannEntropy_of_absolutelyContinuous h]
  by_cases hA : ∫⁻ x, ENNReal.ofReal (llr μ m x) ∂μ = ∞
  · rw [potentialEnergy_eq_top_iff.2 hA, potentialEnergy_eq_top_iff.2 (hpos.trans hA)]
  rw [potentialEnergy_of_lintegral_ne_top hA, potentialEnergy_of_lintegral_ne_top (hpos ▸ hA),
    hpos, hneg]

/-- **Change of reference for the Boltzmann entropy.** If `exp f` is integrable against `m`, so
that the tilted measure `m.tilted f = Z⁻¹ exp(f) m` with `Z = ∫ exp f dm` is a finite reference
measure, then for every finite measure `μ` against which `f` is integrable,
`Ent_{m.tilted f}(μ) = Ent_m(μ) - ∫ f dμ + μ(X) log Z`. The reference `m` may be infinite. -/
theorem boltzmannEntropy_tilted [SigmaFinite m] [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Integrable (fun x ↦ Real.exp (f x)) m) (hfμ : Integrable f μ) :
    boltzmannEntropy (m.tilted f) μ = boltzmannEntropy m μ - ((∫ x, f x ∂μ : ℝ) : EReal) +
      ((μ.real univ * Real.log (∫ x, Real.exp (f x) ∂m) : ℝ) : EReal) := by
  by_cases hac : μ ≪ m
  swap
  · have hac' : ¬ μ ≪ m.tilted f := fun h ↦ hac (h.trans (tilted_absolutelyContinuous m f))
    rw [boltzmannEntropy_of_not_absolutelyContinuous hac,
      boltzmannEntropy_of_not_absolutelyContinuous hac', EReal.top_sub_coe, EReal.top_add_coe]
  have hac' : μ ≪ m.tilted f := hac.trans (absolutelyContinuous_tilted hf)
  have hfun : (fun x ↦ -f x + Real.log (∫ z, Real.exp (f z) ∂m) + llr μ m x) =
      fun x ↦ llr μ m x + (-f x + Real.log (∫ z, Real.exp (f z) ∂m)) := by
    ext x
    ring
  rw [boltzmannEntropy_eq_potentialEnergy_llr hac', boltzmannEntropy_eq_potentialEnergy_llr hac,
    potentialEnergy_congr_ae (llr_tilted_right hac hf), hfun,
    potentialEnergy_add_of_integrable (W := fun x ↦ -f x + Real.log (∫ z, Real.exp (f z) ∂m))
      (measurable_llr μ m).aestronglyMeasurable (hfμ.neg.add (integrable_const _)),
    integral_add (f := fun x ↦ -f x) hfμ.neg (integrable_const _), integral_neg, integral_const,
    smul_eq_mul, EReal.coe_add, ← add_assoc, EReal.coe_neg, ← sub_eq_add_neg]

/-- **Change of reference to a Gibbs measure.** If `exp f` is integrable against a nonzero
σ-finite reference `m`, then the tilted measure `m.tilted f = Z⁻¹ exp(f) m`, with
`Z = ∫ exp f dm`, is a probability measure, and for every finite measure `μ` against which `f` is
integrable, `klDiv μ (m.tilted f) = Ent_m(μ) - ∫ f dμ + μ(X) log Z + 1 - μ(X)`. For
`f x = -a d(x, x₀)²` this is the confining Gaussian reference against which the entropy of laws
with finite second moment is controlled. -/
theorem klDiv_tilted_eq_boltzmannEntropy [SigmaFinite m] [NeZero m] [IsFiniteMeasure μ]
    {f : X → ℝ} (hf : Integrable (fun x ↦ Real.exp (f x)) m) (hfμ : Integrable f μ) :
    (klDiv μ (m.tilted f) : EReal) = boltzmannEntropy m μ - ((∫ x, f x ∂μ : ℝ) : EReal) +
      ((μ.real univ * Real.log (∫ x, Real.exp (f x) ∂m) : ℝ) : EReal) + 1 - μ.real univ := by
  have := isProbabilityMeasure_tilted hf
  have h1 : (m.tilted f).real univ = 1 := probReal_univ
  rw [klDiv_eq_boltzmannEntropy_add_sub, boltzmannEntropy_tilted hf hfμ, h1, EReal.coe_one]

/-- If `exp f` is integrable against the reference `m` and `f` is integrable against a finite
measure `μ`, then the Boltzmann entropy of `μ` is not `⊥`, even when `m` is infinite: it is
bounded below through the entropy against the finite reference `m.tilted f`. -/
theorem boltzmannEntropy_ne_bot_of_integrable_exp [SigmaFinite m] [IsFiniteMeasure μ] {f : X → ℝ}
    (hf : Integrable (fun x ↦ Real.exp (f x)) m) (hfμ : Integrable f μ) :
    boltzmannEntropy m μ ≠ ⊥ := fun h ↦ by
  have := boltzmannEntropy_tilted hf hfμ
  rw [h, EReal.bot_sub, EReal.bot_add] at this
  exact boltzmannEntropy_ne_bot this

end BoltzmannEntropy

end TauCeti
