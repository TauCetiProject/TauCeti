/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.CharacteristicFunction.Basic
public import Mathlib.Probability.ConditionalExpectation
public import Mathlib.Probability.HasLaw
public import Mathlib.Probability.Independence.Basic
import TauCeti.MeasureTheory.Function.ConditionalExpectation
import TauCeti.MeasureTheory.Measure.CharacteristicFunction.Basic

/-!
# Independence from a sub-sigma-algebra via characteristic functions

Characterizes independence of an a.e.-measurable random variable `X` in a complete second-countable
real inner product space from a sub-sigma-algebra `m` via deterministic conditional characteristic
functions (`P[exp (⟪X, t⟫ * I) | m]`) and set-integral factorizations
`∫ ω in A, exp (⟪X ω, t⟫ * I) ∂P = P.real A * φ t` for `A ∈ m`, using
`MeasureTheory.Measure.ext_of_charFun`.

## References

* O. Kallenberg, *Foundations of Modern Probability*, third edition, Springer, 2021,
  Chapter 6 (conditional characteristic functions).
-/

public section

open MeasureTheory Complex
open scoped RealInnerProductSpace

namespace ProbabilityTheory
variable {Ω E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [SecondCountableTopology E] {m mΩ : MeasurableSpace Ω}
  {P : Measure Ω}

/-- A random variable in a complete second-countable real inner product space has law `μ`
whenever its characteristic integral matches `charFun μ` everywhere. -/
theorem hasLaw_of_forall_integral_exp_inner_mul_I [IsFiniteMeasure P] {μ : Measure E}
    [IsFiniteMeasure μ] {X : Ω → E} (hX : AEMeasurable X P)
    (h : ∀ t : E, ∫ ω, exp ((⟪X ω, t⟫ : ℂ) * I) ∂P = charFun μ t) : HasLaw X μ P where
  aemeasurable := hX
  map_eq := by
    have : IsFiniteMeasure (P.map X) := Measure.isFiniteMeasure_map P X
    exact Measure.ext_of_charFun (funext fun t ↦ by rw [charFun_map_eq_integral hX t, h t])

/-- A random variable in a complete second-countable real inner product space is independent
of a sub-sigma-algebra `m` if and only if its characteristic integral over every event `A ∈ m`
factors as `(P A).toReal * charFun (P.map X) t`. -/
theorem indep_comap_iff_forall_setIntegral_exp_inner_mul_I [IsZeroOrProbabilityMeasure P]
    (hm : m ≤ mΩ) {X : Ω → E} (hX : AEMeasurable X P) :
    Indep (.comap X inferInstance) m P ↔ ∀ t : E, ∀ A, MeasurableSet[m] A →
      ∫ ω in A, exp ((⟪X ω, t⟫ : ℂ) * I) ∂P = ((P A).toReal : ℂ) * charFun (P.map X) t := by
  rcases eq_zero_or_isProbabilityMeasure P with rfl | hP; · simp [Indep_iff]
  have : IsFiniteMeasure (P.map X) := Measure.isFiniteMeasure_map P X
  refine ⟨fun hind t A hA ↦ ?_, fun h ↦ (Indep_iff _ _ _).2 ?_⟩
  · have hmap : (P.restrict A).map X = P A • P.map X := by
      ext S hS; rw [Measure.map_apply_of_aemeasurable hX.restrict hS,
        Measure.restrict_apply' (hm A hA), smul_apply, smul_eq_mul,
        Measure.map_apply_of_aemeasurable hX hS, mul_comm]
      exact (Indep_iff _ _ _).1 hind _ _ ⟨S, hS, rfl⟩ hA
    rw [← charFun_map_eq_integral hX.restrict t, hmap, charFun_smul_measure]
  · rintro _ A ⟨S, hS, rfl⟩ hA
    have : IsFiniteMeasure ((P.restrict A).map X) := Measure.isFiniteMeasure_map _ X
    have : IsFiniteMeasure (P A • P.map X) := ⟨by simp⟩
    have hmap := Measure.ext_of_charFun (μ := (P.restrict A).map X) (ν := P A • P.map X)
      (funext fun t ↦ by rw [charFun_map_eq_integral hX.restrict t, h t A hA, charFun_smul_measure])
    simpa only [Measure.map_apply_of_aemeasurable hX.restrict hS, Measure.restrict_apply' (hm A hA),
      smul_apply, smul_eq_mul, Measure.map_apply_of_aemeasurable hX hS, mul_comm] using
      congrArg (fun ν : Measure E ↦ ν S) hmap

/-- If the characteristic integral of `X` over every event `A ∈ m` factors as
`(P A).toReal * φ t` for some deterministic function `φ`, then `X` is independent of `m`.
When `P` is a probability measure (`P ≠ 0`), evaluating at `A = univ` identifies `φ` with
`charFun (P.map X)`. -/
theorem indep_comap_of_setIntegral_exp_inner_mul_I [IsZeroOrProbabilityMeasure P] (hm : m ≤ mΩ)
    {X : Ω → E} (hX : AEMeasurable X P) {φ : E → ℂ} (h : ∀ t : E, ∀ A, MeasurableSet[m] A →
      ∫ ω in A, exp ((⟪X ω, t⟫ : ℂ) * I) ∂P = ((P A).toReal : ℂ) * φ t) :
    Indep (.comap X inferInstance) m P := by
  rcases eq_zero_or_isProbabilityMeasure P with rfl | hP; · simp [Indep_iff]
  have hφ (t : E) : charFun (P.map X) t = φ t := by
    simpa [charFun_map_eq_integral hX t] using h t Set.univ MeasurableSet.univ
  exact (indep_comap_iff_forall_setIntegral_exp_inner_mul_I hm hX).2 fun t A hA ↦ by
    rw [hφ t]
    exact h t A hA

/-- A random variable in a complete second-countable real inner product space is independent
of a sub-sigma-algebra `m` if and only if its conditional characteristic function given `m`
almost surely equals its unconditional characteristic function. -/
theorem indep_comap_iff_forall_condExp_exp_inner_mul_I [IsZeroOrProbabilityMeasure P] (hm : m ≤ mΩ)
    {X : Ω → E} (hX : AEMeasurable X P) : Indep (.comap X inferInstance) m P ↔
      ∀ t : E, P[fun ω ↦ exp ((⟪X ω, t⟫ : ℂ) * I) | m] =ᵐ[P] fun _ ↦ charFun (P.map X) t := by
  rw [indep_comap_iff_forall_setIntegral_exp_inner_mul_I hm hX]
  refine forall_congr' fun t ↦ ?_
  rw [TauCeti.MeasureTheory.condExp_ae_eq_const_iff hm (hX.integrable_exp_inner_mul_I t)]
  simp only [Measure.real, Complex.real_smul, measure_lt_top, true_implies]

/-- If the conditional characteristic function of `X` given `m` is almost surely equal to a
deterministic function `φ`, then `X` is independent of `m`. -/
theorem indep_comap_of_condExp_exp_inner_mul_I [IsZeroOrProbabilityMeasure P] (hm : m ≤ mΩ)
    {X : Ω → E} (hX : AEMeasurable X P) {φ : E → ℂ}
    (h : ∀ t : E, P[fun ω ↦ exp ((⟪X ω, t⟫ : ℂ) * I) | m] =ᵐ[P] fun _ ↦ φ t) :
    Indep (.comap X inferInstance) m P :=
  indep_comap_of_setIntegral_exp_inner_mul_I hm hX fun t A hA ↦ by
    simpa only [Measure.real, Complex.real_smul] using
      (TauCeti.MeasureTheory.condExp_ae_eq_const_iff hm
        (hX.integrable_exp_inner_mul_I t) (φ t)).1 (h t) A hA (measure_lt_top _ _)

end ProbabilityTheory
