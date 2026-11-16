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

/-!
# Independence from a sub-sigma-algebra via characteristic functions

A random variable `X` taking values in a complete second-countable real inner product space is
independent of a sub-sigma-algebra `m` if and only if its conditional characteristic function
given `m` is almost surely deterministic, equivalently if and only if for every `t` and every
event `A ∈ m`,

`∫ ω in A, exp (⟪X ω, t⟫ * I) ∂P = P.real A * charFun (P.map X) t`.

For applications such as Lévy's characterization of Brownian motion, we also provide the
sufficient forms where the deterministic factor `φ t` is not identified with `charFun (P.map X) t`
in advance: setting `A = univ` recovers `charFun (P.map X) = φ` automatically.

The proof reduces independence on each event `A ∈ m` to the measure identity
`(P.restrict A).map X = P A • P.map X`, established by `MeasureTheory.Measure.ext_of_charFun`.
Only almost-everywhere measurability of `X` is required.

## References

* O. Kallenberg, *Foundations of Modern Probability*, third edition, Springer, 2021,
  Chapter 6 (conditional characteristic functions).
-/

public section

open MeasureTheory Complex
open scoped RealInnerProductSpace

namespace ProbabilityTheory

variable {Ω E : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

private lemma charFun_smul_measure {μ : Measure E} (c : ENNReal) (t : E) :
    charFun (c • μ) t = (c.toReal : ℂ) * charFun μ t := by
  simp [charFun_apply, integral_smul_measure, Complex.real_smul]

variable [BorelSpace E]

private lemma integrable_exp_inner_I {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {X : Ω → E} (hX : AEMeasurable X P) (t : E) :
    Integrable (fun ω ↦ exp ((⟪X ω, t⟫ : ℂ) * I)) P := by
  refine (integrable_const (1 : ℝ)).mono' ?_ (ae_of_all P fun ω ↦ ?_)
  · exact ((continuous_exp.comp ((Complex.continuous_ofReal.comp
      (continuous_id.inner continuous_const)).mul continuous_const)).measurable.comp_aemeasurable
      hX).aestronglyMeasurable
  · rw [Complex.norm_exp_ofReal_mul_I]

private lemma charFun_map_eq_integral {mΩ : MeasurableSpace Ω} {Q : Measure Ω} {X : Ω → E}
    (hX : AEMeasurable X Q) (t : E) :
    charFun (Q.map X) t = ∫ ω, exp ((⟪X ω, t⟫ : ℂ) * I) ∂Q := by
  rw [charFun_apply, integral_map hX]
  exact (continuous_exp.comp ((Complex.continuous_ofReal.comp
    (continuous_id.inner continuous_const)).mul continuous_const)).aestronglyMeasurable

variable [CompleteSpace E] [SecondCountableTopology E]

/-- A random variable in a complete second-countable real inner product space has law `μ`
whenever its characteristic integral matches `charFun μ` everywhere. -/
theorem hasLaw_of_forall_integral_exp_inner_I {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] {μ : Measure E} [IsFiniteMeasure μ] {X : Ω → E}
    (hX : AEMeasurable X P)
    (h : ∀ t : E, ∫ ω, exp ((⟪X ω, t⟫ : ℂ) * I) ∂P = charFun μ t) :
    HasLaw X μ P where
  aemeasurable := hX
  map_eq := by
    have : IsFiniteMeasure (P.map X) := Measure.isFiniteMeasure_map P X
    refine Measure.ext_of_charFun (funext fun t ↦ ?_)
    rw [charFun_map_eq_integral hX t, h t]

section SubSigmaAlgebra

variable {m mΩ : MeasurableSpace Ω} {P : Measure Ω}

/-- A random variable in a complete second-countable real inner product space is independent
of a sub-sigma-algebra `m` if and only if its characteristic integral over every event `A ∈ m`
factors as `(P A).toReal * charFun (P.map X) t`. -/
theorem indep_comap_iff_forall_setIntegral_exp_inner_I [IsZeroOrProbabilityMeasure P]
    (hm : m ≤ mΩ) {X : Ω → E} (hX : AEMeasurable X P) :
    Indep (.comap X inferInstance) m P ↔
      ∀ t : E, ∀ A, MeasurableSet[m] A →
        ∫ ω in A, exp ((⟪X ω, t⟫ : ℂ) * I) ∂P =
          ((P A).toReal : ℂ) * charFun (P.map X) t := by
  rcases eq_zero_or_isProbabilityMeasure P with rfl | hP
  · simp [Indep_iff]
  have : IsFiniteMeasure (P.map X) := Measure.isFiniteMeasure_map P X
  constructor
  · intro hind t A hA
    have hmap : (P.restrict A).map X = P A • P.map X := by
      ext S hS
      rw [Measure.map_apply_of_aemeasurable hX.restrict hS, Measure.restrict_apply' (hm A hA),
        smul_apply, smul_eq_mul, Measure.map_apply_of_aemeasurable hX hS, mul_comm]
      exact (Indep_iff _ _ _).1 hind _ _ ⟨S, hS, rfl⟩ hA
    rw [← charFun_map_eq_integral hX.restrict t, hmap, charFun_smul_measure]
  · intro h
    rw [Indep_iff]
    rintro _ A ⟨S, hS, rfl⟩ hA
    have : IsFiniteMeasure ((P.restrict A).map X) := Measure.isFiniteMeasure_map _ X
    have : IsFiniteMeasure (P A • P.map X) := ⟨by simp⟩
    have hmap : (P.restrict A).map X = P A • P.map X := by
      refine Measure.ext_of_charFun (funext fun t ↦ ?_)
      rw [charFun_map_eq_integral hX.restrict t, h t A hA, charFun_smul_measure]
    have hS_eq := congrArg (fun ν : Measure E ↦ ν S) hmap
    rw [Measure.map_apply_of_aemeasurable hX.restrict hS, Measure.restrict_apply' (hm A hA),
      smul_apply, smul_eq_mul, Measure.map_apply_of_aemeasurable hX hS, mul_comm] at hS_eq
    exact hS_eq

/-- If the characteristic integral of `X` over every event `A ∈ m` factors as
`(P A).toReal * φ t` for some deterministic function `φ`, then `X` is independent of `m`.
Evaluating at `A = univ` identifies `φ` with `charFun (P.map X)`. -/
theorem indep_comap_of_setIntegral_exp_inner_I [IsZeroOrProbabilityMeasure P]
    (hm : m ≤ mΩ) {X : Ω → E} (hX : AEMeasurable X P) {φ : E → ℂ}
    (h : ∀ t : E, ∀ A, MeasurableSet[m] A →
      ∫ ω in A, exp ((⟪X ω, t⟫ : ℂ) * I) ∂P = ((P A).toReal : ℂ) * φ t) :
    Indep (.comap X inferInstance) m P := by
  rcases eq_zero_or_isProbabilityMeasure P with rfl | hP
  · simp [Indep_iff]
  refine (indep_comap_iff_forall_setIntegral_exp_inner_I hm hX).2 fun t A hA ↦ ?_
  have hφ : charFun (P.map X) t = φ t := by
    have huniv := h t Set.univ MeasurableSet.univ
    rw [Measure.restrict_univ, measure_univ, ENNReal.toReal_one, Complex.ofReal_one, one_mul]
      at huniv
    rw [charFun_map_eq_integral hX t, huniv]
  rw [hφ]
  exact h t A hA

/-- A random variable in a complete second-countable real inner product space is independent
of a sub-sigma-algebra `m` if and only if its conditional characteristic function given `m`
almost surely equals its unconditional characteristic function. -/
theorem indep_comap_iff_forall_condExp_exp_inner_I [IsZeroOrProbabilityMeasure P]
    (hm : m ≤ mΩ) {X : Ω → E} (hX : AEMeasurable X P) :
    Indep (.comap X inferInstance) m P ↔
      ∀ t : E, P[fun ω ↦ exp ((⟪X ω, t⟫ : ℂ) * I) | m] =ᵐ[P]
        fun _ ↦ charFun (P.map X) t := by
  rw [indep_comap_iff_forall_setIntegral_exp_inner_I hm hX]
  constructor
  · intro h t
    refine (ae_eq_condExp_of_forall_setIntegral_eq hm (integrable_exp_inner_I hX t)
      (fun _ _ _ ↦ (integrable_const _).integrableOn) (fun A hA _ ↦ ?_)
      aestronglyMeasurable_const).symm
    rw [setIntegral_const, Measure.real, Complex.real_smul, h t A hA]
  · intro h t A hA
    calc
      ∫ ω in A, exp ((⟪X ω, t⟫ : ℂ) * I) ∂P
          = ∫ ω in A, P[fun ω ↦ exp ((⟪X ω, t⟫ : ℂ) * I) | m] ω ∂P :=
        (setIntegral_condExp hm (integrable_exp_inner_I hX t) hA).symm
      _ = ∫ _ in A, charFun (P.map X) t ∂P :=
        setIntegral_congr_ae (hm A hA) ((h t).mono fun _ hω _ ↦ hω)
      _ = ((P A).toReal : ℂ) * charFun (P.map X) t := by
        rw [setIntegral_const, Measure.real, Complex.real_smul]

/-- If the conditional characteristic function of `X` given `m` is almost surely equal to a
deterministic function `φ`, then `X` is independent of `m`. -/
theorem indep_comap_of_condExp_exp_inner_I [IsZeroOrProbabilityMeasure P]
    (hm : m ≤ mΩ) {X : Ω → E} (hX : AEMeasurable X P) {φ : E → ℂ}
    (h : ∀ t : E,
      P[fun ω ↦ exp ((⟪X ω, t⟫ : ℂ) * I) | m] =ᵐ[P] fun _ ↦ φ t) :
    Indep (.comap X inferInstance) m P := by
  refine indep_comap_of_setIntegral_exp_inner_I hm hX (φ := φ) fun t A hA ↦ ?_
  calc
    ∫ ω in A, exp ((⟪X ω, t⟫ : ℂ) * I) ∂P
        = ∫ ω in A, P[fun ω ↦ exp ((⟪X ω, t⟫ : ℂ) * I) | m] ω ∂P :=
      (setIntegral_condExp hm (integrable_exp_inner_I hX t) hA).symm
    _ = ∫ _ in A, φ t ∂P :=
      setIntegral_congr_ae (hm A hA) ((h t).mono fun _ hω _ ↦ hω)
    _ = ((P A).toReal : ℂ) * φ t := by
      rw [setIntegral_const, Measure.real, Complex.real_smul]

end SubSigmaAlgebra

end ProbabilityTheory
