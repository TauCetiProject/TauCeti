/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.SpecialFunctions.Exp.Negative
public import Mathlib.MeasureTheory.Measure.GiryMonad
public import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

/-!
# Laplace functionals of random measures

The Laplace functional of `N : Ω → Measure X` is the expectation of
`exp (-∫ f dN)` for a nonnegative extended-valued test function. Infinite test integrals
contribute zero. No local finiteness or integrability assumption is needed to define it.

This file gives law transfer, restriction and mapping identities, continuity under increasing
tests, and multiplicativity under independent superposition. These are the basic operations
used in exponential characterizations of Poisson random measures. Deterministic measures
and single occurrences are included as evaluation rules.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Chapters 2–3.
-/

public section

noncomputable section

open Filter ProbabilityTheory Set
open scoped ENNReal NNReal Topology

namespace MeasureTheory.Measure

variable {Ω X Y : Type*} [MeasurableSpace Ω] [MeasurableSpace X] [MeasurableSpace Y]
  {P : Measure Ω} {N M : Ω → Measure X} {f g : X → ℝ≥0∞}

/-- The Laplace functional of a random measure, with `exp (-∞) = 0`. -/
def laplaceFunctional (P : Measure Ω) (N : Ω → Measure X) (f : X → ℝ≥0∞) : ℝ≥0∞ :=
  ∫⁻ ω, (ENNReal.expNeg (∫⁻ x, f x ∂N ω) : ℝ≥0∞) ∂P

/-- The defining integral of the Laplace functional. -/
theorem laplaceFunctional_def (P : Measure Ω) (N : Ω → Measure X) (f : X → ℝ≥0∞) :
    P.laplaceFunctional N f = ∫⁻ ω, (ENNReal.expNeg (∫⁻ x, f x ∂N ω) : ℝ≥0∞) ∂P := (rfl)

/-- The integrand in a Laplace functional is measurable. -/
@[fun_prop] theorem measurable_expNeg_lintegral (hN : Measurable N) (hf : Measurable f) :
    Measurable (fun ω ↦ (ENNReal.expNeg (∫⁻ x, f x ∂N ω) : ℝ≥0∞)) :=
  measurable_coe_nnreal_ennreal.comp
    (ENNReal.measurable_expNeg.comp ((measurable_lintegral hf).comp hN))

/-- Almost-surely equal random measures have equal Laplace functionals. -/
theorem laplaceFunctional_congr_ae (hNM : N =ᵐ[P] M) :
    P.laplaceFunctional N = P.laplaceFunctional M := by
  funext f
  exact lintegral_congr_ae (hNM.fun_comp fun μ ↦ (ENNReal.expNeg (∫⁻ x, f x ∂μ) : ℝ≥0∞))

/-- Tests equal almost everywhere for almost every realization give the same functional. -/
theorem laplaceFunctional_congr_test_ae (hfg : ∀ᵐ ω ∂P, f =ᵐ[N ω] g) :
    P.laplaceFunctional N f = P.laplaceFunctional N g := by
  apply lintegral_congr_ae
  filter_upwards [hfg] with ω hω
  rw [lintegral_congr_ae hω]

/-- A zero sample-space measure gives a zero functional. -/
@[simp] theorem laplaceFunctional_zero_measure (N : Ω → Measure X) (f : X → ℝ≥0∞) :
    (0 : Measure Ω).laplaceFunctional N f = 0 := by simp [laplaceFunctional_def]

/-- The zero test recovers total sample-space mass. -/
@[simp] theorem laplaceFunctional_zero_test (P : Measure Ω) (N : Ω → Measure X) :
    P.laplaceFunctional N 0 = P univ := by simp [laplaceFunctional_def]

/-- The functional of a deterministic measure, also for infinite test integrals. -/
@[simp] theorem laplaceFunctional_const (P : Measure Ω) (μ : Measure X) (f : X → ℝ≥0∞) :
    P.laplaceFunctional (fun _ ↦ μ) f = (ENNReal.expNeg (∫⁻ x, f x ∂μ) : ℝ≥0∞) * P univ := by
  simp [laplaceFunctional_def]

/-- A single random occurrence evaluates the test at its location. -/
theorem laplaceFunctional_dirac (P : Measure Ω) (Z : Ω → X) (hf : Measurable f) :
    P.laplaceFunctional (fun ω ↦ dirac (Z ω)) f =
      ∫⁻ ω, (ENNReal.expNeg (f (Z ω)) : ℝ≥0∞) ∂P := by
  simp [laplaceFunctional_def, lintegral_dirac' _ hf]

/-- A constant test on a measurable set is the scalar Laplace transform of its count. -/
theorem laplaceFunctional_indicator_const (P : Measure Ω) (N : Ω → Measure X)
    {A : Set X} (hA : MeasurableSet A) (c : ℝ≥0∞) :
    P.laplaceFunctional N (A.indicator (fun _ ↦ c)) =
      ∫⁻ ω, (ENNReal.expNeg (c * N ω A) : ℝ≥0∞) ∂P := by
  simp [laplaceFunctional_def, lintegral_indicator_const hA]

/-- The infinite test on a set recovers its void probability. This does not require
integer-valued or locally finite realizations. -/
theorem laplaceFunctional_indicator_top (hN : Measurable N)
    {A : Set X} (hA : MeasurableSet A) :
    P.laplaceFunctional N (A.indicator (fun _ ↦ ∞)) = P {ω | N ω A = 0} := by
  rw [laplaceFunctional_indicator_const P N hA]
  have heq : (fun ω ↦ (ENNReal.expNeg (∞ * N ω A) : ℝ≥0∞)) =
      {ω | N ω A = 0}.indicator (fun _ ↦ 1) := by
    funext ω
    by_cases h : N ω A = 0 <;> simp [h]
  have hvoid : MeasurableSet {ω | N ω A = 0} :=
    measurableSet_eq_fun ((measurable_coe hA).comp hN) measurable_const
  simp [heq, lintegral_indicator_const hvoid]

/-- A Laplace functional is bounded by the total mass of the sample-space measure. -/
theorem laplaceFunctional_le (P : Measure Ω) (N : Ω → Measure X) (f : X → ℝ≥0∞) :
    P.laplaceFunctional N f ≤ P univ := by
  calc
    _ ≤ ∫⁻ _ : Ω, (1 : ℝ≥0∞) ∂P := lintegral_mono fun ω ↦ by
      exact ENNReal.coe_le_one_iff.mpr (ENNReal.expNeg_le_one _)
    _ = _ := by simp

/-- Increasing the test decreases its Laplace functional. -/
theorem antitone_laplaceFunctional (P : Measure Ω) (N : Ω → Measure X) :
    Antitone (P.laplaceFunctional N) := by
  intro f g hfg
  apply lintegral_mono
  intro ω
  exact ENNReal.coe_le_coe.mpr (ENNReal.antitone_expNeg (lintegral_mono hfg))

/-- Changing the sample space by a measurable map preserves the functional. -/
theorem laplaceFunctional_map {Ω' : Type*} [MeasurableSpace Ω'] (Q : Measure Ω')
    {Z : Ω' → Ω} (hZ : Measurable Z) (hN : Measurable N) (hf : Measurable f) :
    (Q.map Z).laplaceFunctional N f = Q.laplaceFunctional (N ∘ Z) f := by
  exact lintegral_map (measurable_expNeg_lintegral hN hf) hZ

/-- Mapping every realization pulls the test back along the same measurable map. -/
theorem laplaceFunctional_map_measure (P : Measure Ω) (N : Ω → Measure X)
    {q : X → Y} (hq : Measurable q) {f : Y → ℝ≥0∞} (hf : Measurable f) :
    P.laplaceFunctional (fun ω ↦ (N ω).map q) f = P.laplaceFunctional N (f ∘ q) := by
  simp only [laplaceFunctional_def, lintegral_map hf hq, Function.comp_def]

/-- Restricting every realization is equivalent to restricting the test. -/
theorem laplaceFunctional_restrict (P : Measure Ω) (N : Ω → Measure X)
    {A : Set X} (hA : MeasurableSet A) (f : X → ℝ≥0∞) :
    P.laplaceFunctional (fun ω ↦ (N ω).restrict A) f =
      P.laplaceFunctional N (A.indicator f) := by
  simp only [laplaceFunctional_def, lintegral_indicator hA]

/-- Increasing measurable tests give convergence of the Laplace functionals, including
when the limiting test integral is infinite. -/
theorem tendsto_laplaceFunctional_iSup [IsFiniteMeasure P] (hN : Measurable N)
    {f : ℕ → X → ℝ≥0∞} (hf : ∀ n, Measurable (f n)) (hmono : Monotone f) :
    Tendsto (fun n ↦ P.laplaceFunctional N (f n)) atTop
      (𝓝 (P.laplaceFunctional N (fun x ↦ ⨆ n, f n x))) := by
  apply tendsto_lintegral_of_dominated_convergence (fun _ ↦ 1)
    (fun n ↦ measurable_expNeg_lintegral hN (hf n))
  · intro n
    exact ae_of_all _ fun ω ↦ ENNReal.coe_le_coe.mpr (ENNReal.expNeg_le_one _)
  · simp
  · exact ae_of_all _ fun ω ↦ by
      apply ENNReal.continuous_coe.continuousAt.tendsto.comp
      apply ENNReal.continuous_expNeg.continuousAt.tendsto.comp
      rw [lintegral_iSup hf hmono]
      exact tendsto_atTop_iSup (fun i j hij ↦ lintegral_mono (hmono hij))

end MeasureTheory.Measure

namespace ProbabilityTheory

open MeasureTheory

variable {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
  {P : Measure Ω} {N M : Ω → Measure X}

/-- The Laplace functional depends only on the law of the random measure. -/
theorem IdentDistrib.laplaceFunctional_eq {Ω' : Type*} [MeasurableSpace Ω']
    {Q : Measure Ω'} {M : Ω' → Measure X} (h : IdentDistrib N M P Q)
    {f : X → ℝ≥0∞} (hf : Measurable f) :
    P.laplaceFunctional N f = Q.laplaceFunctional M f := by
  have hm : Measurable (fun μ : Measure X ↦ (ENNReal.expNeg (∫⁻ x, f x ∂μ) : ℝ≥0∞)) :=
    Measure.measurable_expNeg_lintegral measurable_id hf
  exact (h.comp hm).lintegral_eq

/-- Independent superposition turns Laplace functionals into products. -/
theorem IndepFun.laplaceFunctional_add (hind : IndepFun N M P)
    (hN : Measurable N) (hM : Measurable M) {f : X → ℝ≥0∞} (hf : Measurable f) :
    P.laplaceFunctional (fun ω ↦ N ω + M ω) f =
      P.laplaceFunctional N f * P.laplaceFunctional M f := by
  simp only [Measure.laplaceFunctional_def, lintegral_add_measure, ENNReal.expNeg_add,
    ENNReal.coe_mul]
  exact lintegral_mul_eq_lintegral_mul_lintegral_of_indepFun
    (Measure.measurable_expNeg_lintegral hN hf) (Measure.measurable_expNeg_lintegral hM hf)
    (hind.comp (Measure.measurable_expNeg_lintegral measurable_id hf)
      (Measure.measurable_expNeg_lintegral measurable_id hf))

end ProbabilityTheory
