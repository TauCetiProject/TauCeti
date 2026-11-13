/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.Stieltjes.Basic
public import TauCeti.Probability.Process.Predictable.Basic
public import TauCeti.Probability.Process.TimeIntegral

/-!
# Progressive signed Stieltjes integrals

Integrating a strongly progressive Banach-valued process against an adapted increasing
right-continuous process preserves strong progressivity on the original filtration.
The assertion concerns ordinary pathwise Bochner integrals, including their zero value
for nonintegrable sections; it requires no moment bounds or usual conditions.

When the increasing paths are continuous and the integrand is pathwise locally integrable,
the accumulated integral has continuous paths. For almost-sure hypotheses, a predictable
indistinguishable representative is selected on the raw filtration. This gives measurable
continuous finite-variation terms for stochastic change-of-variables formulas without
requiring the signed integrand to be nonnegative or continuous.

The increasing paths are supplied as native `StieltjesFunction`s. The interval `(a,t]`
excludes an initial atom and retains terminal jumps. Continuity of the integral requires
continuity of the integrator; the progressivity result permits jumps.

## References

* P. Protter, *Stochastic Integration and Differential Equations*, second edition,
  Springer, 2005, Chapter I (finite-variation processes).
-/

public section

open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped Topology NNReal

namespace MeasureTheory

variable {Ω R E : Type*} {mΩ : MeasurableSpace Ω}
  [LinearOrder R] [TopologicalSpace R] [OrderTopology R] [CompactIccSpace R]
  [MeasurableSpace R] [BorelSpace R] [SecondCountableTopology R] [DenselyOrdered R]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {ℱ : Filtration R mΩ} {f : Ω → StieltjesFunction R} {H : R → Ω → E}

/-- Pathwise Bochner integration against an adapted increasing right-continuous process
preserves strong progressivity. Neither pathwise integrability nor sample moments are
needed for this measurability assertion. -/
theorem IsStronglyProgressive.setIntegral_stieltjesFunction
    (hH : IsStronglyProgressive ℱ H) (hf : Adapted ℱ (fun t ω ↦ f ω t)) (a : R) :
    IsStronglyProgressive ℱ (fun t ω ↦ ∫ u in Ioc a t, H u ω ∂(f ω).measure) := by
  refine hH.integral_Ioc_kernel (fun ω ↦ (f ω).measure) a
    (fun T ↦ hf.measurable_restrict_measure_Ioc a T) fun T ↦ ?_
  have : ∀ ω, IsFiniteMeasure ((f ω).measure.restrict (Ioc a T)) := fun ω ↦ by
    constructor
    simp [StieltjesFunction.measure_Ioc]
  exact Kernel.isSFiniteKernel_of_isFiniteMeasure _

end MeasureTheory

namespace MeasureTheory.IsStronglyProgressive

variable {Ω E : Type*} {mΩ : MeasurableSpace Ω} {ℱ : Filtration ℝ≥0 mΩ}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  {P : Measure Ω} {f : Ω → StieltjesFunction ℝ≥0} {H : ℝ≥0 → Ω → E}

/-- With everywhere-continuous increasing paths and pathwise local integrability, the
actual accumulated Stieltjes integral is predictable on the original filtration. -/
theorem isStronglyPredictable_setIntegral_stieltjesFunction
    (hH : IsStronglyProgressive ℱ H) (hf : Adapted ℱ (fun t ω ↦ f ω t))
    (hc : ∀ ω, Continuous (f ω)) (a : ℝ≥0)
    (hi : ∀ ω T, IntegrableOn (H · ω) (Ioc a T) (f ω).measure) :
    IsStronglyPredictable ℱ (fun t ω ↦ ∫ u in Ioc a t, H u ω ∂(f ω).measure) := by
  exact (hH.setIntegral_stieltjesFunction hf a).stronglyAdapted.isStronglyPredictable_of_continuous
    (fun ω ↦ (f ω).continuous_setIntegral_Ioc (hc ω) a (hi ω))

/-- Under almost-sure continuity and pathwise local integrability, an accumulated Stieltjes
integral admits a predictable, almost-surely continuous indistinguishable representative.
No completeness, right continuity, or moment hypothesis is imposed on the raw basis. -/
theorem exists_isStronglyPredictable_setIntegral_stieltjesFunction
    [IsCompletelyMetrizableSpace E]
    (hH : IsStronglyProgressive ℱ H) (hf : Adapted ℱ (fun t ω ↦ f ω t))
    (hc : ∀ᵐ ω ∂P, Continuous (f ω)) (a : ℝ≥0)
    (hi : ∀ᵐ ω ∂P, ∀ T, IntegrableOn (H · ω) (Ioc a T) (f ω).measure) :
    ∃ I : ℝ≥0 → Ω → E, IsStronglyPredictable ℱ I ∧
      (∀ᵐ ω ∂P, Continuous (I · ω)) ∧
      ∀ᵐ ω ∂P, ∀ t, I t ω = ∫ u in Ioc a t, H u ω ∂(f ω).measure := by
  have hcont : ∀ᵐ ω ∂P,
      Continuous (fun t ↦ ∫ u in Ioc a t, H u ω ∂(f ω).measure) := by
    filter_upwards [hc, hi] with ω hc hi
    exact (f ω).continuous_setIntegral_Ioc hc a hi
  have ha := (hH.setIntegral_stieltjesFunction hf a).stronglyAdapted
  obtain ⟨I, hI, heq⟩ :=
    ha.exists_isStronglyPredictable_indist_of_ae_isLeftContinuous
      (hcont.mono fun _ h ↦ h.isLeftContinuous)
  refine ⟨I, hI, ?_, heq⟩
  filter_upwards [hcont, heq] with ω hω heqω
  exact hω.congr (fun t ↦ (heqω t).symm)

end MeasureTheory.IsStronglyProgressive
