/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Laplace
public import TauCeti.Probability.PointProcess.Poisson.LaplaceCharacterization
public import TauCeti.Probability.RandomMeasure.Superposition

/-!
# Countable independent superposition of Poisson random measures

The sum of countably many independent Poisson random measures is Poisson, with intensity
equal to the sum of the component intensities. This includes independence of disjoint-set
counts and almost-surely infinite counts on sets of infinite summed intensity. It allows
atomic intensities, multiplicities, zero components and an empty index type.

Neither the component intensities nor their sum need be sigma-finite. In particular, this
result can assemble Poisson measures on finite-intensity pieces without assuming a finite
total intensity or local finiteness. The proof combines the countable independent
superposition formula for Laplace functionals with the Poisson Laplace characterization.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Theorem 3.3 (superposition).
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- **Countable Poisson superposition.** Independent Poisson random measures sum to a
Poisson random measure whose intensity is the sum of their intensities. No finiteness,
sigma-finiteness, simplicity or topological hypothesis is required. -/
theorem isPoissonRandomMeasure_sum {ι Ω X : Type*} [Countable ι]
    [MeasurableSpace Ω] [MeasurableSpace X] {P : Measure Ω}
    {N : ι → Ω → Measure X} {Λ : ι → Measure X}
    (hind : iIndepFun N P) (h : ∀ i, IsPoissonRandomMeasure P (N i) (Λ i)) :
    IsPoissonRandomMeasure P (fun ω => Measure.sum fun i => N i ω) (Measure.sum Λ) := by
  apply isPoissonRandomMeasure_of_laplaceFunctional
  · apply Measure.measurable_of_measurable_coe
    intro A hA
    simp only [Measure.sum_apply _ hA]
    exact Measurable.tsum fun i => (Measure.measurable_coe hA).comp (h i).measurable
  · intro f hf
    exact hind.laplaceFunctional_sum_eq_expNeg (fun i => (h i).measurable) hf
      (fun i => (h i).laplaceFunctional_eq_expNeg hf)

end TauCeti.Probability
