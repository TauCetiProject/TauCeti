/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.PointProcess.Poisson.Superposition.Countable

/-!
# Finite independent superposition of Poisson random measures

Adding independent Poisson random measures adds their intensity measures. Independence of
counts on disjoint sets is preserved, not merely the individual Poisson count laws.
The result holds on arbitrary measurable spaces, permits atomic intensities and multiple
occurrences, and includes the empty family. Counts on sets of infinite intensity remain
almost surely infinite.

The finite result specializes countable independent superposition to the subtype of
selected components. The sum of two independent Poisson random measures, which needs only
their pairwise independence, is computed directly from their Laplace functionals.

## References

* G. Last and M. Penrose, *Lectures on the Poisson Process*, Cambridge University Press,
  2018, Theorem 3.3 (superposition).
-/

public section

open MeasureTheory ProbabilityTheory

namespace TauCeti.Probability

/-- A finite superposition of independent Poisson random measures is Poisson with the sum
of their intensities. Only the selected components need be independent or Poisson.
Atomic and infinite intensities, zero components and the empty family are allowed.
No topology, simplicity or local finiteness assumption is required. -/
theorem isPoissonRandomMeasure_finsetSum {Ω X ι : Type*}
    [MeasurableSpace Ω] [MeasurableSpace X] {P : Measure Ω}
    {N : ι → Ω → Measure X} {Λ : ι → Measure X} {s : Finset ι}
    (h : ∀ i ∈ s, IsPoissonRandomMeasure P (N i) (Λ i))
    (hind : iIndepFun (fun i : s => N i) P) :
    IsPoissonRandomMeasure P (fun ω => ∑ i ∈ s, N i ω) (∑ i ∈ s, Λ i) := by
  have hs := isPoissonRandomMeasure_sum hind (fun i : s => h i i.property)
  simp only [Measure.sum_fintype] at hs
  have he (ω : Ω) : (∑ i : s, N i ω) = ∑ i ∈ s, N i ω :=
    Finset.sum_coe_sort s (fun i => N i ω)
  rwa [funext he, Finset.sum_coe_sort] at hs

/-- The sum of two independent Poisson random measures is Poisson with the sum of their
intensities. Atomic and infinite intensities are allowed. No topology, simplicity or local
finiteness assumption is required. -/
theorem isPoissonRandomMeasure_add {Ω X : Type*} [MeasurableSpace Ω] [MeasurableSpace X]
    {P : Measure Ω} {N M : Ω → Measure X} {Λ Λ' : Measure X}
    (hN : IsPoissonRandomMeasure P N Λ) (hM : IsPoissonRandomMeasure P M Λ')
    (hind : IndepFun N M P) :
    IsPoissonRandomMeasure P (fun ω => N ω + M ω) (Λ + Λ') := by
  refine isPoissonRandomMeasure_of_laplaceFunctional (hN.measurable.add hM.measurable)
    fun f hf => ?_
  rw [hind.laplaceFunctional_add hN.measurable hM.measurable hf,
    hN.laplaceFunctional_eq_expNeg hf, hM.laplaceFunctional_eq_expNeg hf,
    lintegral_add_measure, ENNReal.expNeg_add, ENNReal.coe_mul]

end TauCeti.Probability
