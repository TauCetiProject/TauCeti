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
selected components.

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

end TauCeti.Probability
