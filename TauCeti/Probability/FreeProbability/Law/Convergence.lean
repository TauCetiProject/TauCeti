/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.FreeProbability.Law.Basic
public import TauCeti.Probability.Moments.WeakConvergence

/-!
# Weak convergence of scalar laws

For selfadjoint elements in C⋆-probability spaces, convergence of all scalar moments to the
moments of a compactly supported probability measure implies weak convergence of their laws.
The ambient algebras and states may vary with the parameter. No common bound on the norms of
the elements, and hence no common compact support for their laws, is required.

This connects `PositiveLinearMap.ofReal_integral_pow_law` to the method of moments
`MeasureTheory.ProbabilityMeasure.tendsto_of_tendsto_integral_pow`. It allows algebraic
moment limit theorems to yield weak convergence for C⋆-realizations without imposing
traciality or faithfulness.

## References

* P. Billingsley, *Probability and Measure*, 3rd ed., Theorem 30.2.
* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Lecture 3.
-/

public section

open MeasureTheory Filter Topology
open scoped ComplexOrder

namespace PositiveLinearMap

variable {ι : Type*} {A : ι → Type*} [∀ i, CStarAlgebra (A i)]
  [∀ i, PartialOrder (A i)] [∀ i, StarOrderedRing (A i)]

/-- Convergence of every scalar moment of selfadjoint elements to the moments of a compactly
supported probability measure implies weak convergence of their laws. The algebras and states
may vary, and the approximating elements need not have uniformly bounded norms. -/
theorem tendsto_law_of_tendsto_apply_pow (φ : (i : ι) → A i →ₚ[ℂ] ℂ)
    (hφ : ∀ i, φ i 1 = 1) (a : (i : ι) → A i) (ha : ∀ i, IsSelfAdjoint (a i))
    {l : Filter ι} {μ : ProbabilityMeasure ℝ} {K : Set ℝ}
    (hK : IsCompact K) (hμK : (μ : Measure ℝ) Kᶜ = 0)
    (hmom : ∀ n : ℕ, Tendsto (fun i => φ i (a i ^ n)) l
      (𝓝 ((∫ x, x ^ n ∂(μ : Measure ℝ) : ℝ) : ℂ))) :
    Tendsto (β := ProbabilityMeasure ℝ)
      (fun i => ⟨(φ i).law (a i), (φ i).isProbabilityMeasure_law (hφ i) (ha i)⟩) l (𝓝 μ) := by
  apply ProbabilityMeasure.tendsto_of_tendsto_integral_pow hK hμK
  · intro n
    exact Eventually.of_forall fun i => (φ i).integrable_pow_law (a i) n
  · intro n
    apply Filter.tendsto_ofReal_iff.mp
    simpa only [ProbabilityMeasure.coe_mk, ofReal_integral_pow_law _ (ha _) n] using hmom n

end PositiveLinearMap
