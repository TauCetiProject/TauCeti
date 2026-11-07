/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.FreePoisson
public import TauCeti.Probability.FreeProbability.Law.Convergence
public import TauCeti.Probability.FreeProbability.PoissonLimit

/-!
# Weak convergence in the free Poisson limit theorem

For a triangular array of free selfadjoint elements with Bernoulli moments
`φ_N(b_(N,j)^k) = (r/N) c^k`, the scalar laws of the row sums converge weakly to the free
Poisson measure of rate `r ≥ 0` and real jump size `c`. The Bernoulli moment identities are
required only for sufficiently large `N`, allowing arbitrary initial rows when `r/N > 1`.

The proof combines the algebraic rare-event moment limit with compact moment determinacy and
the higher-moment tightness criterion. There is no uniform norm bound on the row sums and no
traciality or faithfulness assumption. Zero rate and negative or zero jumps are included.
The conclusion concerns scalar probability laws, without an operator-norm convergence claim.

## Main results

* `TauCeti.tendsto_law_sum_freePoisson`: weak convergence of the row-sum laws.

## References

* A. Nica, R. Speicher, *Lectures on the Combinatorics of Free Probability*, Proposition 12.11.
* P. Billingsley, *Probability and Measure*, 3rd ed., Theorem 30.2.
-/

public section

open MeasureTheory Filter Topology
open scoped NNReal ComplexOrder

namespace TauCeti

/-- **The weak free Poisson limit theorem.** Free selfadjoint triangular arrays with eventual
Bernoulli moments of mass `r/N` at jump `c` have row-sum laws converging weakly to
`freePoisson r c`. The ambient C⋆-algebras and states may vary with the row. -/
theorem tendsto_law_sum_freePoisson {A : ℕ → Type*} [∀ N, CStarAlgebra (A N)]
    [∀ N, PartialOrder (A N)] [∀ N, StarOrderedRing (A N)]
    (φ : ∀ N, A N →ₚ[ℂ] ℂ) (hφ : ∀ N, φ N 1 = 1) {b : ∀ N, Fin N → A N}
    (h : ∀ N, IsFreelyIndependentElements (φ N).toLinearMap (b N))
    (ha : ∀ N j, IsSelfAdjoint (b N j)) (r : ℝ≥0) (c : ℝ)
    (hb : ∀ᶠ N in atTop, ∀ j k, k ≠ 0 →
      φ N (b N j ^ k) = ((r : ℝ) : ℂ) / N * (c : ℂ) ^ k) :
    Tendsto (β := ProbabilityMeasure ℝ) (fun N =>
      ⟨(φ N).law (∑ j, b N j), (φ N).isProbabilityMeasure_law (hφ N)
        (isSelfAdjoint_sum _ fun j _ => ha N j)⟩) atTop
      (𝓝 (Probability.freePoisson r c).toProbabilityMeasure) := by
  apply PositiveLinearMap.tendsto_law_of_tendsto_apply_pow φ hφ
    (fun N => ∑ j, b N j) (fun N => isSelfAdjoint_sum _ fun j _ => ha N j)
    (Probability.isCompact_support_freePoisson r c) Measure.measure_compl_support
  intro n
  simpa [Probability.integral_pow_freePoisson] using
    tendsto_apply_sum_pow_of_apply_pow_eq_div_mul_pow h hφ hb n

end TauCeti
