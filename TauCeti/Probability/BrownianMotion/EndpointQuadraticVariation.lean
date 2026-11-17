/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.QuadraticVariation
public import TauCeti.Probability.Process.EndpointQuadraticVariation

/-!
# Endpoint independence for weighted Brownian quadratic sums

For an almost surely continuous real weight process, the difference between right- and
left-endpoint weighted Brownian quadratic sums tends to zero in probability on every
fixed compact horizon along deterministic vanishing-mesh partitions. The weight need
not be bounded by a deterministic constant, adapted, or integrable.

In particular one can use the Brownian path itself as the weight. Right-endpoint weights
are anticipative, so they cannot be inserted directly into an adapted weighted
quadratic-variation theorem; this result supplies the endpoint change first. It does not
assert that arbitrary bounded predictable weights admit a left-sum limit.

Only the Brownian finite-dimensional laws are used for the integrator. Path continuity
is required of the weight, not of the integrator.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.3.
-/

public section

open MeasureTheory Finset Filter Set
open scoped NNReal Topology

namespace ProbabilityTheory.IsPreBrownianReal

/-- Right- and left-endpoint weighted Brownian quadratic sums differ by a quantity
converging to zero in probability. Weights need only be measurable at grid dates and
continuous on the horizon outside one common null set; no adaptation or moments are needed.
The partitions may have repeated dates, may start after zero, and need not be nested. -/
theorem tendstoInMeasure_sum_succ_mul_sq_sub_sum_castSucc
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {B X : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {a T : ℝ≥0} {N : ℕ → ℕ} {grid : ∀ k, Fin (N k + 1) → ℝ≥0}
    (hX : ∀ k i, AEStronglyMeasurable (X (grid k i)) P)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t ↦ X t ω) (Icc a T))
    (hgrid : ∀ k, Monotone (grid k)) (ha : ∀ k, grid k 0 = a)
    (hT : ∀ k, grid k (Fin.last (N k)) = T) {δ : ℕ → ℝ}
    (hmesh : ∀ k (i : Fin (N k)), (grid k i.succ : ℝ) - grid k i.castSucc ≤ δ k)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    TendstoInMeasure P (fun k ω ↦
      (∑ i : Fin (N k), X (grid k i.succ) ω *
        (B (grid k i.succ) ω - B (grid k i.castSucc) ω) ^ 2) -
      ∑ i : Fin (N k), X (grid k i.castSucc) ω *
        (B (grid k i.succ) ω - B (grid k i.castSucc) ω) ^ 2) atTop (fun _ ↦ 0) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hmem (k : ℕ) (j : Fin (N k + 1)) : grid k j ∈ Icc a T := by
    constructor
    · rw [← ha k]; exact hgrid k (Fin.zero_le j)
    · rw [← hT k]; exact hgrid k (Fin.le_last j)
  apply TauCeti.Probability.tendstoInMeasure_sum_succ_mul_sq_sub_sum_castSucc
    isCompact_Icc hmem (δ := δ) _ hδ
    (fun k i ↦ (hB.aemeasurable (grid k i)).aestronglyMeasurable) hX hc
    (hB.tendstoInMeasure_quadraticSum hgrid ha hT hmesh hδ)
  intro k i
  rw [NNReal.dist_eq, abs_of_nonneg (sub_nonneg.2 (by
    exact_mod_cast (hgrid k (Fin.castSucc_le_succ i))))]
  exact hmesh k i

end ProbabilityTheory.IsPreBrownianReal
