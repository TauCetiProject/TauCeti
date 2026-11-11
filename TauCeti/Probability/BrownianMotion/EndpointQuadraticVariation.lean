/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.QuadraticVariation
public import TauCeti.Analysis.Calculus.QuadraticSums

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
converging to zero in probability. Weights need only be measurable at each time and
continuous on the horizon outside one common null set; no adaptation or moments are needed.
The partitions may have repeated dates, may start after zero, and need not be nested. -/
theorem tendstoInMeasure_sum_right_mul_sq_sub_sum_left
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    {B X : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    {a T : ℝ≥0} (hX : ∀ t ∈ Icc a T, AEStronglyMeasurable (X t) P)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (fun t ↦ X t ω) (Icc a T))
    {N : ℕ → ℕ} {grid : ∀ k, Fin (N k + 1) → ℝ≥0}
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
  have hm (k : ℕ) (j : Fin (N k + 1)) := hX _ (hmem k j)
  have hinc (k : ℕ) (i : Fin (N k)) : AEStronglyMeasurable
      (fun ω ↦ (B (grid k i.succ) ω - B (grid k i.castSucc) ω) ^ 2) P :=
    (((hB.aemeasurable _).aestronglyMeasurable).sub
      (hB.aemeasurable _).aestronglyMeasurable).pow 2
  have hmeas (k : ℕ) : AEStronglyMeasurable (fun ω ↦
      (∑ i : Fin (N k), X (grid k i.succ) ω *
        (B (grid k i.succ) ω - B (grid k i.castSucc) ω) ^ 2) -
      ∑ i : Fin (N k), X (grid k i.castSucc) ω *
        (B (grid k i.succ) ω - B (grid k i.castSucc) ω) ^ 2) P :=
    (Finset.aestronglyMeasurable_fun_sum univ
      (fun i _ ↦ (hm k i.succ).mul (hinc k i))).sub
      (Finset.aestronglyMeasurable_fun_sum univ
        (fun i _ ↦ (hm k i.castSucc).mul (hinc k i)))
  apply (exists_seq_tendstoInMeasure_atTop_iff hmeas).2
  intro ns hns
  -- Extract only for the unweighted quadratic sum; the continuous weights need no moments.
  have hQ := hB.tendstoInMeasure_quadraticSum hgrid ha hT hmesh hδ
  obtain ⟨ms, hms, hlim⟩ := (hQ.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hc, hlim] with ω hcω hω
  apply hcω.tendsto_sum_right_mul_sq_sub_sum_left
    (B := fun t ↦ B t ω) (grid := fun k ↦ grid (ns (ms k)))
    (δ := fun k ↦ δ (ns (ms k))) (q := (T : ℝ) - a)
    (fun k ↦ hgrid (ns (ms k))) (fun k ↦ (ha (ns (ms k))).ge)
    (fun k ↦ (hT (ns (ms k))).le)
    (fun k i ↦ hmesh (ns (ms k)) i) (hδ.comp (hns.comp hms).tendsto_atTop)
  simpa only [TauCeti.Probability.quadraticSum_def, Function.comp_apply] using hω

end ProbabilityTheory.IsPreBrownianReal
