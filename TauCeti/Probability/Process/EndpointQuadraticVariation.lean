/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Process.QuadraticVariation
public import TauCeti.Analysis.QuadraticSums.EndpointChange

/-!
# Endpoint independence for weighted quadratic sums

If unweighted quadratic sums converge in probability, changing a continuous weight from
left to right endpoints produces an error tending to zero in probability. The grids lie
in a fixed compact set and their mesh tends to zero. Only grid-date measurability of the
processes and almost sure continuity of the weight on that set are needed; no adaptation,
moments, or path regularity of the integrator are required.

## References

* I. Karatzas, S. E. Shreve, *Brownian Motion and Stochastic Calculus*, second edition,
  Springer, 1991, §3.3.
-/

public section

open MeasureTheory Finset Filter Set
open scoped NNReal Topology

namespace TauCeti.Probability

/-- When unweighted quadratic sums converge in probability, the difference between right-
and left-endpoint weighted sums tends to zero in probability for almost surely continuous
weights on a compact set. Measurability is required only at the grid dates. -/
theorem tendstoInMeasure_sum_succ_mul_sq_sub_sum_castSucc
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
    {B X : ℝ≥0 → Ω → ℝ} {s : Set ℝ≥0} (hs : IsCompact s)
    {N : ℕ → ℕ} {grid : ∀ k, Fin (N k + 1) → ℝ≥0}
    (hmem : ∀ k i, grid k i ∈ s) {δ : ℕ → ℝ}
    (hmesh : ∀ k (i : Fin (N k)), dist (grid k i.succ) (grid k i.castSucc) ≤ δ k)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hBmeas : ∀ k i, AEStronglyMeasurable (B (grid k i)) P)
    (hXmeas : ∀ k i, AEStronglyMeasurable (X (grid k i)) P)
    (hc : ∀ᵐ ω ∂P, ContinuousOn (X · ω) s)
    {V : Ω → ℝ} (hV : TendstoInMeasure P (fun k ↦ quadraticSum B (grid k)) atTop V) :
    TendstoInMeasure P (fun k ω ↦
      (∑ i : Fin (N k), X (grid k i.succ) ω *
        (B (grid k i.succ) ω - B (grid k i.castSucc) ω) ^ 2) -
      ∑ i : Fin (N k), X (grid k i.castSucc) ω *
        (B (grid k i.succ) ω - B (grid k i.castSucc) ω) ^ 2) atTop (fun _ ↦ 0) := by
  have hinc (k : ℕ) (i : Fin (N k)) : AEStronglyMeasurable
      (fun ω ↦ (B (grid k i.succ) ω - B (grid k i.castSucc) ω) ^ 2) P :=
    ((hBmeas k i.succ).sub (hBmeas k i.castSucc)).pow 2
  have hmeas (k : ℕ) : AEStronglyMeasurable (fun ω ↦
      (∑ i : Fin (N k), X (grid k i.succ) ω *
        (B (grid k i.succ) ω - B (grid k i.castSucc) ω) ^ 2) -
      ∑ i : Fin (N k), X (grid k i.castSucc) ω *
        (B (grid k i.succ) ω - B (grid k i.castSucc) ω) ^ 2) P :=
    (Finset.aestronglyMeasurable_fun_sum univ
      (fun i _ ↦ (hXmeas k i.succ).mul (hinc k i))).sub
      (Finset.aestronglyMeasurable_fun_sum univ
        (fun i _ ↦ (hXmeas k i.castSucc).mul (hinc k i)))
  apply (exists_seq_tendstoInMeasure_atTop_iff hmeas).2
  intro ns hns
  -- Extract only for the unweighted quadratic sum; the continuous weights need no moments.
  obtain ⟨ms, hms, hlim⟩ := (hV.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [hc, hlim] with ω hcω hω
  apply (hs.uniformContinuousOn_of_continuous hcω).tendsto_sum_succ_mul_sq_sub_sum_castSucc
    (B := fun t ↦ B t ω) (grid := fun k ↦ grid (ns (ms k)))
    (δ := fun k ↦ δ (ns (ms k)))
    (Eventually.of_forall fun k i ↦ hmem (ns (ms k)) i)
    (Eventually.of_forall fun k i ↦ hmesh (ns (ms k)) i)
    (hδ.comp (hns.comp hms).tendsto_atTop)
  have hQ : Tendsto (fun k ↦ ∑ i : Fin (N (ns (ms k))),
      (B (grid (ns (ms k)) i.succ) ω - B (grid (ns (ms k)) i.castSucc) ω) ^ 2)
      atTop (𝓝 (V ω)) := by
    simpa only [quadraticSum_def, Function.comp_apply] using hω
  exact hQ.isBoundedUnder_le

end TauCeti.Probability
