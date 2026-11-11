/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.BrownianMotion.QuadraticVariation
public import TauCeti.Analysis.BoundedVariation.QuadraticSums

/-!
# Quadratic sums are unchanged by continuous finite variation

Adding a continuous finite-variation process to a continuous real process does not change
its partition quadratic-variation limit in probability. The pathwise difference of quadratic
sums tends to zero: both the cross term and the finite-variation square term vanish.
This separates the finite-variation part of a continuous semimartingale from the part
contributing to its quadratic variation.

The result concerns deterministic partitions and their limits, not construction of a bracket.
It requires neither adaptation nor a martingale hypothesis. Path regularity and finite variation
hold outside a common sample-null set; no moment bound on total variation is assumed.

## References

* D. Revuz and M. Yor, *Continuous Martingales and Brownian Motion*, third edition,
  Chapter IV, §1.
-/

public section

open Filter MeasureTheory Set
open scoped NNReal Topology

namespace TauCeti.Probability

variable {Ω : Type*} {X A : ℝ≥0 → Ω → ℝ} {s : Set ℝ≥0}

private theorem tendsto_quadraticSum_add_sub {ι : Type*} {l : Filter ι} {N : ι → ℕ}
    {grid : ∀ k, Fin (N k + 1) → ℝ≥0} (hgrid : ∀ k, Monotone (grid k))
    (hmem : ∀ k i, grid k i ∈ s) {δ : ι → ℝ}
    (hmesh : ∀ k (i : Fin (N k)), dist (grid k i.succ) (grid k i.castSucc) ≤ δ k)
    (hδ : Tendsto δ l (𝓝 0)) {ω : Ω} (hA : BoundedVariationOn (A · ω) s)
    (hcA : UniformContinuousOn (A · ω) s) (hcX : UniformContinuousOn (X · ω) s) :
    Tendsto (fun k ↦ quadraticSum (X + A) (grid k) ω - quadraticSum X (grid k) ω)
      l (𝓝 0) := by
  -- Extend a finite grid constantly to use the existing natural-index pathwise estimate.
  let u (k : ι) (j : ℕ) :=
    grid k ⟨min j (N k), Nat.lt_succ_of_le (Nat.min_le_right j (N k))⟩
  have hu (k : ι) : MonotoneOn (u k) (Iic (N k)) :=
    fun i _ j _ hij ↦ hgrid k (min_le_min_right (N k) hij)
  have hleft (k : ι) (i : Fin (N k)) : u k i = grid k i.castSucc := by
    simp only [u, min_eq_left (Nat.le_of_lt i.isLt)]
    rfl
  have hright (k : ι) (i : Fin (N k)) : u k (i + 1) = grid k i.succ := by
    simp only [u, min_eq_left (Nat.succ_le_of_lt i.isLt)]
    rfl
  have hmesh' (k : ι) (i : ℕ) (hi : i < N k) :
      dist (u k (i + 1)) (u k i) ≤ δ k := by
    simpa only [hright k ⟨i, hi⟩, hleft k ⟨i, hi⟩] using hmesh k ⟨i, hi⟩
  have hlim := hcX.tendsto_sum_sq_add_sub_of_boundedVariationOn hcA hA hu
    (fun k i _ ↦ hmem k _) hmesh' hδ
  simpa only [← Fin.sum_univ_eq_sum_range, hleft, hright, quadraticSum_def,
    Pi.add_apply] using hlim

/-- A continuous finite-variation perturbation preserves any quadratic-sum limit in
probability. Both processes need only have measurable values at the grid dates. -/
theorem tendstoInMeasure_quadraticSum_add {mΩ : MeasurableSpace Ω} {P : Measure Ω}
    [IsFiniteMeasure P] (hs : IsCompact s) {N : ℕ → ℕ}
    {grid : ∀ k, Fin (N k + 1) → ℝ≥0} (hgrid : ∀ k, Monotone (grid k))
    (hmem : ∀ k i, grid k i ∈ s) {δ : ℕ → ℝ}
    (hmesh : ∀ k (i : Fin (N k)), dist (grid k i.succ) (grid k i.castSucc) ≤ δ k)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hXmeas : ∀ k i, AEStronglyMeasurable (X (grid k i)) P)
    (hAmeas : ∀ k i, AEStronglyMeasurable (A (grid k i)) P)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (X · ω) s ∧ ContinuousOn (A · ω) s ∧
      BoundedVariationOn (A · ω) s)
    {V : Ω → ℝ} (hV : TendstoInMeasure P (fun k ↦ quadraticSum X (grid k)) atTop V) :
    TendstoInMeasure P (fun k ↦ quadraticSum (X + A) (grid k)) atTop V := by
  have hmeas (k : ℕ) : AEStronglyMeasurable (quadraticSum (X + A) (grid k)) P := by
    rw [quadraticSum_def]
    simpa only [Finset.sum_fn, Pi.pow_apply, Pi.sub_apply, Pi.add_apply] using
      Finset.aestronglyMeasurable_sum Finset.univ (fun (i : Fin (N k)) _ ↦
        (((hXmeas k i.succ).add (hAmeas k i.succ)).sub
          ((hXmeas k i.castSucc).add (hAmeas k i.castSucc))).pow 2)
  have herr : ∀ᵐ ω ∂P, Tendsto (fun k ↦
      quadraticSum (X + A) (grid k) ω - quadraticSum X (grid k) ω) atTop (𝓝 0) := by
    filter_upwards [hcont] with ω hω
    exact tendsto_quadraticSum_add_sub hgrid hmem hmesh hδ hω.2.2
      (hs.uniformContinuousOn_of_continuous hω.2.1)
      (hs.uniformContinuousOn_of_continuous hω.1)
  apply (exists_seq_tendstoInMeasure_atTop_iff hmeas).2
  intro ns hns
  obtain ⟨ms, hms, hlim⟩ := (hV.comp hns.tendsto_atTop).exists_seq_tendsto_ae
  refine ⟨ms, hms, ?_⟩
  filter_upwards [herr, hlim] with ω he hv
  have he' := he.comp (hns.comp hms).tendsto_atTop
  simpa only [Function.comp_apply, sub_add_cancel, zero_add] using he'.add hv

end TauCeti.Probability

namespace ProbabilityTheory.IsBrownianReal

open TauCeti.Probability

/-- Brownian motion plus a continuous finite-variation process has quadratic sums converging
in probability to elapsed time, with no integrability assumption on the perturbation. -/
theorem tendstoInMeasure_quadraticSum_add_of_boundedVariationOn
    {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} {B A : ℝ≥0 → Ω → ℝ}
    (hB : IsBrownianReal B P) {N : ℕ → ℕ} {grid : ∀ k, Fin (N k + 1) → ℝ≥0}
    {a b : ℝ≥0} (hgrid : ∀ k, Monotone (grid k)) (ha : ∀ k, grid k 0 = a)
    (hb : ∀ k, grid k (Fin.last (N k)) = b) {δ : ℕ → ℝ}
    (hmesh : ∀ k (i : Fin (N k)), dist (grid k i.succ) (grid k i.castSucc) ≤ δ k)
    (hδ : Tendsto δ atTop (𝓝 0))
    (hAmeas : ∀ k i, AEStronglyMeasurable (A (grid k i)) P)
    (hA : ∀ᵐ ω ∂P, ContinuousOn (A · ω) (Icc a b) ∧
      BoundedVariationOn (A · ω) (Icc a b)) :
    TendstoInMeasure P (fun k ↦ quadraticSum (B + A) (grid k)) atTop
      (fun _ ↦ (b : ℝ) - a) := by
  have : IsProbabilityMeasure P := (hB.hasLaw_eval 0).isProbabilityMeasure
  have hmem (k : ℕ) (i : Fin (N k + 1)) : grid k i ∈ Icc a b := by
    constructor
    · simpa only [ha k] using hgrid k (Fin.zero_le i)
    · simpa only [hb k] using hgrid k (Fin.le_last i)
  apply tendstoInMeasure_quadraticSum_add isCompact_Icc hgrid hmem hmesh hδ
    (fun k i ↦ (hB.hasLaw_eval (grid k i)).aemeasurable.aestronglyMeasurable) hAmeas
  · filter_upwards [hB.cont, hA] with ω hc hω
    exact ⟨hc.continuousOn, hω⟩
  · exact hB.toIsPreBrownianReal.tendstoInMeasure_quadraticSum hgrid ha hb
      (fun k i ↦ (le_abs_self _).trans (by simpa only [NNReal.dist_eq] using hmesh k i)) hδ

end ProbabilityTheory.IsBrownianReal
