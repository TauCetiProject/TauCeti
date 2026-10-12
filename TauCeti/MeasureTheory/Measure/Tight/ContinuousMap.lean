/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.MeasureTheory.Measure.Tight
public import TauCeti.Topology.ContinuousMap.Ascoli

/-!
# Tightness of laws on a space of continuous curves

Let `α` be a compact pseudometric space, for instance a compact time interval `[0, T]`, and let
`X` be a complete metric space. This file characterizes the tight sets of measures on the space
`C(α, X)` of continuous curves, with its compact-open (equivalently, uniform) topology. A set `S`
of measures on `C(α, X)` is tight exactly when

* its time marginals are tight: for every `t` in a dense set `D ⊆ α`, the laws of the evaluation
  `γ ↦ γ t` under the members of `S` form a tight set of measures on `X`; and
* it satisfies a uniform modulus of continuity in probability: for all `η, ε > 0` there is
  `δ > 0` such that, for every `P ∈ S`, the curves `γ` having two times `s, t` with
  `dist s t < δ` and `η ≤ dist (γ s) (γ t)` have `P`-measure at most `ε`.

The sufficiency result also holds for a Lindelöf pseudometric domain `α`, for instance `ℝ`,
with the compact-open topology on `C(α, X)`. Compactness of `α` is needed for the converse.

This is the tightness criterion used to extract limits of laws of random curves, for instance in
the superposition principle for absolutely continuous curves of probability measures. The
sufficiency of the two conditions is proved by intersecting countably many events of large
measure, each controlling either the oscillation of the curves at one scale or their position at
one time of a countable dense subset of `D`. The resulting set of curves is equicontinuous with
values in a compact set at each of these times, so it has compact closure by the Arzelà–Ascoli
theorem `ArzelaAscoli.isCompact_closure_of_equicontinuous_of_totallyBounded`. Completeness of `X`
is what turns total boundedness of the values at the remaining times into compactness; the
modulus condition is stated for arbitrary sets of curves, with no measurability requirement,
because measures are outer measures.

Without a hypothesis on the time marginals the modulus condition is not enough when `X` is not
proper: the Dirac masses at the curves `t • eₙ` of
`TauCeti.exists_lipschitzWith_one_not_isCompact_closure_range` satisfy it, since all these curves
are `1`-Lipschitz, but they do not form a tight set.

## Main results

* `TauCeti.isTightMeasureSet_of_map_eval_of_continuity_modulus`: tight time marginals on a dense
  set of times and a uniform modulus of continuity in probability give tightness.
* `MeasureTheory.IsTightMeasureSet.exists_measure_continuity_modulus_le`: conversely, a tight set
  of measures on `C(α, X)` satisfies the uniform modulus of continuity in probability.
* `TauCeti.isTightMeasureSet_iff_map_eval_and_continuity_modulus`: the characterization.

## References

* P. Billingsley, *Convergence of Probability Measures*, 2nd ed., Wiley 1999, Theorem 7.3, the
  case of real-valued curves on `[0, 1]`, where tightness of the marginal at the single time `0`
  suffices.
-/

public section

open Filter MeasureTheory Metric Set Topology
open scoped ENNReal NNReal

variable {α X : Type*} [PseudoMetricSpace α] [PseudoMetricSpace X]
  [MeasurableSpace C(α, X)] {S : Set (Measure C(α, X))}

/-- **A tight set of laws of curves has a uniform modulus of continuity in probability.** If `S`
is a tight set of measures on `C(α, X)`, then for all `η, ε > 0` there is `δ > 0` such that, for
every `P ∈ S`, the curves with two times closer than `δ` at which their values are at least `η`
apart have `P`-measure at most `ε`. -/
theorem MeasureTheory.IsTightMeasureSet.exists_measure_continuity_modulus_le
    [CompactSpace α] (hS : IsTightMeasureSet S) :
    ∀ η > 0, ∀ ε > 0, ∃ δ > 0, ∀ P ∈ S,
      P {γ | ∃ s t, dist s t < δ ∧ η ≤ dist (γ s) (γ t)} ≤ ε := by
  intro η hη ε hε
  obtain ⟨K, hK, hKS⟩ := isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp hS ε hε
  -- A compact set of curves is uniformly equicontinuous, so it misses the bad event.
  obtain ⟨δ, hδ, hKδ⟩ := Metric.uniformEquicontinuous_iff.mp
    (CompactSpace.uniformEquicontinuous_of_equicontinuous
      hK.equicontinuous) η hη
  refine ⟨δ, hδ, fun P hP ↦ (measure_mono ?_).trans (hKS P hP)⟩
  rintro γ ⟨s, t, hst, hle⟩ hγK
  exact (hKδ s t hst ⟨γ, hγK⟩).not_ge hle

namespace TauCeti

variable [MeasurableSpace X] [BorelSpace X] [OpensMeasurableSpace C(α, X)] {D : Set α}

/-- **Tightness criterion for laws of curves.** Let `α` be a Lindelöf pseudometric space, `X` a
complete metric space, and `D ⊆ α` dense. A set `S` of measures on `C(α, X)` is tight if its time
marginals at the times of `D` are tight and it satisfies a uniform modulus of continuity in
probability: for all `η, ε > 0` there is `δ > 0` such that, for every `P ∈ S`, the curves with two
times closer than `δ` at which their values are at least `η` apart have `P`-measure at most `ε`. -/
theorem isTightMeasureSet_of_map_eval_of_continuity_modulus [LindelofSpace α]
    [CompleteSpace X] [T2Space X]
    (hD : Dense D)
    (h_eval : ∀ t ∈ D, IsTightMeasureSet ((fun P : Measure C(α, X) ↦ P.map fun γ ↦ γ t) '' S))
    (h_mod : ∀ η > 0, ∀ ε > 0, ∃ δ > 0, ∀ P ∈ S,
      P {γ | ∃ s t, dist s t < δ ∧ η ≤ dist (γ s) (γ t)} ≤ ε) :
    IsTightMeasureSet S := by
  rw [isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨T, hTD, hTc, hT⟩ := hD.exists_countable_dense_subset
  have : Countable T := hTc.to_subtype
  -- Split the budget `ε` over the oscillation scales `1 / (k + 1)` and the times of `T`.
  obtain ⟨ε', hε'pos, hε'sum⟩ := ENNReal.exists_pos_sum_of_countable hε.ne' (ℕ ⊕ T)
  choose δ hδpos hδ using fun k : ℕ ↦
    h_mod (1 / (k + 1)) Nat.one_div_pos_of_nat (ε' (.inl k)) (by exact_mod_cast hε'pos _)
  choose Q hQ hQS using fun t : T ↦ isTightMeasureSet_iff_exists_isCompact_measure_compl_le.mp
    (h_eval t (hTD t.2)) (ε' (.inr t)) (by exact_mod_cast hε'pos _)
  -- The bad events: oscillating at scale `1 / (k + 1)`, or leaving `Q t` at time `t`.
  set B : ℕ ⊕ T → Set C(α, X) := Sum.elim
    (fun k ↦ {γ | ∃ s t, dist s t < δ k ∧ 1 / (k + 1 : ℝ) ≤ dist (γ s) (γ t)})
    (fun t ↦ (fun γ : C(α, X) ↦ γ t) ⁻¹' (Q t)ᶜ) with hB
  refine ⟨closure (⋃ i, B i)ᶜ, ?_, fun P hP ↦ ?_⟩
  · refine ArzelaAscoli.isCompact_closure_of_equicontinuous_of_totallyBounded hT ?_ ?_
    · refine (Metric.uniformEquicontinuous_iff.mpr fun e he ↦ ?_).equicontinuous
      obtain ⟨k, hk⟩ := exists_nat_one_div_lt he
      refine ⟨δ k, hδpos k, fun s t hst γ ↦ ?_⟩
      have hγ : γ.1 ∉ B (.inl k) := fun h ↦ γ.2 (mem_iUnion.mpr ⟨_, h⟩)
      simp only [hB, Sum.elim_inl, mem_ofPred_eq, not_exists, not_and, not_le] at hγ
      exact (hγ s t hst).trans hk
    · intro t ht
      refine (hQ ⟨t, ht⟩).totallyBounded.subset ?_
      rintro _ ⟨γ, hγ, rfl⟩
      by_contra h
      exact hγ (mem_iUnion.mpr ⟨.inr ⟨t, ht⟩, h⟩)
  · calc P (closure (⋃ i, B i)ᶜ)ᶜ ≤ P (⋃ i, B i) :=
          measure_mono (compl_subset_comm.mp subset_closure)
      _ ≤ ∑' i, P (B i) := measure_iUnion_le B
      _ ≤ ∑' i, (ε' i : ℝ≥0∞) := ENNReal.tsum_le_tsum fun i ↦ ?_
      _ ≤ ε := hε'sum.le
    rcases i with k | t
    · exact hδ k P hP
    · exact (Measure.le_map_apply (continuous_eval_const (t : α)).aemeasurable
        _).trans (hQS t _ ⟨P, hP, rfl⟩)

/-- **Characterization of tight laws of curves.** Let `X` be a complete metric space and `D ⊆ α`
dense. A set `S` of measures on `C(α, X)` is tight if and only if its time marginals at the times
of `D` are tight and it satisfies a uniform modulus of continuity in probability. -/
theorem isTightMeasureSet_iff_map_eval_and_continuity_modulus [CompactSpace α]
    [CompleteSpace X] [T2Space X]
    (hD : Dense D) :
    IsTightMeasureSet S ↔
      (∀ t ∈ D, IsTightMeasureSet ((fun P : Measure C(α, X) ↦ P.map fun γ ↦ γ t) '' S)) ∧
        ∀ η > 0, ∀ ε > 0, ∃ δ > 0, ∀ P ∈ S,
          P {γ | ∃ s t, dist s t < δ ∧ η ≤ dist (γ s) (γ t)} ≤ ε :=
  ⟨fun hS ↦ ⟨fun t _ ↦ hS.map (continuous_eval_const t),
      hS.exists_measure_continuity_modulus_le⟩,
    fun h ↦ isTightMeasureSet_of_map_eval_of_continuity_modulus hD h.1 h.2⟩

end TauCeti
