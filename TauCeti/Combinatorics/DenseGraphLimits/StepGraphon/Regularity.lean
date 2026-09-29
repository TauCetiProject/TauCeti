/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
module

public import TauCeti.Combinatorics.DenseGraphLimits.StepGraphon.Energy
public import TauCeti.Combinatorics.DenseGraphLimits.Kernel.CutNorm
import TauCeti.MeasureTheory.MeasurableSpace.Finpartition

/-!
# Frieze--Kannan weak regularity for graphons

This file proves the weak regularity lemma for strict graphons.  Starting from the indiscrete
finite partition, a cut-norm witness for the current block-average defect cuts every part along
two measurable sets.  The common refinement has at most four times as many parts, while the
Pythagoras identity for `graphonPartitionEnergy` and Cauchy--Schwarz show that its energy rises by
*strictly more than* `ε²`.  Since the energy stays in `[0, 1]`, the process stops after at most
`⌈1 / ε²⌉` steps.

Null parts need no special case: `Finpartition.bipartition` omits empty sets but retains nonempty
null sets, and `stepGraphonAvg` uses Mathlib's zero set-average convention on their rectangles.

## Main results

* `TauCeti.DenseGraphLimits.exists_refinement_energy_add_sq_lt` is the quantitative refinement
  step: a bad cut-norm approximation yields an energy gain of more than `ε²` while multiplying the
  number of parts by at most four;
* `TauCeti.DenseGraphLimits.weak_regularity_frieze_kannan` is the weak regularity theorem, with
  complexity `4 ^ (Nat.ceil (1 / ε ^ 2))`.

## References

* A. Frieze and R. Kannan, *Quick approximation to matrices and applications*, Combinatorica 19
  (1999), 175--220.
* L. Lovász, *Large Networks and Graph Limits*, AMS Colloquium Publications 60 (2012), §9.2.
* The refinement-and-energy iteration follows `Graphon/Regularity.lean` in
  `cameronfreer/graphon` (Apache 2.0) at commit
  `6eccca5bbe5c9df46d7129bf59575b8b9b1d6699`, adapted here to Mathlib `Finpartition`, strict
  block-average graphons, and the Pythagoras energy API.  The iteration count differs from that
  route's `⌈1 / ε²⌉ + 1`: there the energy gain of a bad step is only `≥ ε²`, while here the
  cut-norm witness is squared strictly, so the gain is `> ε²` and `⌈1 / ε²⌉` steps already
  contradict the energy bound.
-/

public section

noncomputable section

open MeasureTheory Set

namespace TauCeti

namespace DenseGraphLimits

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]

/-- A cut-norm defect larger than `ε` produces a measurable common refinement with at most four
times as many parts and graphon partition energy **more than** `ε²` larger. -/
theorem exists_refinement_energy_add_sq_lt (P : Finpartition (Set.univ : Set Ω))
    (hP : ∀ p ∈ P.parts, MeasurableSet p) (W : Graphon Ω μ) {ε : ℝ} (hε : 0 ≤ ε)
    (hbad : ε < cutNorm μ (W.toSymmKernel - (stepGraphonAvg (μ := μ) P hP W).toSymmKernel)) :
    ∃ (Q : Finpartition (Set.univ : Set Ω)) (hQ : ∀ q ∈ Q.parts, MeasurableSet q),
      Q ≤ P ∧ Q.parts.card ≤ 4 * P.parts.card ∧
        graphonPartitionEnergy μ P hP W + ε ^ 2 < graphonPartitionEnergy μ Q hQ W := by
  let D := W.toSymmKernel - (stepGraphonAvg (μ := μ) P hP W).toSymmKernel
  obtain ⟨S, T, hS, hT, hrect⟩ := exists_lt_abs_rectIntegral μ D hbad
  have hS_ne : S ≠ ∅ := by
    intro h
    subst S
    simp only [SymmKernel.rectIntegral_empty_left, abs_zero] at hrect
    linarith
  have hT_ne : T ≠ ∅ := by
    intro h
    subst T
    simp only [SymmKernel.rectIntegral_empty_right, abs_zero] at hrect
    linarith
  let PS := Finpartition.bipartition S
  let PT := Finpartition.bipartition T
  let Q := (P ⊓ PS) ⊓ PT
  have hPS : ∀ p ∈ PS.parts, MeasurableSet p := fun _ hp =>
    Finpartition.measurableSet_of_mem_bipartition hS hp
  have hPT : ∀ p ∈ PT.parts, MeasurableSet p := fun _ hp =>
    Finpartition.measurableSet_of_mem_bipartition hT hp
  have hPPS : ∀ q ∈ (P ⊓ PS).parts, MeasurableSet q := fun _ hq =>
    Finpartition.measurableSet_of_mem_inf hP hPS hq
  have hQ : ∀ q ∈ Q.parts, MeasurableSet q := fun _ hq =>
    Finpartition.measurableSet_of_mem_inf hPPS hPT hq
  have hQP : Q ≤ P := le_trans inf_le_left inf_le_left
  have hQS : Q ≤ PS := le_trans inf_le_left inf_le_right
  have hQT : Q ≤ PT := inf_le_right
  have hcard : Q.parts.card ≤ 4 * P.parts.card := by
    calc
      Q.parts.card ≤ (P ⊓ PS).parts.card * PT.parts.card :=
        Finpartition.card_parts_inf_le_mul _ _
      _ ≤ (P.parts.card * PS.parts.card) * PT.parts.card :=
        Nat.mul_le_mul_right _ (Finpartition.card_parts_inf_le_mul P PS)
      _ ≤ (P.parts.card * 2) * 2 := Nat.mul_le_mul
        (Nat.mul_le_mul_left _ (Finpartition.card_parts_bipartition_le S))
        (Finpartition.card_parts_bipartition_le T)
      _ = 4 * P.parts.card := by omega
  let pS : PS.parts := ⟨S, Finpartition.mem_bipartition_of_ne_bot hS_ne⟩
  let pT : PT.parts := ⟨T, Finpartition.mem_bipartition_of_ne_bot hT_ne⟩
  have havg :
      (stepGraphonAvg (μ := μ) Q hQ W).toSymmKernel.rectIntegral μ S T =
        W.toSymmKernel.rectIntegral μ S T := by
    simpa [pS, pT] using stepGraphonAvg_rectIntegral_of_le_of_le μ pS pT hQ
      hQS hQT W
  let L := (stepGraphonAvg (μ := μ) Q hQ W).toSymmKernel -
    (stepGraphonAvg (μ := μ) P hP W).toSymmKernel
  have hLrect : L.rectIntegral μ S T = D.rectIntegral μ S T := by
    simp only [L, D, SymmKernel.rectIntegral_sub, havg]
  -- The gain is strict because the cut-norm witness `|∫_{S ×ˢ T} D| > ε` is squared strictly
  -- before being compared with the `L²` seminorm.
  have hsq : ε ^ 2 < (D.rectIntegral μ S T) ^ 2 := by
    simpa only [sq_abs] using
      (sq_lt_sq' (by linarith [abs_nonneg (D.rectIntegral μ S T)]) hrect)
  have hgain : ε ^ 2 < l2sq μ L := by
    rw [← hLrect] at hsq
    exact lt_of_lt_of_le hsq (sq_rectIntegral_le_l2sq μ L S T)
  refine ⟨Q, hQ, hQP, hcard, ?_⟩
  rw [graphonPartitionEnergy_increment μ P Q hP hQ hQP W]
  simpa only [L, add_comm] using add_lt_add_left hgain (graphonPartitionEnergy μ P hP W)

/-- **Iteration invariant.** Given a measurable partition `P` and `n + 1` refinement steps, there
is a measurable partition with at most `4 ^ (n + 1)` times as many parts whose block averages
either approximate `W` to within `ε` in cut norm, or — when every one of those steps was actually
taken — carry energy *strictly more than* `(n + 1) * ε ^ 2` above `P`'s. -/
private theorem exists_partition_cutNorm_le_or_energy_add_mul_sq_lt
    (W : Graphon Ω μ) {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ (n : ℕ) (P : Finpartition (Set.univ : Set Ω)) (hP : ∀ p ∈ P.parts, MeasurableSet p),
      ∃ (Q : Finpartition (Set.univ : Set Ω)) (hQ : ∀ q ∈ Q.parts, MeasurableSet q),
        Q.parts.card ≤ 4 ^ (n + 1) * P.parts.card ∧
          (cutNorm μ (W.toSymmKernel - (stepGraphonAvg (μ := μ) Q hQ W).toSymmKernel) ≤ ε ∨
            graphonPartitionEnergy μ P hP W + ((n + 1 : ℕ) : ℝ) * ε ^ 2 <
              graphonPartitionEnergy μ Q hQ W) := by
  intro n
  induction n with
  | zero =>
      -- One step: stop if already good, otherwise take a single refinement.
      intro P hP
      by_cases hgood :
          cutNorm μ (W.toSymmKernel - (stepGraphonAvg (μ := μ) P hP W).toSymmKernel) ≤ ε
      · refine ⟨P, hP, ?_, Or.inl hgood⟩
        exact Nat.le_mul_of_pos_left _ (by positivity)
      · obtain ⟨Q, hQ, _, hQcard_step, hQenergy⟩ :=
          exists_refinement_energy_add_sq_lt μ P hP W hε (lt_of_not_ge hgood)
        exact ⟨Q, hQ, by simpa using hQcard_step, Or.inr (by simpa using hQenergy)⟩
  | succ n ih =>
      -- One further step: stop if already good, otherwise refine once and iterate, composing the
      -- two strict energy gains.
      intro P hP
      by_cases hgood :
          cutNorm μ (W.toSymmKernel - (stepGraphonAvg (μ := μ) P hP W).toSymmKernel) ≤ ε
      · refine ⟨P, hP, ?_, Or.inl hgood⟩
        exact Nat.le_mul_of_pos_left _ (by positivity)
      · obtain ⟨Q, hQ, _, hQcard_step, hQenergy⟩ :=
          exists_refinement_energy_add_sq_lt μ P hP W hε (lt_of_not_ge hgood)
        obtain ⟨R, hR, hRcard, hRdichotomy⟩ := ih Q hQ
        have hRbound : R.parts.card ≤ 4 ^ (n + 1 + 1) * P.parts.card := by
          calc R.parts.card ≤ 4 ^ (n + 1) * Q.parts.card := hRcard
            _ ≤ 4 ^ (n + 1) * (4 * P.parts.card) := Nat.mul_le_mul_left _ hQcard_step
            _ = 4 ^ (n + 1 + 1) * P.parts.card := by ring
        rcases hRdichotomy with hRgood | hRenergy
        · exact ⟨R, hR, hRbound, Or.inl hRgood⟩
        · refine ⟨R, hR, hRbound, Or.inr ?_⟩
          calc
            graphonPartitionEnergy μ P hP W + ((n + 1 + 1 : ℕ) : ℝ) * ε ^ 2
                = ((n + 1 : ℕ) : ℝ) * ε ^ 2
                    + (graphonPartitionEnergy μ P hP W + ε ^ 2) := by push_cast; ring
            _ < ((n + 1 : ℕ) : ℝ) * ε ^ 2 + graphonPartitionEnergy μ Q hQ W :=
              add_lt_add_right hQenergy _
            _ = graphonPartitionEnergy μ Q hQ W + ((n + 1 : ℕ) : ℝ) * ε ^ 2 := by ring
            _ < graphonPartitionEnergy μ R hR W := hRenergy

/-- **Frieze--Kannan weak regularity.** Every graphon has a measurable block-average step graphon
within `ε` in cut norm, on a partition with at most `4 ^ ⌈1 / ε²⌉` parts. -/
theorem weak_regularity_frieze_kannan (W : Graphon Ω μ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (P : Finpartition (Set.univ : Set Ω)) (hP : ∀ p ∈ P.parts, MeasurableSet p),
      P.parts.card ≤ 4 ^ (Nat.ceil (1 / ε ^ 2)) ∧
      cutNorm μ (W.toSymmKernel - (stepGraphonAvg (μ := μ) P hP W).toSymmKernel) ≤ ε := by
  let N := Nat.ceil (1 / ε ^ 2)
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  have hceil : 1 / ε ^ 2 ≤ (N : ℝ) := by
    dsimp only [N]
    exact Nat.le_ceil _
  have hN1 : 1 ≤ N := by
    have hone : (0 : ℝ) < 1 / ε ^ 2 := by positivity
    have hNpos : 0 < N := by
      exact_mod_cast (lt_of_lt_of_le hone hceil)
    omega
  have hNsub : N - 1 + 1 = N := Nat.sub_add_cancel hN1
  -- Instantiate the refinement invariant at the indiscrete partition, then rule out the
  -- energy-growth branch: `N` steps would push the energy past its upper bound of one.
  let P₀ : Finpartition (Set.univ : Set Ω) := ⊤
  have hP₀ : ∀ p ∈ P₀.parts, MeasurableSet p := by
    intro p hp
    have : p = Set.univ := Finset.mem_singleton.mp
      (Finpartition.parts_top_subset (Set.univ : Set Ω) hp)
    subst p
    exact MeasurableSet.univ
  have hP₀_card : P₀.parts.card ≤ 1 :=
    Finset.card_le_one.mpr (Finpartition.parts_top_subsingleton _)
  obtain ⟨Q, hQ, hQcard, hgood | henergy⟩ :=
    exists_partition_cutNorm_le_or_energy_add_mul_sq_lt μ W hε.le (N - 1) P₀ hP₀
  · refine ⟨Q, hQ, ?_, hgood⟩
    have hbound : Q.parts.card ≤ 4 ^ N := by
      calc Q.parts.card ≤ 4 ^ (N - 1 + 1) * P₀.parts.card := hQcard
        _ ≤ 4 ^ (N - 1 + 1) * 1 := Nat.mul_le_mul_left _ hP₀_card
        _ = 4 ^ (N - 1 + 1) := mul_one _
      rw [hNsub]
    simpa [N] using hbound
  · have hQenergy := graphonPartitionEnergy_le_one μ Q hQ W
    have hP₀energy := graphonPartitionEnergy_nonneg μ P₀ hP₀ W
    have hN : 1 ≤ ((N - 1 + 1 : ℕ) : ℝ) * ε ^ 2 := by
      calc
        1 = (1 / ε ^ 2) * ε ^ 2 := by field_simp
        _ ≤ ((N - 1 + 1 : ℕ) : ℝ) * ε ^ 2 := by
          rw [hNsub]
          exact mul_le_mul_of_nonneg_right hceil (le_of_lt hεsq)
    linarith

end DenseGraphLimits

end TauCeti
