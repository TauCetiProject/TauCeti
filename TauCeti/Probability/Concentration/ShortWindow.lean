/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Probability.Independence.Basic
import TauCeti.Probability.Independence.Basic

/-!
# Short-window bounds conditional on a selected position

If a window contains more than `k` selected positions, at least `k` remain after deleting
one specified position. The probability of the specified success and a given `k`-subset of
further successes factors by independence. Counting the subsets bounds the probability of
overcrowding in any of `J` windows by `card J * (L.choose k) * p ^ k` conditional on that
success, where the windows have length at most `L` after deletion and the other selection rates
are bounded by `p`. The joint form does not require measurability or positive mass of the
specified event.

The use of this bound for short windows along Frobenius orbits follows Levent Alpöge's
`Formalism.MainNotions.G.TopChoiceBounds.good_orbit_failure_prob_le`
(<https://github.com/leanprover-community/riemann-hypothesis>).
-/

public section

open MeasureTheory Set Finset
open scoped ENNReal NNReal

namespace ProbabilityTheory

open scoped Classical in
/-- The probability that a specified trial succeeds and some window contains more than `k`
successes is at most the binomial-coefficient window bound times the probability of the
specified success. Windows can intersect, and their trials need not have equal success rates. -/
theorem iIndepSet.measure_inter_exists_lt_card_filter_mem_le {Ω ι J : Type*} [MeasurableSpace Ω]
    [Fintype J] [DecidableEq ι] {μ : Measure Ω} {E : ι → Set Ω} (h : iIndepSet E μ) (i : ι)
    (W : J → Finset ι) {L k : ℕ} (hW : ∀ j, ((W j).erase i).card ≤ L) {p : ℝ≥0∞}
    (hp : ∀ j, ∀ a ∈ (W j).erase i, μ (E a) ≤ p) :
    μ (E i ∩ {ω | ∃ j, k < ((W j).filter (fun a ↦ ω ∈ E a)).card}) ≤
      (Fintype.card J : ℝ≥0∞) * L.choose k * p ^ k * μ (E i) := by
  classical
  let T (j : J) := (W j).erase i
  let F (j : J) (a : T j) := E a.val
  have hsub : E i ∩ {ω | ∃ j, k < ((W j).filter (fun a ↦ ω ∈ E a)).card} ⊆
      E i ∩ {ω | ∃ j, k ≤ (univ.filter (fun a : T j ↦ ω ∈ F j a)).card} := by
    rintro ω ⟨hi, j, hj⟩
    refine ⟨hi, j, ?_⟩
    have hcard : (univ.filter (fun a : T j ↦ ω ∈ F j a)).card =
        (((W j).filter (fun a ↦ ω ∈ E a)).erase i).card := by
      rw [Finset.univ_eq_attach]
      simpa only [Finset.card_map, Finset.card_attach, T, filter_erase] using
        congrArg Finset.card (Finset.filter_attach (fun a ↦ ω ∈ E a) (T j))
    rw [hcard]
    exact (Nat.le_pred_of_lt hj).trans pred_card_le_card_erase
  have hmass (j : J) (S : Finset (T j)) (hS : S.card = k) :
      μ (E i ∩ ⋂ a ∈ S, F j a) ≤ μ (E i) * p ^ k := by
    let U := S.map (Function.Embedding.subtype (· ∈ T j))
    have hU : U ⊆ T j := by
      intro a ha
      obtain ⟨b, _, rfl⟩ := mem_map.mp ha
      exact b.property
    have hi : i ∉ U := fun ha ↦ notMem_erase i (W j) (hU ha)
    have hInter : (⋂ a ∈ insert i U, E a) = E i ∩ ⋂ a ∈ S, F j a := by
      ext ω
      simp only [mem_iInter, Finset.mem_insert, mem_inter_iff, or_imp, forall_and, forall_eq]
      refine and_congr_right fun _ ↦ ⟨fun hw a ha ↦ hw _ (mem_map.mpr ⟨a, ha, rfl⟩), ?_⟩
      intro hw a ha
      obtain ⟨b, hb, rfl⟩ := mem_map.mp ha
      exact hw b hb
    rw [← hInter, h.meas_biInter, prod_insert hi]
    have hcard : U.card = k := (card_map _).trans hS
    rw [← hcard, ← Finset.prod_const]
    gcongr with a ha
    exact hp j a (hU ha)
  refine ((measure_mono hsub).trans
    (TauCeti.Probability.measure_inter_exists_le_card_filter_mem_le (E i) F k hmass)).trans ?_
  calc
    _ ≤ ∑ _j : J, (L.choose k : ℝ≥0∞) * (μ (E i) * p ^ k) := by
      refine sum_le_sum fun j _ ↦ mul_le_mul_left (α := ℝ≥0∞) ?_ _
      rw [Fintype.card_coe]
      exact_mod_cast Nat.choose_le_choose k (hW j)
    _ = _ := by
      rw [sum_const, card_univ, nsmul_eq_mul, mul_comm (μ (E i)), ← mul_assoc, ← mul_assoc]

open scoped Classical in
/-- The short-window union bound conditional on one successful trial. The conditional measure
at a null conditioning event is zero. -/
theorem iIndepSet.cond_exists_lt_card_filter_mem_le {Ω ι J : Type*} [MeasurableSpace Ω]
    [Fintype J] [DecidableEq ι] {μ : Measure Ω} {E : ι → Set Ω} (h : iIndepSet E μ) {i : ι}
    (hEi : MeasurableSet (E i)) (W : J → Finset ι) {L k : ℕ}
    (hW : ∀ j, ((W j).erase i).card ≤ L) {p : ℝ≥0∞} (hp : ∀ j, ∀ a ∈ (W j).erase i, μ (E a) ≤ p) :
    cond μ (E i) {ω | ∃ j, k < ((W j).filter (fun a ↦ ω ∈ E a)).card} ≤
      (Fintype.card J : ℝ≥0∞) * L.choose k * p ^ k := by
  have := h.isProbabilityMeasure
  rw [cond_apply hEi]
  by_cases h₀ : μ (E i) = 0
  · simp [measure_mono_null inter_subset_left h₀]
  calc
    _ ≤ (μ (E i))⁻¹ * ((Fintype.card J : ℝ≥0∞) * L.choose k * p ^ k * μ (E i)) :=
      mul_le_mul_right (h.measure_inter_exists_lt_card_filter_mem_le i W hW hp) _
    _ = ((μ (E i))⁻¹ * μ (E i)) * ((Fintype.card J : ℝ≥0∞) * L.choose k * p ^ k) := by
      rw [mul_comm _ (μ (E i)), ← mul_assoc]
    _ = _ := by rw [ENNReal.inv_mul_cancel h₀ (measure_ne_top μ _), one_mul]

open scoped Classical in
/-- The joint short-window bound in real probabilities, for use in sums of weighted failure
probabilities. -/
theorem iIndepSet.measureReal_inter_exists_lt_card_filter_mem_le {Ω ι J : Type*} [MeasurableSpace Ω]
    [Fintype J] [DecidableEq ι] {μ : Measure Ω} {E : ι → Set Ω} (h : iIndepSet E μ) (i : ι)
    (W : J → Finset ι) {L k : ℕ} (hW : ∀ j, ((W j).erase i).card ≤ L) {p : ℝ≥0}
    (hp : ∀ j, ∀ a ∈ (W j).erase i, μ (E a) ≤ p) :
    μ.real (E i ∩ {ω | ∃ j, k < ((W j).filter (fun a ↦ ω ∈ E a)).card}) ≤
      (Fintype.card J : ℝ) * L.choose k * (p : ℝ) ^ k * μ.real (E i) := by
  have := h.isProbabilityMeasure
  simpa [measureReal_def, ENNReal.toReal_mul, ENNReal.toReal_pow] using ENNReal.toReal_mono
    (by finiteness) (h.measure_inter_exists_lt_card_filter_mem_le i W hW hp (k := k))

end ProbabilityTheory
