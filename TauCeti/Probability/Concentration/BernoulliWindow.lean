/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Distributions.PoissonBinomial.StochasticOrder
public import TauCeti.Probability.ConditionalProbability

/-!
# Binomial bounds for windows in a Bernoulli sample

For independent selection events, a finite window has a Poisson-binomial count. On the event
that a specified position is selected, delete that position from the window before comparing
with a binomial tail. This avoids comparing the forced success with an ordinary trial. The
resulting joint probability bound requires no positivity assumption on the probability of the
specified position, and a union bound applies to overlapping windows as well as disjoint ones.

The application to the large-window term in the failure probability for a good orbit follows
Levent Alpöge's `Formalism.MainNotions.G.TopChoiceBounds.good_orbit_failure_prob_le`
in the [published formalization][alpoege].

[alpoege]: https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005
-/

public section

open Finset MeasureTheory Set

namespace ProbabilityTheory

variable {ι Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {E : ι → Set Ω}

open Classical in
/-- The probability of at least `k` successes in a window with at most `n` independent trials
of probability at most `δ` is bounded by the upper tail of `Bin(n, δ)`. -/
theorem iIndepSet.measureReal_card_filter_ge_le_binomial (hE : iIndepSet E P)
    (s : Finset ι) (hM : ∀ i ∈ s, NullMeasurableSet (E i) P) {δ : unitInterval} {n k : ℕ}
    (hn : s.card ≤ n) (hp : ∀ i ∈ s, P.real (E i) ≤ δ) :
    P.real {ω | k ≤ (s.filter fun i ↦ ω ∈ E i).card} ≤ (binomial n δ).real (Ici k) := by
  classical
  let : IsProbabilityMeasure P := hE.isProbabilityMeasure
  let p (i : s) : unitInterval := ⟨P.real (E i), ⟨measureReal_nonneg, measureReal_le_one⟩⟩
  have hi : iIndepFun (fun i : s ↦ (E i).indicator fun _ ↦ (1 : ℕ)) P :=
    (hE.iIndepFun_indicator (β := ℕ)).precomp Subtype.val_injective
  have hcount := hi.hasLaw_sum_poissonBinomialMeasure (p := p)
    (fun i ↦ hasLaw_indicator_one_bernoulliMeasure (hM i i.property))
  have hsum (ω : Ω) : (∑ i : s, (E i).indicator (fun _ ↦ (1 : ℕ)) ω) =
      (s.filter fun i ↦ ω ∈ E i).card := by
    rw [sum_coe_sort s (fun i ↦ (E i).indicator (fun _ ↦ (1 : ℕ)) ω)]
    simp only [Set.indicator_apply, sum_boole, Nat.cast_id]
  have heq := hcount.measureReal_eq (p := fun j ↦ k ≤ j) MeasurableSet.of_discrete
  simp_rw [hsum] at heq
  rw [heq]
  exact TauCeti.Probability.poissonBinomialMeasure_real_Ici_le_binomial (p := p)
    (by simpa using hn) (fun i ↦ hp i i.property) k

open Classical in
/-- Joint probability that `a` is selected and a window has at least `k` selections. The
forced success costs one from the threshold only if `a` belongs to the window. The trial-count
bound and the probability cap concern only the other positions. -/
theorem iIndepSet.measureReal_inter_card_filter_ge_le_binomial (hE : iIndepSet E P)
    (hM : ∀ i, MeasurableSet (E i)) (a : ι) (s : Finset ι) {δ : unitInterval} {n k : ℕ}
    (hn : (s.erase a).card ≤ n) (hp : ∀ i ∈ s.erase a, P.real (E i) ≤ δ) :
    P.real (E a ∩ {ω | k ≤ (s.filter fun i ↦ ω ∈ E i).card}) ≤
      P.real (E a) * (binomial n δ).real (Ici (k - if a ∈ s then 1 else 0)) := by
  classical
  let r := k - if a ∈ s then 1 else 0
  let F (i : ι) := (E i).indicator fun _ ↦ (1 : ℕ)
  have hI : IndepFun (∑ i ∈ s.erase a, F i) (F a) P :=
    (hE.iIndepFun_indicator (β := ℕ)).indepFun_finsetSum_of_notMem
      (fun i ↦ measurable_one.indicator (hM i)) (notMem_erase a s)
  have hmul := hI.symm.measure_inter_preimage_eq_mul {1} (Ici r)
    (measurableSet_singleton _) measurableSet_Ici
  have hpre : F a ⁻¹' {1} = E a := by
    ext ω
    by_cases h : ω ∈ E a <;> simp [F, h]
  have hsum : (∑ i ∈ s.erase a, F i) ⁻¹' Ici r =
      {ω | r ≤ ((s.erase a).filter fun i ↦ ω ∈ E i).card} := by
    ext ω
    simp [F, Set.indicator_apply, sum_boole]
  rw [hpre, hsum] at hmul
  have hsub : E a ∩ {ω | k ≤ (s.filter fun i ↦ ω ∈ E i).card} ⊆
      E a ∩ {ω | r ≤ ((s.erase a).filter fun i ↦ ω ∈ E i).card} := by
    rintro ω ⟨ha, hk⟩
    refine ⟨ha, ?_⟩
    simp only [Set.mem_ofPred_eq] at hk ⊢
    by_cases has : a ∈ s
    · rw [filter_erase, card_erase_of_mem (mem_filter.mpr ⟨has, ha⟩)]
      simpa [r, has] using Nat.sub_le_sub_right hk 1
    · simpa [r, has, erase_eq_of_notMem has] using hk
  let : IsProbabilityMeasure P := hE.isProbabilityMeasure
  refine (measureReal_mono hsub).trans ?_
  rw [measureReal_def, hmul, ENNReal.toReal_mul, ← measureReal_def, ← measureReal_def]
  exact mul_le_mul_of_nonneg_left
    (hE.measureReal_card_filter_ge_le_binomial _ (fun i _ ↦ (hM i).nullMeasurableSet) hn hp)
    measureReal_nonneg

open Classical in
/-- With a specified position selected, the joint probability that some window has at least
`k` successes is bounded by the number of windows times the shifted binomial tail times the
probability of the specified selection. For a cyclic orbit of length `n'`, index the windows
by their starting positions to get the factor `n'`. No disjointness of the windows is needed. -/
theorem iIndepSet.measureReal_inter_exists_card_filter_ge_le_binomial {ν : Type*}
    (hE : iIndepSet E P) (hM : ∀ i, MeasurableSet (E i)) (a : ι) (t : Finset ν)
    (window : ν → Finset ι) {δ : unitInterval} {n k : ℕ}
    (hn : ∀ j ∈ t, ((window j).erase a).card ≤ n)
    (hp : ∀ j ∈ t, ∀ i ∈ (window j).erase a, P.real (E i) ≤ δ) :
    P.real (E a ∩ {ω | ∃ j ∈ t, k ≤ ((window j).filter fun i ↦ ω ∈ E i).card}) ≤
      P.real (E a) * t.card * (binomial n δ).real (Ici (k - 1)) := by
  let : IsProbabilityMeasure P := hE.isProbabilityMeasure
  let B (j : ν) : Set Ω := E a ∩ {ω | k ≤ ((window j).filter fun i ↦ ω ∈ E i).card}
  have hUnion : E a ∩ {ω | ∃ j ∈ t, k ≤ ((window j).filter fun i ↦ ω ∈ E i).card} =
      ⋃ j ∈ t, B j := by
    ext ω
    simp [B, exists_and_left]
  rw [hUnion]
  calc
    _ ≤ ∑ j ∈ t, P.real (B j) := measureReal_biUnion_finset_le t B
    _ ≤ ∑ _j ∈ t, P.real (E a) * (binomial n δ).real (Ici (k - 1)) := by
      apply sum_le_sum
      intro j hj
      refine (hE.measureReal_inter_card_filter_ge_le_binomial hM a _ (hn j hj) (hp j hj)).trans ?_
      apply mul_le_mul_of_nonneg_left (measureReal_mono ?_) measureReal_nonneg
      exact Ici_subset_Ici.mpr (Nat.sub_le_sub_left (by split_ifs <;> omega) k)
    _ = _ := by rw [sum_const, nsmul_eq_mul, mul_left_comm, mul_assoc]

open Classical in
/-- Conditional on `a` being selected, the chance that some window has at least `k` selections
is at most the number of windows times the binomial tail at `k - 1`. If the conditioning event
has probability zero, `cond` gives the zero measure and the same bound holds. -/
theorem iIndepSet.cond_measureReal_exists_card_filter_ge_le_binomial {ν : Type*}
    (hE : iIndepSet E P) (hM : ∀ i, MeasurableSet (E i)) (a : ι) (t : Finset ν)
    (window : ν → Finset ι) {δ : unitInterval} {n k : ℕ}
    (hn : ∀ j ∈ t, ((window j).erase a).card ≤ n)
    (hp : ∀ j ∈ t, ∀ i ∈ (window j).erase a, P.real (E i) ≤ δ) :
    (cond P (E a)).real {ω | ∃ j ∈ t, k ≤ ((window j).filter fun i ↦ ω ∈ E i).card} ≤
      t.card * (binomial n δ).real (Ici (k - 1)) := by
  rw [cond_real_apply (hM a)]
  rcases (measureReal_nonneg (μ := P) (s := E a)).eq_or_lt with hzero | hpos
  · rw [← hzero, div_zero]
    positivity
  · apply (div_le_iff₀ hpos).2
    rw [mul_comm _ (P.real (E a)), ← mul_assoc]
    exact hE.measureReal_inter_exists_card_filter_ge_le_binomial hM a t window hn hp

end ProbabilityTheory
