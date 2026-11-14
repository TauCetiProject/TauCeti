/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.MarkovChain.StrongMarkov.Basic

/-!
# First-passage decompositions of transition probabilities

The probability of being at a state at time `n` is the convolution of the law of
its first entrance after a cutoff `m ≤ n` and the return transition probabilities.
Taking `m = 1` counts first returns at positive times even when the initial state
is the target. Neither recurrence nor countability of the state space is needed.

The proof applies the strong Markov property on each finite first-entrance event
and sums these disjoint events. The resulting identity lets finite-time
transition observations be recovered recursively from first-passage observations.

## References

* J. R. Norris, *Markov Chains*, Cambridge University Press, 1997, §§1.4–1.5.
-/

public section

open MeasureTheory ProbabilityTheory TauCeti.Probability Set
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α : Type*} [MeasurableSpace α] [MeasurableSingletonClass α]
  (ν : Measure α) [IsFiniteMeasure ν] (κ : Kernel α α) [IsMarkovKernel κ]

/-- On the event of first entering `y` at time `k`, the state `n` steps later
has transition law `(κ ^ n) y`, independently of the first-entrance event.
The entrance search starts at `m`, and may fail to be finite. -/
theorem markovChainLaw_hittingAfter_eq_inter_eval (y : α) (m k n : ℕ)
    {s : Set α} (hs : MeasurableSet s) :
    markovChainLaw ν κ
        {w | hittingAfter (fun i w => w i) {y} m w = k ∧ w (k + n) ∈ s} =
      markovChainLaw ν κ {w | hittingAfter (fun i w => w i) {y} m w = k} *
        (κ ^ n) y s := by
  let τ := hittingAfter (fun i (w : ℕ → α) => w i) {y} m
  let A : Set (ℕ → α) := {w | τ w = k}
  let B : Set (ℕ → α) := {w | w n ∈ s}
  let θ := stoppedValue (fun i => (shift α)^[i]) τ
  have hτ : IsStoppingTime (Filtration.piLE (X := fun _ : ℕ => α)) τ :=
    Filtration.adapted_piLE.isStoppingTime_hittingAfter (measurableSet_singleton y)
  have hA : MeasurableSet[hτ.measurableSpace] A :=
    (measurableSet_singleton (k : WithTop ℕ)).preimage hτ.measurable
  have hB : MeasurableSet B := hs.preimage (measurable_pi_apply n)
  have hθ : Measurable θ :=
    measurable_stoppedValue_of_countable (fun i => measurable_shift_iterate i) hτ.measurable'
  have hkval : (k : WithTop ℕ).untopA = k :=
    WithTop.untopD_coe (Classical.arbitrary ℕ) k
  have hy : ∀ w ∈ A ∩ {w | τ w ≠ ⊤}, stoppedValue (fun i w => w i) τ w = y := by
    rintro w ⟨hw, hfin⟩
    have hwk : τ w = k := hw
    have hk : hittingAfter (fun i (w : ℕ → α) => w i) {y} m w = k := hw
    have hmem := hittingAfter_mem_set_of_ne_top (u := fun i (w : ℕ → α) => w i)
      (s := {y}) (n := m) hfin
    have hwy : w k = y := by
      simpa only [hk, hkval, Set.mem_singleton_iff] using hmem
    simpa only [stoppedValue, hwk, hkval] using hwy
  -- On the fixed first-entrance event, the stopped future starts afresh from `y`.
  have hlaw := markovChainLaw_restrict_map_stoppedValue_shift_iterate_eq_smul ν κ hτ hA hy
  have hAf : A ∩ {w | τ w ≠ ⊤} = A := by
    ext w
    simp only [A, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · exact And.left
    · intro hw
      exact ⟨hw, by simp [hw]⟩
  have hevent : {w | τ w = k ∧ w (k + n) ∈ s} =
      (A ∩ {w | τ w ≠ ⊤}) ∩ θ ⁻¹' B := by
    rw [hAf]
    ext w
    by_cases hw : τ w = k
    · simp [A, B, θ, stoppedValue, hw, hkval, shift_iterate_apply, Nat.add_comm]
    · simp [A, hw]
  -- Evaluate the restarted path law at the coordinate `n`.
  rw [hevent, Set.inter_comm, ← Measure.restrict_apply (hB.preimage hθ),
    ← Measure.map_apply hθ hB, hlaw, hAf]
  rw [smul_apply, smul_eq_mul]
  congr 1
  calc
    markovChainLaw (dirac y) κ B =
        ((markovChainLaw (dirac y) κ).map (fun w => w n)) s :=
      (Measure.map_apply (measurable_pi_apply n) hs).symm
    _ = (κ ^ n) y s := by
      rw [markovChainLaw_map_eval, Measure.dirac_bind (Kernel.measurable _)]

/-- **First-passage convolution.** The time-`n` mass at `y` splits according
to the first entrance to `y` at times `m, …, n`, followed by a return to `y`.
The search may miss `y` forever; those paths contribute no time-`n` mass. -/
theorem markovChainLaw_eval_eq_sum_hittingAfter (y : α) {m n : ℕ} (hmn : m ≤ n) :
    markovChainLaw ν κ {w | w n = y} =
      ∑ k ∈ Finset.Icc m n,
        markovChainLaw ν κ {w | hittingAfter (fun i w => w i) {y} m w = k} *
          (κ ^ (n - k)) y {y} := by
  classical
  let τ := hittingAfter (fun i (w : ℕ → α) => w i) {y} m
  let E (k : ℕ) : Set (ℕ → α) := {w | τ w = k ∧ w n = y}
  have hτ : Measurable τ :=
    (Filtration.adapted_piLE.isStoppingTime_hittingAfter
      (n := m) (measurableSet_singleton y)).measurable'
  have hE (k : ℕ) : MeasurableSet (E k) :=
    ((measurableSet_singleton (k : WithTop ℕ)).preimage hτ).inter
      ((measurableSet_singleton y).preimage (measurable_pi_apply n))
  have hdisj : (Finset.Icc m n : Set ℕ).PairwiseDisjoint E := by
    intro i hi j hj hij
    apply Set.disjoint_left.mpr
    rintro w ⟨hwi, _⟩ ⟨hwj, _⟩
    exact hij (WithTop.coe_injective (hwi.symm.trans hwj))
  -- A visit at time `n` forces a finite first entrance between `m` and `n`.
  have hcover : {w : ℕ → α | w n = y} = ⋃ k ∈ Finset.Icc m n, E k := by
    ext w
    constructor
    · intro hw
      have hle : τ w ≤ n := hittingAfter_le_of_mem hmn (by simpa using hw)
      have hfin : τ w ≠ ⊤ := ne_top_of_le_ne_top WithTop.coe_ne_top hle
      obtain ⟨k, hk⟩ := WithTop.ne_top_iff_exists.mp hfin
      have hm : m ≤ k := by
        have h : (m : WithTop ℕ) ≤ τ w := le_hittingAfter w
        rw [← hk] at h
        exact WithTop.coe_le_coe.mp h
      have hn : k ≤ n := by
        rw [← hk] at hle
        exact WithTop.coe_le_coe.mp hle
      exact Set.mem_iUnion.mpr ⟨k, Set.mem_iUnion.mpr
        ⟨Finset.mem_Icc.mpr ⟨hm, hn⟩, hk.symm, hw⟩⟩
    · intro hw
      obtain ⟨k, _, hk⟩ := Set.mem_iUnion₂.mp hw
      exact hk.2
  rw [hcover, measure_biUnion_finset hdisj (fun k _ => hE k)]
  -- Factor each first-entrance event by the Markov property.
  apply Finset.sum_congr rfl
  intro k hk
  have hkn : k + (n - k) = n := Nat.add_sub_of_le (Finset.mem_Icc.mp hk).2
  have h := markovChainLaw_hittingAfter_eq_inter_eval ν κ y m k (n - k)
    (measurableSet_singleton y)
  rw [hkn] at h
  simpa only [E, τ, Set.mem_singleton_iff] using h

end MeasureTheory.Measure
