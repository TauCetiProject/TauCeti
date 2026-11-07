/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Probability.Kernel.ClosedClass

/-!
# The renewal countdown chain

Given a probability law `μ` on `ℕ`, the countdown chain moves deterministically from `j + 1`
to `j`, and at zero samples a fresh value from `μ`. Thus `μ` represents the law of a strictly
positive renewal gap minus one. Its natural state space is `countdownStates μ`, the states
`j` with `μ [j, ∞) > 0`. We prove that this set is closed and that the restricted chain is
irreducible, including bounded gap laws and deterministic gaps.

Before the countdown reaches zero its transitions are deterministic. Every state reaches zero,
and zero reaches every state with positive tail mass. These facts provide the state-space and
irreducibility inputs for the Markov-chain proof of the lattice renewal theorem; no finite mean
or aperiodicity is assumed.

## References

* William Feller, *An Introduction to Probability Theory and Its Applications*, vol. II,
  second edition (1971), Chapter XI, the residual-life chain for arithmetic renewals.
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory Set

namespace MeasureTheory.Measure

/-- The countdown kernel with reset law `μ`: sample `μ` at zero and otherwise subtract one. -/
def countdownKernel (μ : Measure ℕ) : Kernel ℕ ℕ :=
  Kernel.ofFunOfCountable fun j => if j = 0 then μ else Measure.dirac (j - 1)

/-- The transition measure at zero is the reset law. -/
@[simp] theorem countdownKernel_zero (μ : Measure ℕ) : μ.countdownKernel 0 = μ := by
  simp [countdownKernel, Kernel.ofFunOfCountable]

/-- Positive states count down deterministically. -/
@[simp] theorem countdownKernel_succ (μ : Measure ℕ) (j : ℕ) :
    μ.countdownKernel (j + 1) = Measure.dirac j := by
  simp [countdownKernel, Kernel.ofFunOfCountable]

instance (μ : Measure ℕ) [IsProbabilityMeasure μ] : IsMarkovKernel μ.countdownKernel := by
  refine ⟨fun j => ?_⟩
  cases j <;> simp only [countdownKernel_zero, countdownKernel_succ] <;> infer_instance

/-- Up to and including the first visit to zero, the chain is a deterministic countdown. -/
theorem countdownKernel_pow_apply_of_le (μ : Measure ℕ) {n j : ℕ} (hn : n ≤ j) :
    (μ.countdownKernel ^ n) j = Measure.dirac (j - n) := by
  induction n generalizing j with
  | zero => simp [Kernel.one_def, Kernel.id_apply]
  | succ n ih =>
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
    rw [Kernel.pow_add _ n 1, pow_one, Kernel.comp_apply, countdownKernel_succ,
      Measure.dirac_bind (μ.countdownKernel ^ n).measurable, ih (by omega)]
    congr 1
    omega

/-- After the deterministic countdown, the chain evolves as if started at zero. -/
theorem countdownKernel_pow_add_apply (μ : Measure ℕ) (j n : ℕ) :
    (μ.countdownKernel ^ (j + n)) j = (μ.countdownKernel ^ n) 0 := by
  rw [Nat.add_comm j n, Kernel.pow_add _ n j, Kernel.comp_apply,
    countdownKernel_pow_apply_of_le μ le_rfl, Nat.sub_self,
    Measure.dirac_bind (μ.countdownKernel ^ n).measurable]

/-- Every state reaches zero after exactly its initial countdown length. -/
theorem countdownKernel_reaches_zero (μ : Measure ℕ) (j : ℕ) :
    μ.countdownKernel.Reaches j 0 := by
  rw [Kernel.reaches_def]
  refine ⟨j, ?_⟩
  simp [countdownKernel_pow_apply_of_le μ le_rfl]

/-- The natural state space: the downward closure of the atoms of the reset law. -/
def countdownStates (μ : Measure ℕ) : Set ℕ := {j | 0 < μ (Ici j)}

/-- A state belongs to the countdown state space exactly when its reset tail has positive mass. -/
@[simp] theorem mem_countdownStates (μ : Measure ℕ) (j : ℕ) :
    j ∈ μ.countdownStates ↔ 0 < μ (Ici j) := Iff.rfl

/-- Countdown state spaces are measurable. -/
@[measurability] theorem measurableSet_countdownStates (μ : Measure ℕ) :
    MeasurableSet μ.countdownStates := (to_countable _).measurableSet

/-- The countdown state space is downward closed. -/
theorem countdownStates_mono (μ : Measure ℕ) {i j : ℕ} (hij : i ≤ j)
    (hj : j ∈ μ.countdownStates) : i ∈ μ.countdownStates :=
  lt_of_lt_of_le hj (measure_mono (Ici_subset_Ici.mpr hij))

/-- Zero is a state for every nonzero reset law. -/
theorem zero_mem_countdownStates (μ : Measure ℕ) [NeZero μ] :
    0 ∈ μ.countdownStates := by
  simpa [mem_countdownStates] using (measure_univ_pos.mpr (NeZero.ne μ))

/-- The natural countdown state space of a nonzero reset law is nonempty. -/
instance (μ : Measure ℕ) [NeZero μ] : Nonempty μ.countdownStates :=
  ⟨⟨0, μ.zero_mem_countdownStates⟩⟩

/-- A state has positive tail mass exactly when some atom at or above it has positive mass. -/
theorem mem_countdownStates_iff_exists (μ : Measure ℕ) (j : ℕ) :
    j ∈ μ.countdownStates ↔ ∃ k, j ≤ k ∧ 0 < μ {k} := by
  simp only [mem_countdownStates, pos_iff_ne_zero,
    ne_eq, measure_null_iff_singleton (to_countable (Ici j)), not_forall, mem_Ici]
  tauto

/-- The reset law is concentrated on the countdown state space. -/
theorem measure_compl_countdownStates (μ : Measure ℕ) : μ μ.countdownStatesᶜ = 0 := by
  apply (measure_null_iff_singleton (to_countable _)).2
  intro j hj
  by_contra h
  exact hj ((mem_countdownStates_iff_exists μ j).2 ⟨j, le_rfl, pos_iff_ne_zero.2 h⟩)

/-- Countdown transitions never leave the natural state space. -/
theorem countdownKernel_isClosedSet (μ : Measure ℕ) :
    μ.countdownKernel.IsClosedSet μ.countdownStates := by
  rw [Kernel.isClosedSet_def]
  intro j hj
  cases j with
  | zero => simpa using measure_compl_countdownStates μ
  | succ j =>
    rw [countdownKernel_succ]
    simp [μ.countdownStates_mono (by omega : j ≤ j + 1) hj]

/-- Restricting the countdown kernel to its natural states loses no mass. -/
instance (μ : Measure ℕ) [IsProbabilityMeasure μ] :
    IsMarkovKernel (μ.countdownKernel.subtype μ.measurableSet_countdownStates) :=
  (Kernel.isMarkovKernel_subtype_iff_isClosedSet _).2 μ.countdownKernel_isClosedSet

/-- From zero, every state with positive reset tail is reachable. -/
theorem countdownKernel_zero_reaches (μ : Measure ℕ) {j : ℕ}
    (hj : j ∈ μ.countdownStates) : μ.countdownKernel.Reaches 0 j := by
  obtain ⟨k, hjk, hk⟩ := (mem_countdownStates_iff_exists μ j).1 hj
  have hreset : μ.countdownKernel.Reaches 0 k :=
    Kernel.reaches_of_pos (by simpa using hk)
  have hdown : μ.countdownKernel.Reaches k j := by
    rw [Kernel.reaches_def]
    refine ⟨k - j, ?_⟩
    rw [countdownKernel_pow_apply_of_le μ (Nat.sub_le k j)]
    have heq : k - (k - j) = j := by omega
    simp [heq]
  exact hreset.trans hdown

/-- Any two natural countdown states communicate, without a moment or span assumption. -/
theorem countdownKernel_communicates (μ : Measure ℕ) {i j : ℕ}
    (hi : i ∈ μ.countdownStates) (hj : j ∈ μ.countdownStates) :
    μ.countdownKernel.Communicates i j :=
  (Kernel.communicates_def _ _).2
    ⟨(μ.countdownKernel_reaches_zero i).trans (μ.countdownKernel_zero_reaches hj),
      (μ.countdownKernel_reaches_zero j).trans (μ.countdownKernel_zero_reaches hi)⟩

/-- The countdown chain on its natural state space is irreducible for counting measure. -/
theorem isIrreducible_countdownKernel_subtype (μ : Measure ℕ) :
    Kernel.IsIrreducible Measure.count
      (μ.countdownKernel.subtype μ.measurableSet_countdownStates) := by
  rw [Kernel.isIrreducible_subtype_iff _ μ.countdownKernel_isClosedSet]
  exact fun _ hi _ hj => μ.countdownKernel_communicates hi hj

/-- For a nonzero reset law, the natural state space is exactly the communicating class of zero. -/
theorem countdownKernel_communicatingClass_zero (μ : Measure ℕ) [NeZero μ] :
    μ.countdownKernel.communicatingClass 0 = μ.countdownStates := by
  ext j
  rw [Kernel.mem_communicatingClass_iff]
  constructor
  · intro hj
    exact (Kernel.isClosedSet_iff_forall_reaches_mem.1 μ.countdownKernel_isClosedSet)
      0 μ.zero_mem_countdownStates j ((Kernel.communicates_def _ _).1 hj).1
  · exact μ.countdownKernel_communicates μ.zero_mem_countdownStates

/-- For a positive integer gap law `ν`, resetting with the law of the gap minus one gives
exactly the states `j` with positive gap tail `ν (j, ∞)`. In particular zero gaps are excluded,
but no upper bound or moment assumption on the gaps is needed. -/
theorem countdownStates_map_pred (ν : Measure ℕ) (hν : ν {0} = 0) :
    (ν.map Nat.pred).countdownStates = {j | 0 < ν (Ioi j)} := by
  have hpos : ∀ᵐ n ∂ν, n ≠ 0 := by
    apply ae_iff.mpr
    simpa using hν
  ext j
  rw [mem_countdownStates, Measure.map_apply (measurable_of_countable _) measurableSet_Ici]
  have heq : ν (Nat.pred ⁻¹' Ici j) = ν (Ioi j) := by
    apply measure_congr
    filter_upwards [hpos] with n hn
    simp only [mem_preimage, mem_Ici, mem_Ioi, Nat.pred_eq_sub_one]
    exact propext (by omega)
  rw [heq]
  rfl

end MeasureTheory.Measure
