/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Probability.Distributions.Bernoulli
public import TauCeti.Probability.Distributions.Uniform.Finite
public import TauCeti.Probability.Kernel.PMF
public import TauCeti.Probability.Kernel.Reachability
public import TauCeti.Probability.MarkovChain.Period

/-!
# The hard-core sampling chain

The states are independent vertex sets of a finite simple graph. One update chooses a vertex
uniformly, removes it, and attempts to insert it with probability `p`. An insertion is accepted
exactly when the resulting set is independent. Thus the update is the usual single-site
hard-core heat bath, with `p = λ / (1 + λ)` for activity `λ`.

The kernel is irreducible when `0 < p < 1`: delete vertices to reach the empty set, then insert
the desired vertices. Every state has a self-loop under these same hypotheses, so the chain is
aperiodic. These properties do not require connectedness of the graph. The zero probability
boundary is retained in the construction, but no irreducibility is asserted there.

This file constructs the chain and establishes its communication and period properties.
The equilibrium law and convergence are developed in `HardCore.Equilibrium`.

## References

* Vincent Tassion, *Applied Stochastic Processes*, ETH Zürich, Spring 2025, Chapter 4
  (hard-core sampling).
-/

public section

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace TauCeti.Probability.HardCore

/-- The insertion probability corresponding to a finite nonnegative hard-core activity.
Activity one gives probability one half; activity zero permits only deletions. -/
def activityProbability (a : ℝ≥0) : unitInterval :=
  ⟨(a : ℝ) / (1 + a), by
    constructor
    · positivity
    · exact (div_le_one (by positivity)).mpr (by linarith [a.coe_nonneg])⟩

@[simp] theorem coe_activityProbability (a : ℝ≥0) :
    (activityProbability a : ℝ) = (a : ℝ) / (1 + a) := (rfl)

/-- Finite activity always gives a positive deletion probability. -/
theorem activityProbability_lt_one (a : ℝ≥0) : (activityProbability a : ℝ) < 1 := by
  rw [coe_activityProbability, div_lt_one (by positivity)]
  linarith

/-- The insertion probability is positive exactly for positive activity. -/
theorem activityProbability_pos_iff (a : ℝ≥0) :
    0 < (activityProbability a : ℝ) ↔ 0 < a := by
  rw [coe_activityProbability, div_pos_iff_of_pos_right (by positivity)]
  exact NNReal.coe_pos

@[simp] theorem activityProbability_zero : activityProbability 0 = 0 := by
  apply Subtype.ext
  simp

variable {V : Type*} (G : SimpleGraph V)

/-- The independent vertex sets, with no fixed cardinality. -/
abbrev State := {s : Finset V // G.IsIndepSet (s : Set V)}

/-- Independent sets carry the discrete measurable space. -/
instance instMeasurableSpaceState : MeasurableSpace (State G) := ⊤

instance instMeasurableSingletonClassState : MeasurableSingletonClass (State G) :=
  ⟨fun _ => trivial⟩

/-- The empty independent set. -/
def empty : State G := ⟨∅, by simp [SimpleGraph.IsIndepSet]⟩

@[simp] theorem empty_val : (empty G).val = ∅ := (rfl)

variable [DecidableEq V]

/-- Remove a vertex from an independent set. -/
def erase (I : State G) (v : V) : State G :=
  ⟨I.val.erase v, I.property.mono (by simp only [Finset.coe_subset]; exact Finset.erase_subset v _)⟩

@[simp] theorem erase_val (I : State G) (v : V) : (erase G I v).val = I.val.erase v := (rfl)

/-- Deleting an absent vertex leaves the state unchanged. -/
@[simp] theorem erase_of_notMem (I : State G) {v : V} (hv : v ∉ I.val) :
    erase G I v = I := by
  exact Subtype.ext (Finset.erase_eq_of_notMem hv)

variable [DecidableRel G.Adj]

/-- Remove the selected vertex, then insert it if this is allowed by independence. -/
def occupy (I : State G) (v : V) : State G :=
  if h : G.IsIndepSet (↑(insert v I.val) : Set V) then
    ⟨insert v I.val, h⟩ else erase G I v

/-- An allowed insertion gives precisely the set with the vertex inserted. -/
theorem occupy_val_of_indep (I : State G) (v : V)
    (h : G.IsIndepSet (↑(insert v I.val) : Set V)) :
    (occupy G I v).val = insert v I.val := by rw [occupy, dite_eq_left h]

/-- A blocked insertion leaves the selected vertex absent. -/
theorem occupy_of_not_indep (I : State G) (v : V)
    (h : ¬G.IsIndepSet (↑(insert v I.val) : Set V)) :
    occupy G I v = erase G I v := by rw [occupy, dite_eq_right h]

/-- The two single-site outcomes agree away from the selected vertex. -/
@[simp] theorem erase_occupy (I : State G) (v : V) :
    erase G (occupy G I v) v = erase G I v := by
  unfold occupy
  split
  · apply Subtype.ext
    simp [erase_val]
  · simp

/-- Either single-site outcome preserves the configuration away from the selected vertex. -/
theorem erase_eq_of_single_site_eq (I J : State G) (v : V)
    (h : occupy G I v = J ∨ erase G I v = J) : erase G I v = erase G J v := by
  rcases h with h | h <;>
    simpa using congrArg (fun K => erase G K v) h

/-- Resampling a vertex already present can retain the state. -/
@[simp] theorem occupy_of_mem (I : State G) {v : V} (hv : v ∈ I.val) : occupy G I v = I := by
  have h : insert v I.val = I.val := Finset.insert_eq_of_mem hv
  simp [occupy, h, I.property]

/-- Inserting a vertex after erasing it recovers the original state when it was present. -/
@[simp] theorem occupy_erase_of_mem (I : State G) {v : V} (hv : v ∈ I.val) :
    occupy G (erase G I v) v = I := by
  have h : insert v (erase G I v).val = I.val := by simp [hv]
  rw [occupy, dite_eq_left (by rw [h]; exact I.property)]
  exact Subtype.ext h

variable [Fintype V] [Nonempty V]

/-- Vertex selection uses the discrete measurable space. -/
local instance instMeasurableSpaceVertex : MeasurableSpace V := ⊤

/-- The hard-core transition kernel with insertion probability `p`. The chosen vertex is
uniform, and at that vertex the two possible outcomes are the accepted insertion and deletion.
Blocked insertions coincide with deletion, so their probabilities add rather than disappear. -/
def kernel (p : unitInterval) : Kernel (State G) (State G) :=
  Kernel.ofPMF fun I =>
    (Measure.uniformOfFinset (Finset.univ : Finset V)).toPMF.bind fun v =>
      (bernoulliMeasure (occupy G I v) (erase G I v) p).toPMF

instance (p : unitInterval) : IsMarkovKernel (kernel G p) := by
  unfold kernel
  infer_instance

/-- The singleton transition formula is the uniform average of the single-site updates. It
also covers blocked insertions and updates that leave the state unchanged. -/
theorem kernel_apply_singleton (p : unitInterval) (I J : State G) :
    kernel G p I {J} = ∑ v : V, (Fintype.card V : ℝ≥0∞)⁻¹ *
      ((if occupy G I v = J then ENNReal.ofReal p else 0) +
        if erase G I v = J then ENNReal.ofReal (1 - p) else 0) := by
  simp only [kernel, Kernel.ofPMF_apply_singleton, PMF.bind_apply, tsum_fintype,
    Measure.toPMF_apply]
  congr 1
  ext v
  simp [bernoulliMeasure_def, Pi.single_apply,
    ← ENNReal.ofReal_coe_nnreal, unitInterval.coe_symm_eq, eq_comm]

/-- Any deletion is a positive transition when the deletion probability is positive. -/
theorem kernel_erase_pos (p : unitInterval) (hp : (p : ℝ) < 1) (I : State G) (v : V) :
    0 < kernel G p I {erase G I v} := by
  rw [kernel_apply_singleton]
  apply lt_of_lt_of_le _ (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ v))
  simp only [ite_true]
  exact ENNReal.mul_pos (by simp)
    (ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr (sub_pos.mpr hp))
      (le_add_left le_rfl)))

/-- Any allowed insertion outcome is a positive transition when `p` is positive. -/
theorem kernel_occupy_pos (p : unitInterval) (hp : 0 < (p : ℝ)) (I : State G) (v : V) :
    0 < kernel G p I {occupy G I v} := by
  rw [kernel_apply_singleton]
  apply lt_of_lt_of_le _ (Finset.single_le_sum (fun _ _ => bot_le) (Finset.mem_univ v))
  simp only [ite_true]
  exact ENNReal.mul_pos (by simp)
    (ne_of_gt (lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hp) (le_add_right le_rfl)))

/-- Delete the finitely many occupied vertices to reach the empty state. -/
theorem reaches_empty (p : unitInterval) (hp : (p : ℝ) < 1) (I : State G) :
    (kernel G p).Reaches I (empty G) := by
  induction hn : I.val.card using Nat.strong_induction_on generalizing I with
  | ind n ih =>
    by_cases he : I.val = ∅
    · have : I = empty G := Subtype.ext he
      subst I
      exact Kernel.Reaches.refl _
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr he
    exact (Kernel.reaches_of_pos (kernel_erase_pos G p hp I v)).trans
      (ih (erase G I v).val.card (by simpa [← hn] using Finset.card_erase_lt_of_mem hv)
        (erase G I v) rfl)

/-- Insert the desired vertices, all intermediate subsets remaining independent. -/
theorem empty_reaches (p : unitInterval) (hp : 0 < (p : ℝ)) (I : State G) :
    (kernel G p).Reaches (empty G) I := by
  induction hn : I.val.card using Nat.strong_induction_on generalizing I with
  | ind n ih =>
    by_cases he : I.val = ∅
    · have : I = empty G := Subtype.ext he
      subst I
      exact Kernel.Reaches.refl _
    obtain ⟨v, hv⟩ := Finset.nonempty_iff_ne_empty.mpr he
    have hsmall := ih (erase G I v).val.card
      (by simpa [← hn] using Finset.card_erase_lt_of_mem hv) (erase G I v) rfl
    exact hsmall.trans (Kernel.reaches_of_pos (by
      simpa [hv] using kernel_occupy_pos G p hp (erase G I v) v))

/-- The hard-core chain is irreducible on all independent sets for an interior insertion
probability, even when the underlying graph is disconnected. -/
theorem isIrreducible (p : unitInterval) (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) < 1) :
    Kernel.IsIrreducible Measure.count (kernel G p) :=
  Kernel.isIrreducible_count_iff_forall_reaches.mpr fun I J =>
    (reaches_empty G p hp₁ I).trans (empty_reaches G p hp₀ J)

/-- Every state has a self-loop: retain an occupied selected vertex, or delete an absent one. -/
theorem kernel_self_pos (p : unitInterval) (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) < 1)
    (I : State G) : 0 < kernel G p I {I} := by
  let v : V := Classical.choice inferInstance
  by_cases hv : v ∈ I.val
  · simpa [hv] using kernel_occupy_pos G p hp₀ I v
  · have h : erase G I v = I := Subtype.ext (Finset.erase_eq_of_notMem hv)
    simpa [h] using kernel_erase_pos G p hp₁ I v

/-- The hard-core chain has period one at every independent set. -/
theorem isAperiodic (p : unitInterval) (hp₀ : 0 < (p : ℝ)) (hp₁ : (p : ℝ) < 1) :
    (kernel G p).IsAperiodic :=
  Kernel.isAperiodic_iff.mpr fun I =>
    Kernel.period_eq_one_of_pos_apply (kernel_self_pos G p hp₀ hp₁ I)

end TauCeti.Probability.HardCore
