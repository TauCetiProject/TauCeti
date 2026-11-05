/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.SimpleGraph.Clique
public import Mathlib.Probability.Distributions.Uniform

/-!
# The hard-core distribution on independent sets

For a finite simple graph and a nonnegative activity `a`, the hard-core law assigns
an independent set `I` mass proportional to `a ^ I.card`. The empty set ensures
that the partition function is positive, even at activity zero and on an empty
vertex type. At activity zero the law is concentrated on the empty set; at
activity one it is uniform on all independent sets.

The single-site balance identity compares two configurations that agree away
from one vertex. It is the weight identity behind reversibility of single-site
hard-core sampling: the occupied and vacant choices have weights `a` and `1`.
No Markov kernel or convergence assertion is introduced here. The carrier is
Mathlib's finite-set subtype with its existing independent-set predicate.

## References

* Vincent Tassion, *Applied Stochastic Processes*, ETH Zürich, Spring 2025,
  Chapter 4 (hard-core sampling).
-/

public section

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory MeasureTheory.Measure

namespace SimpleGraph

variable {V : Type*} [Fintype V] (G : SimpleGraph V)

open Classical in
/-- The normalizing constant for the activity-weighted law on independent sets. -/
def hardCorePartition (a : ℝ≥0) : ℝ≥0 :=
  ∑ I : {s : Finset V // G.IsIndepSet (s : Set V)}, a ^ I.val.card

open Classical in
/-- The partition function is the sum of the activity weights of all independent sets. -/
theorem hardCorePartition_def (a : ℝ≥0) :
    G.hardCorePartition a =
      ∑ I : {s : Finset V // G.IsIndepSet (s : Set V)}, a ^ I.val.card := (rfl)

/-- The empty configuration contributes one to the partition function. -/
theorem one_le_hardCorePartition (a : ℝ≥0) : 1 ≤ G.hardCorePartition a := by
  classical
  let e : {s : Finset V // G.IsIndepSet (s : Set V)} :=
    ⟨∅, by simp [isIndepSet_iff]⟩
  have h := Finset.single_le_sum (fun I _ => (zero_le : (0 : ℝ≥0) ≤ a ^ I.val.card))
    (Finset.mem_univ e)
  simpa [hardCorePartition, e] using h

/-- The hard-core partition function never vanishes. -/
theorem hardCorePartition_pos (a : ℝ≥0) : 0 < G.hardCorePartition a :=
  lt_of_lt_of_le zero_lt_one (G.one_le_hardCorePartition a)

open Classical in
/-- The hard-core probability mass function on the independent sets of a finite graph.
Activity zero is allowed and gives the empty configuration with probability one. -/
def hardCorePMF (a : ℝ≥0) : PMF {s : Finset V // G.IsIndepSet (s : Set V)} :=
  PMF.normalize (fun I => (a : ℝ≥0∞) ^ I.val.card)
    (by
      simp_rw [tsum_fintype, ← ENNReal.coe_pow]
      rw [← ENNReal.ofNNReal_finsetSum]
      exact_mod_cast (G.hardCorePartition_pos a).ne')
    (by
      simp_rw [tsum_fintype, ← ENNReal.coe_pow]
      rw [← ENNReal.ofNNReal_finsetSum]
      exact ENNReal.coe_ne_top)

/-- Each independent set has its activity weight divided by the partition function. -/
@[simp] theorem hardCorePMF_apply (a : ℝ≥0)
    (I : {s : Finset V // G.IsIndepSet (s : Set V)}) :
    G.hardCorePMF a I = (a : ℝ≥0∞) ^ I.val.card / G.hardCorePartition a := by
  classical
  simp only [hardCorePMF, PMF.normalize_apply, tsum_fintype, hardCorePartition,
    div_eq_mul_inv, ENNReal.ofNNReal_finsetSum, ENNReal.coe_pow]

/-- A configuration has positive mass exactly when the activity is positive or it is empty. -/
theorem hardCorePMF_pos_iff (a : ℝ≥0)
    (I : {s : Finset V // G.IsIndepSet (s : Set V)}) :
    0 < G.hardCorePMF a I ↔ 0 < a ∨ I.val = ∅ := by
  rw [hardCorePMF_apply, ENNReal.div_pos_iff]
  simp only [ENNReal.coe_ne_top, ne_eq, not_false_eq_true, and_true,
    pos_iff_ne_zero, pow_eq_zero_iff', ENNReal.coe_eq_zero, Finset.card_eq_zero]
  tauto

open Classical in
/-- At activity one the partition function counts independent sets. -/
@[simp] theorem hardCorePartition_one :
    G.hardCorePartition 1 =
      Fintype.card {s : Finset V // G.IsIndepSet (s : Set V)} := by
  simp [hardCorePartition]

/-- At activity zero the partition function is one, contributed by the empty set alone. -/
@[simp] theorem hardCorePartition_zero : G.hardCorePartition 0 = 1 := by
  classical
  let e : {s : Finset V // G.IsIndepSet (s : Set V)} :=
    ⟨∅, by simp [isIndepSet_iff]⟩
  rw [hardCorePartition, Finset.sum_eq_single e]
  · simp [e]
  · intro I _ hI
    have hne : I.val ≠ ∅ := fun h => hI (Subtype.ext h)
    simp [hne]
  · simp

/-- Activity zero gives the point mass at the empty independent set. -/
@[simp] theorem hardCorePMF_zero :
    G.hardCorePMF 0 = PMF.pure ⟨∅, by simp [isIndepSet_iff]⟩ := by
  classical
  ext I
  simp [PMF.pure_apply, Subtype.ext_iff, zero_pow_eq]

open Classical in
/-- The activity-one law agrees with Mathlib's uniform measure on independent sets. -/
theorem hardCorePMF_one_toMeasure
    [MeasurableSpace {s : Finset V // G.IsIndepSet (s : Set V)}]
    [MeasurableSingletonClass {s : Finset V // G.IsIndepSet (s : Set V)}] :
    (G.hardCorePMF 1).toMeasure = uniformOfFinset Finset.univ := by
  apply Measure.ext_of_singleton
  intro I
  simp [uniformOfFinset_apply_singleton]

open Classical in
/-- Single-site balance: if two independent sets agree off `v`, their Gibbs
masses balance the occupied/vacant weights. This includes activity zero. -/
theorem hardCorePMF_single_site_balance (a : ℝ≥0)
    (I J : {s : Finset V // G.IsIndepSet (s : Set V)}) (v : V)
    (h : I.val.erase v = J.val.erase v) :
    G.hardCorePMF a I * (if v ∈ J.val then (a : ℝ≥0∞) else 1) =
      G.hardCorePMF a J * (if v ∈ I.val then (a : ℝ≥0∞) else 1) := by
  -- Factor each weight into the common outside configuration and the choice at `v`.
  have hw (s : Finset V) : (a : ℝ≥0∞) ^ s.card =
      (a : ℝ≥0∞) ^ (s.erase v).card * (if v ∈ s then (a : ℝ≥0∞) else 1) := by
    by_cases hs : v ∈ s
    · rw [← Finset.card_erase_add_one hs, pow_succ]
      simp [hs]
    · simp [hs]
  rw [hardCorePMF_apply, hardCorePMF_apply, hw I.val, hw J.val, h]
  simp only [div_eq_mul_inv]
  ring

end SimpleGraph
