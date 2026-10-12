/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Combinatorics.PermutationTriple.OrbitDecomposition.Basic
public import TauCeti.Combinatorics.PermutationTriple.EulerCharacteristic
import TauCeti.GroupTheory.Perm.SigmaCongr

/-!
# Additivity over the connected components of a permutation triple

The cycle partitions, cycle counts and Euler characteristic of an indexed disjoint sum
are the sums of those of its summands. Applying these calculations to the monodromy-orbit
decomposition computes the invariants of any permutation triple from its connected
restrictions.

In particular, if there are `c` monodromy orbits, the Euler characteristic is
`2c - 2∑ g`, where the sum ranges over the genera of the connected restrictions. The genus
of a disconnected triple itself has no such geometric meaning; all genera in this formula
are those of the connected components.

## References

* S. K. Lando, A. K. Zvonkin, *Graphs on Surfaces and Their Applications*, Encyclopaedia of
  Mathematical Sciences 141, Springer 2004, §1.5.
-/

public section

namespace TauCeti.PermutationTriple

open Equiv Equiv.Perm

section IndexedDisjointSum

variable {N : ℕ} {ι : Type*} [Fintype ι] {d : ι → ℕ}
  (t : ∀ i, PermutationTriple (d i)) (e : (Σ i, Fin (d i)) ≃ Fin N)

/-- The three full cycle partitions of an indexed disjoint sum concatenate independently
at each branch point. -/
@[simp]
theorem cycleData_indexedDisjointSum :
    (indexedDisjointSum t e).cycleData =
      (∑ i, (t i).cycleData.1, ∑ i, (t i).cycleData.2.1,
        ∑ i, (t i).cycleData.2.2) := by
  classical
  apply Prod.ext
  · simp
  · apply Prod.ext <;> simp

/-- Cycle counts, including the fixed points, add over indexed disjoint sums. -/
@[simp]
theorem cycleCounts_indexedDisjointSum :
    (indexedDisjointSum t e).cycleCounts =
      (∑ i, (t i).cycleCounts.1, ∑ i, (t i).cycleCounts.2.1,
        ∑ i, (t i).cycleCounts.2.2) := by
  apply Prod.ext
  · simp
  · apply Prod.ext <;> simp

/-- The Euler characteristic adds over indexed disjoint sums, including an empty sum. -/
@[simp]
theorem eulerChar_indexedDisjointSum :
    (indexedDisjointSum t e).eulerChar = ∑ i, (t i).eulerChar := by
  classical
  have hdegree : ∑ i, d i = N := by simpa using Fintype.card_congr e
  have hdegree' : (∑ i, (d i : ℤ)) = N := by exact_mod_cast hdegree
  simp only [eulerChar_def, indexedDisjointSum_σ0, indexedDisjointSum_σ1,
    indexedDisjointSum_σinf, Equiv.orbitCount_permCongr, orbitCount_sigmaCongrRight,
    Nat.cast_sum, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [hdegree']

end IndexedDisjointSum

variable {n : ℕ} (t : PermutationTriple n)

attribute [local instance] Fintype.ofFinite

/-- The degrees of the connected restrictions sum to the degree of the original triple. -/
theorem sum_ncard_monodromyOrbit : ∑ O : t.MonodromyOrbit, O.orbit.ncard = n := by
  simpa using Fintype.card_congr t.orbitDecompositionEquiv

/-- The full cycle partitions of a triple are the sums of those of its connected
restrictions. -/
theorem cycleData_eq_sum_restrictToOrbit :
    t.cycleData =
      (∑ O : t.MonodromyOrbit, (t.restrictToOrbit O).cycleData.1,
        ∑ O : t.MonodromyOrbit, (t.restrictToOrbit O).cycleData.2.1,
        ∑ O : t.MonodromyOrbit, (t.restrictToOrbit O).cycleData.2.2) := by
  simpa only [indexedDisjointSum_restrictToOrbit] using
    cycleData_indexedDisjointSum (fun O => t.restrictToOrbit O) t.orbitDecompositionEquiv

/-- The cycle counts of a triple are the sums of those of its connected restrictions. -/
theorem cycleCounts_eq_sum_restrictToOrbit :
    t.cycleCounts =
      (∑ O : t.MonodromyOrbit, (t.restrictToOrbit O).cycleCounts.1,
        ∑ O : t.MonodromyOrbit, (t.restrictToOrbit O).cycleCounts.2.1,
        ∑ O : t.MonodromyOrbit, (t.restrictToOrbit O).cycleCounts.2.2) := by
  simpa only [indexedDisjointSum_restrictToOrbit] using
    cycleCounts_indexedDisjointSum (fun O => t.restrictToOrbit O) t.orbitDecompositionEquiv

/-- The Euler characteristic of any triple is the sum of the Euler characteristics of its
connected restrictions. -/
theorem eulerChar_eq_sum_restrictToOrbit :
    t.eulerChar = ∑ O : t.MonodromyOrbit, (t.restrictToOrbit O).eulerChar := by
  simpa only [indexedDisjointSum_restrictToOrbit] using
    eulerChar_indexedDisjointSum (fun O => t.restrictToOrbit O) t.orbitDecompositionEquiv

/-- The Euler characteristic of a possibly disconnected triple is twice the number of
connected components minus twice the sum of their genera. -/
theorem eulerChar_eq_two_mul_card_sub_two_mul_sum_genus :
    t.eulerChar = 2 * Nat.card t.MonodromyOrbit -
      2 * ∑ O : t.MonodromyOrbit, ((t.restrictToOrbit O).genus : ℤ) := by
  rw [eulerChar_eq_sum_restrictToOrbit]
  simp_rw [← (isConnected_restrictToOrbit t _).two_sub_two_mul_genus]
  simp [Finset.sum_sub_distrib, ← Finset.mul_sum, Nat.card_eq_fintype_card, mul_comm]

end TauCeti.PermutationTriple
