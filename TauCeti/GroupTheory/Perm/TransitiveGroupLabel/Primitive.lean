/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Classification
import TauCeti.GroupTheory.GroupAction.Primitive
import TauCeti.GroupTheory.Perm.SylowFour
import Mathlib.GroupTheory.GroupAction.MultipleTransitivity

/-!
# Primitivity of the transitive groups of degree at most five

The reference subgroups `TauCeti.referenceSubgroup` represent the transitive subgroups of the
symmetric groups on at most five points. This file determines which of them act primitively.

In prime degree every transitive group is primitive, which settles the degrees two, three and
five, and the one-point action of degree one is primitive by Mathlib's convention. In degree
four, the alternating group `4T4` and the symmetric group `4T5` are primitive, while the cyclic
group `4T1`, the Klein four-group `4T2` and the dihedral group `4T3` are not: the dihedral group
of order eight is the image of the imprimitive wreath product `C₂ ≀ S₂`, which preserves a
partition of the four points into two pairs, and the other two groups lie inside it.

Primitivity of a permutation group with a transitive-group label depends only on the label
(`TauCeti.TransitiveGroupLabel.isPreprimitive_iff`), so the table applies to every transitive
subgroup of degree at most five.

## Main results

* `TauCeti.isPreprimitive_referenceSubgroup_of_prime`: in prime degree every reference subgroup
  is primitive.
* `TauCeti.not_isPreprimitive_referenceSubgroup_four_two`, with its companions for `4T1` and
  `4T2`: the three imprimitive quartic labels.
* `TauCeti.isPreprimitive_referenceSubgroup_four_iff`: in degree four exactly `4T4` and `4T5`
  are primitive.
* `TauCeti.isPreprimitive_referenceSubgroup_iff`: the primitivity column of the table of
  transitive groups of degree at most five.
* `TauCeti.TransitiveGroupLabel.isPreprimitive_iff_ne_four_or_three_le`: a permutation group
  with a label is primitive exactly when its label is not `4T1`, `4T2` or `4T3`.
-/

public section

open Equiv MulAction

namespace TauCeti

/-- In degree one the unique reference subgroup acts primitively on the single point. -/
theorem isPreprimitive_referenceSubgroup_one (j : TransitiveGroupIndex 1) :
    IsPreprimitive (referenceSubgroup 1 j) (Fin 1) :=
  IsPreprimitive.of_subsingleton

/-- **In prime degree every reference subgroup is primitive**, being transitive on a set of prime
cardinality. -/
theorem isPreprimitive_referenceSubgroup_of_prime {n : ℕ} (hn : n.Prime)
    (j : TransitiveGroupIndex n) : IsPreprimitive (referenceSubgroup n j) (Fin n) :=
  haveI := isPretransitive_referenceSubgroup n j
  IsPreprimitive.of_prime_card (by rwa [Nat.card_fin])

/-- The reference subgroup of `4T3`, the dihedral group of order eight, is not primitive: it is
conjugate to the image of the imprimitive wreath product `C₂ ≀ S₂`, which preserves a partition
of the four points into two pairs. -/
theorem not_isPreprimitive_referenceSubgroup_four_two :
    ¬ IsPreprimitive (referenceSubgroup 4 ⟨2, by simp⟩) (Fin 4) := by
  rw [← transitiveGroupLabel_wreathTwoToPermFour.isPreprimitive_iff]
  exact not_isPreprimitive_range_wreathTwoToPermFour

/-- The reference subgroup of `4T1`, the cyclic group of order four, is not primitive: it lies in
the dihedral group of `4T3`. -/
theorem not_isPreprimitive_referenceSubgroup_four_zero :
    ¬ IsPreprimitive (referenceSubgroup 4 ⟨0, by simp⟩) (Fin 4) := fun _ =>
  not_isPreprimitive_referenceSubgroup_four_two
    (IsPreprimitive.of_le referenceSubgroup_four_zero_le_referenceSubgroup_four_two)

/-- The reference subgroup of `4T2`, the Klein four-group, is not primitive: it lies in the
dihedral group of `4T3`. -/
theorem not_isPreprimitive_referenceSubgroup_four_one :
    ¬ IsPreprimitive (referenceSubgroup 4 ⟨1, by simp⟩) (Fin 4) := fun _ =>
  not_isPreprimitive_referenceSubgroup_four_two
    (IsPreprimitive.of_le referenceSubgroup_four_one_le_referenceSubgroup_four_two)

/-- The reference subgroup of `4T4`, the alternating group, is primitive. -/
theorem isPreprimitive_referenceSubgroup_four_three :
    IsPreprimitive (referenceSubgroup 4 ⟨3, by simp⟩) (Fin 4) := by
  rw [referenceSubgroup_four_three]
  exact alternatingGroup.isPreprimitive_of_three_le_card (Fin 4) (by simp)

/-- The reference subgroup of `4T5`, the symmetric group, is primitive. -/
theorem isPreprimitive_referenceSubgroup_four_four :
    IsPreprimitive (referenceSubgroup 4 ⟨4, by simp⟩) (Fin 4) := by
  rw [referenceSubgroup_four_four]
  have := alternatingGroup.isPreprimitive_of_three_le_card (Fin 4) (by simp)
  exact IsPreprimitive.of_le (H := alternatingGroup (Fin 4)) le_top

/-- **The primitive quartic labels.** Of the five transitive subgroups of the symmetric group on
four points, the alternating group of `4T4` and the symmetric group of `4T5` are primitive, and
the cyclic, Klein four and dihedral groups of `4T1`, `4T2` and `4T3` are not. -/
theorem isPreprimitive_referenceSubgroup_four_iff (j : TransitiveGroupIndex 4) :
    IsPreprimitive (referenceSubgroup 4 j) (Fin 4) ↔ 3 ≤ (j : ℕ) := by
  obtain ⟨a, ha⟩ := j
  rw [numTransitiveGroups_four] at ha
  interval_cases a
  · exact iff_of_false not_isPreprimitive_referenceSubgroup_four_zero (by simp)
  · exact iff_of_false not_isPreprimitive_referenceSubgroup_four_one (by simp)
  · exact iff_of_false not_isPreprimitive_referenceSubgroup_four_two (by simp)
  · exact iff_of_true isPreprimitive_referenceSubgroup_four_three (by simp)
  · exact iff_of_true isPreprimitive_referenceSubgroup_four_four (by simp)

/-- **The primitivity column of the table of transitive groups of degree at most five.** A
reference subgroup acts primitively unless its label is one of `4T1`, `4T2` and `4T3`. -/
@[simp]
theorem isPreprimitive_referenceSubgroup_iff :
    ∀ {n : ℕ} (j : TransitiveGroupIndex n),
      IsPreprimitive (referenceSubgroup n j) (Fin n) ↔ n ≠ 4 ∨ 3 ≤ (j : ℕ)
  | 0, j => (lt_irrefl 0 (pos_of_transitiveGroupIndex j)).elim
  | 1, j => iff_of_true (isPreprimitive_referenceSubgroup_one j) (Or.inl (by decide))
  | 2, j =>
    iff_of_true (isPreprimitive_referenceSubgroup_of_prime Nat.prime_two j) (Or.inl (by decide))
  | 3, j =>
    iff_of_true (isPreprimitive_referenceSubgroup_of_prime Nat.prime_three j)
      (Or.inl (by decide))
  | 4, j => (isPreprimitive_referenceSubgroup_four_iff j).trans (by simp)
  | 5, j =>
    iff_of_true (isPreprimitive_referenceSubgroup_of_prime Nat.prime_five j)
      (Or.inl (by decide))
  | n + 6, j => by
    have hj := j.isLt
    have h0 : numTransitiveGroups (n + 6) = 0 := numTransitiveGroups_eq_zero_of_five_lt (by omega)
    omega

/-- A permutation group with a transitive-group label acts primitively exactly when its label is
not one of `4T1`, `4T2` and `4T3`. -/
theorem TransitiveGroupLabel.isPreprimitive_iff_ne_four_or_three_le {n : ℕ}
    {j : TransitiveGroupIndex n} {G : Subgroup (Perm (Fin n))} (h : TransitiveGroupLabel j G) :
    IsPreprimitive G (Fin n) ↔ n ≠ 4 ∨ 3 ≤ (j : ℕ) := by
  rw [h.isPreprimitive_iff, isPreprimitive_referenceSubgroup_iff]

end TauCeti
