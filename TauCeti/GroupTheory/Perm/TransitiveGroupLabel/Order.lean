/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Classification

/-! # Recognition of the low-degree transitive groups by order

In degrees at most five, the order of a transitive permutation group determines its
transitive-group label up to one collision: the two labels of order four, `4T1` and `4T2`, are
distinguished by cyclicity. Together with `TauCeti.TransitiveGroupLabel.isCyclic_iff`, which
transports cyclicity across a transitive-group label, this recognizes every label of degree at
most five from the order of the labelled subgroup alone, or from its order and cyclicity in
degree four.

## Main results

* `TauCeti.TransitiveGroupLabel.natCard_mem_three`,
  `TauCeti.TransitiveGroupLabel.natCard_mem_four`: the order of a subgroup labelled `3Tj` or
  `4Tj` is one of `3, 6` or `4, 8, 12, 24`, respectively. In degree five the corresponding
  fact follows from `TauCeti.natCard_mem_of_natCard_eq_five_of_isPretransitive` and
  `TauCeti.TransitiveGroupLabel.isPretransitive`.
* `TauCeti.transitiveGroupLabel_three_iff_natCard_eq`,
  `TauCeti.transitiveGroupLabel_five_iff_natCard_eq`: in degrees three and five the order
  recognizes the label.
* `TauCeti.transitiveGroupLabel_four_zero_iff`, `TauCeti.transitiveGroupLabel_four_one_iff`: the
  two labels of order four in degree four are exactly distinguished by cyclicity.
* `TauCeti.transitiveGroupLabel_four_iff_natCard_eq_of_two_le`: the order recognizes the labels
  `4T3`, `4T4` and `4T5`.

## Tags

transitive group, recognition, order
-/

public section

namespace TauCeti

open Equiv Equiv.Perm MulAction

/-- **The order of a labelled subgroup of `S₃` is `3` or `6`.** These are the orders `3, 6` of
the labels `3T1` and `3T2`. -/
theorem TransitiveGroupLabel.natCard_mem_three {j : TransitiveGroupIndex 3}
    {G : Subgroup (Perm (Fin 3))} (h : TransitiveGroupLabel j G) :
    Nat.card G ∈ ({3, 6} : Finset ℕ) := by
  obtain ⟨a, ha⟩ := j
  rw [numTransitiveGroups_three] at ha
  interval_cases a
  · rw [h.natCard_eq, natCard_referenceSubgroup_three_zero]
    simp
  · rw [h.natCard_eq, natCard_referenceSubgroup_three_one]
    simp

/-- **The order of a labelled subgroup of `S₄` is one of `4, 8, 12, 24`.** These are the orders
`4, 4, 8, 12, 24` of the labels `4T1` through `4T5`; the two labels of order four give the single
value `4`. -/
theorem TransitiveGroupLabel.natCard_mem_four {j : TransitiveGroupIndex 4}
    {G : Subgroup (Perm (Fin 4))} (h : TransitiveGroupLabel j G) :
    Nat.card G ∈ ({4, 8, 12, 24} : Finset ℕ) := by
  obtain ⟨a, ha⟩ := j
  rw [numTransitiveGroups_four] at ha
  interval_cases a
  · rw [h.natCard_eq, natCard_referenceSubgroup_four_zero]
    simp
  · rw [h.natCard_eq, natCard_referenceSubgroup_four_one]
    simp
  · rw [h.natCard_eq, natCard_referenceSubgroup_four_two]
    simp
  · rw [h.natCard_eq, natCard_referenceSubgroup_four_three]
    simp
  · rw [h.natCard_eq, natCard_referenceSubgroup_four_four]
    simp

/-- **Order recognition in degree three.** A transitive subgroup of `S₃` is labelled `3Tj`
exactly when its order is that of `3Tj`: the orders `3, 6` of `3T1` and `3T2` are distinct. -/
theorem transitiveGroupLabel_three_iff_natCard_eq (j : TransitiveGroupIndex 3)
    (G : Subgroup (Perm (Fin 3))) [IsPretransitive G (Fin 3)] :
    TransitiveGroupLabel j G ↔ Nat.card G = Nat.card (referenceSubgroup 3 j) :=
  ⟨fun h => h.natCard_eq, fun h => by
    obtain ⟨k, hk, -⟩ := existsUnique_transitiveGroupLabel_three G
    have hjk : j = k := by
      have h2 : Nat.card (referenceSubgroup 3 j) = Nat.card (referenceSubgroup 3 k) :=
        h.symm.trans hk.natCard_eq
      obtain ⟨a, ha⟩ := j
      obtain ⟨b, hb⟩ := k
      rw [numTransitiveGroups_three] at ha hb
      interval_cases a <;> interval_cases b <;> first
        | rfl
        | simp only [natCard_referenceSubgroup_three_zero,
            natCard_referenceSubgroup_three_one] at h2
          omega
    rw [hjk]
    exact hk⟩

/-- **Order recognition in degree five.** A transitive subgroup of `S₅` is labelled `5Tj` exactly
when its order is that of `5Tj`: the orders `5, 10, 20, 60, 120` of `5T1` through `5T5` are
pairwise distinct. -/
theorem transitiveGroupLabel_five_iff_natCard_eq (j : TransitiveGroupIndex 5)
    (G : Subgroup (Perm (Fin 5))) [IsPretransitive G (Fin 5)] :
    TransitiveGroupLabel j G ↔ Nat.card G = Nat.card (referenceSubgroup 5 j) :=
  ⟨fun h => h.natCard_eq, fun h => by
    obtain ⟨k, hk, -⟩ := existsUnique_transitiveGroupLabel_five G
    have hjk : j = k := by
      have h2 : Nat.card (referenceSubgroup 5 j) = Nat.card (referenceSubgroup 5 k) :=
        h.symm.trans hk.natCard_eq
      obtain ⟨a, ha⟩ := j
      obtain ⟨b, hb⟩ := k
      rw [numTransitiveGroups_five] at ha hb
      interval_cases a <;> interval_cases b <;> first
        | rfl
        | simp only [natCard_referenceSubgroup_five_zero, natCard_referenceSubgroup_five_one,
            natCard_referenceSubgroup_five_two, natCard_referenceSubgroup_five_three,
            natCard_referenceSubgroup_five_four] at h2
          omega
    rw [hjk]
    exact hk⟩

/-- **`4T1` is recognized by its order and cyclicity.** A transitive subgroup of `S₄` is
labelled `4T1` exactly when it has order four and is cyclic. The hypothesis `IsCyclic G` cannot
be dropped: `4T2` also has order four. -/
theorem transitiveGroupLabel_four_zero_iff (G : Subgroup (Perm (Fin 4)))
    [IsPretransitive G (Fin 4)] :
    TransitiveGroupLabel (⟨0, by simp⟩ : TransitiveGroupIndex 4) G ↔
      (Nat.card G = 4 ∧ IsCyclic G) := by
  constructor
  · intro h
    exact ⟨by rw [h.natCard_eq, natCard_referenceSubgroup_four_zero],
      h.isCyclic_iff.mpr isCyclic_referenceSubgroup_four_zero⟩
  · rintro ⟨hcard, hcyc⟩
    obtain ⟨k, hk, -⟩ := existsUnique_transitiveGroupLabel_four G
    have hcards : Nat.card (referenceSubgroup 4 k) = 4 := by rw [← hk.natCard_eq, hcard]
    obtain ⟨b, hb⟩ := k
    rw [numTransitiveGroups_four] at hb
    interval_cases b
    · exact hk
    · exact absurd (hk.isCyclic_iff.mp hcyc) not_isCyclic_referenceSubgroup_four_one
    · simp only [natCard_referenceSubgroup_four_two] at hcards
      omega
    · simp only [natCard_referenceSubgroup_four_three] at hcards
      omega
    · simp only [natCard_referenceSubgroup_four_four] at hcards
      omega

/-- **`4T2` is recognized by its order and non-cyclicity.** A transitive subgroup of `S₄` is
labelled `4T2` exactly when it has order four and is not cyclic, that is, exactly when it is a
Klein four-group up to conjugacy. -/
theorem transitiveGroupLabel_four_one_iff (G : Subgroup (Perm (Fin 4)))
    [IsPretransitive G (Fin 4)] :
    TransitiveGroupLabel (⟨1, by simp⟩ : TransitiveGroupIndex 4) G ↔
      (Nat.card G = 4 ∧ ¬ IsCyclic G) := by
  constructor
  · intro h
    exact ⟨by rw [h.natCard_eq, natCard_referenceSubgroup_four_one],
      fun hc => not_isCyclic_referenceSubgroup_four_one (h.isCyclic_iff.mp hc)⟩
  · rintro ⟨hcard, hcyc⟩
    obtain ⟨k, hk, -⟩ := existsUnique_transitiveGroupLabel_four G
    have hcards : Nat.card (referenceSubgroup 4 k) = 4 := by rw [← hk.natCard_eq, hcard]
    obtain ⟨b, hb⟩ := k
    rw [numTransitiveGroups_four] at hb
    interval_cases b
    · exact (hcyc (hk.isCyclic_iff.mpr isCyclic_referenceSubgroup_four_zero)).elim
    · exact hk
    · simp only [natCard_referenceSubgroup_four_two] at hcards
      omega
    · simp only [natCard_referenceSubgroup_four_three] at hcards
      omega
    · simp only [natCard_referenceSubgroup_four_four] at hcards
      omega

/-- **Order recognition in degree four away from order four.** A transitive subgroup of `S₄` is
labelled `4Tj`, `2 ≤ j`, exactly when its order is that of `4Tj`: the orders `8, 12, 24` of
`4T3`, `4T4` and `4T5` are pairwise distinct and differ from the order four of `4T1` and `4T2`. -/
theorem transitiveGroupLabel_four_iff_natCard_eq_of_two_le (j : TransitiveGroupIndex 4)
    (hj : 2 ≤ (j : ℕ)) (G : Subgroup (Perm (Fin 4))) [IsPretransitive G (Fin 4)] :
    TransitiveGroupLabel j G ↔ Nat.card G = Nat.card (referenceSubgroup 4 j) :=
  ⟨fun h => h.natCard_eq, fun h => by
    obtain ⟨k, hk, -⟩ := existsUnique_transitiveGroupLabel_four G
    have hjk : j = k := by
      have h2 : Nat.card (referenceSubgroup 4 j) = Nat.card (referenceSubgroup 4 k) :=
        h.symm.trans hk.natCard_eq
      obtain ⟨a, ha⟩ := j
      obtain ⟨b, hb⟩ := k
      rw [numTransitiveGroups_four] at ha hb
      have hj' : 2 ≤ a := by simpa using hj
      have hval : a = b := by
        interval_cases a <;> interval_cases b <;> first
          | rfl
          | simp only [natCard_referenceSubgroup_four_zero, natCard_referenceSubgroup_four_one,
              natCard_referenceSubgroup_four_two, natCard_referenceSubgroup_four_three,
              natCard_referenceSubgroup_four_four] at h2
            omega
      subst hval
      rfl
    rw [hjk]
    exact hk⟩

end TauCeti
