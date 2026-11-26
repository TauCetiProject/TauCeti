/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Perm.TransitiveGroupLabel.Classification

/-!
# Parity of the transitive groups of degree at most five

The reference groups consisting entirely of even permutations are exactly `1T1`, `3T1`,
`4T2`, `4T4`, `5T1`, `5T2`, and `5T4`. The theorem
`TauCeti.referenceSubgroup_le_alternatingGroup_iff` gives this complete list, using zero-based
label indices. Its counterpart for `TauCeti.TransitiveGroupLabel` reads the same list for any
labelled subgroup, since parity is invariant under conjugation.

Together with the discriminant test, this list determines which polynomial labels have square
discriminant away from characteristic two.

## References

* LMFDB, *Galois group labels*, <https://www.lmfdb.org/GaloisGroup/>.
-/

public section

namespace TauCeti

open Equiv Equiv.Perm

/-- **The parity column of the transitive groups of degree at most five.** In degree at most
five, the reference subgroup consists of even permutations exactly for the labels `1T1`, `3T1`,
`4T2`, `4T4`, `5T1`, `5T2`, and `5T4`. The label index is zero-based. -/
@[simp]
theorem referenceSubgroup_le_alternatingGroup_iff :
    ∀ {n : ℕ} (_ : n ≤ 5) (j : TransitiveGroupIndex n),
      referenceSubgroup n j ≤ alternatingGroup (Fin n) ↔
        n = 1 ∨ (n = 3 ∧ (j : ℕ) = 0) ∨
          (n = 4 ∧ ((j : ℕ) = 1 ∨ (j : ℕ) = 3)) ∨
          (n = 5 ∧ ((j : ℕ) = 0 ∨ (j : ℕ) = 1 ∨ (j : ℕ) = 3))
  | 0, _, j => (lt_irrefl 0 (pos_of_transitiveGroupIndex j)).elim
  | 1, _, j => by
    refine iff_of_true ?_ (by simp)
    intro σ _
    have hσ : σ = 1 := Subsingleton.elim _ _
    simp [hσ]
  | 2, _, j => by
    refine iff_of_false ?_ (by simp)
    rw [referenceSubgroup_two]
    intro h
    have hswap := h (Subgroup.mem_top (swap (0 : Fin 2) 1))
    simp [mem_alternatingGroup] at hswap
  | 3, _, j => by
    obtain ⟨j, hj⟩ := j
    rw [numTransitiveGroups_three] at hj
    interval_cases j
    · exact iff_of_true referenceSubgroup_three_zero_le_alternatingGroup (by simp)
    · exact iff_of_false not_referenceSubgroup_three_one_le_alternatingGroup (by simp)
  | 4, _, j => (referenceSubgroup_four_le_alternatingGroup_iff j).trans (by simp)
  | 5, _, j => (referenceSubgroup_five_le_alternatingGroup_iff j).trans (by simp)
  | _ + 6, hn, _ => by omega

/-- A labelled subgroup of degree at most five consists of even permutations exactly for the
labels `1T1`, `3T1`, `4T2`, `4T4`, `5T1`, `5T2`, and `5T4`. -/
theorem TransitiveGroupLabel.le_alternatingGroup_iff_label {n : ℕ} (hn : n ≤ 5)
    {j : TransitiveGroupIndex n} {G : Subgroup (Perm (Fin n))}
    (h : TransitiveGroupLabel j G) :
    G ≤ alternatingGroup (Fin n) ↔
      n = 1 ∨ (n = 3 ∧ (j : ℕ) = 0) ∨
        (n = 4 ∧ ((j : ℕ) = 1 ∨ (j : ℕ) = 3)) ∨
        (n = 5 ∧ ((j : ℕ) = 0 ∨ (j : ℕ) = 1 ∨ (j : ℕ) = 3)) := by
  rw [h.le_alternatingGroup_iff, referenceSubgroup_le_alternatingGroup_iff hn]

end TauCeti
