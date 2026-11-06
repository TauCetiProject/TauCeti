/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced

/-!
# Cyclic reduction and word length in a free group

These lemmas relate cyclic reduction to the identity and give the length of a positive power.
A cyclically reduced word has no nontrivial conjugating prefix and suffix.
-/

public section

namespace FreeGroup

variable {α : Type*}

/-- A cyclically reduced word of the form `c ++ x ++ invRev c` has `c = []`: otherwise its first
and last letters would be inverse to each other. -/
@[to_additive]
theorem IsCyclicallyReduced.eq_nil_of_append_append_invRev {c x : List (α × Bool)}
    (h : IsCyclicallyReduced (c ++ x ++ invRev c)) : c = [] := by
  cases c with
  | nil => rfl
  | cons a t =>
    have hhead : a ∈ (a :: t ++ x ++ invRev (a :: t)).head? := by simp
    have hlast : (a.1, !a.2) ∈ (a :: t ++ x ++ invRev (a :: t)).getLast? := by
      rw [List.getLast?_append]
      simp [invRev]
    simpa using h.2 _ hlast _ hhead rfl

variable [DecidableEq α]

/-- A free-group element has empty cyclic reduction exactly when it is the identity. -/
@[to_additive (attr := simp)]
theorem reduceCyclically_toWord_eq_nil_iff {x : FreeGroup α} :
    reduceCyclically x.toWord = [] ↔ x = 1 := by
  constructor
  · intro h
    have hw := reduceCyclically.conj_conjugator_reduceCyclically x.toWord
    rw [h, List.append_nil] at hw
    have hm := congrArg mk hw
    simpa [← mul_mk, ← inv_mk, mk_toWord] using hm.symm
  · intro h
    subst x
    simp [toWord_one]

/-- A free-group element has nonempty cyclic reduction exactly when it is not the identity. -/
@[to_additive]
theorem length_reduceCyclically_toWord_pos_iff {x : FreeGroup α} :
    0 < (reduceCyclically x.toWord).length ↔ x ≠ 1 := by
  rw [List.length_pos_iff, Ne, reduceCyclically_toWord_eq_nil_iff]

/-- The reduced-word length of a positive power is the length of the conjugating
prefix twice, plus the exponent times the cyclically reduced length. -/
@[to_additive]
theorem norm_pow_eq (x : FreeGroup α) {n : ℕ} (hn : 0 < n) :
    norm (x ^ n) = 2 * (reduceCyclically.conjugator x.toWord).length +
      n * (reduceCyclically x.toWord).length := by
  have hn0 : n ≠ 0 := by omega
  simp [norm, toWord_pow,
    reduceCyclically.reduce_flatten_replicate isReduced_toWord, hn0,
    List.length_flatten, List.map_replicate]
  omega

end FreeGroup
