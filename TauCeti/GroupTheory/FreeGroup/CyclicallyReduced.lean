/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import TauCeti.GroupTheory.FreeGroup.Reduce

/-!
# Cyclic reduction and word length in a free group

These lemmas bound the length of a cyclic reduction, relate cyclic reduction to the identity
and give the length of a positive power. Words of constant sign are cyclically reduced.
-/

public section

namespace FreeGroup

/-- A word all of whose letters have the same sign is cyclically reduced. -/
theorem isCyclicallyReduced_of_forall_snd_eq {α : Type*} {w : List (α × Bool)} {e : Bool}
    (h : ∀ x ∈ w, x.2 = e) : IsCyclicallyReduced w :=
  ⟨isReduced_of_forall_snd_eq h, fun x hx y hy _ ↦
    (h x (List.mem_of_getLast? hx)).trans (h y (List.mem_of_mem_head? hy)).symm⟩

variable {α : Type*} [DecidableEq α]

/-- Cyclic reduction does not lengthen a word. -/
@[to_additive]
theorem length_reduceCyclically_le (L : List (α × Bool)) :
    (reduceCyclically L).length ≤ L.length := by
  have h := congrArg List.length (reduceCyclically.conj_conjugator_reduceCyclically L)
  simp only [List.length_append] at h
  omega

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
