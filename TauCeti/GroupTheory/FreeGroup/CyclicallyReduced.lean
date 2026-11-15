/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.FreeGroup.CyclicallyReduced
public import TauCeti.GroupTheory.FreeGroup.Reduce
import TauCeti.Data.List.Infix

/-!
# Cyclic reduction and word length in a free group

These lemmas bound the length of a cyclic reduction, relate cyclic reduction to the identity
and give the length of a positive power. Words of constant sign are cyclically reduced, and being
cyclically reduced is decidable.

If the reduced word of `x ≠ 1` is `c ++ v ++ c⁻¹` with `v` cyclically reduced, then the reduced
word of `x ^ m` is `c ++ vᵐ ++ c⁻¹` for `m ≥ 1`. Its first `L` letters therefore do not depend on
`m ≥ L` (`FreeGroup.take_toWord_pow_of_le`): they are the first `L` letters of the attracting ray
`c ++ v ++ v ++ ⋯` of `x`.
-/

public section

namespace FreeGroup

/-- A word all of whose letters have the same sign is cyclically reduced. -/
theorem isCyclicallyReduced_of_forall_snd_eq {α : Type*} {w : List (α × Bool)} {e : Bool}
    (h : ∀ x ∈ w, x.2 = e) : IsCyclicallyReduced w :=
  ⟨isReduced_of_forall_snd_eq h, fun x hx y hy _ ↦
    (h x (List.mem_of_getLast? hx)).trans (h y (List.mem_of_mem_head? hy)).symm⟩

variable {α : Type*} [DecidableEq α]

/-- A word is cyclically reduced exactly when free reduction leaves it alone and its last letter
does not cancel against its first, and both halves of that are decidable. -/
instance instDecidableIsCyclicallyReduced (w : List (α × Bool)) :
    Decidable (IsCyclicallyReduced w) :=
  decidable_of_iff _ (and_congr_left' isReduced_iff_reduce_eq).symm

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

section Prefix

open reduceCyclically

/-- The word `c ++ vᵐ`, where `c ++ v ++ c⁻¹` is the reduced word of `x` with `v` cyclically
reduced. Its prefixes are the prefixes of the attracting ray of `x`. -/
private def ray (x : FreeGroup α) (m : ℕ) : List (α × Bool) :=
  conjugator x.toWord ++ (List.replicate m (reduceCyclically x.toWord)).flatten

private theorem le_length_ray {x : FreeGroup α} (hx : x ≠ 1) (m : ℕ) : m ≤ (ray x m).length := by
  simp only [ray, List.length_append, List.length_flatten, List.map_replicate,
    List.sum_replicate, smul_eq_mul]
  exact (Nat.le_mul_of_pos_right m (length_reduceCyclically_toWord_pos_iff.2 hx)).trans
    (Nat.le_add_left _ _)

/-- For `m ≥ L` and `m ≠ 0`, the reduced word of `x ^ m` begins with the first `L` letters of
`c ++ vᴸ`. -/
private theorem take_toWord_pow {x : FreeGroup α} (hx : x ≠ 1) {L m : ℕ} (hL : L ≤ m)
    (hm : m ≠ 0) : (x ^ m).toWord.take L = (ray x L).take L := by
  have hw : (x ^ m).toWord = ray x m ++ invRev (conjugator x.toWord) := by
    simp [ray, toWord_pow, reduce_flatten_replicate isReduced_toWord, hm]
  have hp : ray x L <+: ray x m :=
    (List.prefix_append_right_inj _).2 (List.flatten_replicate_prefix_flatten_replicate _ hL)
  rw [hw, List.take_append_of_le_length (hL.trans (le_length_ray hx m)), eq_comm,
    List.prefix_iff_eq_take.1 hp, List.take_take, Nat.min_eq_left (le_length_ray hx L)]

/-- The first `L` letters of the reduced word of `x ^ m` are the same for every `m ≥ L`: they are
the first `L` letters of the attracting ray of `x`. -/
theorem take_toWord_pow_of_le (x : FreeGroup α) {L m : ℕ} (h : L ≤ m) :
    (x ^ m).toWord.take L = (x ^ L).toWord.take L := by
  rcases eq_or_ne x 1 with rfl | hx
  · simp
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp
  rw [take_toWord_pow hx h (by omega), take_toWord_pow hx le_rfl (by omega)]

end Prefix

end FreeGroup
