/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# An executable search for a primitive root of unity modulo `p`

Mathlib proves that `ZMod p` contains a primitive `k`-th root of unity when `p` is prime and
`k ∣ p - 1`, but the witness comes from the cyclicity of the unit group and cannot be evaluated.
An algorithm that works modulo `p` with a root of unity needs one it can compute. This file supplies
`TauCeti.ZMod.primitiveRoot?`, which tests the residues `0, 1, …, p - 1` in turn and returns the
first one that is a primitive `k`-th root of unity, together with the proof that it is one.

The test is the finite criterion of `IsPrimitiveRoot.mk_of_lt`: `0 < k`, `ζ ^ k = 1` and
`ζ ^ l ≠ 1` for `0 < l < k`. It is decidable in `ZMod p`, so the search runs, and since every
residue is tested, for `p ≠ 0` and `k ≠ 0` the search fails only when there is nothing to find
(`TauCeti.ZMod.isSome_primitiveRoot?_iff`). The criterion deliberately excludes order zero, so the
search always fails for `k = 0`, even though `0 : ZMod p` is a primitive `0`-th root of unity when
`p ≠ 1`.

## Main definitions

* `TauCeti.ZMod.primitiveRoot?`: for `p ≠ 0` and `k ≠ 0`, the least residue modulo `p` that is a
  primitive `k`-th root of unity, if there is one; always `none` when `k = 0`.

## Main results

* `TauCeti.ZMod.isSome_primitiveRoot?_iff`: the search succeeds exactly when `ZMod p` has a
  primitive `k`-th root of unity, for `p` and `k` nonzero.
* `TauCeti.ZMod.map_val_primitiveRoot?_eq_some_iff`: the search returns the least residue passing
  the criterion, a decidable description of its value.
-/

public section

namespace TauCeti

namespace ZMod

/-- **An executable search for a primitive `k`-th root of unity in `ZMod p`.** The residues
`0, 1, …, p - 1` are tested in increasing order against the criterion `ζ ^ k = 1` and `ζ ^ l ≠ 1`
for `0 < l < k`, and the first one that passes is returned with the proof that it is a primitive
root. The result is `none` when no residue passes, in particular when `k = 0`. -/
def primitiveRoot? (p k : ℕ) : Option {ζ : ZMod p // IsPrimitiveRoot ζ k} :=
  (List.range p).findSome? fun (a : ℕ) ↦
    if h : 0 < k ∧ (a : ZMod p) ^ k = 1 ∧ ∀ l < k, 0 < l → (a : ZMod p) ^ l ≠ 1 then
      some ⟨a, IsPrimitiveRoot.mk_of_lt _ h.1 h.2.1 fun l hl hlk ↦ h.2.2 l hlk hl⟩
    else none

/-- **The search finds a primitive root whenever there is one.** For `p` and `k` nonzero, the
search over all residues modulo `p` succeeds exactly when `ZMod p` contains a primitive `k`-th
root of unity. -/
theorem isSome_primitiveRoot?_iff {p k : ℕ} [NeZero p] (hk : k ≠ 0) :
    (primitiveRoot? p k).isSome ↔ ∃ ζ : ZMod p, IsPrimitiveRoot ζ k := by
  refine ⟨fun h ↦ ?_, fun ⟨ζ, hζ⟩ ↦ ?_⟩
  · obtain ⟨ζ, -⟩ := Option.isSome_iff_exists.mp h
    exact ⟨ζ.1, ζ.2⟩
  · rw [primitiveRoot?, List.findSome?_isSome_iff]
    refine ⟨ζ.val, List.mem_range.mpr (ζ.val_lt), ?_⟩
    have htest : 0 < k ∧ ((ζ.val : ℕ) : ZMod p) ^ k = 1 ∧
        ∀ l < k, 0 < l → ((ζ.val : ℕ) : ZMod p) ^ l ≠ 1 :=
      ⟨Nat.pos_of_ne_zero hk, by simpa using hζ.pow_eq_one,
        fun l hlk hl ↦ by simpa using hζ.pow_ne_one_of_pos_of_lt hl.ne' hlk⟩
    rw [dite_eq_left_of_eq_true (eq_true htest)]
    rfl

/-- **Which root the search returns.** The search returns `ζ` exactly when `ζ` passes the
criterion `ζ ^ k = 1` and `ζ ^ l ≠ 1` for `0 < l < k` and no smaller residue does; the condition
`ζ.val < p` only fails for `p = 0`, where there are no residues to test. Every condition is
decidable, so a concrete value of the search can be checked without unfolding it. -/
theorem map_val_primitiveRoot?_eq_some_iff {p k : ℕ} {ζ : ZMod p} :
    (primitiveRoot? p k).map Subtype.val = some ζ ↔
      ζ.val < p ∧ (0 < k ∧ ζ ^ k = 1 ∧ ∀ l < k, 0 < l → ζ ^ l ≠ 1) ∧
        ∀ a < ζ.val, ¬(0 < k ∧ (a : ZMod p) ^ k = 1 ∧ ∀ l < k, 0 < l → (a : ZMod p) ^ l ≠ 1) := by
  have hsearch : (primitiveRoot? p k).map Subtype.val =
      ((List.range p).find? fun a : ℕ ↦
        decide (0 < k ∧ (a : ZMod p) ^ k = 1 ∧ ∀ l < k, 0 < l → (a : ZMod p) ^ l ≠ 1)).map
        Nat.cast := by
    rw [primitiveRoot?, List.map_findSome?, List.find?_eq_findSome?_guard, List.map_findSome?]
    congr 1
    funext a
    simp only [Function.comp_apply, Option.guard, decide_eq_true_eq]
    split_ifs <;> simp_all
  rw [hsearch, Option.map_eq_some_iff]
  simp only [List.find?_range_eq_some, decide_eq_true_eq, List.mem_range, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not]
  constructor
  · rintro ⟨a, ⟨htest, hlt, hmin⟩, rfl⟩
    rw [ZMod.val_cast_of_lt hlt]
    exact ⟨hlt, htest, hmin⟩
  · rintro ⟨hlt, htest, hmin⟩
    have : NeZero p := ⟨by omega⟩
    exact ⟨ζ.val, ⟨by simpa using htest, hlt, hmin⟩, ZMod.natCast_zmod_val ζ⟩

end ZMod

end TauCeti
