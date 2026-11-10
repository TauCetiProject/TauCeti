/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coxeter.Basic

/-!
# Elementary facts about Coxeter words

This file evaluates Mathlib's alternating words through an arbitrary family, specialises that
evaluation to the lengths the braid relations are read off at, and computes the reversal of an
alternating word. It also records the degenerate rank-zero case: a Coxeter system whose simple
reflections are indexed by an empty type has a trivial group.

## Main results

* `TauCeti.prod_map_alternatingWord`: an alternating word of length `m`, evaluated through any
  family `f`. This is the shape in which a braid relation is checked against a family that is not
  yet known to satisfy it, so it cannot be routed through
  `CoxeterSystem.prod_alternatingWord_eq_mul_pow`, which evaluates only the simple reflections
  themselves. The evaluations at lengths `2` and `3` are special cases.
* `TauCeti.reverse_alternatingWord`: reversing an alternating word swaps its two letters when
  its length is even, and leaves it unchanged when its length is odd.
* `CoxeterSystem.subsingleton_of_isEmpty`: a Coxeter system of rank zero has a trivial group.
* `CoxeterSystem.commute_simple_of_eq_two`: two simple reflections commute when their entry of the
  Coxeter matrix is `2`.
-/

public section

namespace TauCeti

variable {B N : Type*} [Monoid N]

/-- An alternating word of length `m`, evaluated through any family `f`. Unlike
`CoxeterSystem.prod_alternatingWord_eq_mul_pow`, which evaluates the word at the simple reflections
of a Coxeter system, this holds for an arbitrary family, so it is available while checking that a
family satisfies the braid relations. -/
theorem prod_map_alternatingWord (f : B → N) (i i' : B) (m : ℕ) :
    ((CoxeterSystem.alternatingWord i i' m).map f).prod
      = (if Even m then 1 else f i') * (f i * f i') ^ (m / 2) := by
  induction m with
  | zero => simp [CoxeterSystem.alternatingWord]
  | succ m ih =>
    rw [CoxeterSystem.alternatingWord_succ', List.map_cons, List.prod_cons, ih]
    rcases Nat.even_or_odd' m with ⟨k, rfl | rfl⟩ <;>
      simp [parity_simps, ← pow_succ', ← mul_assoc, add_assoc, Nat.mul_add_div]

/-- An alternating word of length `2`, evaluated through any family `f`. -/
theorem prod_map_alternatingWord_two (f : B → N) (i i' : B) :
    ((CoxeterSystem.alternatingWord i i' 2).map f).prod = f i * f i' := by
  simp [prod_map_alternatingWord]

/-- An alternating word of length `3`, evaluated through any family `f`. -/
theorem prod_map_alternatingWord_three (f : B → N) (i i' : B) :
    ((CoxeterSystem.alternatingWord i i' 3).map f).prod = f i' * f i * f i' := by
  simp [prod_map_alternatingWord, Nat.even_iff, mul_assoc]

/-! ### Reversing alternating words -/

/-- Reversing an alternating word swaps its two letters when its length is even, and fixes it when
its length is odd (an odd alternating word is a palindrome). -/
theorem reverse_alternatingWord (i i' : B) (m : ℕ) :
    (CoxeterSystem.alternatingWord i i' m).reverse
      = if Even m then CoxeterSystem.alternatingWord i' i m
        else CoxeterSystem.alternatingWord i i' m := by
  induction m generalizing i i' with
  | zero => simp [CoxeterSystem.alternatingWord]
  | succ m ih =>
    conv_lhs => rw [CoxeterSystem.alternatingWord_succ, List.concat_eq_append,
      List.reverse_append, ih]
    by_cases hm : Even m <;> simp [hm, CoxeterSystem.alternatingWord_succ', parity_simps]

end TauCeti

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

include cs in
/-- A Coxeter system whose simple reflections are indexed by an empty type has a trivial group:
every element is the product of a word in the generators, and the only such word is empty. -/
theorem subsingleton_of_isEmpty [IsEmpty B] : Subsingleton W :=
  cs.wordProd_surjective.subsingleton

/-- Two simple reflections commute when their entry of the Coxeter matrix is `2`. -/
theorem commute_simple_of_eq_two {i i' : B} (h : M i i' = 2) :
    Commute (cs.simple i) (cs.simple i') := by
  simpa [h, pow_two, ← eq_inv_iff_mul_eq_one, commute_iff_eq] using cs.simple_mul_simple_pow i i'

end CoxeterSystem
