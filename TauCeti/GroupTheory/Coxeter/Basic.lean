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
alternating word. It splits the Coxeter relations into involutions and braid relations, and it
also records the degenerate rank-zero case: a Coxeter system whose simple reflections are indexed
by an empty type has a trivial group.

## Main results

* `TauCeti.prod_map_alternatingWord`: an alternating word of length `m`, evaluated through any
  family `f`. This is the shape in which a braid relation is checked against a family that is not
  yet known to satisfy it, so it cannot be routed through
  `CoxeterSystem.prod_alternatingWord_eq_mul_pow`, which evaluates only the simple reflections
  themselves. The evaluations at lengths `2` and `3` are special cases.
* `TauCeti.reverse_alternatingWord`: reversing an alternating word swaps its two letters when
  its length is even, and leaves it unchanged when its length is odd.
* `CoxeterMatrix.isLiftable_iff`: a family satisfies the Coxeter relations exactly when it
  consists of involutions satisfying the braid relations.
* `CoxeterSystem.subsingleton_of_isEmpty`: a Coxeter system of rank zero has a trivial group.
* `CoxeterSystem.commute_simple_of_eq_two`: two simple reflections commute when their entry of the
  Coxeter matrix is `2`.
* `CoxeterSystem.isConj_wordProd_append_comm`: rotating a word `l₁ ++ l₂` to `l₂ ++ l₁` conjugates
  the element it spells.
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

namespace CoxeterMatrix

variable {B G : Type*} (M : CoxeterMatrix B)

/-- In a group, involutions satisfying the braid relations of `M` satisfy its Coxeter relations. -/
private theorem isLiftable_of_braidWord [Group G] {f : B → G} (hsq : ∀ i, f i * f i = 1)
    (hbraid : ∀ i i', ((CoxeterSystem.braidWord M i i').map f).prod =
      ((CoxeterSystem.braidWord M i' i).map f).prod) :
    M.IsLiftable f := by
  intro i i'
  have h := hbraid i i'
  rw [CoxeterSystem.braidWord, CoxeterSystem.braidWord, M.symmetric i' i,
    TauCeti.prod_map_alternatingWord, TauCeti.prod_map_alternatingWord] at h
  -- With `a = f i` and `b = f i'` involutions, `b * a` is the inverse of `x = a * b`.
  have hinv : f i' * f i = (f i * f i')⁻¹ := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right (hsq i), inv_eq_of_mul_eq_one_right (hsq i')]
  rw [hinv, inv_pow] at h
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' (M i i')
  · -- `x ^ k = x⁻ᵏ`, so `x ^ (2 * k) = 1`.
    have hk2 : 2 * k / 2 = k := by omega
    simp only [hk, even_two_mul, ite_true, one_mul, hk2] at h
    rw [hk, pow_mul', pow_two, mul_eq_one_iff_eq_inv]
    exact h
  · -- `b * x ^ k = a * x⁻ᵏ`, so `x ^ (k + 1) = x⁻ᵏ` and `x ^ (2 * k + 1) = 1`.
    have hk2 : (2 * k + 1) / 2 = k := by omega
    have hodd : ¬ Even (2 * k + 1) := by simp [parity_simps]
    simp only [hk, hodd, ite_false, hk2] at h
    calc (f i * f i') ^ M i i' = f i * (f i' * (f i * f i') ^ k) * (f i * f i') ^ k := by
          rw [hk, pow_succ', two_mul, pow_add]
          simp only [mul_assoc]
      _ = 1 := by rw [h, ← mul_assoc (f i), hsq i, one_mul, inv_mul_cancel]

/-- **The Coxeter relations are involutions plus braid relations.** A family `f` of elements of a
monoid satisfies the Coxeter relations `(f i * f i') ^ M i i' = 1` of `M` exactly when every `f i`
is an involution and the family satisfies the braid relations of `M`, the equalities of the two
alternating words of length `M i i'`. So a Coxeter group with matrix `M` is the quotient of the
Artin-Tits group of `M` by the squares of its generators. -/
theorem isLiftable_iff [Monoid G] {f : B → G} :
    M.IsLiftable f ↔ (∀ i, f i * f i = 1) ∧
      ∀ i i', ((CoxeterSystem.braidWord M i i').map f).prod =
        ((CoxeterSystem.braidWord M i' i).map f).prod := by
  constructor
  · intro hf
    refine ⟨fun i ↦ by simpa [M.diagonal] using hf i i, fun i i' ↦ ?_⟩
    have h := congrArg (M.toCoxeterSystem.lift ⟨f, hf⟩)
      (M.toCoxeterSystem.wordProd_braidWord_eq i i')
    simpa only [CoxeterSystem.wordProd, map_list_prod, List.map_map, Function.comp_def,
      CoxeterSystem.lift_apply_simple] using h
  · -- Every `f i` is a unit; apply the group case in the units of `G`.
    rintro ⟨hsq, hbraid⟩ i i'
    let u : B → Gˣ := fun i ↦ ⟨f i, f i, hsq i, hsq i⟩
    have hu : ∀ l : List B, (((l.map u).prod : Gˣ) : G) = (l.map f).prod := fun l ↦ by
      rw [← Units.coeHom_apply, map_list_prod, List.map_map]
      simp [u, Function.comp_def]
    have h := isLiftable_of_braidWord M (f := u) (fun i ↦ Units.ext (hsq i))
      (fun i i' ↦ Units.ext (by rw [hu, hu, hbraid])) i i'
    simpa [u] using congrArg Units.val h

end CoxeterMatrix

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

/-- **Rotating a word conjugates the element it spells**: `l₁ ++ l₂` and `l₂ ++ l₁` spell
conjugate elements. -/
theorem isConj_wordProd_append_comm (l₁ l₂ : List B) :
    IsConj (cs.wordProd (l₁ ++ l₂)) (cs.wordProd (l₂ ++ l₁)) := by
  rw [wordProd_append, wordProd_append]
  exact isConj_iff.mpr ⟨(cs.wordProd l₁)⁻¹, by simp⟩

end CoxeterSystem
