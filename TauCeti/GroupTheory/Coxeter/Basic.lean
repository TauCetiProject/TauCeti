/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coxeter.Basic

/-!
# Elementary facts about Coxeter words and systems

This file evaluates Mathlib's alternating words through an arbitrary family, specialises that
evaluation to the lengths the braid relations are read off at, computes the reversal of an
alternating word, and proves that involutions in a monoid satisfying the braid-word equations of a
Coxeter matrix are liftable (`CoxeterMatrix.isLiftable_of_mul_self_of_braidWord`). It also provides
elementary transport and rank-zero helpers for Coxeter matrices and Coxeter systems.

## Main definitions

* `CoxeterSystem.castMatrix`: transport a `CoxeterSystem M W` along an equality `M = M'` of Coxeter
  matrices on the same index type.

## Main results

* `TauCeti.prod_map_alternatingWord`: an alternating word of length `m`, evaluated through any
  family `f`. This is the shape in which a braid relation is checked against a family that is not
  yet known to satisfy it, so it cannot be routed through
  `CoxeterSystem.prod_alternatingWord_eq_mul_pow`, which evaluates only the simple reflections
  themselves. The evaluations at lengths `2` and `3` are special cases.
* `TauCeti.reverse_alternatingWord`: reversing an alternating word swaps its two letters when
  its length is even, and leaves it unchanged when its length is odd.
* `CoxeterMatrix.reindex_refl` and `CoxeterMatrix.reindex_reindex`: functoriality of
  `CoxeterMatrix.reindex`.
* `CoxeterMatrix.isLiftable_of_mul_self_of_braidWord` and
  `CoxeterMatrix.isLiftable_iff_mul_self_and_braidWord`: `M.IsLiftable f` is equivalent to each
  `f i` squaring to `1` together with the braid-word equations of `M`.
* `CoxeterSystem.castMatrix_simple` and `CoxeterSystem.wordProd_castMatrix`: `castMatrix` preserves
  simple reflections and word products.
* `CoxeterSystem.subsingleton_of_isEmpty`: a Coxeter system of rank zero has a trivial group.
* `CoxeterSystem.commute_simple_of_eq_two`: two simple reflections commute when their entry of the
  Coxeter matrix is `2`.
* `CoxeterSystem.isConj_wordProd_append_comm`: rotating a word `l₁ ++ l₂` to `l₂ ++ l₁` conjugates
  the element it spells.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter IV, §1.
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

variable {B B' B'' G : Type*}

/-- Reindexing a Coxeter matrix by the identity equivalence leaves it unchanged. -/
@[simp]
theorem reindex_refl (M : CoxeterMatrix B) : M.reindex (Equiv.refl B) = M := by
  ext
  rfl

/-- Reindexing a Coxeter matrix twice is reindexing by the composite equivalence. -/
@[simp]
theorem reindex_reindex (M : CoxeterMatrix B) (e : B ≃ B') (e' : B' ≃ B'') :
    (M.reindex e).reindex e' = M.reindex (e.trans e') := by
  ext
  rfl

/-- **Liftability from involutions and braid words.** A family `f : B → G` into a monoid satisfies
`M.IsLiftable f` whenever each `f i` squares to `1` and `f` satisfies the Artin--Tits braid-word
equations of `M`. -/
theorem isLiftable_of_mul_self_of_braidWord [Monoid G] (M : CoxeterMatrix B) {f : B → G}
    (hsq : ∀ i, f i * f i = 1)
    (hbraid : ∀ i i', ((CoxeterSystem.braidWord M i i').map f).prod =
      ((CoxeterSystem.braidWord M i' i).map f).prod) :
    M.IsLiftable f := by
  let u (i : B) : Gˣ := ⟨f i, f i, hsq i, hsq i⟩
  have hu_sq (i : B) : u i * u i = 1 := Units.ext (hsq i)
  have hu_inv (i : B) : (u i)⁻¹ = u i := rfl
  have hcoe (ω : List B) : (((ω.map u).prod : Gˣ) : G) = (ω.map f).prod := by
    induction ω with
    | nil => rfl
    | cons k ω ih => simp [u, ih]
  intro i i'
  have hb : ((CoxeterSystem.braidWord M i i').map u).prod =
      ((CoxeterSystem.braidWord M i' i).map u).prod :=
    Units.ext ((hcoe _).trans ((hbraid i i').trans (hcoe _).symm))
  have hrev : u i' * u i = (u i * u i')⁻¹ := by rw [mul_inv_rev, hu_inv, hu_inv]
  rw [CoxeterSystem.braidWord, CoxeterSystem.braidWord, M.symmetric i' i,
    TauCeti.prod_map_alternatingWord, TauCeti.prod_map_alternatingWord, hrev, inv_pow] at hb
  have hmul : (if Even (M i i') then 1 else u i') * (u i * u i') ^ (2 * (M i i' / 2)) =
      if Even (M i i') then 1 else u i := by
    have h := congrArg (· * (u i * u i') ^ (M i i' / 2)) hb
    rwa [mul_assoc, ← pow_add, ← two_mul, mul_assoc, inv_mul_cancel, mul_one] at h
  have hu_pow : (u i * u i') ^ M i i' = 1 := by
    by_cases hm : Even (M i i')
    · simpa only [hm, ↓reduceIte, one_mul, Nat.two_mul_div_two_of_even hm] using hmul
    · have hodd : 2 * (M i i' / 2) + 1 = M i i' := by
        have := Nat.not_even_iff.mp hm
        omega
      have h' := congrArg (u i * ·) hmul
      simp only [hm, ↓reduceIte, hu_sq] at h'
      rwa [← mul_assoc, ← pow_succ', hodd] at h'
  simpa [u] using congrArg Units.val hu_pow

/-- A family `f : B → G` into a monoid is liftable along `M` if and only if each `f i` squares to
`1` and `f` satisfies the braid-word equations of `M`. -/
theorem isLiftable_iff_mul_self_and_braidWord [Monoid G] (M : CoxeterMatrix B) {f : B → G} :
    M.IsLiftable f ↔
      (∀ i, f i * f i = 1) ∧
        ∀ i i', ((CoxeterSystem.braidWord M i i').map f).prod =
          ((CoxeterSystem.braidWord M i' i).map f).prod := by
  refine ⟨fun hf => ⟨fun i => by simpa using hf i i, fun i i' => ?_⟩,
    fun ⟨hsq, hbraid⟩ => M.isLiftable_of_mul_self_of_braidWord hsq hbraid⟩
  let φ : M.Group →* G := M.toCoxeterSystem.lift ⟨f, hf⟩
  have hword (ω : List B) : (ω.map f).prod = φ (M.toCoxeterSystem.wordProd ω) := by
    induction ω with
    | nil => simp
    | cons k ω ih =>
      rw [List.map_cons, List.prod_cons, CoxeterSystem.wordProd_cons, map_mul,
        M.toCoxeterSystem.lift_apply_simple hf k, ih]
  rw [hword, hword, M.toCoxeterSystem.wordProd_braidWord_eq]

end CoxeterMatrix

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-- Transport a `CoxeterSystem` along an equality of Coxeter matrices on the same index type. -/
protected def castMatrix {M' : CoxeterMatrix B} (h : M = M') : CoxeterSystem M' W :=
  h ▸ cs

/-- `CoxeterSystem.castMatrix` leaves every simple reflection unchanged. -/
@[simp]
theorem castMatrix_simple {M' : CoxeterMatrix B} (h : M = M') (i : B) :
    (cs.castMatrix h).simple i = cs.simple i := by
  subst h
  rfl

/-- `CoxeterSystem.castMatrix` leaves every word product unchanged. -/
@[simp]
theorem wordProd_castMatrix {M' : CoxeterMatrix B} (h : M = M') (ω : List B) :
    (cs.castMatrix h).wordProd ω = cs.wordProd ω := by
  subst h
  rfl

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
