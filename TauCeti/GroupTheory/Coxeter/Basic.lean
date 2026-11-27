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
evaluation to the lengths the braid relations are read off at, and computes the reversal of an
alternating word. It splits the Coxeter relations into involutions and braid relations, and it
also provides elementary transport and rank-zero helpers for Coxeter systems: a Coxeter system
whose simple reflections are indexed by an empty type has a trivial group. Finally, it builds the
homomorphism of Coxeter groups induced by a map of index types along which the Coxeter matrices
agree.

## Main definitions

* `CoxeterSystem.castMatrix`: transport a `CoxeterSystem M W` along an equality `M = M'` of Coxeter
  matrices on the same index type.

## Main results

* `TauCeti.prod_map_alternatingWord`: an alternating word of length `m`, evaluated through any
  family `f`. This is the shape in which a braid relation is checked against a family that is not
  yet known to satisfy it, so it cannot be routed through
  `CoxeterSystem.prod_alternatingWord_eq_mul_pow`, which evaluates only the simple reflections
  themselves. The evaluations at lengths `2` and `3` are special cases.
* `TauCeti.commute_of_prod_map_braidWord` and `TauCeti.mul_mul_eq_of_prod_map_braidWord`: a
  family satisfying the braid relation at an entry `2` or `3` of the Coxeter matrix satisfies the
  commutation or the length-three braid relation.
* `TauCeti.prod_map_alternatingWord_eq_mul_pow`: for a family taking involutions at `i` and `i'`,
  the two alternating words of length `m` differ by the `m`-th power of `f i * f i'`.
* `TauCeti.pow_eq_one_of_prod_map_alternatingWord_eq`: two involutions satisfying a braid relation
  of length `m` have product of order dividing `m`.
* `TauCeti.reverse_alternatingWord`: reversing an alternating word swaps its two letters when
  its length is even, and leaves it unchanged when its length is odd.
* `CoxeterMatrix.isLiftable_iff`: a family satisfies the Coxeter relations exactly when it
  consists of involutions satisfying the braid relations.
* `CoxeterSystem.castMatrix_simple` and `CoxeterSystem.wordProd_castMatrix`: `castMatrix` preserves
  simple reflections and word products.
* `CoxeterSystem.subsingleton_of_isEmpty`: a Coxeter system of rank zero has a trivial group.
* `CoxeterSystem.commute_simple_of_eq_two`: two simple reflections commute when their entry of the
  Coxeter matrix is `2`.
* `CoxeterSystem.isConj_wordProd_append_comm`: rotating a word `l₁ ++ l₂` to `l₂ ++ l₁` conjugates
  the element it spells.
* `CoxeterSystem.parabolicHom`: the homomorphism `W →* W'` sending `s i` to `s' (f i)`, induced by
  a map `f` of index types along which the Coxeter matrices agree. It sends the product of a word to
  the product of its image (`CoxeterSystem.parabolicHom_wordProd`) and is functorial in `f`
  (`CoxeterSystem.parabolicHom_id`, `CoxeterSystem.parabolicHom_comp`); along a bijection it is the
  identity of a reindexed system (`CoxeterSystem.parabolicHom_reindex`) and the inverse of
  `CoxeterMatrix.reindexGroupEquiv` on the presented groups
  (`CoxeterMatrix.toCoxeterSystem_parabolicHom_reindex`). That it is injective and
  length-preserving is proved in `TauCeti/GroupTheory/Coxeter/Restriction.lean`.

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

/-- A family satisfying the braid relation of a Coxeter matrix `M` at an entry `M i j = 2` takes
commuting values at `i` and `j`. -/
theorem commute_of_prod_map_braidWord {M : CoxeterMatrix B} {f : B → N} {i j : B}
    (hf : ((CoxeterSystem.braidWord M i j).map f).prod =
      ((CoxeterSystem.braidWord M j i).map f).prod) (h : M i j = 2) :
    Commute (f i) (f j) := by
  rwa [CoxeterSystem.braidWord, h, CoxeterSystem.braidWord, M.symmetric j i, h,
    prod_map_alternatingWord_two, prod_map_alternatingWord_two] at hf

/-- A family satisfying the braid relation of a Coxeter matrix `M` at an entry `M i j = 3`
satisfies the length-three braid relation `f i * f j * f i = f j * f i * f j`. -/
theorem mul_mul_eq_of_prod_map_braidWord {M : CoxeterMatrix B} {f : B → N} {i j : B}
    (hf : ((CoxeterSystem.braidWord M i j).map f).prod =
      ((CoxeterSystem.braidWord M j i).map f).prod) (h : M i j = 3) :
    f i * f j * f i = f j * f i * f j := by
  rw [CoxeterSystem.braidWord, h, CoxeterSystem.braidWord, M.symmetric j i, h,
    prod_map_alternatingWord_three, prod_map_alternatingWord_three] at hf
  exact hf.symm

/-- **The two alternating words of length `m` differ by the `m`-th power of the rotation**, for
any family `f` taking involutions at `i` and `i'`: the word alternating between `i` and `i'` and
ending with `i'` evaluates to the word ending with `i` followed by `(f i * f i') ^ m`. -/
theorem prod_map_alternatingWord_eq_mul_pow {G : Type*} [Group G] (f : B → G) {i i' : B}
    (hi : f i * f i = 1) (hi' : f i' * f i' = 1) (m : ℕ) :
    ((CoxeterSystem.alternatingWord i i' m).map f).prod =
      ((CoxeterSystem.alternatingWord i' i m).map f).prod * (f i * f i') ^ m := by
  induction m generalizing i i' with
  | zero => simp [CoxeterSystem.alternatingWord]
  | succ m ih =>
    -- Conjugating by `f i'` carries the rotation `f i * f i'` to its inverse `f i' * f i`.
    have hsemi : SemiconjBy (f i') ((f i * f i') ^ m) ((f i' * f i) ^ m) :=
      SemiconjBy.pow_right (by simp only [SemiconjBy, mul_assoc]) m
    have hcancel (y : G) : f i * (f i * y) = y := by rw [← mul_assoc, hi, one_mul]
    simp only [CoxeterSystem.alternatingWord_succ, List.concat_eq_append, List.map_append,
      List.prod_append, List.map_singleton, List.prod_singleton, ih hi' hi, pow_succ', mul_assoc,
      hcancel, hsemi.eq]

/-- If `f i` and `f j` are involutions satisfying the braid relation of length `m`, then
`(f i * f j) ^ m = 1`. Thus a family of involutions satisfying the braid relations of a Coxeter
matrix satisfies its Coxeter relations. -/
theorem pow_eq_one_of_prod_map_alternatingWord_eq {G : Type*} [Group G] (f : B → G)
    {i j : B} (hi : f i * f i = 1) (hj : f j * f j = 1) (m : ℕ)
    (h : ((CoxeterSystem.alternatingWord i j m).map f).prod =
      ((CoxeterSystem.alternatingWord j i m).map f).prod) :
    (f i * f j) ^ m = 1 := by
  rwa [prod_map_alternatingWord_eq_mul_pow f hi hj, mul_eq_left] at h

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

/-! ### Homomorphisms induced by maps of index types -/

section ParabolicHom

variable {B' W' : Type*} [Group W'] {M' : CoxeterMatrix B'} (cs' : CoxeterSystem M' W')
  {f : B → B'}

/-- The homomorphism of Coxeter groups induced by a map `f : B → B'` of index types along which the
Coxeter matrices agree, `M i j = M' (f i) (f j)`: it sends `s i` to `s' (f i)`. It is injective
and length-preserving, with image the standard parabolic subgroup of `Set.range f`
(`CoxeterSystem.parabolicHom_injective`, `CoxeterSystem.length_parabolicHom` and
`CoxeterSystem.range_parabolicHom` in `TauCeti/GroupTheory/Coxeter/Restriction.lean`). -/
def parabolicHom (hf : ∀ i j, M i j = M' (f i) (f j)) : W →* W' :=
  cs.lift ⟨fun i ↦ cs'.simple (f i), fun i j ↦ by rw [hf]; exact cs'.simple_mul_simple_pow _ _⟩

variable {cs'} (hf : ∀ i j, M i j = M' (f i) (f j))

/-- The homomorphism `CoxeterSystem.parabolicHom` sends the simple reflection `s i` to
`s' (f i)`. -/
@[simp]
theorem parabolicHom_simple (i : B) : cs.parabolicHom cs' hf (cs.simple i) = cs'.simple (f i) :=
  cs.lift_apply_simple _ i

/-- The homomorphism `CoxeterSystem.parabolicHom` sends the product of a word to the product of its
image under `f`. -/
@[simp]
theorem parabolicHom_wordProd (ω : List B) :
    cs.parabolicHom cs' hf (cs.wordProd ω) = cs'.wordProd (ω.map f) := by
  induction ω with
  | nil => simp
  | cons i ω ih => simp [wordProd_cons, ih]

/-- **The identity of index types induces the identity of `W`.** -/
@[simp]
theorem parabolicHom_id (hid : ∀ i j, M i j = M (id i) (id j)) :
    cs.parabolicHom cs hid = MonoidHom.id W :=
  cs.ext_simple fun i ↦ parabolicHom_simple cs hid i

/-- **The homomorphisms `CoxeterSystem.parabolicHom` compose** along composites of maps of index
types: extending along `f` and then along `g` is extending along `g ∘ f`. -/
theorem parabolicHom_comp {B'' W'' : Type*} [Group W''] {M'' : CoxeterMatrix B''}
    {cs'' : CoxeterSystem M'' W''} {g : B' → B''} (hg : ∀ i j, M' i j = M'' (g i) (g j))
    (hgf : ∀ i j, M i j = M'' ((g ∘ f) i) ((g ∘ f) j)) :
    (cs'.parabolicHom cs'' hg).comp (cs.parabolicHom cs' hf) = cs.parabolicHom cs'' hgf :=
  cs.ext_simple fun i ↦ by simp

/-- **Reindexing a Coxeter system along `e` does not change the group**: the homomorphism of
`CoxeterSystem.parabolicHom` from `cs` to `cs.reindex e` along `e` is the identity of `W`. -/
@[simp]
theorem parabolicHom_reindex (e : B ≃ B') (he : ∀ i j, M i j = M.reindex e (e i) (e j)) :
    cs.parabolicHom (cs.reindex e) he = MonoidHom.id W :=
  cs.ext_simple fun i ↦ by simp

/-- On the presented Coxeter groups, the homomorphism of `CoxeterSystem.parabolicHom` along a
bijection `e` is the inverse of Mathlib's isomorphism `CoxeterMatrix.reindexGroupEquiv`. -/
@[simp]
theorem _root_.CoxeterMatrix.toCoxeterSystem_parabolicHom_reindex (M : CoxeterMatrix B)
    (e : B ≃ B') (he : ∀ i j, M i j = M.reindex e (e i) (e j)) :
    M.toCoxeterSystem.parabolicHom (M.reindex e).toCoxeterSystem he =
      (M.reindexGroupEquiv e).symm.toMonoidHom :=
  M.toCoxeterSystem.ext_simple fun i ↦ by
    rw [parabolicHom_simple]
    simp [CoxeterMatrix.reindexGroupEquiv_symm_apply_simple]

end ParabolicHom

end CoxeterSystem
