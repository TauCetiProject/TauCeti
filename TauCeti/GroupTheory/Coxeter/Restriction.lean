/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.ExchangeCondition
public import TauCeti.GroupTheory.Coxeter.Geometric
import Mathlib.Data.Set.List

/-!
# Standard parabolic subgroups are Coxeter groups

Let `cs : CoxeterSystem M W` and `cs' : CoxeterSystem M' W'` be Coxeter systems with simple
reflections indexed by `B` and `B'`, and let `f : B → B'` be a map along which the Coxeter matrices
agree, `M i j = M' (f i) (f j)`. Sending `s i` to `s' (f i)` respects the Coxeter relations of `M`,
so it defines a homomorphism `CoxeterSystem.parabolicHom cs cs' hf : W →* W'` onto the standard
parabolic subgroup `cs'.parabolic (Set.range f)`.

The main theorem is that this homomorphism is injective and preserves lengths. In other words, the
standard parabolic subgroup of `W'` attached to a set `J` of indices is the Coxeter group of the
restriction of `M'` to `J`, and its length function is the restriction of the length function of
`W'` (Bourbaki, Chapter IV, §1, no. 8, Theorem 2). For instance, the symmetric group on the first
`n` letters sits inside the group of finitary permutations of `ℕ` with the same lengths.

The proof applies the characterization of Coxeter systems by the exchange condition
(`CoxeterSystem.injective_of_exchange`): a reduced word in `W'` for an element of the parabolic
subgroup has all of its letters in `Set.range f`
(`CoxeterSystem.simple_mem_parabolic_of_isReduced` with `CoxeterSystem.simple_mem_parabolic_iff`),
so the length in `W'` is computed by words in `B`, and the exchange condition of `W'` then gives the
exchange condition for these words. The orders of the products of two generators are the entries
of the Coxeter matrix (`CoxeterSystem.orderOf_simple_mul_simple`).

## Main definitions

* `CoxeterSystem.parabolicHom`: the homomorphism `W →* W'` induced by a map of index types along
  which the Coxeter matrices agree.

## Main results

* `CoxeterSystem.simple_mem_parabolic_iff`: a simple reflection lies in the standard parabolic
  subgroup of `J` exactly when its index lies in `J`.
* `CoxeterSystem.parabolicHom_wordProd`: the homomorphism sends the product of a word to the
  product of its image.
* `CoxeterSystem.range_parabolicHom`: its image is the standard parabolic subgroup of
  `Set.range f`.
* `CoxeterSystem.length_parabolicHom`: **it preserves lengths.**
* `CoxeterSystem.parabolicHom_injective`: **it is injective.**
* `CoxeterSystem.isReduced_map_iff`: a word is reduced exactly when its image is.

## References

* N. Bourbaki, *Lie Groups and Lie Algebras, Chapters 4--6*, Chapter IV, §1, no. 8, Theorem 2.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, Cambridge Studies in Advanced
  Mathematics 29 (1990), Section 5.5.
-/

public section

namespace CoxeterSystem

variable {B B' W W' : Type*} [Group W] [Group W'] {M : CoxeterMatrix B} {M' : CoxeterMatrix B'}

/-- **A simple reflection lies in a standard parabolic subgroup exactly when its index lies in the
defining set.** -/
@[simp]
theorem simple_mem_parabolic_iff (cs : CoxeterSystem M W) {J : Set B} {i : B} :
    cs.simple i ∈ cs.parabolic J ↔ i ∈ J := by
  -- A reduced word for `s i` inside `cs.parabolic J` has a single letter `j ∈ J`, and distinct
  -- indices give distinct simple reflections.
  refine ⟨fun h ↦ ?_, cs.simple_mem_parabolic⟩
  obtain ⟨ω, hred, hωJ, hω⟩ := cs.exists_isReduced_wordProd_eq_of_mem_parabolic h
  have hlen : ω.length = 1 := by rw [← hred.eq, hω, length_simple]
  obtain ⟨j, rfl⟩ := List.length_eq_one_iff.mp hlen
  rw [wordProd_singleton] at hω
  exact cs.simple_injective hω ▸ hωJ j (List.mem_singleton_self j)

variable (cs : CoxeterSystem M W) (cs' : CoxeterSystem M' W') {f : B → B'}

/-- The homomorphism of Coxeter groups induced by a map `f : B → B'` of index types along which the
Coxeter matrices agree, `M i j = M' (f i) (f j)`: it sends `s i` to `s' (f i)`. It is injective
(`CoxeterSystem.parabolicHom_injective`) and length-preserving
(`CoxeterSystem.length_parabolicHom`), with image the standard parabolic subgroup of
`Set.range f` (`CoxeterSystem.range_parabolicHom`). -/
def parabolicHom (hf : ∀ i j, M i j = M' (f i) (f j)) : W →* W' :=
  cs.lift ⟨fun i ↦ cs'.simple (f i), fun i j ↦ by rw [hf]; exact cs'.simple_mul_simple_pow _ _⟩

variable {cs'} (hf : ∀ i j, M i j = M' (f i) (f j))

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

/-- The image of `CoxeterSystem.parabolicHom` is the standard parabolic subgroup of
`Set.range f`. -/
theorem range_parabolicHom :
    (cs.parabolicHom cs' hf).range = cs'.parabolic (Set.range f) := by
  ext w
  refine ⟨?_, fun hw ↦ ?_⟩
  · rintro ⟨v, rfl⟩
    obtain ⟨ω, rfl⟩ := cs.wordProd_surjective v
    rw [parabolicHom_wordProd]
    exact cs'.wordProd_mem_parabolic fun i hi ↦ by
      obtain ⟨j, -, rfl⟩ := List.mem_map.mp hi
      exact Set.mem_range_self j
  · obtain ⟨ω, hω, rfl⟩ := cs'.exists_wordProd_eq_of_mem_parabolic hw
    obtain ⟨τ, rfl⟩ : ω ∈ Set.range (List.map f) := by rwa [Set.range_list_map]
    exact ⟨cs.wordProd τ, parabolicHom_wordProd cs hf τ⟩

/-- The length in `W'` of the image of `w` is the least length of a word in `B` spelling it: a
reduced word for it in `W'` has all of its letters in `Set.range f`. -/
private theorem isLeast_length_parabolicHom (w : W) :
    IsLeast {n | ∃ ω : List B, cs.parabolicHom cs' hf (cs.wordProd ω) = cs.parabolicHom cs' hf w ∧
      ω.length = n} (cs'.length (cs.parabolicHom cs' hf w)) := by
  refine ⟨?_, ?_⟩
  · obtain ⟨σ, hσ, hσw⟩ := cs'.exists_isReduced (cs.parabolicHom cs' hf w)
    have hmem : cs'.wordProd σ ∈ cs'.parabolic (Set.range f) := by
      rw [← hσw, ← range_parabolicHom cs hf]
      exact ⟨w, rfl⟩
    obtain ⟨τ, rfl⟩ : σ ∈ Set.range (List.map f) := by
      rw [Set.range_list_map]
      exact fun i hi ↦
        cs'.simple_mem_parabolic_iff.mp (cs'.simple_mem_parabolic_of_isReduced σ hσ hmem i hi)
    refine ⟨τ, by rw [parabolicHom_wordProd, ← hσw], ?_⟩
    rw [hσw, hσ.eq, List.length_map]
  · rintro n ⟨ω, hω, rfl⟩
    rw [← hω, parabolicHom_wordProd]
    exact (cs'.length_wordProd_le _).trans_eq (List.length_map _)

/-- The exchange condition of `W'`, read on words in `B`: deleting a letter of a word in `B` that is
reduced in `W'` realizes right multiplication by a right descent. -/
private theorem exchange_parabolicHom (ω : List B) (i : B)
    (hlen : cs'.length (cs.parabolicHom cs' hf (cs.wordProd ω)) = ω.length)
    (hle : cs'.length (cs.parabolicHom cs' hf (cs.wordProd ω * cs.simple i)) ≤ ω.length) :
    ∃ j < ω.length, cs.parabolicHom cs' hf (cs.wordProd (ω.eraseIdx j)) =
      cs.parabolicHom cs' hf (cs.wordProd ω * cs.simple i) := by
  rw [parabolicHom_wordProd] at hlen
  rw [map_mul, parabolicHom_wordProd, parabolicHom_simple] at hle ⊢
  have hred : cs'.IsReduced (ω.map f) := by rw [IsReduced, hlen, List.length_map]
  have hdesc : cs'.IsRightDescent (cs'.wordProd (ω.map f)) (f i) := by
    rcases cs'.length_mul_simple (cs'.wordProd (ω.map f)) (f i) with h | h
    · omega
    · rw [IsRightDescent]
      omega
  obtain ⟨j, hj, hje, -⟩ := cs'.exchangeCondition_right hred hdesc
  refine ⟨j, by simpa using hj, ?_⟩
  rw [parabolicHom_wordProd, hje, List.eraseIdx_map]

/-- **The homomorphism `CoxeterSystem.parabolicHom` preserves lengths.** -/
@[simp]
theorem length_parabolicHom (w : W) : cs'.length (cs.parabolicHom cs' hf w) = cs.length w :=
  length_eq_of_exchange (cs := cs) _ cs'.length
    (fun i j ↦ by rw [parabolicHom_simple, parabolicHom_simple, orderOf_simple_mul_simple, hf])
    (isLeast_length_parabolicHom cs hf) (exchange_parabolicHom cs hf) w

/-- **The homomorphism `CoxeterSystem.parabolicHom` is injective**: the Coxeter relations of `M`
are the only relations among the simple reflections `s' (f i)` of `W'`. -/
theorem parabolicHom_injective : Function.Injective (cs.parabolicHom cs' hf) :=
  injective_of_exchange (cs := cs) _ cs'.length
    (fun i j ↦ by rw [parabolicHom_simple, parabolicHom_simple, orderOf_simple_mul_simple, hf])
    (isLeast_length_parabolicHom cs hf) (exchange_parabolicHom cs hf)

include hf in
/-- A word in `B` is reduced exactly when its image under `f` is reduced in `W'`. -/
theorem isReduced_map_iff {ω : List B} : cs'.IsReduced (ω.map f) ↔ cs.IsReduced ω := by
  rw [IsReduced, IsReduced, ← parabolicHom_wordProd cs hf, length_parabolicHom, List.length_map]

end CoxeterSystem
