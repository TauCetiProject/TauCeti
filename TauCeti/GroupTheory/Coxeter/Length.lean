/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.Coxeter.Length
import Mathlib.Data.Fintype.Lattice

/-!
# The parity and the functoriality of the length function of a Coxeter system

Let `cs : CoxeterSystem M W` be a Coxeter system. A simple reflection has length one, so it is not
the identity and has order exactly two (`CoxeterSystem.orderOf_simple`).

Left multiplication by a fixed simple reflection changes the length of an element by exactly one
(`CoxeterSystem.length_mul_mod_two`), so it flips the parity of the length. This file packages
that pairing as an explicit equivalence `CoxeterSystem.lengthParityEquiv` between the elements of
even length and the elements of odd length, and records its two immediate consequences: the two
parity classes are equinumerous, and a Coxeter group with at least one simple reflection has even
order. The same fact shows that an element of maximal length in a finite Coxeter group has every
simple reflection as a left descent.

Finally, the length function is transported along the two canonical constructions on Coxeter
systems, `CoxeterSystem.reindex` and `CoxeterSystem.map`: relabelling the simple reflections or
pushing the system through a group isomorphism leaves lengths unchanged. Both follow from the
fact that a homomorphism carrying simple reflections to simple reflections does not increase
length. These facts feed the Poincaré polynomial in `TauCeti/GroupTheory/Coxeter/Poincare.lean`.

## Main definitions

* `CoxeterSystem.lengthParityEquiv`: left multiplication by a simple reflection, as an
  equivalence between the even-length and the odd-length elements.

## Main results

* `CoxeterSystem.simple_ne_one` and `CoxeterSystem.orderOf_simple`: a simple reflection has
  order exactly two.
* `CoxeterSystem.natCard_length_even_eq_natCard_length_odd`: as many elements have even length
  as odd length, provided there is at least one simple reflection.
* `CoxeterSystem.even_natCard_of_nonempty_index`: hence a Coxeter group of positive rank has even
  order.
* `CoxeterSystem.exists_forall_isLeftDescent`: a finite Coxeter group has an element of which
  every simple reflection is a left descent.
* `CoxeterSystem.length_apply_le_of_map_simple`: a homomorphism carrying simple reflections to
  simple reflections does not increase length.
* `CoxeterSystem.wordProd_map`: a word for `CoxeterSystem.map` is the image of the word for the
  original system.
* `CoxeterSystem.length_reindex` and `CoxeterSystem.length_map`: the length function is unchanged
  by `CoxeterSystem.reindex` and by `CoxeterSystem.map`.

## References

* A. Björner and F. Brenti, *Combinatorics of Coxeter Groups*, Springer GTM 231 (2005),
  Section 1.4.
* J. E. Humphreys, *Reflection Groups and Coxeter Groups*, CUP (1990), Section 1.11.
-/

public section

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

/-! ### Simple reflections are involutions -/

/-- **A simple reflection is not the identity**: it has length one. -/
@[simp]
theorem simple_ne_one (i : B) : cs.simple i ≠ 1 := fun h => by
  simpa [h] using cs.length_simple i

/-- **Each simple reflection has order exactly two.** -/
@[simp]
theorem orderOf_simple (i : B) : orderOf (cs.simple i) = 2 :=
  orderOf_eq_prime (cs.simple_sq i) (cs.simple_ne_one i)

/-! ### Left multiplication by a simple reflection flips the parity of the length -/

/-- Multiplying on the left by a simple reflection changes the length by one, hence changes its
residue modulo two. -/
theorem length_simple_mul_mod_two (i : B) (w : W) :
    cs.length (cs.simple i * w) % 2 = (cs.length w + 1) % 2 := by
  rw [cs.length_mul_mod_two, cs.length_simple, Nat.add_comm]

/-- Left multiplication by a simple reflection turns an element of even length into one of odd
length, and only those. -/
@[simp]
theorem odd_length_simple_mul_iff (i : B) (w : W) :
    Odd (cs.length (cs.simple i * w)) ↔ Even (cs.length w) := by
  rw [Nat.odd_iff, Nat.even_iff, length_simple_mul_mod_two]
  omega

/-- Left multiplication by a simple reflection turns an element of odd length into one of even
length, and only those. -/
@[simp]
theorem even_length_simple_mul_iff (i : B) (w : W) :
    Even (cs.length (cs.simple i * w)) ↔ Odd (cs.length w) := by
  rw [Nat.even_iff, Nat.odd_iff, length_simple_mul_mod_two]
  omega

/-- **Left multiplication by a simple reflection matches the two parity classes.** It is an
involution of `W` exchanging the elements of even length with those of odd length. -/
def lengthParityEquiv (i : B) :
    {w : W // Even (cs.length w)} ≃ {w : W // Odd (cs.length w)} :=
  (Equiv.mulLeft (cs.simple i)).subtypeEquiv fun w => (cs.odd_length_simple_mul_iff i w).symm

/-- `lengthParityEquiv` is left multiplication by the simple reflection. -/
@[simp]
theorem lengthParityEquiv_apply_coe (i : B) (x : {w : W // Even (cs.length w)}) :
    (cs.lengthParityEquiv i x : W) = cs.simple i * (x : W) := (rfl)

/-- The inverse of `lengthParityEquiv` is again left multiplication by the simple reflection: the
simple reflection is its own inverse. -/
@[simp]
theorem lengthParityEquiv_symm_apply_coe (i : B) (x : {w : W // Odd (cs.length w)}) :
    ((cs.lengthParityEquiv i).symm x : W) = cs.simple i * (x : W) := by
  conv_rhs => rw [← (cs.lengthParityEquiv i).apply_symm_apply x, lengthParityEquiv_apply_coe,
    simple_mul_simple_cancel_left]

/-- **The two parity classes of a Coxeter group of positive rank are equinumerous**: there are as
many elements of even length as of odd length. No finiteness is needed, since the two classes are
matched by an explicit bijection. -/
theorem natCard_length_even_eq_natCard_length_odd [Nonempty B] :
    Nat.card {w : W // Even (cs.length w)} = Nat.card {w : W // Odd (cs.length w)} :=
  Nat.card_congr (cs.lengthParityEquiv (Classical.arbitrary B))

include cs in
/-- **A Coxeter group of positive rank has even order**: a simple reflection is an element of order
two, so two divides the order of the group. (For infinite `W` this reads `Even 0`, since
`Nat.card W = 0`; the content is the finite case.) -/
theorem even_natCard_of_nonempty_index [Nonempty B] : Even (Nat.card W) :=
  even_iff_two_dvd.mpr <|
    cs.orderOf_simple (Classical.arbitrary B) ▸ orderOf_dvd_natCard _

/-! ### An element with every simple reflection as a left descent -/

/-- **A finite Coxeter group has an element of which every simple reflection is a left descent.**
Any element of maximal length will do: left multiplication by a simple reflection changes the
length by one, so it cannot raise it. (There is exactly one such element, the longest element `w₀`,
but uniqueness is not proved here.) -/
theorem exists_forall_isLeftDescent [Finite W] : ∃ w : W, ∀ i, cs.IsLeftDescent w i := by
  obtain ⟨w, hw⟩ := Finite.exists_max cs.length
  refine ⟨w, fun i ↦ ?_⟩
  rcases cs.length_simple_mul w i with h | h
  · have := hw (cs.simple i * w)
    omega
  · exact cs.isLeftDescent_iff.mpr h

/-! ### Transport along a reindexing or a group isomorphism -/

section Transport

variable {B' H : Type*} [Group H] {M' : CoxeterMatrix B'}

/-- **Length does not increase along a homomorphism matching simple reflections**: if
`φ : W →* H` carries each simple reflection of `cs` to a simple reflection of `cs'`, then it
carries a word for `w` to a word of the same length for `φ w`. -/
theorem length_apply_le_of_map_simple (cs' : CoxeterSystem M' H) (φ : W →* H) (f : B → B')
    (hφ : ∀ i, φ (cs.simple i) = cs'.simple (f i)) (w : W) :
    cs'.length (φ w) ≤ cs.length w := by
  obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
  have hmap : φ (cs.wordProd ω) = cs'.wordProd (ω.map f) := by
    simp only [wordProd, map_list_prod, List.map_map]
    exact congrArg List.prod (List.map_congr_left fun i _ => hφ i)
  rw [hmap, hω.eq, ← List.length_map f]
  exact cs'.length_wordProd_le _

/-- Pushing a word through the isomorphism computes the corresponding word for the transported
Coxeter system. -/
@[simp]
theorem wordProd_map (e : W ≃* H) (ω : List B) :
    (cs.map e).wordProd ω = e (cs.wordProd ω) := by
  rw [wordProd, wordProd, map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun i _ => cs.map_simple e i)

/-- **The length function is unchanged by reindexing the simple reflections**: a bijection of the
indexing set carries words to words of the same length. -/
@[simp]
theorem length_reindex (e : B ≃ B') (w : W) : (cs.reindex e).length w = cs.length w :=
  le_antisymm (by simpa using cs.length_apply_le_of_map_simple (cs.reindex e) (.id W) e (by simp) w)
    (by simpa using (cs.reindex e).length_apply_le_of_map_simple cs (.id W) e.symm (by simp) w)

/-- **The length function is transported by a group isomorphism**: an isomorphism `e : W ≃* H`
matches the simple reflections of `cs` with those of `cs.map e`, hence their lengths. -/
@[simp]
theorem length_map (e : W ≃* H) (w : W) : (cs.map e).length (e w) = cs.length w :=
  le_antisymm (by simpa using cs.length_apply_le_of_map_simple (cs.map e) e id (by simp) w)
    (by simpa using (cs.map e).length_apply_le_of_map_simple cs e.symm id (by simp) (e w))

end Transport

end CoxeterSystem
