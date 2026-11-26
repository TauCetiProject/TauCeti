/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.FreeGroup.GenEq.Basic

/-!
# Items and words in the coordinate group of a generalised equation

Let `Ω` be a generalised equation over `F(A)` with coordinate group `F_{R(Ω)}`. We record the
image of an item in `F_{R(Ω)}` (`TauCeti.GenEq.item`, a coordinate of the generic point of `Ω*`)
and the value in `F_{R(Ω)}` of a word in the items and the letters of `A`
(`TauCeti.GenEq.wordElem`). Under the homomorphism `F_{R(Ω)} → F(A)` of a solution, the value of
a word goes to the element of `F(A)` represented by the word obtained by substituting the words of
the solution for the items (`TauCeti.GenEq.Solution.toHom_wordElem`). Solutions move between
generalised equations through `F(A)`-homomorphisms of coordinate groups
(`TauCeti.GenEq.CoordHom`).

## Main definitions

* `TauCeti.GenEq.CoordHom`: `F(A)`-homomorphisms between coordinate groups.
* `TauCeti.GenEq.item`, `TauCeti.GenEq.wordElem`: an item, and the value of a word in the items
  and the letters, in the coordinate group.

## Main results

* `TauCeti.GenEq.Solution.toHom_wordElem`: the homomorphism of a solution evaluates the value of
  a word by substituting the words of the solution for the items.

## References

* O. Kharlampovich, A. Myasnikov, *Implicit function theorem over free groups*, J. Algebra 290
  (2005), §2.4 (coordinate groups).
-/

public section

namespace TauCeti

namespace GenEq

open GroupAlgGeom Monoid.Coprod

variable {A : Type*}

/-- `F(A)`-homomorphisms from the coordinate group of `Ω` to that of `Ω'`. -/
abbrev CoordHom (Ω Ω' : GenEq A) : Type _ :=
  GHom (CoordGroup.coeff (MonoidHom.id (FreeGroup A)) Ω.toSystem)
    (CoordGroup.coeff (MonoidHom.id (FreeGroup A)) Ω'.toSystem)

variable (Ω : GenEq A)

/-- The image of an item in the coordinate group: the coordinate of the generic point of `Ω*`
at that item. -/
abbrev item (k : Fin Ω.numItems) : Ω.coordGroup :=
  CoordGroup.genericPoint (MonoidHom.id (FreeGroup A)) Ω.toSystem k

/-- The value in the coordinate group of a word in the items and the letters of `A`. -/
def wordElem (w : List ((Fin Ω.numItems ⊕ A) × Bool)) : Ω.coordGroup :=
  ((EqIneqSystem.toGX (Fin Ω.numItems) FreeGroup.of (FreeGroup.mk w) :
    GX (FreeGroup A) (Fin Ω.numItems)) : Ω.coordGroup)

@[simp]
theorem wordElem_nil : Ω.wordElem [] = 1 := by
  simp [wordElem, ← FreeGroup.one_eq_mk]

@[simp]
theorem wordElem_append (w₁ w₂ : List ((Fin Ω.numItems ⊕ A) × Bool)) :
    Ω.wordElem (w₁ ++ w₂) = Ω.wordElem w₁ * Ω.wordElem w₂ := by
  simp [wordElem, ← FreeGroup.mul_mk]

/-- The value of a word `x :: w` is the value of its first letter times the value of `w`. This is
not a `simp` lemma: since `[x]` is `x :: []`, its right-hand side contains an instance of its
left-hand side, so `simp` would loop on it. -/
theorem wordElem_cons (x : (Fin Ω.numItems ⊕ A) × Bool) (w : List ((Fin Ω.numItems ⊕ A) × Bool)) :
    Ω.wordElem (x :: w) = Ω.wordElem [x] * Ω.wordElem w := by
  rw [← List.singleton_append, wordElem_append]

@[simp]
theorem wordElem_singleton_inl (k : Fin Ω.numItems) :
    Ω.wordElem [(Sum.inl k, true)] = Ω.item k :=
  (congrArg ((↑) : GX (FreeGroup A) (Fin Ω.numItems) → Ω.coordGroup)
    (EqIneqSystem.toGX_of_inl FreeGroup.of k)).trans (CoordGroup.genericPoint_apply _ k).symm

@[simp]
theorem wordElem_singleton_inr (a : A) : Ω.wordElem [(Sum.inr a, true)] =
    CoordGroup.coeff (MonoidHom.id (FreeGroup A)) Ω.toSystem (FreeGroup.of a) :=
  (congrArg ((↑) : GX (FreeGroup A) (Fin Ω.numItems) → Ω.coordGroup)
    (EqIneqSystem.toGX_of_inr FreeGroup.of a)).trans (CoordGroup.coeff_apply _ _).symm

@[simp]
theorem wordElem_singleton_false (x : Fin Ω.numItems ⊕ A) :
    Ω.wordElem [(x, false)] = (Ω.wordElem [(x, true)])⁻¹ := by
  rw [wordElem, wordElem, ← QuotientGroup.mk_inv, ← map_inv, FreeGroup.inv_mk]
  simp [FreeGroup.invRev]

namespace Solution

variable {Ω} (U : Ω.Solution)

@[simp]
theorem toHom_item (k : Fin Ω.numItems) : U.toHom (Ω.item k) = FreeGroup.mk (U.word k) := by
  rw [item, CoordGroup.genericPoint_apply, U.toHom_inr_of]

/-- The homomorphism of a solution sends the image of a word to the element of `F(A)` represented
by the word obtained by substituting the words of the solution for the items. -/
@[simp]
theorem toHom_wordElem (w : List ((Fin Ω.numItems ⊕ A) × Bool)) :
    U.toHom (Ω.wordElem w) = FreeGroup.mk (FreeGroup.substituteVars U.word w) := by
  simp [wordElem]

end Solution

end GenEq

end TauCeti
