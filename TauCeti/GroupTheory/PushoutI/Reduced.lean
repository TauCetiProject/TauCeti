/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.PushoutI

/-!
# Reduced words in an amalgamated product

Let `φ i : H →* G i` be a family of group homomorphisms, with amalgamated product
`Monoid.PushoutI φ`. A word of the free product of the `G i` is *reduced*
(`Monoid.PushoutI.Reduced`) when none of its letters lies in the amalgamated subgroup. Every element
of the amalgamated product is an element of the amalgamated subgroup times the product of a reduced
word: merging adjacent letters of the same factor and absorbing letters of the amalgamated subgroup
reduces any word. This is the existence part of the normal form theorem; unlike uniqueness, it does
not need the `φ i` to be injective.

## Main results

* `Monoid.PushoutI.exists_eq_base_mul_ofCoprodI_prod`: every element is `h * w` with `h` in the
  amalgamated subgroup and `w` the product of a reduced word.

## References

* J.-P. Serre, *Trees*, Chapter I, §1.2, Theorem 1 (the normal form theorem for amalgamated
  products).
-/

public section

namespace Monoid.PushoutI

open Function CoprodI

variable {ι : Type*} {G : ι → Type*} {H : Type*} [∀ i, Group (G i)] [Group H]
  {φ : ∀ i, H →* G i}

/-- Left multiplication by a letter `g : G i` preserves the products `h * w` of an element `h` of
the amalgamated subgroup and the product `w` of a reduced word. -/
private theorem exists_of_mul_base_mul_ofCoprodI_prod (i : ι) (g : G i) (h : H) {w : Word G}
    (hw : Reduced φ w) : ∃ (h' : H) (w' : Word G), Reduced φ w' ∧
      of i g * (base φ h * ofCoprodI w.prod) = base φ h' * ofCoprodI w'.prod := by
  classical
  -- Write `w` as its first letter in `G i` (possibly `1`) followed by a word not starting in `G i`.
  generalize hp : Word.equivPair i w = p
  have hwp : w.prod = CoprodI.of p.head * p.tail.prod := by
    rw [← hp, ← Word.prod_rcons, ← Word.equivPair_symm, Equiv.symm_apply_apply]
  have hgw : of i g * (base φ h * ofCoprodI w.prod) =
      of i (g * φ i h * p.head) * ofCoprodI p.tail.prod := by
    simp only [hwp, map_mul, ofCoprodI_of, ← of_apply_eq_base φ i, mul_assoc]
  have htail : Reduced φ p.tail := fun l hl => hw l (Word.mem_of_mem_equivPair_tail _ (hp ▸ hl))
  by_cases ha : g * φ i h * p.head ∈ (φ i).range
  · obtain ⟨h', hh'⟩ := ha
    exact ⟨h', p.tail, htail, by rw [hgw, ← hh', of_apply_eq_base]⟩
  have ha1 : g * φ i h * p.head ≠ 1 := fun h1 => ha (h1 ▸ one_mem _)
  refine ⟨1, .cons _ p.tail p.fstIdx_ne ha1, fun l hl => ?_, ?_⟩
  · rcases List.mem_cons.1 hl with rfl | hl
    exacts [ha, htail l hl]
  · rw [hgw, map_one, one_mul, Word.prod_cons, map_mul ofCoprodI, ofCoprodI_of]

/-- Every element of an amalgamated product of groups is the product of an element of the
amalgamated subgroup and the product of a reduced word: a word whose consecutive letters lie in
different factors and none of whose letters lies in the amalgamated subgroup. -/
theorem exists_eq_base_mul_ofCoprodI_prod (x : PushoutI φ) :
    ∃ (h : H) (w : Word G), Reduced φ w ∧ x = base φ h * ofCoprodI w.prod := by
  suffices ∀ y : PushoutI φ, (∃ (h : H) (w : Word G), Reduced φ w ∧
      y = base φ h * ofCoprodI w.prod) →
      ∃ (h : H) (w : Word G), Reduced φ w ∧ x * y = base φ h * ofCoprodI w.prod by
    simpa using this 1 ⟨1, .empty, by simp [Reduced], by simp⟩
  induction x using induction_on with
  | of i g =>
    rintro _ ⟨h, w, hw, rfl⟩
    exact exists_of_mul_base_mul_ofCoprodI_prod i g h hw
  | base h =>
    rintro _ ⟨h', w, hw, rfl⟩
    exact ⟨h * h', w, hw, by rw [map_mul, mul_assoc]⟩
  | mul x y hx hy =>
    intro z hz
    rw [mul_assoc]
    exact hx _ (hy z hz)

end Monoid.PushoutI
