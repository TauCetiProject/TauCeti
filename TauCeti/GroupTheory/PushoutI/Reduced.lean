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

When the `φ i` are injective, uniqueness (Mathlib's `Monoid.PushoutI.Reduced.eq_empty_of_mem_range`)
says that the product of a nonempty reduced word is not in the amalgamated subgroup. This file
restates it for lists of letters `⟨i, g⟩` with `g : G i`, consecutive letters in different factors,
which is the form in which it is applied to concrete words.

## Main results

* `Monoid.PushoutI.exists_eq_base_mul_ofCoprodI_prod`: every element is `h * w` with `h` in the
  amalgamated subgroup and `w` the product of a reduced word.
* `Monoid.PushoutI.exists_eq_of_mul_list_prod`: every element is `g * w` with `g` in a given
  factor `G i` and `w` the product of a reduced list of letters not starting in `G i`.
* `Monoid.PushoutI.list_prod_notMem_range_base`: the product of a nonempty reduced list of letters
  is not in the amalgamated subgroup.
* `Monoid.PushoutI.list_prod_inv_mul_of_mul_list_prod_notMem_range_base`: the conjugate
  `w⁻¹ * g * w` of a letter `g` outside the amalgamated subgroup by the product `w` of a reduced
  list that does not start in the factor of `g` is not in the amalgamated subgroup.

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

/-- The normal form in an amalgamated product of groups, seen from a factor `G i`: every element
is `g * a₁ * ⋯ * aᵣ` with `g ∈ G i` and letters `aⱼ`, consecutive ones from different factors, none
of them in the amalgamated subgroup and the first one not in `G i`. -/
theorem exists_eq_of_mul_list_prod (i : ι) (x : PushoutI φ) :
    ∃ (g : G i) (L : List (Σ j, G j)), L.IsChain (fun l l' => l.1 ≠ l'.1) ∧
      (∀ l ∈ L, l.2 ∉ (φ l.1).range) ∧ (∀ l ∈ L.head?, l.1 ≠ i) ∧
      x = of i g * (L.map fun l => of l.1 l.2).prod := by
  obtain ⟨h, ⟨L, _, hc⟩, hred, rfl⟩ := exists_eq_base_mul_ofCoprodI_prod x
  simp only [Reduced] at hred
  rw [← of_apply_eq_base φ i, Word.prod, map_list_prod, List.map_map]
  simp only [Function.comp_def, ofCoprodI_of]
  rcases L with _ | ⟨⟨j, a⟩, L⟩
  · exact ⟨φ i h, [], hc, hred, by simp, rfl⟩
  by_cases hj : j = i
  · -- A leading letter of `G i` is absorbed into `g`.
    subst hj
    refine ⟨φ j h * a, L, hc.tail, fun l hl => hred l (List.mem_cons_of_mem _ hl),
      fun l hl => ((List.isChain_cons.1 hc).1 l hl).symm, ?_⟩
    simp only [List.map_cons, List.prod_cons, map_mul, mul_assoc]
  · exact ⟨φ i h, _, hc, hred, by simpa using hj, rfl⟩

/-- In an amalgamated product of groups, the product of a nonempty list of letters, consecutive
ones from different factors and none of them in the amalgamated subgroup, is not in the
amalgamated subgroup. -/
theorem list_prod_notMem_range_base (hφ : ∀ i, Injective (φ i)) {L : List (Σ i, G i)}
    (hL : L ≠ []) (hc : L.IsChain fun l l' => l.1 ≠ l'.1) (hred : ∀ l ∈ L, l.2 ∉ (φ l.1).range) :
    (L.map fun l => of l.1 l.2).prod ∉ (base φ).range := by
  intro h
  let w : CoprodI.Word G :=
    ⟨L, fun l hl h1 => hred l hl ⟨1, by rw [map_one, h1]⟩, hc⟩
  have hw : ofCoprodI w.prod = (L.map fun l => of (φ := φ) l.1 l.2).prod := by
    rw [CoprodI.Word.prod, map_list_prod, List.map_map]
    simp [Function.comp_def, w]
  exact hL (congrArg CoprodI.Word.toList
    (Reduced.eq_empty_of_mem_range hφ (w := w) hred (hw ▸ h)))

/-- In an amalgamated product of groups, let `w` be the product of a list of letters, consecutive
ones from different factors and none of them in the amalgamated subgroup, and let `g` be a letter
outside the amalgamated subgroup whose factor is not that of the first letter of the list. Then
the conjugate `w⁻¹ * g * w` is not in the amalgamated subgroup. -/
theorem list_prod_inv_mul_of_mul_list_prod_notMem_range_base (hφ : ∀ i, Injective (φ i))
    {L : List (Σ i, G i)} (hc : L.IsChain fun l l' => l.1 ≠ l'.1)
    (hred : ∀ l ∈ L, l.2 ∉ (φ l.1).range) {i : ι} {g : G i} (hg : g ∉ (φ i).range)
    (hi : ∀ l ∈ L.head?, l.1 ≠ i) :
    (L.map fun l => of l.1 l.2).prod⁻¹ * of i g * (L.map fun l => of l.1 l.2).prod ∉
      (base φ).range := by
  have hprod : (((L.map fun l => (⟨l.1, l.2⁻¹⟩ : Σ i, G i)).reverse ++ ⟨i, g⟩ :: L).map
      fun l => of (φ := φ) l.1 l.2).prod =
      (L.map fun l => of l.1 l.2).prod⁻¹ * of i g * (L.map fun l => of l.1 l.2).prod := by
    rw [List.prod_inv_reverse]
    simp [Function.comp_def, mul_assoc]
  rw [← hprod]
  refine list_prod_notMem_range_base hφ (by simp) ?_ ?_
  · refine List.isChain_append.2 ⟨?_, List.isChain_cons.2 ⟨fun l hl => (hi l hl).symm, hc⟩, ?_⟩
    · rw [List.isChain_reverse, List.isChain_map]
      exact hc.imp fun _ _ h => h.symm
    · intro l hl l' hl'
      obtain rfl : l' = ⟨i, g⟩ := by simpa using hl'.symm
      rw [List.getLast?_reverse, List.head?_map] at hl
      obtain ⟨l₀, hl₀, rfl⟩ := Option.mem_map.1 hl
      exact hi l₀ hl₀
  · intro l hl
    rcases List.mem_append.1 hl with hl | hl
    · obtain ⟨l₀, hl₀, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hl)
      exact fun h => hred l₀ hl₀ (by simpa using inv_mem h)
    · rcases List.mem_cons.1 hl with rfl | hl
      exacts [hg, hred l hl]

end Monoid.PushoutI
