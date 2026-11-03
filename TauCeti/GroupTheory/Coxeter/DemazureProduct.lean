/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.Coxeter.Bruhat
public import TauCeti.GroupTheory.Coxeter.Matsumoto

/-!
# The Demazure product of a word

Let `cs : CoxeterSystem M W` be a Coxeter system. The **Demazure product** `δ(ω)` of a word
`ω = i₁ ⋯ iᵣ` in the simple reflections is the product of its letters in the *0-Hecke monoid*,
where a simple reflection that would shorten the element is absorbed instead of multiplied:

`δ([]) = 1`, and `δ(i :: ω) = δ(ω)` if `sᵢ` is a left descent of `δ(ω)`, `sᵢ δ(ω)` otherwise.

For a reduced word it is the ordinary product `s_{i₁} ⋯ s_{iᵣ}`. For an arbitrary word, reduced
or not, Demazure showed that the Bott–Samelson variety of the word maps onto the Schubert variety
of `δ(ω)`, and that the composite of the Demazure operators of the letters is the Demazure operator
of `δ(ω)`. This file proves the combinatorial side of both statements; no variety is constructed
here.

The combinatorial content of the first statement is the **subword characterization**: `δ(ω)` is
the greatest element, in the Bruhat order, among the products `π σ` of the subwords `σ` of `ω`,
and the Bruhat interval below `δ(ω)` consists exactly of those products
(`CoxeterSystem.bruhatLE_demazureProd_iff_exists_sublist_wordProd_eq`). For a reduced word this is
the subword property `CoxeterSystem.bruhatLE_iff_exists_sublist_wordProd_eq`. The second
statement is the universal property of the 0-Hecke monoid: generators of any monoid satisfying
the braid relations and `f i * f i = f i` have the same product along `ω` as along any reduced
word for `δ(ω)` (`CoxeterSystem.prod_map_eq_of_wordProd_eq_demazureProd`). It extends
Matsumoto's theorem `TauCeti.matsumoto` from reduced words to all words.

## Main definitions

* `CoxeterSystem.demazureProd`: the Demazure product `δ(ω)` of a word `ω`.

## Main results

* `CoxeterSystem.demazureProd_cons_of_isLeftDescent`,
  `CoxeterSystem.demazureProd_cons_of_not_isLeftDescent` and their right-hand counterparts
  `CoxeterSystem.demazureProd_append_singleton_of_isRightDescent`,
  `CoxeterSystem.demazureProd_append_singleton_of_not_isRightDescent`: the recursion on either end.
* `CoxeterSystem.demazureProd_eq_wordProd_of_isReduced`: on a reduced word, `δ(ω) = π ω`.
* `CoxeterSystem.exists_sublist_isReduced_wordProd_eq_demazureProd`: `δ(ω)` is spelled by a
  reduced subword of `ω`; hence `CoxeterSystem.length_demazureProd_le`, and
  `CoxeterSystem.length_demazureProd_eq_length_iff`: `ℓ(δ(ω)) = |ω|` exactly when `ω` is reduced.
* `CoxeterSystem.bruhatLE_demazureProd_of_sublist`: `δ` is monotone for the sublist order.
* `CoxeterSystem.bruhatLE_demazureProd_iff_exists_sublist_wordProd_eq`: **the subword
  characterization**, `u ≤ δ(ω)` exactly when some subword of `ω` spells `u`.
* `CoxeterSystem.demazureProd_reverse`: `δ(ω.reverse) = δ(ω)⁻¹`.
* `CoxeterSystem.mul_prod_map_eq_of_isLeftDescent`: a 0-Hecke generator `f i` is absorbed into
  the product along a reduced word whose element has `sᵢ` as a left descent.
* `CoxeterSystem.prod_map_eq_of_wordProd_eq_demazureProd`: **the universal property of the
  0-Hecke monoid**.

## References

* M. Demazure, *Désingularisation des variétés de Schubert généralisées*, Ann. Sci. École
  Norm. Sup. (4) 7 (1974).
* A. Knutson, E. Miller, *Subword complexes in Coxeter groups*, Adv. Math. 184 (2004), 161–176,
  Section 3.
-/

public section

namespace CoxeterSystem

variable {B W : Type*} [Group W] {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "ℓ " => cs.length
local prefix:100 "π " => cs.wordProd

open scoped Classical in
/-- The **Demazure product** of a word `ω` in the simple reflections: the product of its letters
in the 0-Hecke monoid. Reading the word from the right, a letter `i` multiplies the product `w`
of the letters after it on the left by `sᵢ`, unless `sᵢ` is a left descent of `w`, in which case
`w` is kept. -/
noncomputable def demazureProd (ω : List B) : W :=
  ω.foldr (fun i w ↦ if cs.IsLeftDescent w i then w else cs.simple i * w) 1

@[simp]
theorem demazureProd_nil : cs.demazureProd [] = 1 :=
  (rfl)

/-- A letter `i` is absorbed when `sᵢ` is a left descent of the Demazure product of the rest. -/
@[simp]
theorem demazureProd_cons_of_isLeftDescent {i : B} {ω : List B}
    (h : cs.IsLeftDescent (cs.demazureProd ω) i) :
    cs.demazureProd (i :: ω) = cs.demazureProd ω := by
  classical
  simp only [demazureProd, List.foldr_cons] at h ⊢
  simp [h]

/-- A letter `i` multiplies on the left when `sᵢ` is not a left descent of the Demazure product of
the rest. -/
@[simp]
theorem demazureProd_cons_of_not_isLeftDescent {i : B} {ω : List B}
    (h : ¬cs.IsLeftDescent (cs.demazureProd ω) i) :
    cs.demazureProd (i :: ω) = cs.simple i * cs.demazureProd ω := by
  classical
  simp only [demazureProd, List.foldr_cons] at h ⊢
  simp [h]

@[simp]
theorem demazureProd_singleton (i : B) : cs.demazureProd [i] = cs.simple i := by
  rw [cs.demazureProd_cons_of_not_isLeftDescent (by simpa using cs.not_isLeftDescent_one i),
    demazureProd_nil, mul_one]

/-- The first letter of a word is always a left descent of its Demazure product. -/
theorem isLeftDescent_demazureProd_cons (i : B) (ω : List B) :
    cs.IsLeftDescent (cs.demazureProd (i :: ω)) i := by
  by_cases h : cs.IsLeftDescent (cs.demazureProd ω) i
  · rwa [cs.demazureProd_cons_of_isLeftDescent h]
  · rwa [cs.demazureProd_cons_of_not_isLeftDescent h, cs.isLeftDescent_iff_not_isLeftDescent_mul,
      cs.simple_mul_simple_cancel_left]

/-- A repeated letter is absorbed: `δ(i i ω) = δ(i ω)`. -/
@[simp]
theorem demazureProd_cons_cons_self (i : B) (ω : List B) :
    cs.demazureProd (i :: i :: ω) = cs.demazureProd (i :: ω) :=
  cs.demazureProd_cons_of_isLeftDescent (cs.isLeftDescent_demazureProd_cons i ω)

/-- **The Demazure product of a reduced word is its product.** -/
theorem demazureProd_eq_wordProd_of_isReduced {ω : List B} (hω : cs.IsReduced ω) :
    cs.demazureProd ω = π ω := by
  induction ω with
  | nil => simp
  | cons i ω ih =>
    have hω' : cs.IsReduced ω := by simpa using hω.drop 1
    have h : ¬cs.IsLeftDescent (cs.demazureProd ω) i := by
      rw [ih hω', cs.not_isLeftDescent_iff, ← cs.wordProd_cons, hω.eq, hω'.eq, List.length_cons]
    rw [cs.demazureProd_cons_of_not_isLeftDescent h, ih hω', cs.wordProd_cons]

/-- **The Demazure product is spelled by a reduced subword.** -/
theorem exists_sublist_isReduced_wordProd_eq_demazureProd (ω : List B) :
    ∃ σ : List B, σ.Sublist ω ∧ cs.IsReduced σ ∧ π σ = cs.demazureProd ω := by
  induction ω with
  | nil => exact ⟨[], List.Sublist.slnil, by simp [IsReduced], by simp⟩
  | cons i ω ih =>
    obtain ⟨σ, hσω, hσ, hσprod⟩ := ih
    by_cases h : cs.IsLeftDescent (cs.demazureProd ω) i
    · exact ⟨σ, hσω.cons i, hσ, by rw [cs.demazureProd_cons_of_isLeftDescent h, hσprod]⟩
    · refine ⟨i :: σ, hσω.cons_cons i, ?_, by
        rw [cs.demazureProd_cons_of_not_isLeftDescent h, cs.wordProd_cons, hσprod]⟩
      exact cs.isReduced_cons_of_not_isLeftDescent h hσ hσprod

/-- The Demazure product of a word is no longer than the word. -/
theorem length_demazureProd_le (ω : List B) : ℓ (cs.demazureProd ω) ≤ ω.length := by
  obtain ⟨σ, hσω, hσ, hσprod⟩ := cs.exists_sublist_isReduced_wordProd_eq_demazureProd ω
  rw [← hσprod, hσ.eq]
  exact hσω.length_le

/-- The Demazure product of a word has the length of the word exactly when the word is
reduced. -/
theorem length_demazureProd_eq_length_iff {ω : List B} :
    ℓ (cs.demazureProd ω) = ω.length ↔ cs.IsReduced ω := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [cs.demazureProd_eq_wordProd_of_isReduced h, h.eq]⟩
  obtain ⟨σ, hσω, hσ, hσprod⟩ := cs.exists_sublist_isReduced_wordProd_eq_demazureProd ω
  rw [← hσprod, hσ.eq] at h
  rwa [← hσω.eq_of_length h]

/-! ### The Bruhat order -/

/-- Prepending a letter moves the Demazure product up in the Bruhat order. -/
theorem bruhatLE_demazureProd_cons (i : B) (ω : List B) :
    cs.BruhatLE (cs.demazureProd ω) (cs.demazureProd (i :: ω)) := by
  by_cases h : cs.IsLeftDescent (cs.demazureProd ω) i
  · rw [cs.demazureProd_cons_of_isLeftDescent h]
  · rw [cs.demazureProd_cons_of_not_isLeftDescent h]
    exact (cs.bruhatStep_simple_mul i (by simp [cs.not_isLeftDescent_iff.mp h])).bruhatLE

/-- **The Demazure product is monotone for the sublist order.** -/
theorem bruhatLE_demazureProd_of_sublist {σ ω : List B} (h : σ.Sublist ω) :
    cs.BruhatLE (cs.demazureProd σ) (cs.demazureProd ω) := by
  induction h with
  | slnil => exact cs.bruhatLE_refl _
  | cons i _ ih => exact ih.trans (cs.bruhatLE_demazureProd_cons i _)
  | @cons_cons σ ω i _ ih =>
    -- `sᵢ` is a left descent of `δ(i ω) ≥ δ(ω) ≥ δ(σ)`, and `δ(i σ)` is `δ(σ)` or `sᵢ δ(σ)`.
    have hle := ih.trans (cs.bruhatLE_demazureProd_cons i ω)
    by_cases h : cs.IsLeftDescent (cs.demazureProd σ) i
    · rwa [cs.demazureProd_cons_of_isLeftDescent h]
    · rw [cs.demazureProd_cons_of_not_isLeftDescent h]
      exact hle.simple_mul_of_isLeftDescent i (cs.isLeftDescent_demazureProd_cons i ω)

/-- The product of a word lies below its Demazure product. -/
theorem bruhatLE_wordProd_demazureProd (ω : List B) :
    cs.BruhatLE (π ω) (cs.demazureProd ω) := by
  induction ω with
  | nil => exact cs.bruhatLE_refl _
  | cons i ω ih =>
    rw [cs.wordProd_cons]
    by_cases h : cs.IsLeftDescent (cs.demazureProd ω) i
    · rw [cs.demazureProd_cons_of_isLeftDescent h]
      exact ih.simple_mul_of_isLeftDescent i h
    · rw [cs.demazureProd_cons_of_not_isLeftDescent h]
      exact ih.simple_mul_of_not_isLeftDescent i h

/-- **The subword characterization of the Demazure product.** An element lies below `δ(ω)` in the
Bruhat order exactly when some subword of `ω`, reduced or not, spells it. Together with
`CoxeterSystem.exists_sublist_isReduced_wordProd_eq_demazureProd` this says that `δ(ω)` is the
greatest of the products of the subwords of `ω`. -/
theorem bruhatLE_demazureProd_iff_exists_sublist_wordProd_eq {u : W} {ω : List B} :
    cs.BruhatLE u (cs.demazureProd ω) ↔ ∃ σ : List B, σ.Sublist ω ∧ π σ = u := by
  constructor
  · intro h
    obtain ⟨τ, hτω, hτ, hτprod⟩ := cs.exists_sublist_isReduced_wordProd_eq_demazureProd ω
    obtain ⟨σ, hστ, hσprod⟩ := (cs.bruhatLE_iff_exists_sublist_wordProd_eq hτ).mp (hτprod ▸ h)
    exact ⟨σ, hστ.trans hτω, hσprod⟩
  · rintro ⟨σ, hσω, rfl⟩
    exact (cs.bruhatLE_wordProd_demazureProd σ).trans (cs.bruhatLE_demazureProd_of_sublist hσω)

/-- **The Demazure product of the reversed word is the inverse.** -/
@[simp]
theorem demazureProd_reverse (ω : List B) :
    cs.demazureProd ω.reverse = (cs.demazureProd ω)⁻¹ := by
  -- Both sides have the same Bruhat lower set, the inverses of the subword products of `ω`.
  have key (u : W) : cs.BruhatLE u (cs.demazureProd ω.reverse) ↔
      cs.BruhatLE u (cs.demazureProd ω)⁻¹ := by
    rw [cs.bruhatLE_demazureProd_iff_exists_sublist_wordProd_eq, ← cs.bruhatLE_inv_iff, inv_inv,
      cs.bruhatLE_demazureProd_iff_exists_sublist_wordProd_eq]
    constructor
    · rintro ⟨σ, hσ, rfl⟩
      exact ⟨σ.reverse, by simpa using hσ.reverse, by simp⟩
    · rintro ⟨σ, hσ, hσprod⟩
      exact ⟨σ.reverse, hσ.reverse, by simp [hσprod]⟩
  exact ((key _).mp (cs.bruhatLE_refl _)).antisymm ((key _).mpr (cs.bruhatLE_refl _))

/-- Appending a letter is prepending it to the reversed word, up to inversion. -/
private theorem demazureProd_append_singleton_eq_inv (ω : List B) (i : B) :
    cs.demazureProd (ω ++ [i]) = (cs.demazureProd (i :: ω.reverse))⁻¹ := by
  rw [← demazureProd_reverse]
  simp

/-- A last letter `i` is absorbed when `sᵢ` is a right descent of the Demazure product of the
rest. -/
@[simp]
theorem demazureProd_append_singleton_of_isRightDescent {i : B} {ω : List B}
    (h : cs.IsRightDescent (cs.demazureProd ω) i) :
    cs.demazureProd (ω ++ [i]) = cs.demazureProd ω := by
  rw [← cs.isLeftDescent_inv_iff, ← demazureProd_reverse] at h
  rw [demazureProd_append_singleton_eq_inv, cs.demazureProd_cons_of_isLeftDescent h]
  simp

/-- A last letter `i` multiplies on the right when `sᵢ` is not a right descent of the Demazure
product of the rest. -/
@[simp]
theorem demazureProd_append_singleton_of_not_isRightDescent {i : B} {ω : List B}
    (h : ¬cs.IsRightDescent (cs.demazureProd ω) i) :
    cs.demazureProd (ω ++ [i]) = cs.demazureProd ω * cs.simple i := by
  rw [← cs.isLeftDescent_inv_iff, ← demazureProd_reverse] at h
  rw [demazureProd_append_singleton_eq_inv, cs.demazureProd_cons_of_not_isLeftDescent h]
  simp

/-! ### The universal property of the 0-Hecke monoid -/

/-- **A 0-Hecke generator absorbs into a product along a word it can start.** Let `f` assign to
each simple reflection an element of a monoid, satisfying the braid relations, and let
`f i * f i = f i`. If `ω` is a reduced word and `sᵢ` is a left descent of `π ω`, then
`f i * f(ω) = f(ω)`: some reduced word for `π ω` starts with `i`. -/
theorem mul_prod_map_eq_of_isLeftDescent {G : Type*} [Monoid G] (f : B → G)
    (hbraid : ∀ i j, ((braidWord M i j).map f).prod = ((braidWord M j i).map f).prod)
    {i : B} (hidem : f i * f i = f i) {ω : List B} (hω : cs.IsReduced ω)
    (hi : cs.IsLeftDescent (π ω) i) : f i * (ω.map f).prod = (ω.map f).prod := by
  obtain ⟨σ, hσ, hσw⟩ := cs.exists_isReduced (cs.simple i * π ω)
  have hred := cs.isReduced_cons_of_isLeftDescent hi hσ hσw.symm
  have hprod : π (i :: σ) = π ω := by
    rw [cs.wordProd_cons, ← hσw, cs.simple_mul_simple_cancel_left]
  rw [← TauCeti.matsumoto cs f hbraid hred hω hprod, List.map_cons, List.prod_cons, ← mul_assoc,
    hidem]

/-- **The universal property of the 0-Hecke monoid.** Let `f` assign to each simple reflection
an element of a monoid, satisfying the braid relations and `f i * f i = f i`. Then the product of
`f` along an arbitrary word `ω` equals its product along any reduced word `σ` for the Demazure
product `δ(ω)`. For reduced `ω` this is Matsumoto's theorem `TauCeti.matsumoto`. -/
theorem prod_map_eq_of_wordProd_eq_demazureProd {G : Type*} [Monoid G] (f : B → G)
    (hbraid : ∀ i j, ((braidWord M i j).map f).prod = ((braidWord M j i).map f).prod)
    (hidem : ∀ i, f i * f i = f i) {ω σ : List B} (hσ : cs.IsReduced σ)
    (h : π σ = cs.demazureProd ω) : (ω.map f).prod = (σ.map f).prod := by
  induction ω generalizing σ with
  | nil =>
    have hσnil : σ = [] := List.eq_nil_of_length_eq_zero (by
      rw [← hσ.eq, h, demazureProd_nil, length_one])
    simp [hσnil]
  | cons i ω ih =>
    obtain ⟨τ, hτ, hτprod⟩ := cs.exists_isReduced (cs.demazureProd ω)
    rw [List.map_cons, List.prod_cons, ih hτ hτprod.symm]
    by_cases hd : cs.IsLeftDescent (cs.demazureProd ω) i
    · -- `f i` is absorbed into the product along the reduced word `τ` for `δ(ω) = δ(i ω)`.
      rw [cs.demazureProd_cons_of_isLeftDescent hd] at h
      rw [cs.mul_prod_map_eq_of_isLeftDescent f hbraid (hidem i) hτ (hτprod ▸ hd),
        TauCeti.matsumoto cs f hbraid hτ hσ (by rw [h, hτprod])]
    · -- `i :: τ` is a reduced word for `sᵢ δ(ω) = δ(i ω)`.
      rw [cs.demazureProd_cons_of_not_isLeftDescent hd] at h
      have hiτ := cs.isReduced_cons_of_not_isLeftDescent hd hτ hτprod.symm
      rw [← List.prod_cons, ← List.map_cons,
        TauCeti.matsumoto cs f hbraid hiτ hσ (by rw [h, cs.wordProd_cons, hτprod])]

end CoxeterSystem
