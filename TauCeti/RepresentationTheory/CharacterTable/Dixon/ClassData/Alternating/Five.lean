/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import TauCeti.RepresentationTheory.CharacterTable.Dixon.ClassData.Basic

/-!
# Executable conjugacy-class data for the alternating group of degree five

The alternating group `A₅` has five conjugacy classes.  This file fixes the numbering used by the
exact Dixon character-table certificate:

1. the identity;
2. the double transposition `(0 1)(2 3)`;
3. the three-cycle `(0 1 2)`;
4. the five-cycle `(0 1 2 3 4)`;
5. the square `(0 2 4 1 3)` of that five-cycle.

The last two representatives lie in distinct conjugacy classes in `A₅`, although their classes
fuse in the symmetric group.  Their class sizes are both twelve.

## Main definitions

* `TauCeti.alternatingGroupFiveClassData`: the executable five-class numbering.

## Main results

* `TauCeti.numClasses_alternatingGroupFiveClassData`: the numbering has five classes.

## References

See G. James and M. Liebeck, *Representations and Characters of Groups*, §18.1.
-/

public section

namespace TauCeti

open Equiv

/-- The double transposition `(0 1)(2 3)` in `A₅`. -/
@[expose] def alternatingGroupFiveDoubleTransposition : alternatingGroup (Fin 5) :=
  ⟨Equiv.swap (0 : Fin 5) 1 * Equiv.swap 2 3,
    Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩

/-- The three-cycle `(0 1 2)` in `A₅`. -/
@[expose] def alternatingGroupFiveThreeCycle : alternatingGroup (Fin 5) :=
  ⟨Fin.cycleRange 2, by simp⟩

/-- The five-cycle `(0 1 2 3 4)` in `A₅`. -/
@[expose] def alternatingGroupFiveFiveCycle : alternatingGroup (Fin 5) :=
  ⟨Fin.cycleRange 4, Equiv.Perm.mem_alternatingGroup.mpr (by
    rw [Fin.sign_cycleRange]
    decide)⟩

private abbrev A5 := alternatingGroup (Fin 5)

private def alternatingGroupFivePowerConjugator : Equiv.Perm (Fin 5) :=
  Equiv.swap 1 2 * Equiv.swap 1 4 * Equiv.swap 1 3

private theorem sign_alternatingGroupFivePowerConjugator :
    Equiv.Perm.sign alternatingGroupFivePowerConjugator = -1 := by
  decide

private theorem alternatingGroupFivePowerConjugator_conj_sq :
    alternatingGroupFivePowerConjugator * (alternatingGroupFiveFiveCycle : Equiv.Perm (Fin 5)) ^ 2 *
        alternatingGroupFivePowerConjugator⁻¹ = alternatingGroupFiveFiveCycle := by
  decide

/-- The double-transposition representative has cycle type `(2, 2)`. -/
@[simp] theorem cycleType_alternatingGroupFiveDoubleTransposition :
    (alternatingGroupFiveDoubleTransposition : Equiv.Perm (Fin 5)).cycleType = {2, 2} := by
  rw [alternatingGroupFiveDoubleTransposition]
  rw [Equiv.Perm.Disjoint.cycleType_mul (Equiv.Perm.disjoint_swap_swap (by decide))]
  rw [Equiv.Perm.isSwap_iff_cycleType.mp (Equiv.Perm.swap_isSwap_iff.mpr (by decide))]
  rw [Equiv.Perm.isSwap_iff_cycleType.mp (Equiv.Perm.swap_isSwap_iff.mpr (by decide))]
  rfl

/-- The three-cycle representative has cycle type `(3)`. -/
@[simp] theorem cycleType_alternatingGroupFiveThreeCycle :
    (alternatingGroupFiveThreeCycle : Equiv.Perm (Fin 5)).cycleType = {3} := by
  exact Fin.cycleType_cycleRange (by decide)

/-- The five-cycle representative has cycle type `(5)`. -/
@[simp] theorem cycleType_alternatingGroupFiveFiveCycle :
    (alternatingGroupFiveFiveCycle : Equiv.Perm (Fin 5)).cycleType = {5} := by
  exact Fin.cycleType_cycleRange (by decide)

/-- The square of the five-cycle representative has cycle type `(5)`. -/
@[simp] theorem cycleType_alternatingGroupFiveFiveCycle_sq :
    ((alternatingGroupFiveFiveCycle : Equiv.Perm (Fin 5)) ^ 2).cycleType = {5} := by
  have hcycle : (alternatingGroupFiveFiveCycle : Equiv.Perm (Fin 5)).IsCycle :=
    Fin.isCycle_cycleRange (by decide)
  have horder : orderOf (alternatingGroupFiveFiveCycle : Equiv.Perm (Fin 5)) = 5 := by
    rw [hcycle.orderOf]
    decide
  have hp : ((alternatingGroupFiveFiveCycle : Equiv.Perm (Fin 5)) ^ 2).IsCycle :=
    (Equiv.Perm.IsCycle.pow_iff hcycle).mpr (by rw [horder]; decide)
  rw [hp.cycleType,
    hcycle.support_pow_of_pos_of_lt_orderOf (by decide) (by rw [horder]; decide),
    ← hcycle.orderOf, horder]

private theorem cycleType_alternatingGroupFive (g : A5) :
    (g : Equiv.Perm (Fin 5)).cycleType = 0 ∨
      (g : Equiv.Perm (Fin 5)).cycleType = {2, 2} ∨
      (g : Equiv.Perm (Fin 5)).cycleType = {3} ∨
      (g : Equiv.Perm (Fin 5)).cycleType = {5} := by
  let m := (g : Equiv.Perm (Fin 5)).cycleType
  have hm : (g : Equiv.Perm (Fin 5)).cycleType = m := rfl
  rw [hm]
  have hsum : m.sum ≤ 5 := (g : Equiv.Perm (Fin 5)).sum_cycleType_le
  have htwo : ∀ n ∈ m, 2 ≤ n := fun _ hn ↦ Equiv.Perm.two_le_of_mem_cycleType hn
  have hcard : m.card ≤ 2 := by
    have card_bound : ∀ s : Multiset ℕ, (∀ n ∈ s, 2 ≤ n) → 2 * s.card ≤ s.sum := by
      intro s hs
      induction s using Multiset.induction_on with
      | empty => simp
      | @cons a s ih =>
          have ha : 2 ≤ a := hs a (by simp)
          have hs' : ∀ n ∈ s, 2 ≤ n := fun n hn ↦ hs n (by simp [hn])
          calc
            2 * (a ::ₘ s).card = 2 + 2 * s.card := by simp [Nat.mul_add, Nat.add_comm]
            _ ≤ a + s.sum := Nat.add_le_add ha (ih hs')
            _ = (a ::ₘ s).sum := by simp
    have h := card_bound m htwo
    omega
  have heven : Even (m.sum + m.card) := by
    have hg := g.property
    rw [Equiv.Perm.mem_alternatingGroup, Equiv.Perm.sign_of_cycleType,
      neg_one_pow_eq_one_iff_even (by decide)] at hg
    exact hg
  interval_cases hc : m.card
  · exact Or.inl (Multiset.card_eq_zero.mp hc)
  · obtain ⟨n, hncard⟩ := Multiset.card_eq_one.mp hc
    have hn : 2 ≤ n := htwo n (hncard ▸ by simp)
    have hsum' : n ≤ 5 := by simpa [hncard] using hsum
    have heven' : Even (n + 1) := by simpa [hncard] using heven
    rw [hncard]
    rcases heven' with ⟨k, hk⟩
    have : n = 3 ∨ n = 5 := by omega
    rcases this with rfl | rfl <;> simp
  · obtain ⟨n, k, hncard⟩ := Multiset.card_eq_two.mp hc
    have hn : 2 ≤ n := htwo n (hncard ▸ by simp)
    have hk' : 2 ≤ k := htwo k (hncard ▸ by simp)
    have hsum' : n + k ≤ 5 := by simpa [hncard] using hsum
    have heven' : Even (n + k + 2) := by simpa [hncard] using heven
    rw [hncard]
    rcases heven' with ⟨r, hr⟩
    have : n = 2 ∧ k = 2 := by omega
    rcases this with ⟨rfl, rfl⟩
    simp

private theorem isConj_alternatingGroup_of_isConj_perm_of_odd_centralizer
    {a b : A5} (hab : IsConj (a : Equiv.Perm (Fin 5)) b)
    (c : Equiv.Perm (Fin 5)) (hc : c * a * c⁻¹ = a)
    (hcSign : Equiv.Perm.sign c = -1) : IsConj a b := by
  obtain ⟨π, hπ⟩ := isConj_iff.mp hab
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hsign | hsign
  · rw [isConj_iff]
    exact ⟨⟨π, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩, Subtype.val_injective hπ⟩
  · rw [isConj_iff]
    refine ⟨⟨π * c, Equiv.Perm.mem_alternatingGroup.mpr ?_⟩, Subtype.val_injective ?_⟩
    · rw [map_mul, hsign, hcSign]
      decide
    · calc
        (π * c) * (a : Equiv.Perm (Fin 5)) * (π * c)⁻¹ =
            π * (c * a * c⁻¹) * π⁻¹ := by group
        _ = π * a * π⁻¹ := by rw [hc]
        _ = b := hπ

private theorem isConj_alternatingGroupFiveDoubleTransposition_of_cycleType
    {g : A5} (hg : (g : Equiv.Perm (Fin 5)).cycleType = {2, 2}) :
    IsConj alternatingGroupFiveDoubleTransposition g := by
  exact isConj_alternatingGroup_of_isConj_perm_of_odd_centralizer
    (Equiv.Perm.isConj_iff_cycleType_eq.mpr
      (cycleType_alternatingGroupFiveDoubleTransposition.trans hg.symm))
    (Equiv.swap (0 : Fin 5) 1) (by decide) (by decide)

private theorem isConj_alternatingGroupFiveFiveCycle_or_sq_of_cycleType
    {g : A5} (hg : (g : Equiv.Perm (Fin 5)).cycleType = {5}) :
    IsConj alternatingGroupFiveFiveCycle g ∨ IsConj (alternatingGroupFiveFiveCycle ^ 2) g := by
  have hperm : IsConj (alternatingGroupFiveFiveCycle : Equiv.Perm (Fin 5)) g := by
    exact Equiv.Perm.isConj_iff_cycleType_eq.mpr
      (cycleType_alternatingGroupFiveFiveCycle.trans hg.symm)
  obtain ⟨π, hπ⟩ := isConj_iff.mp hperm
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with hsign | hsign
  · left
    rw [isConj_iff]
    exact ⟨⟨π, Equiv.Perm.mem_alternatingGroup.mpr hsign⟩, Subtype.val_injective hπ⟩
  · right
    rw [isConj_iff]
    refine ⟨⟨π * alternatingGroupFivePowerConjugator,
      Equiv.Perm.mem_alternatingGroup.mpr ?_⟩, Subtype.val_injective ?_⟩
    · rw [map_mul, hsign, sign_alternatingGroupFivePowerConjugator]
      decide
    · calc
        (π * alternatingGroupFivePowerConjugator) *
              (alternatingGroupFiveFiveCycle : Equiv.Perm (Fin 5)) ^ 2 *
              (π * alternatingGroupFivePowerConjugator)⁻¹ =
            π * (alternatingGroupFivePowerConjugator *
              (alternatingGroupFiveFiveCycle : Equiv.Perm (Fin 5)) ^ 2 *
              alternatingGroupFivePowerConjugator⁻¹) * π⁻¹ := by group
        _ = π * alternatingGroupFiveFiveCycle * π⁻¹ := by
          rw [alternatingGroupFivePowerConjugator_conj_sq]
        _ = g := hπ

private theorem not_isConj_alternatingGroupFiveFiveCycle_sq :
    ¬IsConj alternatingGroupFiveFiveCycle (alternatingGroupFiveFiveCycle ^ 2) := by
  intro h
  obtain ⟨q, hq⟩ := isConj_iff.mp h
  have hq' := congrArg Subtype.val hq
  have hq'' : (q : Equiv.Perm (Fin 5)) * alternatingGroupFiveFiveCycle *
      (q : Equiv.Perm (Fin 5))⁻¹ =
      (alternatingGroupFiveFiveCycle : Equiv.Perm (Fin 5)) ^ 2 := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow] using hq'
  have hconj :
      (alternatingGroupFivePowerConjugator * (q : Equiv.Perm (Fin 5))) *
          (alternatingGroupFiveFiveCycle : Equiv.Perm (Fin 5)) *
          (alternatingGroupFivePowerConjugator * (q : Equiv.Perm (Fin 5)))⁻¹ =
            alternatingGroupFiveFiveCycle := by
    calc
      _ = alternatingGroupFivePowerConjugator *
          ((q : Equiv.Perm (Fin 5)) * alternatingGroupFiveFiveCycle *
            (q : Equiv.Perm (Fin 5))⁻¹) *
          alternatingGroupFivePowerConjugator⁻¹ := by group
      _ = alternatingGroupFivePowerConjugator *
          (alternatingGroupFiveFiveCycle : Equiv.Perm (Fin 5)) ^ 2 *
          alternatingGroupFivePowerConjugator⁻¹ := by rw [hq'']
      _ = alternatingGroupFiveFiveCycle := alternatingGroupFivePowerConjugator_conj_sq
  have hcomm : Commute
      (alternatingGroupFivePowerConjugator * (q : Equiv.Perm (Fin 5)))
      (alternatingGroupFiveFiveCycle : Equiv.Perm (Fin 5)) := by
    rw [commute_iff_eq]
    calc
      _ = ((alternatingGroupFivePowerConjugator * (q : Equiv.Perm (Fin 5))) *
            alternatingGroupFiveFiveCycle *
            (alternatingGroupFivePowerConjugator * (q : Equiv.Perm (Fin 5)))⁻¹) *
          (alternatingGroupFivePowerConjugator * (q : Equiv.Perm (Fin 5))) := by group
      _ = alternatingGroupFiveFiveCycle *
          (alternatingGroupFivePowerConjugator * (q : Equiv.Perm (Fin 5))) := by rw [hconj]
  have hcentral : alternatingGroupFivePowerConjugator * (q : Equiv.Perm (Fin 5)) ∈
      Subgroup.centralizer {(alternatingGroupFiveFiveCycle : Equiv.Perm (Fin 5))} :=
    Subgroup.mem_centralizer_singleton_iff.mpr hcomm
  have hcentralEven : Subgroup.centralizer
      {(alternatingGroupFiveFiveCycle : Equiv.Perm (Fin 5))} ≤
      alternatingGroup (Fin 5) := by
    rw [Equiv.Perm.centralizer_le_alternating_iff]
    rw [cycleType_alternatingGroupFiveFiveCycle]
    refine ⟨?_, by norm_num, ?_⟩
    · intro c hc
      simp only [Multiset.mem_singleton] at hc
      subst c
      exact ⟨2, by norm_num⟩
    intro i
    rw [Multiset.count_singleton]
    split <;> omega
  have heven := Equiv.Perm.mem_alternatingGroup.mp (hcentralEven hcentral)
  have hodd : Equiv.Perm.sign
      (alternatingGroupFivePowerConjugator * (q : Equiv.Perm (Fin 5))) = -1 := by
    rw [map_mul, sign_alternatingGroupFivePowerConjugator,
      Equiv.Perm.mem_alternatingGroup.mp q.property]
    decide
  exact (by decide : (1 : ℤˣ) ≠ -1) (heven.symm.trans hodd)

private theorem not_isConj_of_cycleType_ne {a b : A5}
    (h : (a : Equiv.Perm (Fin 5)).cycleType ≠ (b : Equiv.Perm (Fin 5)).cycleType) :
    ¬IsConj a b := fun hab ↦
  h (Equiv.Perm.isConj_iff_cycleType_eq.mp
    ((alternatingGroup (Fin 5)).subtype.map_isConj hab))

/-- Executable conjugacy-class data for `A₅`, ordered as the identity, double transpositions,
three-cycles, and the two classes of five-cycles represented by `g` and `g²`. -/
@[expose] def alternatingGroupFiveClassData : ClassData (alternatingGroup (Fin 5)) where
  reps := [1, alternatingGroupFiveDoubleTransposition, alternatingGroupFiveThreeCycle,
    alternatingGroupFiveFiveCycle, alternatingGroupFiveFiveCycle ^ 2]
  pairwise_not_isConj := by
    apply List.pairwise_cons.mpr
    refine ⟨?_, ?_⟩
    · intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl | rfl | rfl <;>
        apply not_isConj_of_cycleType_ne <;> simp
    · apply List.pairwise_cons.mpr
      refine ⟨?_, ?_⟩
      · intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        rcases hx with rfl | rfl | rfl <;>
          apply not_isConj_of_cycleType_ne <;>
          simp only [cycleType_alternatingGroupFiveDoubleTransposition,
            cycleType_alternatingGroupFiveThreeCycle,
            cycleType_alternatingGroupFiveFiveCycle, SubmonoidClass.coe_pow,
            cycleType_alternatingGroupFiveFiveCycle_sq, Multiset.insert_eq_cons, ne_eq]
        all_goals decide
      · apply List.pairwise_cons.mpr
        refine ⟨?_, ?_⟩
        · intro x hx
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl <;>
            apply not_isConj_of_cycleType_ne <;> simp
        · apply List.pairwise_cons.mpr
          refine ⟨?_, List.pairwise_singleton _ _⟩
          intro x hx
          simp only [List.mem_singleton] at hx
          subst x
          exact not_isConj_alternatingGroupFiveFiveCycle_sq
  exists_isConj := by
    intro g
    rcases cycleType_alternatingGroupFive g with h | h | h | h
    · have hg : g = 1 := Subtype.ext (Equiv.Perm.cycleType_eq_zero.mp h)
      subst g
      exact ⟨1, by simp, IsConj.refl 1⟩
    · exact ⟨alternatingGroupFiveDoubleTransposition, by simp,
        isConj_alternatingGroupFiveDoubleTransposition_of_cycleType h⟩
    · exact ⟨alternatingGroupFiveThreeCycle, by simp,
        alternatingGroup.isThreeCycle_isConj (by norm_num)
          cycleType_alternatingGroupFiveThreeCycle h⟩
    · rcases isConj_alternatingGroupFiveFiveCycle_or_sq_of_cycleType h with hg | hg
      · exact ⟨alternatingGroupFiveFiveCycle, by simp, hg⟩
      · exact ⟨alternatingGroupFiveFiveCycle ^ 2, by simp, hg⟩

/-- The representatives in the executable `A₅` class data, in their defining order. -/
@[simp]
theorem reps_alternatingGroupFiveClassData :
    alternatingGroupFiveClassData.reps =
      [1, alternatingGroupFiveDoubleTransposition, alternatingGroupFiveThreeCycle,
        alternatingGroupFiveFiveCycle, alternatingGroupFiveFiveCycle ^ 2] := by
  rfl

/-- The alternating group of degree five has five conjugacy classes. -/
@[simp]
theorem numClasses_alternatingGroupFiveClassData :
    alternatingGroupFiveClassData.numClasses = 5 := by
  rfl

end TauCeti
