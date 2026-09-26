/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.GroupTheory.SpecificGroups.Alternating.Centralizer
public import TauCeti.Algebra.Group.Conj
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
* `TauCeti.card_classFinset_alternatingGroupFiveClassData`: the class sizes are `1`, `15`,
  `20`, `12`, and `12`.
* `TauCeti.exponent_alternatingGroup_five`: the exponent of `A₅` is thirty.

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

local instance fact_prime_five_alternatingGroupFive : Fact (Nat.Prime 5) := ⟨by decide⟩

/-- The five numbered conjugacy classes of `A₅` have sizes `1`, `15`, `20`, `12`, and `12`. -/
@[simp]
theorem card_classFinset_alternatingGroupFiveClassData
    (i : Fin alternatingGroupFiveClassData.numClasses) :
    (alternatingGroupFiveClassData.classFinset i).card =
      ![1, 15, 20, 12, 12]
        (finCongr numClasses_alternatingGroupFiveClassData i) := by
  have hnum := numClasses_alternatingGroupFiveClassData
  have hzero : (alternatingGroupFiveClassData.classFinset ⟨0, by omega⟩).card = 1 := by
    rw [alternatingGroupFiveClassData.card_classFinset,
      alternatingGroupFiveClassData.classOf_eq_mk]
    -- `ClassData.rep` is executable list lookup; the first entry is definitionally `1`.
    rw [show alternatingGroupFiveClassData.rep ⟨0, by omega⟩ = 1 by rfl]
    exact ConjClasses.ncard_carrier_mk_of_mem_center (Subgroup.one_mem _)
  have hone : (alternatingGroupFiveClassData.classFinset ⟨1, by omega⟩).card = 15 := by
    have hfinset : alternatingGroupFiveClassData.classFinset ⟨1, by omega⟩ =
        ({g : A5 | (g : Equiv.Perm (Fin 5)).cycleType = {2, 2}} : Finset A5) := by
      ext g
      rw [alternatingGroupFiveClassData.mem_classFinset_iff_isConj]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        exact Equiv.Perm.isConj_iff_cycleType_eq.mp
          ((alternatingGroup (Fin 5)).subtype.map_isConj h) |>.symm.trans
            cycleType_alternatingGroupFiveDoubleTransposition
      · exact isConj_alternatingGroupFiveDoubleTransposition_of_cycleType
    rw [hfinset, AlternatingGroup.card_of_cycleType]
    rw [ite_eq_left (by decide)]
    decide
  have htwo : (alternatingGroupFiveClassData.classFinset ⟨2, by omega⟩).card = 20 := by
    have hfinset : alternatingGroupFiveClassData.classFinset ⟨2, by omega⟩ =
        ({g : A5 | (g : Equiv.Perm (Fin 5)).cycleType = {3}} : Finset A5) := by
      ext g
      rw [alternatingGroupFiveClassData.mem_classFinset_iff_isConj]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · intro h
        exact Equiv.Perm.isConj_iff_cycleType_eq.mp
          ((alternatingGroup (Fin 5)).subtype.map_isConj h) |>.symm.trans
            cycleType_alternatingGroupFiveThreeCycle
      · intro h
        exact alternatingGroup.isThreeCycle_isConj (by norm_num)
          cycleType_alternatingGroupFiveThreeCycle h
    rw [hfinset, AlternatingGroup.card_of_cycleType_singleton (by omega) (by simp)]
    rw [ite_eq_left (by decide)]
    decide
  have hle (j : Fin alternatingGroupFiveClassData.numClasses)
      (hj : j = ⟨3, by omega⟩ ∨ j = ⟨4, by omega⟩) :
      (alternatingGroupFiveClassData.classFinset j).card ≤ 12 := by
    have horder : orderOf alternatingGroupFiveFiveCycle = 5 := by
      apply orderOf_eq_prime <;> decide
    have hrep_three : alternatingGroupFiveClassData.rep ⟨3, by omega⟩ =
        alternatingGroupFiveFiveCycle := by
      rfl
    have hrep_four : alternatingGroupFiveClassData.rep ⟨4, by omega⟩ =
        alternatingGroupFiveFiveCycle ^ 2 := by
      rfl
    have hrepOrder : orderOf (alternatingGroupFiveClassData.rep j) = 5 := by
      rcases hj with rfl | rfl
      · rw [hrep_three]
        exact horder
      · rw [hrep_four]
        rw [orderOf_pow, horder]
        norm_num
    have hmem : alternatingGroupFiveClassData.rep j ∈
        (alternatingGroupFiveClassData.classOf j).carrier := by
      simpa only [alternatingGroupFiveClassData.classOf_eq_mk] using
        (ConjClasses.mem_carrier_mk : alternatingGroupFiveClassData.rep j ∈
          (ConjClasses.mk (alternatingGroupFiveClassData.rep j)).carrier)
    have hdvd := (alternatingGroupFiveClassData.classOf j).card_carrier_mul_orderOf_dvd
      (alternatingGroupFiveClassData.rep j) hmem
    rw [← alternatingGroupFiveClassData.card_classFinset, hrepOrder,
      nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin] at hdvd
    norm_num [Nat.factorial] at hdvd
    have hmul_le : (alternatingGroupFiveClassData.classFinset j).card * 5 ≤ 60 :=
      Nat.le_of_dvd (by norm_num) hdvd
    omega
  have hsum := alternatingGroupFiveClassData.sum_card_classFinset
  have hcard : Fintype.card (alternatingGroup (Fin 5)) = 60 := by
    rw [← Nat.card_eq_fintype_card, nat_card_alternatingGroup,
      Nat.card_eq_fintype_card, Fintype.card_fin]
    rfl
  rw [hcard] at hsum
  let e : Fin 5 ≃ Fin alternatingGroupFiveClassData.numClasses := (finCongr hnum).symm
  let f : Fin 5 → ℕ := fun j ↦ (alternatingGroupFiveClassData.classFinset (e j)).card
  have hsum5 : ∑ j, f j = 60 := (e.sum_comp fun j ↦
    (alternatingGroupFiveClassData.classFinset j).card).trans hsum
  have hezero : e 0 = ⟨0, by omega⟩ := Fin.ext rfl
  have heone : e 1 = ⟨1, by omega⟩ := Fin.ext rfl
  have hetwo : e 2 = ⟨2, by omega⟩ := Fin.ext rfl
  have hfzero : f 0 = 1 := by simpa only [f, hezero] using hzero
  have hfone : f 1 = 15 := by simpa only [f, heone] using hone
  have hftwo : f 2 = 20 := by simpa only [f, hetwo] using htwo
  have hsum_last : f 3 + f 4 = 24 := by
    norm_num [Finset.sum_fin_eq_sum_range, Finset.sum_range_succ, hfzero, hfone, hftwo]
      at hsum5
    omega
  fin_cases i
  · exact hzero
  · exact hone
  · exact htwo
  · have hle_three := hle ⟨3, by omega⟩ (Or.inl rfl)
    have hle_four := hle ⟨4, by omega⟩ (Or.inr rfl)
    have hfthree : f 3 = (alternatingGroupFiveClassData.classFinset ⟨3, by omega⟩).card :=
      rfl
    have hffour : f 4 = (alternatingGroupFiveClassData.classFinset ⟨4, by omega⟩).card :=
      rfl
    have hfthree_le : f 3 ≤ 12 := hfthree.trans_le hle_three
    have hffour_le : f 4 ≤ 12 := hffour.trans_le hle_four
    have hfthree_eq : f 3 = 12 := by omega
    exact hfthree.symm.trans hfthree_eq
  · have hle_three := hle ⟨3, by omega⟩ (Or.inl rfl)
    have hle_four := hle ⟨4, by omega⟩ (Or.inr rfl)
    have hfthree : f 3 = (alternatingGroupFiveClassData.classFinset ⟨3, by omega⟩).card :=
      rfl
    have hffour : f 4 = (alternatingGroupFiveClassData.classFinset ⟨4, by omega⟩).card :=
      rfl
    have hfthree_le : f 3 ≤ 12 := hfthree.trans_le hle_three
    have hffour_le : f 4 ≤ 12 := hffour.trans_le hle_four
    have hffour_eq : f 4 = 12 := by omega
    exact hffour.symm.trans hffour_eq

/-- The ordered list of conjugacy-class sizes of `A₅` is `[1, 15, 20, 12, 12]`. -/
@[simp]
theorem card_classes_alternatingGroupFiveClassData :
    alternatingGroupFiveClassData.classes.map Finset.card = [1, 15, 20, 12, 12] := by
  -- `ClassData.classes` is the list packaging of the `Fin`-indexed `classFinset` family.
  change [(alternatingGroupFiveClassData.classFinset ⟨0, by simp⟩).card,
    (alternatingGroupFiveClassData.classFinset ⟨1, by simp⟩).card,
    (alternatingGroupFiveClassData.classFinset ⟨2, by simp⟩).card,
    (alternatingGroupFiveClassData.classFinset ⟨3, by simp⟩).card,
    (alternatingGroupFiveClassData.classFinset ⟨4, by simp⟩).card] = _
  simp

private theorem orderOf_alternatingGroupFiveDoubleTransposition :
    orderOf alternatingGroupFiveDoubleTransposition = 2 := by
  apply orderOf_eq_prime <;> decide

private theorem orderOf_alternatingGroupFiveThreeCycle :
    orderOf alternatingGroupFiveThreeCycle = 3 := by
  apply orderOf_eq_prime <;> decide

private theorem orderOf_alternatingGroupFiveFiveCycle :
    orderOf alternatingGroupFiveFiveCycle = 5 := by
  apply orderOf_eq_prime <;> decide

private theorem alternatingGroupFiveDoubleTransposition_pow_thirty :
    alternatingGroupFiveDoubleTransposition ^ 30 = 1 := by
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [orderOf_alternatingGroupFiveDoubleTransposition]
  decide

private theorem alternatingGroupFiveThreeCycle_pow_thirty :
    alternatingGroupFiveThreeCycle ^ 30 = 1 := by
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [orderOf_alternatingGroupFiveThreeCycle]
  decide

private theorem alternatingGroupFiveFiveCycle_pow_thirty :
    alternatingGroupFiveFiveCycle ^ 30 = 1 := by
  apply orderOf_dvd_iff_pow_eq_one.mp
  rw [orderOf_alternatingGroupFiveFiveCycle]
  decide

private theorem alternatingGroupFiveFiveCycle_sq_pow_thirty :
    (alternatingGroupFiveFiveCycle ^ 2) ^ 30 = 1 := by
  rw [← pow_mul, Nat.mul_comm, pow_mul, alternatingGroupFiveFiveCycle_pow_thirty, one_pow]

/-- The exponent of the alternating group of degree five is thirty. -/
theorem exponent_alternatingGroup_five :
    Monoid.exponent (alternatingGroup (Fin 5)) = 30 := by
  apply Nat.dvd_antisymm
  · rw [Monoid.exponent_dvd_iff_forall_pow_eq_one]
    intro g
    obtain ⟨r, hr, hrg⟩ := alternatingGroupFiveClassData.exists_isConj g
    simp only [reps_alternatingGroupFiveClassData, List.mem_cons, List.not_mem_nil,
      or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · simp [isConj_one_right.mp hrg]
    · exact isConj_one_right.mp
        (alternatingGroupFiveDoubleTransposition_pow_thirty ▸ hrg.pow 30)
    · exact isConj_one_right.mp
        (alternatingGroupFiveThreeCycle_pow_thirty ▸ hrg.pow 30)
    · exact isConj_one_right.mp
        (alternatingGroupFiveFiveCycle_pow_thirty ▸ hrg.pow 30)
    · exact isConj_one_right.mp
        (alternatingGroupFiveFiveCycle_sq_pow_thirty ▸ hrg.pow 30)
  · exact Nat.lcm_dvd
      (orderOf_alternatingGroupFiveDoubleTransposition ▸
        Monoid.order_dvd_exponent alternatingGroupFiveDoubleTransposition)
      (Nat.lcm_dvd
        (orderOf_alternatingGroupFiveThreeCycle ▸
          Monoid.order_dvd_exponent alternatingGroupFiveThreeCycle)
        (orderOf_alternatingGroupFiveFiveCycle ▸
          Monoid.order_dvd_exponent alternatingGroupFiveFiveCycle))

end TauCeti
