/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.Basic
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Fork
import TauCeti.Algebra.Group.AffineSequence
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination

/-!
# Long forks of minimal numerical types of genus one

This file classifies the two arbitrary-length fork families among minimal numerical types of
genus one.  A fork consists of a chain `c 0, ..., c (t - 1)` and an extra leaf at `c (t - 2)`.
When these `t + 1` components exhaust the type and `t >= 5`, the subfork obtained by removing
`c 0` is proper.  Its weights and intersections are therefore simply laced.  The remaining
endpoint has either twice or half the common weight; the fibre relations determine all
multiplicities.

These are cases (29) and (30) of the classification in the Stacks Project.  The first has a
double-weight left endpoint and all other weights equal.  The second has a half-weight left
endpoint and all other weights equal.  In both cases the two leaves at the forked end have the
same multiplicity.

## Main results

* `TauCeti.NumericalType.IsGenusOneLongForkShape` records the two numerical patterns.
* `TauCeti.NumericalType.IsSelfIntersectionMinusTwoFork.isGenusOneLongForkShape` classifies an
  exhaustive fork of length at least five.
* `TauCeti.NumericalType.IsMinimal.isGenusOneLongForkShape` specializes the classification to
  minimal numerical types of arithmetic genus one and also identifies all component genera.

## References

* [Stacks Project, Lemma 55.6.2, cases (29)--(30), Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T).
* The proper-subfork input is
  [Stacks Project, Lemma 55.5.9, Tag 0C8D](https://stacks.math.columbia.edu/tag/0C8D),
  formalized by
  `TauCeti.NumericalType.IsSelfIntersectionMinusTwoFork.exists_weight_intersection_eq`.
-/

public section

namespace TauCeti.NumericalType

universe u

variable {T : NumericalType.{u}} {t : ℕ} {c : ℕ → T.Component} {branch : T.Component}

/-- The two arbitrary-length fork shapes among the minimal numerical types of genus one.

The chain is indexed from its unbranched end; `branch` is the second leaf attached to
`c (t - 2)`, alongside the terminal chain component `c (t - 1)`. -/
def IsGenusOneLongForkShape (T : NumericalType) (t : ℕ) (c : ℕ → T.Component)
    (branch : T.Component) : Prop :=
  ∃ w m : ℤ, 0 < w ∧ 0 < m ∧
    (((∀ i < t, (T.weight (c i) : ℤ) = if i = 0 then 2 * w else w) ∧
        (T.weight branch : ℤ) = w ∧
        (∀ i < t, (T.multiplicity (c i) : ℤ) =
          if i = 0 ∨ i + 1 = t then m else 2 * m) ∧
        (T.multiplicity branch : ℤ) = m ∧
        (∀ i, i + 1 < t → T.intersection (c i) (c (i + 1)) =
          if i = 0 then 2 * w else w) ∧
        T.intersection (c (t - 2)) branch = w) ∨
      ((∀ i < t, (T.weight (c i) : ℤ) = if i = 0 then w else 2 * w) ∧
        (T.weight branch : ℤ) = 2 * w ∧
        (∀ i < t, (T.multiplicity (c i) : ℤ) =
          if i + 1 = t then m else 2 * m) ∧
        (T.multiplicity branch : ℤ) = m ∧
        (∀ i, i + 1 < t → T.intersection (c i) (c (i + 1)) = 2 * w) ∧
        T.intersection (c (t - 2)) branch = 2 * w))

/-- Unfold `IsGenusOneLongForkShape` into the two weight, multiplicity and intersection
patterns of the arbitrary-length fork cases. -/
theorem isGenusOneLongForkShape_iff : T.IsGenusOneLongForkShape t c branch ↔
    ∃ w m : ℤ, 0 < w ∧ 0 < m ∧
      (((∀ i < t, (T.weight (c i) : ℤ) = if i = 0 then 2 * w else w) ∧
          (T.weight branch : ℤ) = w ∧
          (∀ i < t, (T.multiplicity (c i) : ℤ) =
            if i = 0 ∨ i + 1 = t then m else 2 * m) ∧
          (T.multiplicity branch : ℤ) = m ∧
          (∀ i, i + 1 < t → T.intersection (c i) (c (i + 1)) =
            if i = 0 then 2 * w else w) ∧
          T.intersection (c (t - 2)) branch = w) ∨
        ((∀ i < t, (T.weight (c i) : ℤ) = if i = 0 then w else 2 * w) ∧
          (T.weight branch : ℤ) = 2 * w ∧
          (∀ i < t, (T.multiplicity (c i) : ℤ) =
            if i + 1 = t then m else 2 * m) ∧
          (T.multiplicity branch : ℤ) = m ∧
          (∀ i, i + 1 < t → T.intersection (c i) (c (i + 1)) = 2 * w) ∧
          T.intersection (c (t - 2)) branch = 2 * w)) :=
  Iff.rfl

namespace IsSelfIntersectionMinusTwoFork

private lemma end_multiplicities (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    (hcard : Fintype.card T.Component = t + 1) (ht : 4 < t) {W : ℤ} (hW : 0 < W)
    (hw : ∀ i, 0 < i → i < t → (T.weight (c i) : ℤ) = W)
    (hedge : ∀ i, 0 < i → i + 1 < t → T.intersection (c i) (c (i + 1)) = W)
    (hbranchWeight : (T.weight branch : ℤ) = W)
    (hbranchEdge : T.intersection (c (t - 2)) branch = W) :
    (T.multiplicity (c (t - 2)) : ℤ) = 2 * T.multiplicity branch ∧
      (T.multiplicity (c (t - 1)) : ℤ) = T.multiplicity branch ∧
      (T.multiplicity (c (t - 3)) : ℤ) = 2 * T.multiplicity branch := by
  have ht₂ : t - 2 + 1 = t - 1 := by omega
  have ht₃ : t - 3 + 1 = t - 2 := by omega
  have hlastEdge : T.intersection (c (t - 2)) (c (t - 1)) = W := by
    simpa only [ht₂] using hedge (t - 2) (by omega) (by omega)
  have hpreviousEdge : T.intersection (c (t - 3)) (c (t - 2)) = W := by
    simpa only [ht₃] using hedge (t - 3) (by omega) (by omega)
  have hbranch := hf.branch_fiber_relation hcard
  rw [hf.branch_intersection_self, hbranchWeight, T.intersection_comm branch,
    hbranchEdge] at hbranch
  have hpenultimate : (T.multiplicity (c (t - 2)) : ℤ) = 2 * T.multiplicity branch := by
    apply mul_left_cancel₀ hW.ne'
    linear_combination hbranch
  have hlastRel := hf.right_fiber_relation hcard
  rw [T.intersection_comm (c (t - 1)) (c (t - 2)), hlastEdge,
    hf.intersection_self (t - 1) (by omega), hw (t - 1) (by omega) (by omega)] at hlastRel
  have hlast : (T.multiplicity (c (t - 1)) : ℤ) = T.multiplicity branch := by
    nlinarith [hlastRel, hpenultimate]
  have hforkRel := hf.fork_fiber_relation hcard
  rw [T.intersection_comm (c (t - 2)) (c (t - 3)), hpreviousEdge,
    hf.intersection_self (t - 2) (by omega), hw (t - 2) (by omega) (by omega),
    hlastEdge, hbranchEdge] at hforkRel
  have hprevious : (T.multiplicity (c (t - 3)) : ℤ) = 2 * T.multiplicity branch := by
    nlinarith [hforkRel, hpenultimate, hlast]
  exact ⟨hpenultimate, hlast, hprevious⟩

/-- An exhaustive fork of at least five chain components has one of the two arbitrary-length
fork shapes in cases (29) and (30) of Stacks, Tag 0C8T. -/
theorem isGenusOneLongForkShape (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    (hcard : Fintype.card T.Component = t + 1) (ht : 4 < t) :
    T.IsGenusOneLongForkShape t c branch := by
  have hchainCard : t < Fintype.card T.Component := by rw [hcard]; omega
  let c' : ℕ → T.Component := fun i ↦ c (i + 1)
  have hf' : T.IsSelfIntersectionMinusTwoFork (t - 1) c' branch := by
    simpa only [c'] using hf.tail (by omega)
  obtain ⟨w, hw', hbranchWeight, hedge', hbranchEdge⟩ :=
    hf'.exists_weight_intersection_eq (by rw [hcard]; omega)
  let W : ℤ := w
  have hW : 0 < W := by simp [W]
  have hw (i : ℕ) (hi : 0 < i) (hit : i < t) : (T.weight (c i) : ℤ) = W := by
    have := hw' (i - 1) (by omega)
    simpa only [c', Nat.sub_add_cancel hi] using this
  have hedge (i : ℕ) (hi : 0 < i) (hit : i + 1 < t) :
      T.intersection (c i) (c (i + 1)) = W := by
    have := hedge' (i - 1) (by omega)
    simpa only [c', Nat.sub_add_cancel hi] using this
  have hbranchWeight' : (T.weight branch : ℤ) = W := by exact hbranchWeight
  have hbranchEdge' : T.intersection (c (t - 2)) branch = W := by
    have ht₂ : t - 1 - 2 + 1 = t - 2 := by omega
    simpa only [c', ht₂] using hbranchEdge
  obtain ⟨W', -, hint', hleft, -, -⟩ :=
    hf.toIsSelfIntersectionMinusTwoChain.exists_weight_eq_except_one_end hchainCard ht
  have hWW : W' = W := by
    exact (hint' 1 (by omega) (by omega)).symm.trans (hw 1 (by omega) (by omega))
  rw [hWW] at hleft
  have hedge0 : T.intersection (c 0) (c 1) =
      max (T.weight (c 0) : ℤ) W := by
    rw [← hw 1 (by omega) (by omega)]
    exact T.intersection_eq_max_weight (by rw [hcard]; omega)
      (hf.intersection_self 0 (by omega)) (hf.intersection_self 1 (by omega))
      (hf.intersection_succ_pos 0 (by omega))
  have hleftRel := hf.left_fiber_relation hcard
  obtain ⟨hpenultimate, hlast, hprevious⟩ :=
    hf.end_multiplicities hcard ht hW hw hedge hbranchWeight' hbranchEdge'
  have hrec (i : ℕ) (hi : i + 3 < t)
      (hedgeLeft : T.intersection (c i) (c (i + 1)) = W) :
      (T.multiplicity (c i) : ℤ) + T.multiplicity (c (i + 2)) =
        2 * T.multiplicity (c (i + 1)) := by
    have h := hf.interior_fiber_relation hcard (i := i + 1) (by omega) (by omega) (by omega)
    rw [Nat.add_sub_cancel, T.intersection_comm (c (i + 1)) (c i), hedgeLeft,
      hf.intersection_self (i + 1) (by omega), hw (i + 1) (by omega) (by omega),
      hedge (i + 1) (by omega) (by omega)] at h
    nlinarith only [h, hW]
  rcases hleft with hleft | hleft | hleft
  · -- Equal endpoint weights would force linearly increasing multiplicities, contradicting
    -- the equal last two interior multiplicities imposed by the forked end.
    have hedge0' : T.intersection (c 0) (c 1) = W := by
      rw [hedge0, hleft, max_self]
    have hm1 : (T.multiplicity (c 1) : ℤ) = 2 * T.multiplicity (c 0) := by
      rw [hf.intersection_self 0 (by omega), hleft, hedge0'] at hleftRel
      nlinarith only [hleftRel, hW]
    have haffine := eq_add_nsmul_sub_of_add_eq_two_nsmul
      (N := t - 1) (f := fun i ↦ (T.multiplicity (c i) : ℤ))
      (fun i hi ↦ hrec i (by omega) (by
        by_cases hi0 : i = 0
        · simpa only [hi0] using hedge0'
        · exact hedge i (by omega) (by omega)))
    have hmPrev := haffine (t - 3) (by omega)
    have hmPen := haffine (t - 2) (by omega)
    rw [hm1, hprevious] at hmPrev
    rw [hm1, hpenultimate] at hmPen
    have htstep : t - 2 = (t - 3) + 1 := by omega
    rw [htstep, add_nsmul, one_nsmul] at hmPen
    have hm0pos : (0 : ℤ) < T.multiplicity (c 0) := by simp
    have hm0zero : (2 * (T.multiplicity (c 0) : ℤ) - T.multiplicity (c 0)) = 0 := by
      omega
    exfalso
    omega
  · -- A double-weight endpoint gives case (29).
    have hedge0' : T.intersection (c 0) (c 1) = 2 * W := by
      rw [hedge0, hleft, max_eq_left (by omega)]
    have hm1 : (T.multiplicity (c 1) : ℤ) = 2 * T.multiplicity (c 0) := by
      rw [hf.intersection_self 0 (by omega), hleft, hedge0'] at hleftRel
      nlinarith only [hleftRel, hW]
    have hm2 : (T.multiplicity (c 2) : ℤ) = 2 * T.multiplicity (c 0) := by
      have h := hf.interior_fiber_relation hcard (i := 1) (by omega) (by omega) (by omega)
      rw [Nat.sub_self, T.intersection_comm (c 1) (c 0), hedge0',
        hf.intersection_self 1 (by omega), hw 1 (by omega) (by omega),
        hedge 1 (by omega) (by omega), hm1] at h
      nlinarith only [h, hW]
    have hconst (i : ℕ) (hi : 0 < i) (hit : i < t - 1) :
        (T.multiplicity (c i) : ℤ) = 2 * T.multiplicity (c 0) := by
      have h := eq_add_nsmul_sub_of_add_eq_two_nsmul
        (N := t - 2) (f := fun j ↦ (T.multiplicity (c (j + 1)) : ℤ))
        (fun j hj ↦ hrec (j + 1) (by omega) (hedge (j + 1) (by omega) (by omega)))
        (i - 1) (by omega)
      simp only [Nat.sub_add_cancel hi, Nat.zero_add, hm1, hm2,
        sub_self, smul_zero, add_zero] at h
      exact h
    have hm0 : (T.multiplicity (c 0) : ℤ) = T.multiplicity branch := by
      nlinarith only [hconst (t - 2) (by omega) (by omega), hpenultimate]
    refine ⟨W, T.multiplicity branch, hW, by simp, .inl ⟨?_, hbranchWeight', ?_, rfl, ?_,
      hbranchEdge'⟩⟩
    · intro i hi
      by_cases hi0 : i = 0
      · simp [hi0, hleft]
      · simp only [hi0, ↓reduceIte]
        exact hw i (by omega) hi
    · intro i hi
      by_cases hend : i = 0 ∨ i + 1 = t
      · simp only [hend, ↓reduceIte]
        rcases hend with rfl | hend
        · exact hm0
        · obtain rfl : i = t - 1 := by omega
          exact hlast
      · simp only [hend, ↓reduceIte]
        rw [hconst i (by omega) (by omega), hm0]
    · intro i hi
      by_cases hi0 : i = 0
      · simpa only [hi0, ↓reduceIte] using hedge0'
      · simp only [hi0, ↓reduceIte]
        exact hedge i (by omega) hi
  · -- A half-weight endpoint gives case (30).
    have hedge0' : T.intersection (c 0) (c 1) = W := by
      rw [hedge0, max_eq_right]
      omega
    have hm1 : (T.multiplicity (c 1) : ℤ) = T.multiplicity (c 0) := by
      rw [hf.intersection_self 0 (by omega), hedge0'] at hleftRel
      nlinarith only [hleftRel, hleft, hW]
    have hconst (i : ℕ) (hi : i < t - 1) :
        (T.multiplicity (c i) : ℤ) = T.multiplicity (c 0) := by
      have h := eq_add_nsmul_sub_of_add_eq_two_nsmul
        (N := t - 1) (f := fun j ↦ (T.multiplicity (c j) : ℤ))
        (fun j hj ↦ hrec j (by omega) (by
          by_cases hj0 : j = 0
          · simpa only [hj0] using hedge0'
          · exact hedge j (by omega) (by omega))) i hi
      rw [hm1, sub_self, smul_zero, add_zero] at h
      exact h
    have hm0 : (T.multiplicity (c 0) : ℤ) = 2 * T.multiplicity branch := by
      nlinarith only [hconst (t - 2) (by omega), hpenultimate]
    refine ⟨T.weight (c 0), T.multiplicity branch, by simp, by simp, .inr ⟨?_, ?_, ?_, rfl,
      ?_, ?_⟩⟩
    · intro i hi
      by_cases hi0 : i = 0
      · simp [hi0]
      · simp only [hi0, ↓reduceIte]
        rw [hw i (by omega) hi]
        exact hleft.symm
    · rw [hbranchWeight']
      exact hleft.symm
    · intro i hi
      by_cases hilast : i + 1 = t
      · simp only [hilast, ↓reduceIte]
        obtain rfl : i = t - 1 := by omega
        exact hlast
      · simp only [hilast, ↓reduceIte]
        rw [hconst i (by omega), hm0]
    · intro i hi
      by_cases hi0 : i = 0
      · simpa only [hi0] using hedge0'.trans hleft.symm
      · rw [hedge i (by omega) hi]
        exact hleft.symm
    · rw [hbranchEdge']
      exact hleft.symm

end IsSelfIntersectionMinusTwoFork

/-- A minimal numerical type of arithmetic genus one whose components form an exhaustive fork
of length at least five has the numerical data of cases (29) or (30) of Stacks, Tag 0C8T.  Every
component has genus zero. -/
theorem IsMinimal.isGenusOneLongForkShape (hT : T.IsMinimal) (hg : T.arithmeticGenus = 1)
    (hf : T.IsSelfIntersectionMinusTwoFork t c branch)
    (hcard : Fintype.card T.Component = t + 1) (ht : 4 < t) :
    (∀ i < t, T.genus (c i) = 0) ∧ T.genus branch = 0 ∧
      T.IsGenusOneLongForkShape t c branch := by
  have htwo := (T.isMinimal_and_arithmeticGenus_eq_one_iff (by rw [hcard]; omega)).mp ⟨hT, hg⟩
  exact ⟨fun i hi ↦ (T.isMinusTwoIndex_iff.mp (htwo (c i))).1,
    (T.isMinusTwoIndex_iff.mp (htwo branch)).1, hf.isGenusOneLongForkShape hcard ht⟩

/-- For a genus-one long fork on a minus-two fork exhausting all components, some component's
weight divides every weight with quotient at most four, and some component's multiplicity
divides every multiplicity with quotient at most six. -/
lemma IsGenusOneLongForkShape.exists_weight_and_multiplicity_dvd_and_le
    (hfork : T.IsGenusOneLongForkShape t c branch)
    (hcard : Fintype.card T.Component = t + 1)
    (hf : T.IsSelfIntersectionMinusTwoFork t c branch) :
    (∃ j, ∀ i, (T.weight j : ℕ) ∣ T.weight i ∧ (T.weight i : ℕ) ≤ 4 * T.weight j) ∧
      (∃ j, ∀ i, (T.multiplicity j : ℕ) ∣ T.multiplicity i ∧
        (T.multiplicity i : ℕ) ≤ 6 * T.multiplicity j) := by
  classical
  have ht := hf.two_lt
  obtain ⟨w, m, _, _, ⟨hw, hwb, hm, hmb, -⟩ | ⟨hw, hwb, hm, hmb, -⟩⟩ :=
    isGenusOneLongForkShape_iff.mp hfork
  · refine T.exists_weight_and_multiplicity_dvd_and_le_of_int (nw := 4) (nm := 6) branch branch
      (fun i ↦ ?_) (fun i ↦ ?_)
    all_goals simp only [← Nat.lt_succ_iff, Nat.exists_lt_succ_right]
    · rcases hf.eq_or_exists_lt_eq_of_card_eq hcard i with rfl | ⟨k, hk, rfl⟩
      · omega
      · have hwk := hw k hk; split_ifs at hwk <;> omega
    · rcases hf.eq_or_exists_lt_eq_of_card_eq hcard i with rfl | ⟨k, hk, rfl⟩
      · omega
      · have hmk := hm k hk; split_ifs at hmk <;> omega
  · refine T.exists_weight_and_multiplicity_dvd_and_le_of_int (nw := 4) (nm := 6)
      (c 0) branch (fun i ↦ ?_) (fun i ↦ ?_)
    all_goals simp only [← Nat.lt_succ_iff, Nat.exists_lt_succ_right]
    · have hw0 := hw 0 (by omega); simp only [↓reduceIte] at hw0
      rcases hf.eq_or_exists_lt_eq_of_card_eq hcard i with rfl | ⟨k, hk, rfl⟩
      · omega
      · have hwk := hw k hk; split_ifs at hwk <;> omega
    · rcases hf.eq_or_exists_lt_eq_of_card_eq hcard i with rfl | ⟨k, hk, rfl⟩
      · omega
      · have hmk := hm k hk; split_ifs at hmk <;> omega

end TauCeti.NumericalType
