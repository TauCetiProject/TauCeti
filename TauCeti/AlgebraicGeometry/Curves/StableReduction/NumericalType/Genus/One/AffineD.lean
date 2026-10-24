/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.Basic
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.DoubleFork
import TauCeti.Algebra.Group.AffineSequence
import Mathlib.Tactic.LinearCombination

/-!
# Affine D numerical types

This file classifies the numerical data on a numerical type whose components form a double fork
of at least six components, all of self-intersection `-2w`. A double fork is a chain
`c 0 - ⋯ - c (t - 1)` with extra leaves `left` and `right` attached to `c 1` and to `c (t - 2)`.
If these `t + 2` components exhaust the numerical type and `t ≥ 4`, all weights agree, every
displayed intersection number is the common weight, the two extra leaves do not meet, and the
multiplicities are `m` at the four ends and `2m` elsewhere. This is the affine `D` configuration
on `t + 2` components in the classification of minimal numerical types of genus one. Its
five-component member, the four-leaf star, is treated in
`TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.Star`.

## Main results

* `TauCeti.NumericalType.IsGenusOneAffineDShape`: the numerical pattern of affine `D`.
* `TauCeti.NumericalType.IsSelfIntersectionMinusTwoFork.isGenusOneAffineDShape`: a double fork of
  at least six components exhausting a numerical type has the affine `D` shape.
* `TauCeti.NumericalType.IsMinimal.isGenusOneAffineDShape`: the same for a minimal numerical type
  of genus one.

## References

* [Stacks Project, Lemma 55.6.2, case (31), Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T).
* The weight calculation uses the proper fork classification
  [Stacks Project, Lemma 55.5.9, Tag 0C8D](https://stacks.math.columbia.edu/tag/0C8D).
-/

public section

namespace TauCeti.NumericalType

open Finset

universe u

variable {T : NumericalType.{u}}

/-- The numerical data of the affine `D` shape among the minimal numerical types of genus one,
for the chain `c 0, …, c (t - 1)` together with the leaves `left` meeting `c 1` and `right`
meeting `c (t - 2)`: all weights and displayed intersection numbers equal a common `w`, the two
leaves do not meet, and the multiplicities are `m` at the four ends and `2m` elsewhere. This
predicate records only these numerical patterns; the double fork structure must be supplied
separately. -/
def IsGenusOneAffineDShape (T : NumericalType) (t : ℕ) (c : ℕ → T.Component)
    (left right : T.Component) : Prop :=
  ∃ w m : ℤ, 0 < w ∧ 0 < m ∧
    (∀ i < t, (T.weight (c i) : ℤ) = w) ∧ (T.weight left : ℤ) = w ∧
    (T.weight right : ℤ) = w ∧
    (∀ i < t, (T.multiplicity (c i) : ℤ) = if i = 0 ∨ i + 1 = t then m else 2 * m) ∧
    (T.multiplicity left : ℤ) = m ∧ (T.multiplicity right : ℤ) = m ∧
    (∀ i, i + 1 < t → T.intersection (c i) (c (i + 1)) = w) ∧
    T.intersection (c 1) left = w ∧ T.intersection (c (t - 2)) right = w ∧
    T.intersection left right = 0

/-- Unfold `IsGenusOneAffineDShape` into the weight, multiplicity and intersection pattern of
the affine `D` case in the genus-one classification. -/
theorem isGenusOneAffineDShape_iff {t : ℕ} {c : ℕ → T.Component} {left right : T.Component} :
    T.IsGenusOneAffineDShape t c left right ↔
      ∃ w m : ℤ, 0 < w ∧ 0 < m ∧
        (∀ i < t, (T.weight (c i) : ℤ) = w) ∧ (T.weight left : ℤ) = w ∧
        (T.weight right : ℤ) = w ∧
        (∀ i < t, (T.multiplicity (c i) : ℤ) = if i = 0 ∨ i + 1 = t then m else 2 * m) ∧
        (T.multiplicity left : ℤ) = m ∧ (T.multiplicity right : ℤ) = m ∧
        (∀ i, i + 1 < t → T.intersection (c i) (c (i + 1)) = w) ∧
        T.intersection (c 1) left = w ∧ T.intersection (c (t - 2)) right = w ∧
        T.intersection left right = 0 :=
  Iff.rfl

/-- If the multiplicities along `c 1, …, c (t - 2)` have vanishing second differences, as the
interior fibre relations of a simply laced chain give, they are affine there: the multiplicity at
`c i` is the one at `c 1` plus `i - 1` times the common difference, which is also the difference
of the multiplicities at `c (t - 2)` and `c (t - 3)`. -/
private lemma multiplicity_eq_add_of_add_eq_two_mul {t : ℕ} {c : ℕ → T.Component}
    (ht : 4 ≤ t)
    (hrec : ∀ i, 1 < i → i + 2 < t →
      (T.multiplicity (c (i - 1)) : ℤ) + T.multiplicity (c (i + 1)) =
        2 * T.multiplicity (c i)) :
    ((T.multiplicity (c 2) : ℤ) - T.multiplicity (c 1) =
        T.multiplicity (c (t - 2)) - T.multiplicity (c (t - 3))) ∧
      ∀ i, 0 < i → i + 1 < t → (T.multiplicity (c i) : ℤ) =
        T.multiplicity (c 1) +
          (i - 1 : ℕ) • ((T.multiplicity (c 2) : ℤ) - T.multiplicity (c 1)) := by
  have hprog := eq_add_nsmul_sub_of_add_eq_two_nsmul (N := t - 2)
    (f := fun j ↦ (T.multiplicity (c (j + 1)) : ℤ)) (fun j hj ↦ by
      have h := hrec (j + 2) (by omega) (by omega)
      rw [show j + 2 - 1 = j + 1 by omega] at h
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      linear_combination h)
  simp only [zero_add, show 1 + 1 = 2 from rfl] at hprog
  refine ⟨?_, fun i hi hit ↦ ?_⟩
  · have h₁ := hprog (t - 3) (by omega)
    have h₂ := hprog (t - 4) (by omega)
    rw [show t - 3 + 1 = t - 2 by omega, show t - 3 = t - 4 + 1 by omega, succ_nsmul] at h₁
    rw [show t - 4 + 1 = t - 3 by omega] at h₂
    linear_combination h₂ - h₁
  · have h := hprog (i - 1) (by omega)
    rwa [Nat.sub_add_cancel (by omega : 1 ≤ i)] at h

namespace IsSelfIntersectionMinusTwoFork

variable {t : ℕ} {c : ℕ → T.Component} {left right : T.Component}

/-- The fibre relation at `x` for a double fork exhausting the numerical type. -/
private lemma sum_add_add_eq_zero (hr : T.IsSelfIntersectionMinusTwoFork t c right)
    (hleft_ne : ∀ i < t, left ≠ c i) (hleftRight : left ≠ right)
    (hcard : Fintype.card T.Component = t + 2) (x : T.Component) :
    ∑ j ∈ range t, T.intersection x (c j) * T.multiplicity (c j) +
      (T.intersection x left * T.multiplicity left +
        T.intersection x right * T.multiplicity right) = 0 := by
  have h := sum_range_add_sum_intersection_mul_multiplicity_eq_zero hr.injOn
    (S := {left, right}) (fun i hi h ↦ by
      rcases mem_insert.mp h with h | h
      · exact hleft_ne i hi h.symm
      · exact hr.branch_ne i hi (mem_singleton.mp h).symm)
    (by rw [card_pair hleftRight]; exact hcard) x
  rwa [sum_pair hleftRight] at h

/-- A double fork of at least six components exhausting a numerical type, all of
self-intersection `-2w`, is the affine `D` configuration: all weights and displayed intersection
numbers agree, the two extra leaves do not meet, and the multiplicities are `m` at the four ends
and `2m` elsewhere. Here `right` meets `c (t - 2)`, and `left` meets `c 1`, the penultimate
component of the reversed chain. -/
theorem isGenusOneAffineDShape (hr : T.IsSelfIntersectionMinusTwoFork t c right)
    (hl : T.IsSelfIntersectionMinusTwoFork t (fun i ↦ c (t - 1 - i)) left)
    (hcard : Fintype.card T.Component = t + 2) (ht : 4 ≤ t) :
    T.IsGenusOneAffineDShape t c left right := by
  have hchainCard : t < Fintype.card T.Component := by omega
  have hleft_ne : ∀ i < t, left ≠ c i := fun _ hi ↦ hl.branch_ne_reverse hi
  have hl0 (i : ℕ) (hi : i < t) (hi1 : i ≠ 1) : T.intersection (c i) left = 0 := by
    simpa only [show t - 1 - (t - 1 - i) = i by omega] using
      hl.branch_intersection_eq_zero (i := t - 1 - i) (by omega) (by omega)
  have hr0 (i : ℕ) (hi : i < t) (hne : i ≠ t - 2) : T.intersection (c i) right = 0 :=
    hr.branch_intersection_eq_zero hi hne
  have hleftRight := hr.opposite_branch_ne hl (by omega)
  -- Deleting either extra leaf leaves a proper fork, which is simply laced.
  obtain ⟨w, hw, hwr, hedge, hredge⟩ := hr.exists_weight_intersection_eq (by omega)
  obtain ⟨w', hw', hwl, -, hledge⟩ := hl.exists_weight_intersection_eq (by omega)
  have hww : (w' : ℤ) = w := by
    have h := hw' 0 (by omega)
    simp only [Nat.sub_zero] at h
    exact h.symm.trans (hw (t - 1) (by omega))
  rw [hww] at hwl hledge
  rw [show t - 1 - (t - 2) = 1 by omega] at hledge
  have hwpos : (0 : ℤ) < w := by simp
  have hedge' (i : ℕ) (hi : 0 < i) (hit : i < t) : T.intersection (c i) (c (i - 1)) = w := by
    rw [T.intersection_comm]
    simpa only [Nat.sub_add_cancel (by omega : 1 ≤ i)] using hedge (i - 1) (by omega)
  have hfib := hr.sum_add_add_eq_zero hleft_ne hleftRight hcard
  -- The fibre relation at an interior chain component, with the chain terms evaluated.
  have hrow (i : ℕ) (hi : 0 < i) (hit : i + 1 < t) :
      (w : ℤ) * T.multiplicity (c (i - 1)) + w * T.multiplicity (c (i + 1)) +
          (T.intersection (c i) left * T.multiplicity left +
            T.intersection (c i) right * T.multiplicity right) =
        2 * w * T.multiplicity (c i) := by
    have h := hfib (c i)
    rw [hr.interior_sum_eq hchainCard _ hi hit] at h
    rw [hedge' i hi (by omega), hr.intersection_self i (by omega), hw i (by omega),
      hedge i hit] at h
    linear_combination h
  -- The interior fibre relations away from the two branch points make the multiplicities affine
  -- along `c 1, …, c (t - 2)`.
  have hrec (i : ℕ) (hi : 1 < i) (hit : i + 2 < t) :
      (T.multiplicity (c (i - 1)) : ℤ) + T.multiplicity (c (i + 1)) =
        2 * T.multiplicity (c i) := by
    have h := hrow i (by omega) (by omega)
    simp only [hl0 i (by omega) (by omega), hr0 i (by omega) (by omega), zero_mul,
      add_zero] at h
    exact mul_left_cancel₀ hwpos.ne' (by linear_combination h)
  obtain ⟨hdiff, hprog⟩ := multiplicity_eq_add_of_add_eq_two_mul ht hrec
  -- The fibre relations at the four ends and at the two branch points then force the leaves not
  -- to meet and the common difference to vanish.
  have h₀ := hfib (c 0)
  rw [hr.left_sum_eq hchainCard (by omega)] at h₀
  simp only [hl0 0 (by omega) (by omega), hr0 0 (by omega) (by omega),
    hr.intersection_self 0 (by omega), hw 0 (by omega), hedge 0 (by omega), zero_mul,
    add_zero] at h₀
  have h₁ := hrow 1 (by omega) (by omega)
  simp only [hledge, hr0 1 (by omega) (by omega), zero_mul, add_zero] at h₁
  have h₂ := hrow (t - 2) (by omega) (by omega)
  simp only [hredge, hl0 (t - 2) (by omega) (by omega), zero_mul, zero_add,
    show t - 2 - 1 = t - 3 by omega, show t - 2 + 1 = t - 1 by omega] at h₂
  have hlastEdge : T.intersection (c (t - 1)) (c (t - 2)) = w := by
    simpa only [show t - 1 - 1 = t - 2 by omega] using hedge' (t - 1) (by omega) (by omega)
  have h₃ := hfib (c (t - 1))
  rw [hr.right_sum_eq hchainCard (by omega)] at h₃
  simp only [hl0 (t - 1) (by omega) (by omega), hr0 (t - 1) (by omega) (by omega), hlastEdge,
    hr.intersection_self (t - 1) (by omega), hw (t - 1) (by omega), zero_mul, add_zero] at h₃
  have hL := hfib left
  rw [sum_eq_single_of_mem 1 (mem_range.mpr (by omega)) (fun j hj hne ↦ by
      rw [T.intersection_comm, hl0 j (mem_range.mp hj) hne, zero_mul]),
    T.intersection_comm left (c 1), hledge, hl.branch_intersection_self, hwl] at hL
  have hR := hfib right
  rw [sum_eq_single_of_mem (t - 2) (mem_range.mpr (by omega)) (fun j hj hne ↦ by
      rw [T.intersection_comm, hr0 j (mem_range.mp hj) hne, zero_mul]),
    T.intersection_comm right (c (t - 2)), hredge, T.intersection_comm right left,
    hr.branch_intersection_self, hwr] at hR
  -- The two leaves do not meet, so the multiplicities are those of affine `D`.
  have hmL : (0 : ℤ) < T.multiplicity left := by simp
  have hmR : (0 : ℤ) < T.multiplicity right := by simp
  have hx : T.intersection left right *
      ((T.multiplicity left : ℤ) + T.multiplicity right) = 0 := by
    linear_combination hL + hR + h₀ + 2 * h₁ + 2 * h₂ + h₃ - 2 * (w : ℤ) * hdiff
  have hx₀ : T.intersection left right = 0 :=
    (mul_eq_zero.mp hx).resolve_right (by omega)
  rw [hx₀] at hL hR
  have hm₁ : (T.multiplicity (c 1) : ℤ) = 2 * T.multiplicity (c 0) :=
    mul_left_cancel₀ hwpos.ne' (by linear_combination h₀)
  have hmL₀ : (T.multiplicity left : ℤ) = T.multiplicity (c 0) :=
    mul_left_cancel₀ (mul_ne_zero two_ne_zero hwpos.ne') (by linear_combination -hL + w * hm₁)
  have hd : (T.multiplicity (c 2) : ℤ) - T.multiplicity (c 1) = 0 :=
    mul_left_cancel₀ hwpos.ne' (by linear_combination h₁ + w * hm₁ - w * hmL₀)
  have hconst (i : ℕ) (hi : 0 < i) (hit : i + 1 < t) :
      (T.multiplicity (c i) : ℤ) = T.multiplicity (c 1) := by
    rw [hprog i hi hit, hd, smul_zero, add_zero]
  have hm₂ := hconst (t - 2) (by omega) (by omega)
  have hlast : (T.multiplicity (c (t - 1)) : ℤ) = T.multiplicity (c 0) :=
    mul_left_cancel₀ (mul_ne_zero two_ne_zero hwpos.ne')
      (by linear_combination -h₃ + w * hm₂ + w * hm₁)
  have hmR₀ : (T.multiplicity right : ℤ) = T.multiplicity (c 0) :=
    mul_left_cancel₀ (mul_ne_zero two_ne_zero hwpos.ne')
      (by linear_combination -hR + w * hm₂ + w * hm₁)
  refine ⟨w, T.multiplicity (c 0), hwpos, by simp, hw, hwl, hwr, fun i hi ↦ ?_, hmL₀, hmR₀,
    hedge, hledge, hredge, hx₀⟩
  split_ifs with hend
  · rcases hend with rfl | hend
    · rfl
    · rw [show i = t - 1 by omega, hlast]
  · rw [hconst i (by omega) (by omega), hm₁]

end IsSelfIntersectionMinusTwoFork

/-- A minimal numerical type of genus one whose components form a double fork of at least six
components, a chain `c 0 - ⋯ - c (t - 1)` with extra leaves `left` meeting `c 1` and `right`
meeting `c (t - 2)`, is the affine `D` configuration. -/
theorem IsMinimal.isGenusOneAffineDShape (hT : T.IsMinimal) (hg : T.arithmeticGenus = 1)
    {t : ℕ} (hcard : Fintype.card T.Component = t + 2) (ht : 4 ≤ t)
    {c : ℕ → T.Component} {left right : T.Component}
    (hinj : ∀ i < t, ∀ j < t, c i = c j → i = j)
    (hpos : ∀ i, i + 1 < t → 0 < T.intersection (c i) (c (i + 1)))
    (hleft_ne : ∀ i < t, left ≠ c i) (hright_ne : ∀ i < t, right ≠ c i)
    (hleft_pos : 0 < T.intersection (c 1) left)
    (hright_pos : 0 < T.intersection (c (t - 2)) right) :
    T.IsGenusOneAffineDShape t c left right := by
  have h₂ := (T.isMinimal_and_arithmeticGenus_eq_one_iff (by omega)).mp ⟨hT, hg⟩
  have hself (i : T.Component) := (T.isMinusTwoIndex_iff.mp (h₂ i)).2
  have hc : T.IsSelfIntersectionMinusTwoChain t c := ⟨hinj, fun i _ ↦ hself (c i), hpos⟩
  exact IsSelfIntersectionMinusTwoFork.isGenusOneAffineDShape
    ⟨hc, by omega, hright_ne, hself right, hright_pos⟩
    ⟨hc.reverse, by omega, fun i hi ↦ hleft_ne (t - 1 - i) (by omega), hself left, by
      simpa only [show t - 1 - (t - 2) = 1 by omega] using hleft_pos⟩
    hcard ht

/-- For a genus-one affine `D` shape whose chain and two branch vertices exhaust all components,
some component's weight divides every weight with quotient at most four, and some component's
multiplicity divides every multiplicity with quotient at most six. -/
lemma IsGenusOneAffineDShape.exists_weight_and_multiplicity_dvd_and_le
    {t : ℕ} {c : ℕ → T.Component} {left right : T.Component}
    (hD : T.IsGenusOneAffineDShape t c left right) (ht : 4 ≤ t)
    (hcard : Fintype.card T.Component = t + 2)
    (hr : T.IsSelfIntersectionMinusTwoFork t c right)
    (hl : T.IsSelfIntersectionMinusTwoFork t (fun i ↦ c (t - 1 - i)) left) :
    (∃ j, ∀ i, (T.weight j : ℕ) ∣ T.weight i ∧ (T.weight i : ℕ) ≤ 4 * T.weight j) ∧
      (∃ j, ∀ i, (T.multiplicity j : ℕ) ∣ T.multiplicity i ∧
        (T.multiplicity i : ℕ) ≤ 6 * T.multiplicity j) := by
  classical
  obtain ⟨w, m, _, _, hw, hwl, hwr, hm, hml, hmr, -⟩ := isGenusOneAffineDShape_iff.mp hD
  refine T.exists_weight_and_multiplicity_dvd_and_le_of_int (nw := 4) (nm := 6)
    left left (fun i ↦ ?_) (fun i ↦ ?_)
  all_goals simp only [← Nat.lt_succ_iff, Nat.exists_lt_succ_right]
  · rcases hr.eq_or_eq_or_exists_lt_eq_of_card_eq hl ht hcard i with rfl | rfl | ⟨k, hk, rfl⟩
    · omega
    · omega
    · have hwk := hw k hk
      omega
  · rcases hr.eq_or_eq_or_exists_lt_eq_of_card_eq hl ht hcard i with rfl | rfl | ⟨k, hk, rfl⟩
    · omega
    · omega
    · have hmk := hm k hk
      split_ifs at hmk <;> omega

end TauCeti.NumericalType
