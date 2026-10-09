/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.Basic
import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.ProperSubgraph
import Mathlib.Tactic.LinearCombination

/-!
# Minimal numerical types of genus one with four components

This file classifies the numerical data of a minimal numerical type of genus one once its four
components have been exhibited as a path or a three-leaf star. Together with the cycle
classification in `TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.Basic`,
these are cases (10)--(15) of the Stacks Project's classification.

A tree on four vertices is either a path or a three-leaf star. For a path `x - y - z - t`, the
three possible unoriented weight patterns are

* `(w, 2w, 2w, 4w)`, with multiplicities `(2m, 2m, 2m, m)`;
* `(w, 2w, 2w, w)`, with constant multiplicity;
* `(2w, w, w, 2w)`, with multiplicities `(m, 2m, 2m, m)`.

For a star with centre `c`, the two possibilities have weights and multiplicities
`(w; w, w, 2w)` and `(2w; 2w, 2w, w)`, with the corresponding affine-Dynkin kernel vectors.
The proofs use the existing two-component `(-2)` classification to factor every positive
intersection number by the weights at its endpoints. The fibre relations then leave exactly the
displayed possibilities.

## References

* [Stacks Project, Lemma 55.6.2, Tag 0C8T](https://stacks.math.columbia.edu/tag/0C8T).
-/

public section

namespace TauCeti

namespace NumericalType

open Finset

universe u

variable {T : NumericalType.{u}}

/-- The endpoint-factor pairs allowed by the two-component `(-2)` classification. -/
private def IsEdgeFactor (p q : ℤ) : Prop :=
  (p = 1 ∧ q = 1) ∨ (p = 2 ∧ q = 1) ∨ (p = 1 ∧ q = 2) ∨
    (p = 3 ∧ q = 1) ∨ (p = 1 ∧ q = 3)

/-- The three unoriented path shapes among the minimal numerical types of genus one with four
components, listed in the order of cases (11)--(13) of Stacks, Tag 0C8T. -/
def IsGenusOneFourPathShape (T : NumericalType) (x y z t : T.Component) : Prop :=
  ((T.weight y : ℤ) = 2 * T.weight x ∧ (T.weight z : ℤ) = 2 * T.weight x ∧
      (T.weight t : ℤ) = 4 * T.weight x ∧
      (T.multiplicity y : ℤ) = T.multiplicity x ∧
      (T.multiplicity z : ℤ) = T.multiplicity x ∧
      (T.multiplicity x : ℤ) = 2 * T.multiplicity t ∧
      T.intersection x y = 2 * T.weight x ∧
      T.intersection y z = 2 * T.weight x ∧
      T.intersection z t = 4 * T.weight x) ∨
    ((T.weight y : ℤ) = 2 * T.weight x ∧ (T.weight z : ℤ) = 2 * T.weight x ∧
      (T.weight t : ℤ) = T.weight x ∧
      (T.multiplicity y : ℤ) = T.multiplicity x ∧
      (T.multiplicity z : ℤ) = T.multiplicity x ∧
      (T.multiplicity t : ℤ) = T.multiplicity x ∧
      T.intersection x y = 2 * T.weight x ∧
      T.intersection y z = 2 * T.weight x ∧
      T.intersection z t = 2 * T.weight x) ∨
    ((T.weight x : ℤ) = 2 * T.weight y ∧ (T.weight z : ℤ) = T.weight y ∧
      (T.weight t : ℤ) = 2 * T.weight y ∧
      (T.multiplicity y : ℤ) = 2 * T.multiplicity x ∧
      (T.multiplicity z : ℤ) = 2 * T.multiplicity x ∧
      (T.multiplicity t : ℤ) = T.multiplicity x ∧
      T.intersection x y = 2 * T.weight y ∧
      T.intersection y z = T.weight y ∧
      T.intersection z t = 2 * T.weight y)

/-- Unfold `IsGenusOneFourPathShape` into its three weight, multiplicity and intersection
patterns. -/
theorem isGenusOneFourPathShape_iff {x y z t : T.Component} :
    T.IsGenusOneFourPathShape x y z t ↔
      ((T.weight y : ℤ) = 2 * T.weight x ∧ (T.weight z : ℤ) = 2 * T.weight x ∧
          (T.weight t : ℤ) = 4 * T.weight x ∧
          (T.multiplicity y : ℤ) = T.multiplicity x ∧
          (T.multiplicity z : ℤ) = T.multiplicity x ∧
          (T.multiplicity x : ℤ) = 2 * T.multiplicity t ∧
          T.intersection x y = 2 * T.weight x ∧
          T.intersection y z = 2 * T.weight x ∧
          T.intersection z t = 4 * T.weight x) ∨
        ((T.weight y : ℤ) = 2 * T.weight x ∧ (T.weight z : ℤ) = 2 * T.weight x ∧
          (T.weight t : ℤ) = T.weight x ∧
          (T.multiplicity y : ℤ) = T.multiplicity x ∧
          (T.multiplicity z : ℤ) = T.multiplicity x ∧
          (T.multiplicity t : ℤ) = T.multiplicity x ∧
          T.intersection x y = 2 * T.weight x ∧
          T.intersection y z = 2 * T.weight x ∧
          T.intersection z t = 2 * T.weight x) ∨
        ((T.weight x : ℤ) = 2 * T.weight y ∧ (T.weight z : ℤ) = T.weight y ∧
          (T.weight t : ℤ) = 2 * T.weight y ∧
          (T.multiplicity y : ℤ) = 2 * T.multiplicity x ∧
          (T.multiplicity z : ℤ) = 2 * T.multiplicity x ∧
          (T.multiplicity t : ℤ) = T.multiplicity x ∧
          T.intersection x y = 2 * T.weight y ∧
          T.intersection y z = T.weight y ∧
          T.intersection z t = 2 * T.weight y) :=
  Iff.rfl

/-- A component of self-intersection `-2w` has a nonnegative intersection number only with
other components. -/
private lemma ne_of_intersection_nonneg {i j : T.Component}
    (hi : T.intersection i i = -(2 * (T.weight i : ℤ))) (h : 0 ≤ T.intersection i j) :
    i ≠ j := by
  rintro rfl
  have := (T.weight i).pos
  omega

/-- The fibre relation when four distinct components exhaust a numerical type. -/
private lemma fiber_relation_of_card_eq_four (hcard : Fintype.card T.Component = 4)
    {i j k l : T.Component} (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k)
    (hjl : j ≠ l) (hkl : k ≠ l) (r : T.Component) :
    (T.multiplicity i : ℤ) * T.intersection r i +
        T.multiplicity j * T.intersection r j + T.multiplicity k * T.intersection r k +
      T.multiplicity l * T.intersection r l = 0 := by
  have hi : i ∉ ({j, k, l} : Finset T.Component) := by simp [hij, hik, hil]
  have hj : j ∉ ({k, l} : Finset T.Component) := by simp [hjk, hjl]
  have hu : (univ : Finset T.Component) = {i, j, k, l} :=
    (eq_univ_of_card _ (by
      rw [card_insert_of_notMem hi, card_insert_of_notMem hj, card_pair hkl, hcard])).symm
  have h := T.fiber_relation r
  rwa [hu, sum_insert hi, sum_insert hj, sum_pair hkl, ← add_assoc, ← add_assoc] at h

/-- The positive weight of a component cancels from an integer equation. -/
private lemma eq_of_weight_mul_eq_weight_mul {r : T.Component} {a b : ℤ}
    (h : T.weight r * a = T.weight r * b) : a = b :=
  mul_left_cancel₀ (by simp) h

/-- A positive intersection between two components of self-intersection `-2w` has one of the
five endpoint-factor pairs in the two-component classification. -/
private lemma exists_edge_factors (hcard : 2 < Fintype.card T.Component) {i j : T.Component}
    (hi : T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hj : T.intersection j j = -(2 * (T.weight j : ℤ)))
    (hij : 0 < T.intersection i j) :
    ∃ p q : ℤ, IsEdgeFactor p q ∧
      T.intersection i j = T.weight i * p ∧ T.intersection i j = T.weight j * q := by
  obtain ⟨w, hmem⟩ := T.exists_weight_intersection_triple_mem hcard hi hj hij
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  rcases hmem with ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩ |
      ⟨h₁, h₂, h₃⟩ | ⟨h₁, h₂, h₃⟩
  · exact ⟨1, 1, by simp [IsEdgeFactor], by omega, by omega⟩
  · exact ⟨2, 1, by simp [IsEdgeFactor], by omega, by omega⟩
  · exact ⟨1, 2, by simp [IsEdgeFactor], by omega, by omega⟩
  · exact ⟨3, 1, by simp [IsEdgeFactor], by omega, by omega⟩
  · exact ⟨1, 3, by simp [IsEdgeFactor], by omega, by omega⟩

/-- The four oriented endpoint-factor patterns compatible with the fibre relations along a
four-vertex path. -/
private lemma path_factor_cases {m₁ m₂ m₃ m₄ p₁ q₁ p₂ q₂ p₃ q₃ : ℤ}
    (hm₁ : 0 < m₁) (hm₃ : 0 < m₃) (hm₄ : 0 < m₄)
    (h₁ : IsEdgeFactor p₁ q₁) (h₂ : IsEdgeFactor p₂ q₂) (h₃ : IsEdgeFactor p₃ q₃)
    (e₁ : m₂ * p₁ = 2 * m₁) (e₂ : m₁ * q₁ + m₃ * p₂ = 2 * m₂)
    (e₃ : m₂ * q₂ + m₄ * p₃ = 2 * m₃) (e₄ : m₃ * q₃ = 2 * m₄) :
    (p₁ = 2 ∧ q₁ = 1 ∧ p₂ = 1 ∧ q₂ = 1 ∧ p₃ = 2 ∧ q₃ = 1) ∨
      (p₁ = 2 ∧ q₁ = 1 ∧ p₂ = 1 ∧ q₂ = 1 ∧ p₃ = 1 ∧ q₃ = 2) ∨
      (p₁ = 1 ∧ q₁ = 2 ∧ p₂ = 1 ∧ q₂ = 1 ∧ p₃ = 2 ∧ q₃ = 1) ∨
      (p₁ = 1 ∧ q₁ = 2 ∧ p₂ = 1 ∧ q₂ = 1 ∧ p₃ = 1 ∧ q₃ = 2) := by
  unfold IsEdgeFactor at h₁ h₂ h₃
  rcases h₁ with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    rcases h₂ with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    rcases h₃ with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    omega

/-- The six labelled endpoint-factor patterns compatible with the fibre relations at a
three-leaf star. -/
private lemma star_factor_cases {m₀ m₁ m₂ m₃ p₁ q₁ p₂ q₂ p₃ q₃ : ℤ}
    (hm₁ : 0 < m₁) (hm₂ : 0 < m₂) (hm₃ : 0 < m₃)
    (h₁ : IsEdgeFactor p₁ q₁) (h₂ : IsEdgeFactor p₂ q₂) (h₃ : IsEdgeFactor p₃ q₃)
    (e₀ : m₁ * p₁ + m₂ * p₂ + m₃ * p₃ = 2 * m₀) (e₁ : m₀ * q₁ = 2 * m₁)
    (e₂ : m₀ * q₂ = 2 * m₂) (e₃ : m₀ * q₃ = 2 * m₃) :
    (p₁ = 2 ∧ q₁ = 1 ∧ p₂ = 1 ∧ q₂ = 1 ∧ p₃ = 1 ∧ q₃ = 1) ∨
      (p₁ = 1 ∧ q₁ = 1 ∧ p₂ = 2 ∧ q₂ = 1 ∧ p₃ = 1 ∧ q₃ = 1) ∨
      (p₁ = 1 ∧ q₁ = 1 ∧ p₂ = 1 ∧ q₂ = 1 ∧ p₃ = 2 ∧ q₃ = 1) ∨
      (p₁ = 1 ∧ q₁ = 2 ∧ p₂ = 1 ∧ q₂ = 1 ∧ p₃ = 1 ∧ q₃ = 1) ∨
      (p₁ = 1 ∧ q₁ = 1 ∧ p₂ = 1 ∧ q₂ = 2 ∧ p₃ = 1 ∧ q₃ = 1) ∨
      (p₁ = 1 ∧ q₁ = 1 ∧ p₂ = 1 ∧ q₂ = 1 ∧ p₃ = 1 ∧ q₃ = 2) := by
  unfold IsEdgeFactor at h₁ h₂ h₃
  rcases h₁ with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    rcases h₂ with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    rcases h₃ with (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;>
    omega

/-- Four components forming a path and having self-intersection `-2w` have one of the three
path shapes in `IsGenusOneFourPathShape`, after possibly reversing the path. -/
theorem isGenusOneFourPathShape_or_isGenusOneFourPathShape
    (hcard : Fintype.card T.Component = 4)
    {i j k l : T.Component} (hi : T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hj : T.intersection j j = -(2 * (T.weight j : ℤ)))
    (hk : T.intersection k k = -(2 * (T.weight k : ℤ)))
    (hl : T.intersection l l = -(2 * (T.weight l : ℤ)))
    (hik0 : T.intersection i k = 0) (hil0 : T.intersection i l = 0)
    (hjl0 : T.intersection j l = 0) (hij0 : 0 < T.intersection i j)
    (hjk0 : 0 < T.intersection j k) (hkl0 : 0 < T.intersection k l) :
    T.IsGenusOneFourPathShape i j k l ∨ T.IsGenusOneFourPathShape l k j i := by
  -- The four components are distinct, so they exhaust `T` and each satisfies a fibre relation.
  have hr := fiber_relation_of_card_eq_four hcard (ne_of_intersection_nonneg hi hij0.le)
    (ne_of_intersection_nonneg hi hik0.ge) (ne_of_intersection_nonneg hi hil0.ge)
    (ne_of_intersection_nonneg hj hjk0.le) (ne_of_intersection_nonneg hj hjl0.ge)
    (ne_of_intersection_nonneg hk hkl0.le)
  have ri := hr i
  have rj := hr j
  have rk := hr k
  have rl := hr l
  rw [hi, hik0, hil0] at ri
  rw [T.intersection_comm j i, hj, hjl0] at rj
  rw [T.intersection_comm k i, hik0, T.intersection_comm k j, hk] at rk
  rw [T.intersection_comm l i, hil0, T.intersection_comm l j, hjl0,
    T.intersection_comm l k, hl] at rl
  -- Each edge factors through its endpoint weights in one of five ways.
  obtain ⟨p₁, q₁, hpq₁, hp₁, hq₁⟩ := exists_edge_factors (by omega) hi hj hij0
  obtain ⟨p₂, q₂, hpq₂, hp₂, hq₂⟩ := exists_edge_factors (by omega) hj hk hjk0
  obtain ⟨p₃, q₃, hpq₃, hp₃, hq₃⟩ := exists_edge_factors (by omega) hk hl hkl0
  -- Cancelling the weights turns the fibre relations into equations on the factors.
  have e₁ : (T.multiplicity j : ℤ) * p₁ = 2 * T.multiplicity i :=
    eq_of_weight_mul_eq_weight_mul (r := i) (by rw [hp₁] at ri; linear_combination ri)
  have e₂ : (T.multiplicity i : ℤ) * q₁ + T.multiplicity k * p₂ = 2 * T.multiplicity j :=
    eq_of_weight_mul_eq_weight_mul (r := j) (by rw [hq₁, hp₂] at rj; linear_combination rj)
  have e₃ : (T.multiplicity j : ℤ) * q₂ + T.multiplicity l * p₃ = 2 * T.multiplicity k :=
    eq_of_weight_mul_eq_weight_mul (r := k) (by rw [hq₂, hp₃] at rk; linear_combination rk)
  have e₄ : (T.multiplicity k : ℤ) * q₃ = 2 * T.multiplicity l :=
    eq_of_weight_mul_eq_weight_mul (r := l) (by rw [hq₃] at rl; linear_combination rl)
  clear ri rj rk rl hr hi hj hk hl hik0 hil0 hjl0 hij0 hjk0 hkl0
  -- Four factor patterns survive; the first three are the three path shapes on `i j k l`, and
  -- the last is the middle shape on the reversed path.
  rcases path_factor_cases (by simp) (by simp) (by simp) hpq₁ hpq₂ hpq₃ e₁ e₂ e₃ e₄ with
    h | h | h | h <;> rw [isGenusOneFourPathShape_iff, isGenusOneFourPathShape_iff] <;>
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · left; left; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  · left; right; left; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  · left; right; right; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega
  · right; left
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, ?_, ?_, ?_⟩
    · rw [T.intersection_comm l k]; omega
    · rw [T.intersection_comm k j]; omega
    · rw [T.intersection_comm j i]; omega

/-- A minimal numerical type of genus one whose four components form the displayed path has one
of the path shapes in cases (11)--(13) of Stacks, Tag 0C8T. -/
theorem isGenusOneFourPathShape_or_isGenusOneFourPathShape_of_isMinimal_and_arithmeticGenus_eq_one
    (hcard : Fintype.card T.Component = 4) (hT : T.IsMinimal) (hg : T.arithmeticGenus = 1)
    {i j k l : T.Component} (hik0 : T.intersection i k = 0)
    (hil0 : T.intersection i l = 0) (hjl0 : T.intersection j l = 0)
    (hij0 : 0 < T.intersection i j) (hjk0 : 0 < T.intersection j k)
    (hkl0 : 0 < T.intersection k l) :
    T.IsGenusOneFourPathShape i j k l ∨ T.IsGenusOneFourPathShape l k j i := by
  have h₂ := (T.isMinimal_and_arithmeticGenus_eq_one_iff (by omega)).mp ⟨hT, hg⟩
  exact isGenusOneFourPathShape_or_isGenusOneFourPathShape hcard
    (T.isMinusTwoIndex_iff.mp (h₂ i)).2 (T.isMinusTwoIndex_iff.mp (h₂ j)).2
    (T.isMinusTwoIndex_iff.mp (h₂ k)).2 (T.isMinusTwoIndex_iff.mp (h₂ l)).2
    hik0 hil0 hjl0 hij0 hjk0 hkl0

/-- The two star shapes among the minimal numerical types of genus one with four components.
The first argument is the centre, and the last argument is the distinguished leaf: it is the
double-weight leaf in case (14) and the half-weight leaf in case (15) of Stacks, Tag 0C8T. -/
def IsGenusOneFourStarShape (T : NumericalType) (c x y z : T.Component) : Prop :=
  ((T.weight x : ℤ) = T.weight c ∧ (T.weight y : ℤ) = T.weight c ∧
      (T.weight z : ℤ) = 2 * T.weight c ∧
      (T.multiplicity c : ℤ) = 2 * T.multiplicity x ∧
      (T.multiplicity y : ℤ) = T.multiplicity x ∧
      (T.multiplicity z : ℤ) = T.multiplicity x ∧
      T.intersection c x = T.weight c ∧ T.intersection c y = T.weight c ∧
      T.intersection c z = 2 * T.weight c) ∨
    ((T.weight x : ℤ) = T.weight c ∧ (T.weight y : ℤ) = T.weight c ∧
      (T.weight c : ℤ) = 2 * T.weight z ∧
      (T.multiplicity c : ℤ) = 2 * T.multiplicity x ∧
      (T.multiplicity y : ℤ) = T.multiplicity x ∧
      (T.multiplicity z : ℤ) = T.multiplicity c ∧
      T.intersection c x = T.weight c ∧ T.intersection c y = T.weight c ∧
      T.intersection c z = T.weight c)

/-- Unfold `IsGenusOneFourStarShape` into its two weight, multiplicity and intersection
patterns. -/
theorem isGenusOneFourStarShape_iff {c x y z : T.Component} :
    T.IsGenusOneFourStarShape c x y z ↔
      ((T.weight x : ℤ) = T.weight c ∧ (T.weight y : ℤ) = T.weight c ∧
          (T.weight z : ℤ) = 2 * T.weight c ∧
          (T.multiplicity c : ℤ) = 2 * T.multiplicity x ∧
          (T.multiplicity y : ℤ) = T.multiplicity x ∧
          (T.multiplicity z : ℤ) = T.multiplicity x ∧
          T.intersection c x = T.weight c ∧ T.intersection c y = T.weight c ∧
          T.intersection c z = 2 * T.weight c) ∨
        ((T.weight x : ℤ) = T.weight c ∧ (T.weight y : ℤ) = T.weight c ∧
          (T.weight c : ℤ) = 2 * T.weight z ∧
          (T.multiplicity c : ℤ) = 2 * T.multiplicity x ∧
          (T.multiplicity y : ℤ) = T.multiplicity x ∧
          (T.multiplicity z : ℤ) = T.multiplicity c ∧
          T.intersection c x = T.weight c ∧ T.intersection c y = T.weight c ∧
          T.intersection c z = T.weight c) :=
  Iff.rfl

/-- Four components forming a three-leaf star and having self-intersection `-2w` have one of the
two star shapes in `IsGenusOneFourStarShape`, after designating a suitable leaf. -/
theorem exists_isGenusOneFourStarShape (hcard : Fintype.card T.Component = 4)
    {c i j k : T.Component} (hc : T.intersection c c = -(2 * (T.weight c : ℤ)))
    (hi : T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hj : T.intersection j j = -(2 * (T.weight j : ℤ)))
    (hk : T.intersection k k = -(2 * (T.weight k : ℤ)))
    (hij0 : T.intersection i j = 0) (hik0 : T.intersection i k = 0)
    (hjk0 : T.intersection j k = 0) (hci0 : 0 < T.intersection c i)
    (hcj0 : 0 < T.intersection c j) (hck0 : 0 < T.intersection c k) :
    ∃ x y z, ({x, y, z} : Finset T.Component) = {i, j, k} ∧
      T.IsGenusOneFourStarShape c x y z := by
  -- The four components are distinct, so they exhaust `T` and each satisfies a fibre relation.
  have hr := fiber_relation_of_card_eq_four hcard (ne_of_intersection_nonneg hc hci0.le)
    (ne_of_intersection_nonneg hc hcj0.le) (ne_of_intersection_nonneg hc hck0.le)
    (ne_of_intersection_nonneg hi hij0.ge) (ne_of_intersection_nonneg hi hik0.ge)
    (ne_of_intersection_nonneg hj hjk0.ge)
  have rc := hr c
  have ri := hr i
  have rj := hr j
  have rk := hr k
  rw [hc] at rc
  rw [T.intersection_comm i c, hi, hij0, hik0] at ri
  rw [T.intersection_comm j c, T.intersection_comm j i, hij0, hj, hjk0] at rj
  rw [T.intersection_comm k c, T.intersection_comm k i, hik0,
    T.intersection_comm k j, hjk0, hk] at rk
  -- Each edge factors through its endpoint weights in one of five ways.
  obtain ⟨p₁, q₁, hpq₁, hp₁, hq₁⟩ := exists_edge_factors (by omega) hc hi hci0
  obtain ⟨p₂, q₂, hpq₂, hp₂, hq₂⟩ := exists_edge_factors (by omega) hc hj hcj0
  obtain ⟨p₃, q₃, hpq₃, hp₃, hq₃⟩ := exists_edge_factors (by omega) hc hk hck0
  -- Cancelling the weights turns the fibre relations into equations on the factors.
  have e₀ : (T.multiplicity i : ℤ) * p₁ + T.multiplicity j * p₂ +
      T.multiplicity k * p₃ = 2 * T.multiplicity c :=
    eq_of_weight_mul_eq_weight_mul (r := c)
      (by rw [hp₁, hp₂, hp₃] at rc; linear_combination rc)
  have e₁ : (T.multiplicity c : ℤ) * q₁ = 2 * T.multiplicity i :=
    eq_of_weight_mul_eq_weight_mul (r := i) (by rw [hq₁] at ri; linear_combination ri)
  have e₂ : (T.multiplicity c : ℤ) * q₂ = 2 * T.multiplicity j :=
    eq_of_weight_mul_eq_weight_mul (r := j) (by rw [hq₂] at rj; linear_combination rj)
  have e₃ : (T.multiplicity c : ℤ) * q₃ = 2 * T.multiplicity k :=
    eq_of_weight_mul_eq_weight_mul (r := k) (by rw [hq₃] at rk; linear_combination rk)
  clear rc ri rj rk hr hc hi hj hk hij0 hik0 hjk0 hci0 hcj0 hck0
  -- Six labelled factor patterns survive; each is one of the two star shapes once the
  -- distinguished leaf is moved to the last position.
  rcases star_factor_cases (by simp) (by simp) (by simp) hpq₁ hpq₂ hpq₃ e₀ e₁ e₂ e₃ with
    h | h | h | h | h | h <;> simp only [isGenusOneFourStarShape_iff] <;>
    rcases h with ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  · exact ⟨j, k, i, by rw [pair_comm k i, insert_comm j i], .inl <| by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega⟩
  · exact ⟨i, k, j, by rw [pair_comm k j], .inl <| by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega⟩
  · exact ⟨i, j, k, rfl, .inl <| by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega⟩
  · exact ⟨j, k, i, by rw [pair_comm k i, insert_comm j i], .inr <| by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega⟩
  · exact ⟨i, k, j, by rw [pair_comm k j], .inr <| by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega⟩
  · exact ⟨i, j, k, rfl, .inr <| by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega⟩

/-- A minimal numerical type of genus one whose four components form the displayed three-leaf
star has one of the star shapes in cases (14) and (15) of Stacks, Tag 0C8T. -/
theorem exists_isGenusOneFourStarShape_of_isMinimal_and_arithmeticGenus_eq_one
    (hcard : Fintype.card T.Component = 4) (hT : T.IsMinimal) (hg : T.arithmeticGenus = 1)
    {c i j k : T.Component} (hij0 : T.intersection i j = 0)
    (hik0 : T.intersection i k = 0) (hjk0 : T.intersection j k = 0)
    (hci0 : 0 < T.intersection c i) (hcj0 : 0 < T.intersection c j)
    (hck0 : 0 < T.intersection c k) :
    ∃ x y z, ({x, y, z} : Finset T.Component) = {i, j, k} ∧
      T.IsGenusOneFourStarShape c x y z := by
  have h₂ := (T.isMinimal_and_arithmeticGenus_eq_one_iff (by omega)).mp ⟨hT, hg⟩
  exact T.exists_isGenusOneFourStarShape hcard (T.isMinusTwoIndex_iff.mp (h₂ c)).2
    (T.isMinusTwoIndex_iff.mp (h₂ i)).2 (T.isMinusTwoIndex_iff.mp (h₂ j)).2
    (T.isMinusTwoIndex_iff.mp (h₂ k)).2 hij0 hik0 hjk0 hci0 hcj0 hck0

end NumericalType

end TauCeti
