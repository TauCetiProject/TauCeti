/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Classification
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.AffineD
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.AffineE6
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.AffineE7
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.AffineE8
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.FiveComponents
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.FiveFork
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.FourComponents
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.LongFork
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.LongPath
public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.Genus.One.Star
import Mathlib.Tactic.ITauto
import Mathlib.Tactic.IntervalCases

/-!
# Classification of minimal numerical types of genus one

This file combines the structural classification imported from `NumericalType.Classification`
with the per-shape classifications of paths, forks, stars, cycles, and affine `D` and `E` diagrams.
It yields the full list of minimal numerical types of arithmetic genus one
([Stacks, Lemma 55.6.2](https://stacks.math.columbia.edu/tag/0C8T)), together with uniform
divisibility and ratio bounds on their multiplicities and weights.

## Main results

* `TauCeti.NumericalType.IsGenusOneMinimalShape` and
  `TauCeti.NumericalType.isGenusOneMinimalShape_iff_isMinimal_and_arithmeticGenus_eq_one`:
  the complete classification of minimal numerical types of arithmetic genus one ([Stacks, Lemma 55.6.2](https://stacks.math.columbia.edu/tag/0C8T)).
* `TauCeti.NumericalType.IsMinimal.exists_multiplicity_dvd_and_le_six_mul` and
  `TauCeti.NumericalType.IsMinimal.exists_weight_dvd_and_le_four_mul`: in a minimal numerical type
  of genus one, the minimum multiplicity divides every multiplicity with quotient at most `6`, and
  the minimum weight divides every weight with quotient at most `4`.
-/

public section

namespace TauCeti.NumericalType

open Finset

universe u

variable {T : NumericalType.{u}}

/-! ### Complete classification of minimal numerical types of genus one -/

/-- The fifteen shape families into which the 34 minimal numerical types of arithmetic genus one
([Stacks, Lemma 55.6.2](https://stacks.math.columbia.edu/tag/0C8T)) organize:

* Case (1): a single component of component genus one;
* Cases (2)--(3): two rational components of shape `IsGenusOnePairShape`;
* Cases (4), (10), (16), (25): a cycle of rational components (`0 < T.topologicalGenus`) with
  constant weights and multiplicities, each meeting two others with intersection number equal to
  the common weight;
* Cases (5)--(9): three rational components forming a chain of shape `IsGenusOneChainShape`;
* Cases (11)--(13): four rational components forming a path of shape `IsGenusOneFourPathShape`;
* Cases (14)--(15): four rational components forming a three-leaf star of shape
  `IsGenusOneFourStarShape`;
* Cases (17)--(21): five rational components forming a path of shape `IsGenusOneFivePathShape`;
* Case (22): five rational components forming a four-leaf star (affine `D₄`);
* Cases (23)--(24): five rational components forming a fork;
* Cases (26)--(28): `n ≥ 6` rational components forming a path of shape `IsGenusOneLongPathShape`;
* Cases (29)--(30): `t + 1 ≥ 6` rational components forming a fork of shape
  `IsGenusOneLongForkShape`;
* Case (31): `t + 2 ≥ 6` rational components forming a double fork of shape
  `IsGenusOneAffineDShape`;
* Case (32): seven rational components forming an affine `E₆` configuration;
* Case (33): eight rational components forming an affine `E₇` configuration;
* Case (34): nine rational components forming an affine `E₈` configuration. -/
def IsGenusOneMinimalShape (T : NumericalType.{u}) : Prop :=
  (Fintype.card T.Component = 1 ∧ ∀ i, T.genus i = 1 ∧ T.intersection i i = 0) ∨
  ((∀ i, T.genus i = 0 ∧ T.intersection i i = -(2 * (T.weight i : ℤ))) ∧
    (T.IsGenusOneCycleShape ∨
      (Fintype.card T.Component = 2 ∧ ∃ x y, x ≠ y ∧ T.IsGenusOnePairShape x y) ∨
      (Fintype.card T.Component = 3 ∧
        ∃ x j z, x ≠ j ∧ x ≠ z ∧ j ≠ z ∧ T.intersection x z = 0 ∧
          T.IsGenusOneChainShape x j z) ∨
      (Fintype.card T.Component = 4 ∧ ∃ c, T.IsSelfIntersectionMinusTwoChain 4 c ∧
        (∀ i < 4, ∀ j < 4, i ≠ j → i + 1 ≠ j → j + 1 ≠ i → T.intersection (c i) (c j) = 0) ∧
        T.IsGenusOneFourPathShape (c 0) (c 1) (c 2) (c 3)) ∨
      (Fintype.card T.Component = 4 ∧ ∃ c₀ x y z,
        ({c₀, x, y, z} : Finset T.Component) = univ ∧
        T.intersection x y = 0 ∧ T.intersection x z = 0 ∧ T.intersection y z = 0 ∧
        T.IsGenusOneFourStarShape c₀ x y z) ∨
      (Fintype.card T.Component = 5 ∧ ∃ c, T.IsSelfIntersectionMinusTwoChain 5 c ∧
        (∀ i < 5, ∀ j < 5, i ≠ j → i + 1 ≠ j → j + 1 ≠ i → T.intersection (c i) (c j) = 0) ∧
        T.IsGenusOneFivePathShape (c 0) (c 1) (c 2) (c 3) (c 4)) ∨
      T.IsGenusOneFourLeafStarShape ∨
      T.IsGenusOneFiveForkShape ∨
      (∃ n c, 6 ≤ n ∧ Fintype.card T.Component = n ∧ T.IsSelfIntersectionMinusTwoChain n c ∧
        (∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i → T.intersection (c i) (c j) = 0) ∧
        T.IsGenusOneLongPathShape n c) ∨
      (∃ t c b, 5 ≤ t ∧ Fintype.card T.Component = t + 1 ∧
        T.IsSelfIntersectionMinusTwoFork t c b ∧ T.IsGenusOneLongForkShape t c b) ∨
      (∃ t c left right, 4 ≤ t ∧ Fintype.card T.Component = t + 2 ∧
        T.IsSelfIntersectionMinusTwoFork t c right ∧
        T.IsSelfIntersectionMinusTwoFork t (fun i ↦ c (t - 1 - i)) left ∧
        T.IsGenusOneAffineDShape t c left right) ∨
      T.IsGenusOneAffineE6Shape ∨
      T.IsGenusOneAffineE7Shape ∨
      T.IsGenusOneAffineE8Shape))

/-- A minimal genus-one shape is either a single genus-one component or one of the
rational-component shape alternatives, with their complete numerical data. -/
theorem isGenusOneMinimalShape_iff : T.IsGenusOneMinimalShape ↔
  (Fintype.card T.Component = 1 ∧ ∀ i, T.genus i = 1 ∧ T.intersection i i = 0) ∨
  ((∀ i, T.genus i = 0 ∧ T.intersection i i = -(2 * (T.weight i : ℤ))) ∧
    (T.IsGenusOneCycleShape ∨
      (Fintype.card T.Component = 2 ∧ ∃ x y, x ≠ y ∧ T.IsGenusOnePairShape x y) ∨
      (Fintype.card T.Component = 3 ∧
        ∃ x j z, x ≠ j ∧ x ≠ z ∧ j ≠ z ∧ T.intersection x z = 0 ∧
          T.IsGenusOneChainShape x j z) ∨
      (Fintype.card T.Component = 4 ∧ ∃ c, T.IsSelfIntersectionMinusTwoChain 4 c ∧
        (∀ i < 4, ∀ j < 4, i ≠ j → i + 1 ≠ j → j + 1 ≠ i → T.intersection (c i) (c j) = 0) ∧
        T.IsGenusOneFourPathShape (c 0) (c 1) (c 2) (c 3)) ∨
      (Fintype.card T.Component = 4 ∧ ∃ c₀ x y z,
        ({c₀, x, y, z} : Finset T.Component) = univ ∧
        T.intersection x y = 0 ∧ T.intersection x z = 0 ∧ T.intersection y z = 0 ∧
        T.IsGenusOneFourStarShape c₀ x y z) ∨
      (Fintype.card T.Component = 5 ∧ ∃ c, T.IsSelfIntersectionMinusTwoChain 5 c ∧
        (∀ i < 5, ∀ j < 5, i ≠ j → i + 1 ≠ j → j + 1 ≠ i → T.intersection (c i) (c j) = 0) ∧
        T.IsGenusOneFivePathShape (c 0) (c 1) (c 2) (c 3) (c 4)) ∨
      T.IsGenusOneFourLeafStarShape ∨
      T.IsGenusOneFiveForkShape ∨
      (∃ n c, 6 ≤ n ∧ Fintype.card T.Component = n ∧ T.IsSelfIntersectionMinusTwoChain n c ∧
        (∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i → T.intersection (c i) (c j) = 0) ∧
        T.IsGenusOneLongPathShape n c) ∨
      (∃ t c b, 5 ≤ t ∧ Fintype.card T.Component = t + 1 ∧
        T.IsSelfIntersectionMinusTwoFork t c b ∧ T.IsGenusOneLongForkShape t c b) ∨
      (∃ t c left right, 4 ≤ t ∧ Fintype.card T.Component = t + 2 ∧
        T.IsSelfIntersectionMinusTwoFork t c right ∧
        T.IsSelfIntersectionMinusTwoFork t (fun i ↦ c (t - 1 - i)) left ∧
        T.IsGenusOneAffineDShape t c left right) ∨
      T.IsGenusOneAffineE6Shape ∨
      T.IsGenusOneAffineE7Shape ∨
      T.IsGenusOneAffineE8Shape)) := Iff.rfl

/-- Introduce the singleton family in the minimal genus-one classification. -/
lemma IsGenusOneMinimalShape.of_singleton
    (hshape : Fintype.card T.Component = 1 ∧ ∀ i, T.genus i = 1 ∧ T.intersection i i = 0) :
    T.IsGenusOneMinimalShape := by
  rw [isGenusOneMinimalShape_iff]
  itauto

/-- Introduce the cycle family in the minimal genus-one classification. -/
lemma IsGenusOneMinimalShape.of_cycle
    (hindices : ∀ i, T.genus i = 0 ∧ T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hshape : T.IsGenusOneCycleShape) : T.IsGenusOneMinimalShape := by
  rw [isGenusOneMinimalShape_iff]
  itauto

/-- Introduce the pair family in the minimal genus-one classification. -/
lemma IsGenusOneMinimalShape.of_pair
    (hindices : ∀ i, T.genus i = 0 ∧ T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hshape : Fintype.card T.Component = 2 ∧ ∃ x y, x ≠ y ∧ T.IsGenusOnePairShape x y) :
    T.IsGenusOneMinimalShape := by
  rw [isGenusOneMinimalShape_iff]
  itauto

/-- Introduce the chain family in the minimal genus-one classification. -/
lemma IsGenusOneMinimalShape.of_chain
    (hindices : ∀ i, T.genus i = 0 ∧ T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hshape : Fintype.card T.Component = 3 ∧
        ∃ x j z, x ≠ j ∧ x ≠ z ∧ j ≠ z ∧ T.intersection x z = 0 ∧
          T.IsGenusOneChainShape x j z) : T.IsGenusOneMinimalShape := by
  rw [isGenusOneMinimalShape_iff]
  itauto

/-- Introduce the four-component path family in the minimal genus-one classification. -/
lemma IsGenusOneMinimalShape.of_fourPath
    (hindices : ∀ i, T.genus i = 0 ∧ T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hshape : Fintype.card T.Component = 4 ∧ ∃ c, T.IsSelfIntersectionMinusTwoChain 4 c ∧
        (∀ i < 4, ∀ j < 4, i ≠ j → i + 1 ≠ j → j + 1 ≠ i → T.intersection (c i) (c j) = 0) ∧
        T.IsGenusOneFourPathShape (c 0) (c 1) (c 2) (c 3)) : T.IsGenusOneMinimalShape := by
  rw [isGenusOneMinimalShape_iff]
  itauto

/-- Introduce the four-component star family in the minimal genus-one classification. -/
lemma IsGenusOneMinimalShape.of_fourStar
    (hindices : ∀ i, T.genus i = 0 ∧ T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hshape : Fintype.card T.Component = 4 ∧ ∃ c₀ x y z,
        ({c₀, x, y, z} : Finset T.Component) = univ ∧
        T.intersection x y = 0 ∧ T.intersection x z = 0 ∧ T.intersection y z = 0 ∧
        T.IsGenusOneFourStarShape c₀ x y z) : T.IsGenusOneMinimalShape := by
  rw [isGenusOneMinimalShape_iff]
  itauto

/-- Introduce the five-component path family in the minimal genus-one classification. -/
lemma IsGenusOneMinimalShape.of_fivePath
    (hindices : ∀ i, T.genus i = 0 ∧ T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hshape : Fintype.card T.Component = 5 ∧ ∃ c, T.IsSelfIntersectionMinusTwoChain 5 c ∧
        (∀ i < 5, ∀ j < 5, i ≠ j → i + 1 ≠ j → j + 1 ≠ i → T.intersection (c i) (c j) = 0) ∧
        T.IsGenusOneFivePathShape (c 0) (c 1) (c 2) (c 3) (c 4)) : T.IsGenusOneMinimalShape := by
  rw [isGenusOneMinimalShape_iff]
  itauto

/-- Introduce the four-leaf star family in the minimal genus-one classification. -/
lemma IsGenusOneMinimalShape.of_fourLeafStar
    (hindices : ∀ i, T.genus i = 0 ∧ T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hshape : T.IsGenusOneFourLeafStarShape) :
    T.IsGenusOneMinimalShape := by
  rw [isGenusOneMinimalShape_iff]
  itauto

/-- Introduce the five-component fork family in the minimal genus-one classification. -/
lemma IsGenusOneMinimalShape.of_fiveFork
    (hindices : ∀ i, T.genus i = 0 ∧ T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hshape : T.IsGenusOneFiveForkShape) : T.IsGenusOneMinimalShape := by
  rw [isGenusOneMinimalShape_iff]
  itauto

/-- Introduce the long path family in the minimal genus-one classification. -/
lemma IsGenusOneMinimalShape.of_longPath
    (hindices : ∀ i, T.genus i = 0 ∧ T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hshape : ∃ n c, 6 ≤ n ∧ Fintype.card T.Component = n ∧ T.IsSelfIntersectionMinusTwoChain n c ∧
        (∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i → T.intersection (c i) (c j) = 0) ∧
        T.IsGenusOneLongPathShape n c) : T.IsGenusOneMinimalShape := by
  rw [isGenusOneMinimalShape_iff]
  itauto

/-- Introduce the long fork family in the minimal genus-one classification. -/
lemma IsGenusOneMinimalShape.of_longFork
    (hindices : ∀ i, T.genus i = 0 ∧ T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hshape : ∃ t c b, 5 ≤ t ∧ Fintype.card T.Component = t + 1 ∧
        T.IsSelfIntersectionMinusTwoFork t c b ∧ T.IsGenusOneLongForkShape t c b) :
    T.IsGenusOneMinimalShape := by
  rw [isGenusOneMinimalShape_iff]
  itauto

/-- Introduce the affine D family in the minimal genus-one classification. -/
lemma IsGenusOneMinimalShape.of_affineD
    (hindices : ∀ i, T.genus i = 0 ∧ T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hshape : ∃ t c left right, 4 ≤ t ∧ Fintype.card T.Component = t + 2 ∧
        T.IsSelfIntersectionMinusTwoFork t c right ∧
        T.IsSelfIntersectionMinusTwoFork t (fun i ↦ c (t - 1 - i)) left ∧
        T.IsGenusOneAffineDShape t c left right) : T.IsGenusOneMinimalShape := by
  rw [isGenusOneMinimalShape_iff]
  itauto

/-- Introduce the affine E₆ family in the minimal genus-one classification. -/
lemma IsGenusOneMinimalShape.of_affineE6
    (hindices : ∀ i, T.genus i = 0 ∧ T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hshape : T.IsGenusOneAffineE6Shape) :
    T.IsGenusOneMinimalShape := by
  rw [isGenusOneMinimalShape_iff]
  itauto

/-- Introduce the affine E₇ family in the minimal genus-one classification. -/
lemma IsGenusOneMinimalShape.of_affineE7
    (hindices : ∀ i, T.genus i = 0 ∧ T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hshape : T.IsGenusOneAffineE7Shape) :
    T.IsGenusOneMinimalShape := by
  rw [isGenusOneMinimalShape_iff]
  itauto

/-- Introduce the affine E₈ family in the minimal genus-one classification. -/
lemma IsGenusOneMinimalShape.of_affineE8
    (hindices : ∀ i, T.genus i = 0 ∧ T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hshape : T.IsGenusOneAffineE8Shape) :
    T.IsGenusOneMinimalShape := by
  rw [isGenusOneMinimalShape_iff]
  itauto

/-- An exhaustive chain of at least two components has one of the genus-one path shapes.
The chain length selects the finite classifications up to five components and the long-path
classification thereafter; reversing the chain preserves its nonconsecutive zero intersections. -/
lemma IsGenusOneMinimalShape.of_exhaustive_chain {t : ℕ} {c : ℕ → T.Component}
    (hindices : ∀ i, T.genus i = 0 ∧ T.intersection i i = -(2 * (T.weight i : ℤ)))
    (ht2 : 2 ≤ t) (hcard : Fintype.card T.Component = t)
    (hc : T.IsSelfIntersectionMinusTwoChain t c)
    (hzero : ∀ i < t, ∀ j < t, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      T.intersection (c i) (c j) = 0) : T.IsGenusOneMinimalShape := by
  have hself (i : T.Component) := (hindices i).2
  rcases lt_or_ge t 6 with ht6 | ht6
  · interval_cases t
    · obtain ⟨x, y, hxy, hshape⟩ :=
        T.exists_weight_multiplicity_intersection_eq_of_card_eq_two hcard
          (hc.ne (i := 0) (j := 1) (by omega) (by omega) (by omega)) (hself _) (hself _)
      refine IsGenusOneMinimalShape.of_pair hindices ⟨hcard, x, y, ?_, hshape⟩
      rcases hxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hc.ne (by omega) (by omega) (by omega)
      · exact hc.ne (by omega) (by omega) (by omega)
    · obtain ⟨x, z, hxz, hshape⟩ :=
        T.exists_weight_multiplicity_intersection_eq_of_card_eq_three hcard
          (hc.ne (i := 0) (j := 1) (by omega) (by omega) (by omega))
          (hc.ne (i := 0) (j := 2) (by omega) (by omega) (by omega))
          (hc.ne (i := 1) (j := 2) (by omega) (by omega) (by omega))
          (hself _) (hself _) (hself _)
          (hzero 0 (by omega) 2 (by omega) (by omega) (by omega) (by omega))
      refine IsGenusOneMinimalShape.of_chain hindices ⟨hcard, x, c 1, z, ?_⟩
      rcases hxz with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact ⟨hc.ne (by omega) (by omega) (by omega), hc.ne (by omega) (by omega) (by omega),
          hc.ne (by omega) (by omega) (by omega),
          hzero 0 (by omega) 2 (by omega) (by omega) (by omega) (by omega), hshape⟩
      · refine ⟨hc.ne (by omega) (by omega) (by omega), hc.ne (by omega) (by omega) (by omega),
          hc.ne (by omega) (by omega) (by omega), ?_, hshape⟩
        rw [T.intersection_comm]
        exact hzero 0 (by omega) 2 (by omega) (by omega) (by omega) (by omega)
    · rcases T.isGenusOneFourPathShape_or_isGenusOneFourPathShape hcard
          (hself _) (hself _) (hself _) (hself _)
          (hzero 0 (by omega) 2 (by omega) (by omega) (by omega) (by omega))
          (hzero 0 (by omega) 3 (by omega) (by omega) (by omega) (by omega))
          (hzero 1 (by omega) 3 (by omega) (by omega) (by omega) (by omega))
          (hc.intersection_succ_pos 0 (by omega)) (hc.intersection_succ_pos 1 (by omega))
          (hc.intersection_succ_pos 2 (by omega)) with h4 | h4
      · exact IsGenusOneMinimalShape.of_fourPath hindices ⟨hcard, c, hc, hzero, h4⟩
      · exact IsGenusOneMinimalShape.of_fourPath hindices
          ⟨hcard, fun i ↦ c (4 - 1 - i), hc.reverse,
            intersection_reverse_eq_zero_of_nonconsecutive hzero, h4⟩
    · rcases T.isGenusOneFivePathShape_or_isGenusOneFivePathShape hcard
          (hself _) (hself _) (hself _) (hself _) (hself _)
          (hzero 0 (by omega) 2 (by omega) (by omega) (by omega) (by omega))
          (hzero 0 (by omega) 3 (by omega) (by omega) (by omega) (by omega))
          (hzero 0 (by omega) 4 (by omega) (by omega) (by omega) (by omega))
          (hzero 1 (by omega) 3 (by omega) (by omega) (by omega) (by omega))
          (hzero 1 (by omega) 4 (by omega) (by omega) (by omega) (by omega))
          (hzero 2 (by omega) 4 (by omega) (by omega) (by omega) (by omega))
          (hc.intersection_succ_pos 0 (by omega)) (hc.intersection_succ_pos 1 (by omega))
          (hc.intersection_succ_pos 2 (by omega)) (hc.intersection_succ_pos 3 (by omega))
          with h5 | h5
      · exact IsGenusOneMinimalShape.of_fivePath hindices ⟨hcard, c, hc, hzero, h5⟩
      · exact IsGenusOneMinimalShape.of_fivePath hindices
          ⟨hcard, fun i ↦ c (5 - 1 - i), hc.reverse,
            intersection_reverse_eq_zero_of_nonconsecutive hzero, h5⟩
  · rcases T.isGenusOneLongPathShape_or_isGenusOneLongPathShape hcard ht6 hc hzero with
      hlong | hlong
    · exact IsGenusOneMinimalShape.of_longPath hindices ⟨t, c, ht6, hcard, hc, hzero, hlong⟩
    · exact IsGenusOneMinimalShape.of_longPath hindices
        ⟨t, fun i ↦ c (t - 1 - i), ht6, hcard, hc.reverse,
          intersection_reverse_eq_zero_of_nonconsecutive hzero, hlong⟩

/-- An exhaustive fork has one of the genus-one fork shapes. Chain lengths three and four
use the four-component star and five-component fork classifications; longer forks use the
long-fork classification. The five-component equivalence is constructed only in its case. -/
lemma IsGenusOneMinimalShape.of_exhaustive_fork {t : ℕ} {c : ℕ → T.Component}
    {b : T.Component}
    (hindices : ∀ i, T.genus i = 0 ∧ T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hcard : Fintype.card T.Component = t + 1)
    (hf : T.IsSelfIntersectionMinusTwoFork t c b) : T.IsGenusOneMinimalShape := by
  classical
  have hself (i : T.Component) := (hindices i).2
  have ht3 := hf.two_lt
  rcases lt_or_ge t 5 with ht5 | ht5
  · interval_cases t
    · -- `t = 3`: three-leaf star on `4` components.
      have hz02 := hf.intersection_eq_zero (by omega) (p := 0) (q := 2)
        (by omega) (by omega) (by omega) (by omega) (by omega)
      have hz0b := hf.branch_intersection_eq_zero (i := 0) (by omega) (by omega)
      have hz2b := hf.branch_intersection_eq_zero (i := 2) (by omega) (by omega)
      obtain ⟨x, y, z, -, huniv, -, -, -, hxy0, hxz0, hyz0, hstar⟩ :=
        T.exists_isGenusOneFourStarShape hcard
        (hself (c 1)) (hself (c 0)) (hself (c 2)) (hself b) hz02 hz0b hz2b
        (by rw [T.intersection_comm]; exact hf.intersection_succ_pos 0 (by omega))
        (hf.intersection_succ_pos 1 (by omega)) hf.branch_intersection_pos
      exact IsGenusOneMinimalShape.of_fourStar hindices
        ⟨hcard, c 1, x, y, z, huniv, hxy0, hxz0, hyz0, hstar⟩
    · -- `t = 4`: five-component fork.
      let e : Fin 5 ≃ T.Component := hf.equivFinOfCardEq hcard
      have he0 : e 0 = c 0 := by simp [e, hf.equivFinOfCardEq_apply]
      have he1 : e 1 = c 1 := by simp [e, hf.equivFinOfCardEq_apply]
      have he2 : e 2 = c 2 := by simp [e, hf.equivFinOfCardEq_apply]
      have he3 : e 3 = c 3 := by simp [e, hf.equivFinOfCardEq_apply]
      have he4 : e 4 = b := by simp [e, hf.equivFinOfCardEq_apply]
      have hz02 : T.intersection (e 0) (e 2) = 0 := by
        rw [he0, he2]
        exact hf.intersection_eq_zero (by omega) (p := 0) (q := 2)
          (by omega) (by omega) (by omega) (by omega) (by omega)
      have hz03 : T.intersection (e 0) (e 3) = 0 := by
        rw [he0, he3]
        exact hf.intersection_eq_zero (by omega) (p := 0) (q := 3)
          (by omega) (by omega) (by omega) (by omega) (by omega)
      have hz04 : T.intersection (e 0) (e 4) = 0 := by
        rw [he0, he4]
        exact hf.branch_intersection_eq_zero (i := 0) (by omega) (by omega)
      obtain ⟨hT, hg⟩ := (T.isMinimal_and_arithmeticGenus_eq_one_iff (by omega)).mpr
        (fun i ↦ T.isMinusTwoIndex_iff.mpr (hindices i))
      obtain ⟨-, w, m, hfive⟩ := hT.exists_weight_multiplicity_intersection_eq_fiveFork hg e
        (by rw [he0, he1]; exact hf.intersection_succ_pos 0 (by omega))
        (by rw [he1, he2]; exact hf.intersection_succ_pos 1 (by omega))
        (by rw [he2, he3]; exact hf.intersection_succ_pos 2 (by omega))
        (by rw [he2, he4]; exact hf.branch_intersection_pos) hz02 hz03 hz04
      exact IsGenusOneMinimalShape.of_fiveFork hindices
        (isGenusOneFiveForkShape_iff.mpr ⟨e, w, m, hfive⟩)
  · -- `t ≥ 5`: long fork.
    exact IsGenusOneMinimalShape.of_longFork hindices
      ⟨t, c, b, ht5, hcard, hf, hf.isGenusOneLongForkShape hcard (by omega)⟩

/-- **Classification of minimal numerical types of genus one**
([Stacks, Lemma 55.6.2](https://stacks.math.columbia.edu/tag/0C8T)). Every minimal numerical type
of arithmetic genus one belongs to one of the shape families of
`TauCeti.NumericalType.IsGenusOneMinimalShape`. -/
theorem IsMinimal.isGenusOneMinimalShape (hT : T.IsMinimal) (hg : T.arithmeticGenus = 1) :
    T.IsGenusOneMinimalShape := by
  classical
  by_cases hcard1 : Fintype.card T.Component = 1
  · exact IsGenusOneMinimalShape.of_singleton
      ⟨hcard1, fun i ↦ ⟨(T.arithmeticGenus_eq_one_iff_of_card_eq_one hcard1 i).mp hg,
      T.intersection_eq_zero_of_card_eq_one hcard1 i i⟩⟩
  have h1lt : 1 < Fintype.card T.Component := by
    have := Fintype.card_pos (α := T.Component)
    omega
  have hminusTwo := (T.isMinimal_and_arithmeticGenus_eq_one_iff h1lt).mp ⟨hT, hg⟩
  have hgen (i : T.Component) : T.genus i = 0 := (T.isMinusTwoIndex_iff.mp (hminusTwo i)).1
  have hself (i : T.Component) : T.intersection i i = -(2 * (T.weight i : ℤ)) :=
    (T.isMinusTwoIndex_iff.mp (hminusTwo i)).2
  have hself_ge (i : T.Component) : -(2 * (T.weight i : ℤ)) ≤ T.intersection i i := (hself i).ge
  have hindices : ∀ i, T.genus i = 0 ∧ T.intersection i i = -(2 * (T.weight i : ℤ)) :=
    fun i ↦ ⟨hgen i, hself i⟩
  rcases T.topologicalGenus_pos_or_exists_chain_or_fork_or_star_or_affine hself with
    htop | ⟨t, c, ht2, hcard, hc, hzero⟩ | ⟨t, c, b, hcard, hf⟩ |
      ⟨c₀, l, hl, hadj⟩ | ⟨t, c, left, right, ht4, hcard, hr, hl⟩ |
      ⟨l, hl, hadj⟩ | ⟨l, hl, hadj⟩ | ⟨l, hl, hadj⟩
  · -- Cycle case.
    exact IsGenusOneMinimalShape.of_cycle hindices (isGenusOneCycleShape_iff.mpr ⟨htop,
      fun i j ↦ ⟨T.weight_eq_of_topologicalGenus_pos hself_ge htop i j,
        T.multiplicity_eq_of_topologicalGenus_pos hself_ge htop i j⟩,
      T.ncard_neighborSet_eq_two_of_topologicalGenus_pos hself_ge htop,
      fun i j hij ↦ T.intersection_eq_weight_of_topologicalGenus_pos hself_ge htop hij⟩)
  · exact IsGenusOneMinimalShape.of_exhaustive_chain hindices ht2 hcard hc hzero
  · exact IsGenusOneMinimalShape.of_exhaustive_fork hindices hcard hf
  · -- Four-leaf star (affine `D₄`).
    obtain ⟨e, he0, hel, hw, hm, ha⟩ :=
      T.exists_equiv_fourLeafStar c₀ l hl (hself c₀) (fun i ↦ hself (l i)) hadj
    exact IsGenusOneMinimalShape.of_fourLeafStar hindices
      (isGenusOneFourLeafStarShape_iff.mpr
        ⟨e, by simpa [he0] using hw, by simpa [hel 0] using hm, by simpa [he0] using ha⟩)
  · -- Double fork (affine `Dₙ`, `n ≥ 5`).
    exact IsGenusOneMinimalShape.of_affineD hindices
      ⟨t, c, left, right, ht4, hcard, hr, hl, hr.isGenusOneAffineDShape hl hcard ht4⟩
  · -- Affine `E₆`.
    obtain ⟨e, he, hw, hm, ha⟩ := T.exists_equiv_affineE6 l hl (fun i ↦ hself (l i)) hadj
    exact IsGenusOneMinimalShape.of_affineE6 hindices
      (isGenusOneAffineE6Shape_iff.mpr
        ⟨e, by simpa [he 0] using hw, by simpa [he 2] using hm, by simpa [he 0] using ha⟩)
  · -- Affine `E₇`.
    obtain ⟨e, he, hw, hm, ha⟩ := T.exists_equiv_affineE7 l hl (fun i ↦ hself (l i)) hadj
    exact IsGenusOneMinimalShape.of_affineE7 hindices
      ((isGenusOneAffineE7Shape_iff T).mpr
        ⟨e, by simpa [he 0] using hw, by simpa [he 4] using hm, by simpa [he 0] using ha⟩)
  · -- Affine `E₈`.
    obtain ⟨e, he, hw, hm, ha⟩ := T.exists_equiv_affineE8 l hl (fun i ↦ hself (l i)) hadj
    exact IsGenusOneMinimalShape.of_affineE8 hindices
      ((isGenusOneAffineE8Shape_iff T).mpr
        ⟨e, by simpa [he 0] using hw, by simpa [he 8] using hm, by simpa [he 0] using ha⟩)

/-- The displayed shape families characterize minimal numerical types of arithmetic genus one. -/
theorem isGenusOneMinimalShape_iff_isMinimal_and_arithmeticGenus_eq_one :
    T.IsGenusOneMinimalShape ↔ T.IsMinimal ∧ T.arithmeticGenus = 1 := by
  constructor
  · intro h
    rcases isGenusOneMinimalShape_iff.mp h with ⟨hcard, hgen⟩ | ⟨hindices, -⟩
    · obtain ⟨i⟩ := T.componentNonempty
      exact ⟨T.isMinimal_of_card_eq_one hcard,
        (T.arithmeticGenus_eq_one_iff_of_card_eq_one hcard i).mpr (hgen i).1⟩
    · exact (T.isMinimal_and_arithmeticGenus_eq_one_iff
        (T.one_lt_card_of_intersection_self_eq fun i ↦ (hindices i).2)).mpr
          fun i ↦ T.isMinusTwoIndex_iff.mpr (hindices i)
  · rintro ⟨hT, hg⟩
    exact hT.isGenusOneMinimalShape hg

/-! ### Divisibility and ratio bounds for weights and multiplicities -/

/-- Every shape in `IsGenusOneMinimalShape` has a minimum-weight component dividing all weights
with quotient at most `4`, and a minimum-multiplicity component dividing all multiplicities with
quotient at most `6`. -/
private lemma exists_weight_and_multiplicity_dvd_and_le (h : T.IsGenusOneMinimalShape) :
    (∃ j, ∀ i, (T.weight j : ℕ) ∣ T.weight i ∧ (T.weight i : ℕ) ≤ 4 * T.weight j) ∧
      (∃ j, ∀ i, (T.multiplicity j : ℕ) ∣ T.multiplicity i ∧
        (T.multiplicity i : ℕ) ≤ 6 * T.multiplicity j) := by
  classical
  obtain ⟨j₀⟩ := (inferInstance : Nonempty T.Component)
  rcases isGenusOneMinimalShape_iff.mp h with ⟨hcard1, -⟩ | ⟨-,
    hcycle |
    ⟨hcard, x, y, hxy, h2⟩ |
    ⟨hcard, x, j, z, hxj, hxz, hjz, -, h3⟩ |
    ⟨hcard, c, hc, -, h4⟩ |
    ⟨-, c₀, x, y, z, huniv, -, -, -, hstar⟩ |
    ⟨hcard, c, hc, -, h5⟩ |
    hstar | hfive |
    ⟨n, c, hn, hcard, hc, -, hlong⟩ |
    ⟨t, c, b, ht, hcard, hf, hfork⟩ |
    ⟨t, c, left, right, ht, hcard, hr, hl, hD⟩ |
    hE6 | hE7 | hE8⟩
  · exact T.exists_weight_and_multiplicity_dvd_and_le_of_int (nw := 4) (nm := 6) j₀ j₀
      (fun i ↦ ⟨1, by decide, by rw [Fintype.card_le_one_iff.mp hcard1.le i j₀]; simp⟩)
      (fun i ↦ ⟨1, by decide, by rw [Fintype.card_le_one_iff.mp hcard1.le i j₀]; simp⟩)
  · exact hcycle.exists_weight_and_multiplicity_dvd_and_le
  · exact h2.exists_weight_and_multiplicity_dvd_and_le hcard hxy
  · exact h3.exists_weight_and_multiplicity_dvd_and_le hcard hxj hxz hjz
  · apply h4.exists_weight_and_multiplicity_dvd_and_le
    apply eq_univ_of_forall
    intro i
    obtain ⟨k, hk, rfl⟩ := hc.exists_lt_eq_of_card_eq hcard i
    interval_cases k <;> simp
  · exact hstar.exists_weight_and_multiplicity_dvd_and_le huniv
  · apply h5.exists_weight_and_multiplicity_dvd_and_le
    apply eq_univ_of_forall
    intro i
    obtain ⟨k, hk, rfl⟩ := hc.exists_lt_eq_of_card_eq hcard i
    interval_cases k <;> simp
  · exact hstar.exists_weight_and_multiplicity_dvd_and_le
  · exact hfive.exists_weight_and_multiplicity_dvd_and_le
  · exact hlong.exists_weight_and_multiplicity_dvd_and_le (by omega) hcard hc
  · exact hfork.exists_weight_and_multiplicity_dvd_and_le hcard hf
  · exact hD.exists_weight_and_multiplicity_dvd_and_le ht hcard hr hl
  · exact hE6.exists_weight_and_multiplicity_dvd_and_le
  · exact hE7.exists_weight_and_multiplicity_dvd_and_le
  · exact hE8.exists_weight_and_multiplicity_dvd_and_le

/-- In any numerical type satisfying `IsGenusOneMinimalShape`, there is a component whose weight
divides every component's weight with quotient at most `4`. -/
theorem IsGenusOneMinimalShape.exists_weight_dvd_and_le_four_mul
    (h : T.IsGenusOneMinimalShape) :
    ∃ j, ∀ i, (T.weight j : ℕ) ∣ T.weight i ∧ (T.weight i : ℕ) ≤ 4 * T.weight j :=
  (exists_weight_and_multiplicity_dvd_and_le h).1

/-- In any numerical type satisfying `IsGenusOneMinimalShape`, there is a component whose
multiplicity divides every component's multiplicity with quotient at most `6`. -/
theorem IsGenusOneMinimalShape.exists_multiplicity_dvd_and_le_six_mul
    (h : T.IsGenusOneMinimalShape) :
    ∃ j, ∀ i, (T.multiplicity j : ℕ) ∣ T.multiplicity i ∧
      (T.multiplicity i : ℕ) ≤ 6 * T.multiplicity j :=
  (exists_weight_and_multiplicity_dvd_and_le h).2

/-- In a minimal numerical type of arithmetic genus one, there is a component whose weight divides
every component's weight with quotient at most `4`
([Stacks, Lemma 55.6.2](https://stacks.math.columbia.edu/tag/0C8T)). -/
theorem IsMinimal.exists_weight_dvd_and_le_four_mul
    (hT : T.IsMinimal) (hg : T.arithmeticGenus = 1) :
    ∃ j, ∀ i, (T.weight j : ℕ) ∣ T.weight i ∧ (T.weight i : ℕ) ≤ 4 * T.weight j :=
  (hT.isGenusOneMinimalShape hg).exists_weight_dvd_and_le_four_mul

/-- In a minimal numerical type of arithmetic genus one, there is a component whose multiplicity
divides every component's multiplicity with quotient at most `6`
([Stacks, Lemma 55.6.2](https://stacks.math.columbia.edu/tag/0C8T)). -/
theorem IsMinimal.exists_multiplicity_dvd_and_le_six_mul
    (hT : T.IsMinimal) (hg : T.arithmeticGenus = 1) :
    ∃ j, ∀ i, (T.multiplicity j : ℕ) ∣ T.multiplicity i ∧
      (T.multiplicity i : ℕ) ≤ 6 * T.multiplicity j :=
  (hT.isGenusOneMinimalShape hg).exists_multiplicity_dvd_and_le_six_mul

end TauCeti.NumericalType
