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
import TauCeti.Data.PNat.Bounds
import Mathlib.Tactic.IntervalCases

/-!
# Classification of minimal numerical types of genus one

This file assembles the graph-shape and numerical classification of minimal numerical types of
arithmetic genus one ([Stacks, Lemma 55.6.2](https://stacks.math.columbia.edu/tag/0C8T)).

Combining this structural classification with the per-shape classifications of paths, forks, stars,
cycles, and affine `D` and `E` diagrams yields the full list of minimal numerical types of genus
one, together with uniform divisibility and ratio bounds on their multiplicities and weights.

## Main results

* `TauCeti.NumericalType.exists_chain_or_fork_or_star_or_affine_of_topologicalGenus_eq_zero`:
  structural classification of tree-shaped numerical types whose components have self-intersection
  `-2w`.
* `TauCeti.NumericalType.topologicalGenus_pos_or_exists_chain_or_fork_or_star_or_affine`:
  the same without the tree assumption, including the cycle case `0 < T.topologicalGenus`.
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

open Finset _root_.Matrix

universe u

variable {T : NumericalType.{u}}

/-! ### Complete classification of minimal numerical types of genus one -/

/-- The twelve shape families into which the 34 minimal numerical types of arithmetic genus one
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
* Cases (32)--(34): seven, eight, or nine rational components forming an affine `E₆`, `E₇`, or
  `E₈` configuration. -/
def IsGenusOneMinimalShape (T : NumericalType.{u}) : Prop :=
  (Fintype.card T.Component = 1 ∧ ∀ i, T.genus i = 1 ∧ T.intersection i i = 0) ∨
  ((∀ i, T.genus i = 0 ∧ T.intersection i i = -(2 * (T.weight i : ℤ))) ∧
    ((0 < T.topologicalGenus ∧
        (∀ i j, T.weight i = T.weight j ∧ T.multiplicity i = T.multiplicity j) ∧
        (∀ i, (T.intersectionGraph.neighborSet i).ncard = 2) ∧
        ∀ i j, T.Adj i j → T.intersection i j = T.weight i) ∨
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
      (∃ e : Option (Fin 4) ≃ T.Component,
        (∀ v, T.weight (e v) = T.weight (e none)) ∧
        (∀ v, (T.multiplicity (e v) : ℤ) =
          if v = none then 2 * (T.multiplicity (e (some 0)) : ℤ)
          else T.multiplicity (e (some 0))) ∧
        (∀ v w, T.intersection (e v) (e w) =
          if v = w then -(2 * (T.weight (e none) : ℤ))
          else if v = none ∨ w = none then T.weight (e none) else 0)) ∨
      (∃ e : Fin 5 ≃ T.Component, ∃ w m : ℕ+,
        ((∀ i, (T.weight (e i) : ℤ) = ![2 * (w : ℤ), w, w, w, w] i) ∧
          (∀ i, (T.multiplicity (e i) : ℤ) = ![(m : ℤ), 2 * m, 2 * m, m, m] i) ∧
          (∀ i j, T.intersection (e i) (e j) =
            !![-4 * (w : ℤ), 2 * w, 0, 0, 0;
               2 * w, -2 * w, w, 0, 0;
               0, w, -2 * w, w, w;
               0, 0, w, -2 * w, 0;
               0, 0, w, 0, -2 * w] i j)) ∨
        ((∀ i, (T.weight (e i) : ℤ) = ![(w : ℤ), 2 * w, 2 * w, 2 * w, 2 * w] i) ∧
          (∀ i, (T.multiplicity (e i) : ℤ) = ![2 * (m : ℤ), 2 * m, 2 * m, m, m] i) ∧
          (∀ i j, T.intersection (e i) (e j) =
            !![-2 * (w : ℤ), 2 * w, 0, 0, 0;
               2 * w, -4 * w, 2 * w, 0, 0;
               0, 2 * w, -4 * w, 2 * w, 2 * w;
               0, 0, 2 * w, -4 * w, 0;
               0, 0, 2 * w, 0, -4 * w] i j))) ∨
      (∃ n c, 6 ≤ n ∧ Fintype.card T.Component = n ∧ T.IsSelfIntersectionMinusTwoChain n c ∧
        (∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i → T.intersection (c i) (c j) = 0) ∧
        T.IsGenusOneLongPathShape n c) ∨
      (∃ t c b, 5 ≤ t ∧ Fintype.card T.Component = t + 1 ∧
        T.IsSelfIntersectionMinusTwoFork t c b ∧ T.IsGenusOneLongForkShape t c b) ∨
      (∃ t c left right, 4 ≤ t ∧ Fintype.card T.Component = t + 2 ∧
        T.IsSelfIntersectionMinusTwoFork t c right ∧
        T.IsSelfIntersectionMinusTwoFork t (fun i ↦ c (t - 1 - i)) left ∧
        T.IsGenusOneAffineDShape t c left right) ∨
      (∃ e : Fin 7 ≃ T.Component,
        (∀ i, T.weight (e i) = T.weight (e 0)) ∧
        (∀ i, (T.multiplicity (e i) : ℤ) =
          (T.multiplicity (e 2) : ℤ) * AffineDynkinType.E6.marks i) ∧
        (∀ i j, T.intersection (e i) (e j) =
          -(T.weight (e 0) : ℤ) * AffineDynkinType.E6.cartanMatrix i j)) ∨
      (∃ e : Fin 8 ≃ T.Component,
        (∀ i, T.weight (e i) = T.weight (e 0)) ∧
        (∀ i, (T.multiplicity (e i) : ℤ) =
          AffineDynkinType.E7.marks i * T.multiplicity (e 4)) ∧
        (∀ i j, T.intersection (e i) (e j) =
          -(T.weight (e 0) : ℤ) * AffineDynkinType.E7.cartanMatrix i j)) ∨
      (∃ e : Fin 9 ≃ T.Component,
        (∀ i, T.weight (e i) = T.weight (e 0)) ∧
        (∀ i, (T.multiplicity (e i) : ℤ) =
          AffineDynkinType.E8.marks i * T.multiplicity (e 8)) ∧
        (∀ i j, T.intersection (e i) (e j) =
          -(T.weight (e 0) : ℤ) * AffineDynkinType.E8.cartanMatrix i j))))

/-- A minimal genus-one shape is either a single genus-one component or one of the
rational-component shape alternatives, with their complete numerical data. -/
theorem isGenusOneMinimalShape_iff : T.IsGenusOneMinimalShape ↔
  (Fintype.card T.Component = 1 ∧ ∀ i, T.genus i = 1 ∧ T.intersection i i = 0) ∨
  ((∀ i, T.genus i = 0 ∧ T.intersection i i = -(2 * (T.weight i : ℤ))) ∧
    ((0 < T.topologicalGenus ∧
        (∀ i j, T.weight i = T.weight j ∧ T.multiplicity i = T.multiplicity j) ∧
        (∀ i, (T.intersectionGraph.neighborSet i).ncard = 2) ∧
        ∀ i j, T.Adj i j → T.intersection i j = T.weight i) ∨
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
      (∃ e : Option (Fin 4) ≃ T.Component,
        (∀ v, T.weight (e v) = T.weight (e none)) ∧
        (∀ v, (T.multiplicity (e v) : ℤ) =
          if v = none then 2 * (T.multiplicity (e (some 0)) : ℤ)
          else T.multiplicity (e (some 0))) ∧
        (∀ v w, T.intersection (e v) (e w) =
          if v = w then -(2 * (T.weight (e none) : ℤ))
          else if v = none ∨ w = none then T.weight (e none) else 0)) ∨
      (∃ e : Fin 5 ≃ T.Component, ∃ w m : ℕ+,
        ((∀ i, (T.weight (e i) : ℤ) = ![2 * (w : ℤ), w, w, w, w] i) ∧
          (∀ i, (T.multiplicity (e i) : ℤ) = ![(m : ℤ), 2 * m, 2 * m, m, m] i) ∧
          (∀ i j, T.intersection (e i) (e j) =
            !![-4 * (w : ℤ), 2 * w, 0, 0, 0;
               2 * w, -2 * w, w, 0, 0;
               0, w, -2 * w, w, w;
               0, 0, w, -2 * w, 0;
               0, 0, w, 0, -2 * w] i j)) ∨
        ((∀ i, (T.weight (e i) : ℤ) = ![(w : ℤ), 2 * w, 2 * w, 2 * w, 2 * w] i) ∧
          (∀ i, (T.multiplicity (e i) : ℤ) = ![2 * (m : ℤ), 2 * m, 2 * m, m, m] i) ∧
          (∀ i j, T.intersection (e i) (e j) =
            !![-2 * (w : ℤ), 2 * w, 0, 0, 0;
               2 * w, -4 * w, 2 * w, 0, 0;
               0, 2 * w, -4 * w, 2 * w, 2 * w;
               0, 0, 2 * w, -4 * w, 0;
               0, 0, 2 * w, 0, -4 * w] i j))) ∨
      (∃ n c, 6 ≤ n ∧ Fintype.card T.Component = n ∧ T.IsSelfIntersectionMinusTwoChain n c ∧
        (∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i → T.intersection (c i) (c j) = 0) ∧
        T.IsGenusOneLongPathShape n c) ∨
      (∃ t c b, 5 ≤ t ∧ Fintype.card T.Component = t + 1 ∧
        T.IsSelfIntersectionMinusTwoFork t c b ∧ T.IsGenusOneLongForkShape t c b) ∨
      (∃ t c left right, 4 ≤ t ∧ Fintype.card T.Component = t + 2 ∧
        T.IsSelfIntersectionMinusTwoFork t c right ∧
        T.IsSelfIntersectionMinusTwoFork t (fun i ↦ c (t - 1 - i)) left ∧
        T.IsGenusOneAffineDShape t c left right) ∨
      (∃ e : Fin 7 ≃ T.Component,
        (∀ i, T.weight (e i) = T.weight (e 0)) ∧
        (∀ i, (T.multiplicity (e i) : ℤ) =
          (T.multiplicity (e 2) : ℤ) * AffineDynkinType.E6.marks i) ∧
        (∀ i j, T.intersection (e i) (e j) =
          -(T.weight (e 0) : ℤ) * AffineDynkinType.E6.cartanMatrix i j)) ∨
      (∃ e : Fin 8 ≃ T.Component,
        (∀ i, T.weight (e i) = T.weight (e 0)) ∧
        (∀ i, (T.multiplicity (e i) : ℤ) =
          AffineDynkinType.E7.marks i * T.multiplicity (e 4)) ∧
        (∀ i j, T.intersection (e i) (e j) =
          -(T.weight (e 0) : ℤ) * AffineDynkinType.E7.cartanMatrix i j)) ∨
      (∃ e : Fin 9 ≃ T.Component,
        (∀ i, T.weight (e i) = T.weight (e 0)) ∧
        (∀ i, (T.multiplicity (e i) : ℤ) =
          AffineDynkinType.E8.marks i * T.multiplicity (e 8)) ∧
        (∀ i j, T.intersection (e i) (e j) =
          -(T.weight (e 0) : ℤ) * AffineDynkinType.E8.cartanMatrix i j)))) := Iff.rfl

/-- Nonconsecutive vanishing intersections are preserved by reversing a chain. -/
private lemma zero_of_reverse {n : ℕ} {c : ℕ → T.Component}
    (hzero : ∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      T.intersection (c i) (c j) = 0) :
    ∀ i < n, ∀ j < n, i ≠ j → i + 1 ≠ j → j + 1 ≠ i →
      T.intersection (c (n - 1 - i)) (c (n - 1 - j)) = 0 := by
  intro i hi j hj hij h1 h2
  exact hzero (n - 1 - i) (by omega) (n - 1 - j) (by omega) (by omega) (by omega) (by omega)

/-- **Classification of minimal numerical types of genus one**
([Stacks, Lemma 55.6.2](https://stacks.math.columbia.edu/tag/0C8T)). Every minimal numerical type
of arithmetic genus one belongs to one of the shape families of
`TauCeti.NumericalType.IsGenusOneMinimalShape`. -/
theorem IsMinimal.isGenusOneMinimalShape (hT : T.IsMinimal) (hg : T.arithmeticGenus = 1) :
    T.IsGenusOneMinimalShape := by
  classical
  by_cases hcard1 : Fintype.card T.Component = 1
  · exact .inl ⟨hcard1, fun i ↦ ⟨(T.arithmeticGenus_eq_one_iff_of_card_eq_one hcard1 i).mp hg,
      T.intersection_eq_zero_of_card_eq_one hcard1 i i⟩⟩
  have h1lt : 1 < Fintype.card T.Component := by
    have := Fintype.card_pos (α := T.Component)
    omega
  have hminusTwo := (T.isMinimal_and_arithmeticGenus_eq_one_iff h1lt).mp ⟨hT, hg⟩
  have hgen (i : T.Component) : T.genus i = 0 := (T.isMinusTwoIndex_iff.mp (hminusTwo i)).1
  have hself (i : T.Component) : T.intersection i i = -(2 * (T.weight i : ℤ)) :=
    (T.isMinusTwoIndex_iff.mp (hminusTwo i)).2
  have hself_ge (i : T.Component) : -(2 * (T.weight i : ℤ)) ≤ T.intersection i i := (hself i).ge
  refine .inr ⟨fun i ↦ ⟨hgen i, hself i⟩, ?_⟩
  rcases T.topologicalGenus_pos_or_exists_chain_or_fork_or_star_or_affine hself with
    htop | ⟨t, c, ht2, hcard, hc, hzero⟩ | ⟨t, c, b, hcard, hf⟩ |
      ⟨c₀, l, hl, hadj⟩ | ⟨t, c, left, right, ht4, hcard, hr, hl⟩ |
      ⟨l, hl, hadj⟩ | ⟨l, hl, hadj⟩ | ⟨l, hl, hadj⟩
  · -- Cycle case.
    exact .inl ⟨htop,
      fun i j ↦ ⟨T.weight_eq_of_topologicalGenus_pos hself_ge htop i j,
        T.multiplicity_eq_of_topologicalGenus_pos hself_ge htop i j⟩,
      T.ncard_neighborSet_eq_two_of_topologicalGenus_pos hself_ge htop,
      fun i j hij ↦ T.intersection_eq_weight_of_topologicalGenus_pos hself_ge htop hij⟩
  · -- Path cases (`t = 2`, `3`, `4`, `5`, or `t ≥ 6`).
    rcases lt_or_ge t 6 with ht6 | ht6
    · interval_cases t
      · obtain ⟨x, y, hxy, hshape⟩ :=
          T.exists_weight_multiplicity_intersection_eq_of_card_eq_two hcard
            (hc.ne (i := 0) (j := 1) (by omega) (by omega) (by omega)) (hself _) (hself _)
        refine .inr (.inl ⟨hcard, x, y, ?_, hshape⟩)
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
        refine .inr (.inr (.inl ⟨hcard, x, c 1, z, ?_⟩))
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
        · exact .inr (.inr (.inr (.inl ⟨hcard, c, hc, hzero, h4⟩)))
        · exact .inr (.inr (.inr (.inl
            ⟨hcard, fun i ↦ c (4 - 1 - i), hc.reverse, zero_of_reverse hzero, h4⟩)))
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
        · exact .inr (.inr (.inr (.inr (.inr (.inl ⟨hcard, c, hc, hzero, h5⟩)))))
        · exact .inr (.inr (.inr (.inr (.inr (.inl
            ⟨hcard, fun i ↦ c (5 - 1 - i), hc.reverse, zero_of_reverse hzero, h5⟩)))))
    · rcases T.isGenusOneLongPathShape_or_isGenusOneLongPathShape hcard ht6 hc hzero with
        hlong | hlong
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
          ⟨t, c, ht6, hcard, hc, hzero, hlong⟩))))))))
      · exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
          ⟨t, fun i ↦ c (t - 1 - i), ht6, hcard, hc.reverse, zero_of_reverse hzero, hlong⟩))))))))
  · -- Fork cases (`t = 3`, `4`, or `t ≥ 5`).
    have ht3 := hf.two_lt
    rcases lt_or_ge t 5 with ht5 | ht5
    · interval_cases t
      · -- `t = 3`: three-leaf star on `4` components.
        have hz02 := hf.intersection_eq_zero (by omega) (p := 0) (q := 2)
          (by omega) (by omega) (by omega) (by omega) (by omega)
        have hz0b := hf.branch_intersection_eq_zero (i := 0) (by omega) (by omega)
        have hz2b := hf.branch_intersection_eq_zero (i := 2) (by omega) (by omega)
        obtain ⟨x, y, z, hset, hstar⟩ := T.exists_isGenusOneFourStarShape hcard
          (hself (c 1)) (hself (c 0)) (hself (c 2)) (hself b) hz02 hz0b hz2b
          (by rw [T.intersection_comm]; exact hf.intersection_succ_pos 0 (by omega))
          (hf.intersection_succ_pos 1 (by omega)) hf.branch_intersection_pos
        have h10 : c 1 ∉ ({c 0, c 2, b} : Finset T.Component) := by
          simp [hf.ne (i := 1) (j := 0) (by omega) (by omega) (by omega),
            hf.ne (i := 1) (j := 2) (by omega) (by omega) (by omega),
            (hf.branch_ne 1 (by omega)).symm]
        have h02 : c 0 ∉ ({c 2, b} : Finset T.Component) := by
          simp [hf.ne (i := 0) (j := 2) (by omega) (by omega) (by omega),
            (hf.branch_ne 0 (by omega)).symm]
        have h2b : c 2 ≠ b := (hf.branch_ne 2 (by omega)).symm
        have huniv : ({c 1, x, y, z} : Finset T.Component) = univ := by
          have hsub : ({c 1, c 0, c 2, b} : Finset T.Component) = univ :=
            eq_univ_of_card _ (by
              rw [card_insert_of_notMem h10, card_insert_of_notMem h02, card_pair h2b, hcard])
          simpa [← hset] using hsub
        have hxyz_zero (u v : T.Component) (hu : u ∈ ({x, y, z} : Finset T.Component))
            (hv : v ∈ ({x, y, z} : Finset T.Component)) (huv : u ≠ v) :
            T.intersection u v = 0 := by
          rw [hset] at hu hv; simp only [mem_insert, mem_singleton] at hu hv
          grind [T.intersection_comm]
        have hcard3 : #({x, y, z} : Finset T.Component) = 3 := by
          rw [hset, card_insert_of_notMem h02, card_pair h2b]
        have hyz : y ≠ z := fun h ↦ by
          have := card_le_two (a := x) (b := y)
          rw [← h, insert_eq_of_mem (mem_singleton_self y)] at hcard3; omega
        have hxy : x ≠ y := fun h ↦ by
          have := card_le_two (a := x) (b := z)
          rw [← h, insert_eq_of_mem (mem_insert_self x {z})] at hcard3; omega
        have hxz : x ≠ z := fun h ↦ by
          have := card_le_two (a := y) (b := x)
          rw [← h, insert_eq_of_mem (mem_insert_of_mem (mem_singleton_self x))] at hcard3; omega
        exact .inr (.inr (.inr (.inr (.inl ⟨hcard, c 1, x, y, z, huniv,
          hxyz_zero x y (by simp) (by simp) hxy,
          hxyz_zero x z (by simp) (by simp) hxz,
          hxyz_zero y z (by simp) (by simp) hyz, hstar⟩))))
      · -- `t = 4`: five-component fork.
        let f : Fin 5 → T.Component := fun i ↦ if (i : ℕ) = 4 then b else c i
        have hf_inj : Function.Injective f := fun i j hij ↦ Fin.ext
          (hf.injOn_snoc hf.branch_ne i (by omega) j (by omega) hij)
        have hf_bij : Function.Bijective f :=
          (Fintype.bijective_iff_injective_and_card f).mpr ⟨hf_inj, by simpa using hcard.symm⟩
        let e : Fin 5 ≃ T.Component := Equiv.ofBijective f hf_bij
        have he0 : e 0 = c 0 := rfl
        have he1 : e 1 = c 1 := rfl
        have he2 : e 2 = c 2 := rfl
        have he3 : e 3 = c 3 := rfl
        have he4 : e 4 = b := rfl
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
        obtain ⟨-, w, m, hfive⟩ := hT.exists_weight_multiplicity_intersection_eq_fiveFork hg e
          (by rw [he0, he1]; exact hf.intersection_succ_pos 0 (by omega))
          (by rw [he1, he2]; exact hf.intersection_succ_pos 1 (by omega))
          (by rw [he2, he3]; exact hf.intersection_succ_pos 2 (by omega))
          (by rw [he2, he4]; exact hf.branch_intersection_pos) hz02 hz03 hz04
        exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl ⟨e, w, m, hfive⟩)))))))
    · -- `t ≥ 5`: long fork.
      exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
        ⟨t, c, b, ht5, hcard, hf, hf.isGenusOneLongForkShape hcard (by omega)⟩)))))))))
  · -- Four-leaf star (affine `D₄`).
    obtain ⟨e, he0, hel, hw, hm, ha⟩ :=
      T.exists_equiv_fourLeafStar c₀ l hl (hself c₀) (fun i ↦ hself (l i)) hadj
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨e, by simpa [he0] using hw, by simpa [hel 0] using hm, by simpa [he0] using ha⟩))))))
  · -- Double fork (affine `Dₙ`, `n ≥ 5`).
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨t, c, left, right, ht4, hcard, hr, hl, hr.isGenusOneAffineDShape hl hcard ht4⟩))))))))))
  · -- Affine `E₆`.
    obtain ⟨e, he, hw, hm, ha⟩ := T.exists_equiv_affineE6 l hl (fun i ↦ hself (l i)) hadj
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨e, by simpa [he 0] using hw, by simpa [he 2] using hm, by simpa [he 0] using ha⟩)))))))))))
  · -- Affine `E₇`.
    obtain ⟨e, he, hw, hm, ha⟩ := T.exists_equiv_affineE7 l hl (fun i ↦ hself (l i)) hadj
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inl
      ⟨e, by simpa [he 0] using hw, by simpa [he 4] using hm, by simpa [he 0] using ha⟩))))))))))))
  · -- Affine `E₈`.
    obtain ⟨e, he, hw, hm, ha⟩ := T.exists_equiv_affineE8 l hl (fun i ↦ hself (l i)) hadj
    exact .inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr (.inr
      ⟨e, by simpa [he 0] using hw, by simpa [he 8] using hm, by simpa [he 0] using ha⟩))))))))))))

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
  have close (jw jm : T.Component)
      (hw : ∀ i, (T.weight i : ℤ) = T.weight jw ∨ (T.weight i : ℤ) = 2 * T.weight jw ∨
        (T.weight i : ℤ) = 3 * T.weight jw ∨ (T.weight i : ℤ) = 4 * T.weight jw)
      (hm : ∀ i, (T.multiplicity i : ℤ) = T.multiplicity jm ∨
        (T.multiplicity i : ℤ) = 2 * T.multiplicity jm ∨
        (T.multiplicity i : ℤ) = 3 * T.multiplicity jm ∨
        (T.multiplicity i : ℤ) = 4 * T.multiplicity jm ∨
        (T.multiplicity i : ℤ) = 5 * T.multiplicity jm ∨
        (T.multiplicity i : ℤ) = 6 * T.multiplicity jm) :
      (∃ j, ∀ i, (T.weight j : ℕ) ∣ T.weight i ∧ (T.weight i : ℕ) ≤ 4 * T.weight j) ∧
        (∃ j, ∀ i, (T.multiplicity j : ℕ) ∣ T.multiplicity i ∧
          (T.multiplicity i : ℕ) ≤ 6 * T.multiplicity j) :=
    ⟨⟨jw, fun i ↦ PNat.dvd_and_le_four_of_int (hw i)⟩,
      ⟨jm, fun i ↦ PNat.dvd_and_le_six_of_int (hm i)⟩⟩
  obtain ⟨j₀⟩ := (inferInstance : Nonempty T.Component)
  rcases h with ⟨hcard1, -⟩ | ⟨-,
    ⟨-, hwm, -⟩ |
    ⟨hcard, x, y, hxy, h2⟩ |
    ⟨hcard, x, j, z, hxj, hxz, hjz, -, h3⟩ |
    ⟨hcard, c, hc, -, h4⟩ |
    ⟨-, c₀, x, y, z, huniv, -, -, -, hstar⟩ |
    ⟨hcard, c, hc, -, h5⟩ |
    ⟨e, hw, hm, -⟩ |
    ⟨e, w, m, ⟨hw, hm, -⟩ | ⟨hw, hm, -⟩⟩ |
    ⟨n, c, hn, hcard, hc, -, hlong⟩ |
    ⟨t, c, b, ht, hcard, hf, hfork⟩ |
    ⟨t, c, left, right, ht, hcard, hr, hl, hD⟩ |
    ⟨e, hw, hm, -⟩ | ⟨e, hw, hm, -⟩ | ⟨e, hw, hm, -⟩⟩
  · exact close j₀ j₀
      (fun i ↦ by rw [Fintype.card_le_one_iff.mp hcard1.le i j₀]; omega)
      (fun i ↦ by rw [Fintype.card_le_one_iff.mp hcard1.le i j₀]; omega)
  · exact close j₀ j₀
      (fun i ↦ by rw [(hwm i j₀).1]; omega)
      (fun i ↦ by rw [(hwm i j₀).2]; omega)
  · have mem (i : T.Component) : i = x ∨ i = y := by
      have hu : ({x, y} : Finset T.Component) = univ :=
        eq_univ_of_card _ (by rw [card_pair hxy, hcard])
      simpa using (hu ▸ mem_univ i : i ∈ ({x, y} : Finset T.Component))
    rcases isGenusOnePairShape_iff.mp h2 with ⟨hw, hm, -⟩ | ⟨hw, hm, -⟩ <;>
      [refine close x x ?_ ?_; refine close x y ?_ ?_] <;>
      (intro i; rcases mem i with rfl | rfl <;> omega)
  · have mem (i : T.Component) : i = x ∨ i = j ∨ i = z := by
      have hu : ({x, j, z} : Finset T.Component) = univ :=
        eq_univ_of_card _ (by
          rw [card_insert_of_notMem (by simp [hxj, hxz]), card_pair hjz, hcard])
      simpa using (hu ▸ mem_univ i : i ∈ ({x, j, z} : Finset T.Component))
    rcases isGenusOneChainShape_iff.mp h3 with ⟨hw1, hw2, hm1, hm2, -⟩ |
      ⟨hw1, hw2, hm1, hm2, -⟩ | ⟨hw1, hw2, hm1, hm2, -⟩ |
      ⟨hw1, hw2, hm1, hm2, -⟩ | ⟨hw1, hw2, hm1, hm2, -⟩ <;>
      [refine close x x ?_ ?_; refine close z x ?_ ?_; refine close x z ?_ ?_;
        refine close x x ?_ ?_; refine close j x ?_ ?_] <;>
      (intro i; rcases mem i with rfl | rfl | rfl <;> omega)
  · have mem (i : T.Component) : i = c 0 ∨ i = c 1 ∨ i = c 2 ∨ i = c 3 := by
      obtain ⟨k, hk, rfl⟩ := hc.exists_lt_eq_of_card_eq hcard i
      interval_cases k <;> simp
    rcases isGenusOneFourPathShape_iff.mp h4 with ⟨hw1, hw2, hw3, hm1, hm2, hm3, -⟩ |
      ⟨hw1, hw2, hw3, hm1, hm2, hm3, -⟩ | ⟨hw1, hw2, hw3, hm1, hm2, hm3, -⟩ <;>
      [refine close (c 0) (c 3) ?_ ?_; refine close (c 0) (c 0) ?_ ?_;
        refine close (c 1) (c 0) ?_ ?_] <;>
      (intro i; rcases mem i with rfl | rfl | rfl | rfl <;> omega)
  · have mem (i : T.Component) : i = c₀ ∨ i = x ∨ i = y ∨ i = z := by
      simpa using (huniv ▸ mem_univ i : i ∈ ({c₀, x, y, z} : Finset T.Component))
    rcases isGenusOneFourStarShape_iff.mp hstar with ⟨hw1, hw2, hw3, hm1, hm2, hm3, -⟩ |
      ⟨hw1, hw2, hw3, hm1, hm2, hm3, -⟩ <;>
      [refine close c₀ x ?_ ?_; refine close z x ?_ ?_] <;>
      (intro i; rcases mem i with rfl | rfl | rfl | rfl <;> omega)
  · have mem (i : T.Component) : i = c 0 ∨ i = c 1 ∨ i = c 2 ∨ i = c 3 ∨ i = c 4 := by
      obtain ⟨k, hk, rfl⟩ := hc.exists_lt_eq_of_card_eq hcard i
      interval_cases k <;> simp
    obtain ⟨w, m, _, _, ⟨hw0, hw1, hw2, hw3, hw4, hm0, hm1, hm2, hm3, hm4, -⟩ |
      ⟨hw0, hw1, hw2, hw3, hw4, hm0, hm1, hm2, hm3, hm4, -⟩ |
      ⟨hw0, hw1, hw2, hw3, hw4, hm0, hm1, hm2, hm3, hm4, -⟩ |
      ⟨hw0, hw1, hw2, hw3, hw4, hm0, hm1, hm2, hm3, hm4, -⟩ |
      ⟨hw0, hw1, hw2, hw3, hw4, hm0, hm1, hm2, hm3, hm4, -⟩⟩ :=
        isGenusOneFivePathShape_iff.mp h5 <;>
      [refine close (c 0) (c 0) ?_ ?_; refine close (c 3) (c 0) ?_ ?_;
        refine close (c 0) (c 4) ?_ ?_; refine close (c 0) (c 0) ?_ ?_;
        refine close (c 1) (c 0) ?_ ?_] <;>
      (intro i; rcases mem i with rfl | rfl | rfl | rfl | rfl <;> omega)
  · refine close (e none) (e (some 0)) (fun i ↦ ?_) (fun i ↦ ?_)
    · rw [← e.apply_symm_apply i, hw (e.symm i)]; omega
    · have hv := hm (e.symm i); rw [e.apply_symm_apply] at hv; split_ifs at hv <;> omega
  · refine close (e 1) (e 0) (fun i ↦ ?_) (fun i ↦ ?_)
    · rw [← e.apply_symm_apply i, hw (e.symm i), hw 1]
      generalize e.symm i = k; fin_cases k <;> simp
    · rw [← e.apply_symm_apply i, hm (e.symm i), hm 0]
      generalize e.symm i = k; fin_cases k <;> simp
  · refine close (e 0) (e 3) (fun i ↦ ?_) (fun i ↦ ?_)
    · rw [← e.apply_symm_apply i, hw (e.symm i), hw 0]
      generalize e.symm i = k; fin_cases k <;> simp
    · rw [← e.apply_symm_apply i, hm (e.symm i), hm 3]
      generalize e.symm i = k; fin_cases k <;> simp
  · obtain ⟨w, m, _, _, ⟨hw, hm, -⟩ | ⟨hw, hm, -⟩ | ⟨hw, hm, -⟩⟩ :=
      isGenusOneLongPathShape_iff.mp hlong
    · refine close (c 0) (c (n - 1)) (fun i ↦ ?_) (fun i ↦ ?_)
      · obtain ⟨k, hk, rfl⟩ := hc.exists_lt_eq_of_card_eq hcard i
        have hwk := hw k hk; have hw0 := hw 0 (by omega); split_ifs at hwk hw0 <;> omega
      · obtain ⟨k, hk, rfl⟩ := hc.exists_lt_eq_of_card_eq hcard i
        have hmk := hm k hk; have hm0 := hm (n - 1) (by omega); split_ifs at hmk hm0 <;> omega
    · refine close (c 0) (c 0) (fun i ↦ ?_) (fun i ↦ ?_)
      · obtain ⟨k, hk, rfl⟩ := hc.exists_lt_eq_of_card_eq hcard i
        have hwk := hw k hk; have hw0 := hw 0 (by omega); split_ifs at hwk hw0 <;> omega
      · obtain ⟨k, hk, rfl⟩ := hc.exists_lt_eq_of_card_eq hcard i
        have hmk := hm k hk; have hm0 := hm 0 (by omega); omega
    · refine close (c 1) (c 0) (fun i ↦ ?_) (fun i ↦ ?_)
      · have hw1 := hw 1 (by omega); rw [ite_eq_right (by omega)] at hw1
        obtain ⟨k, hk, rfl⟩ := hc.exists_lt_eq_of_card_eq hcard i
        have hwk := hw k hk; split_ifs at hwk <;> omega
      · have hm0 := hm 0 (by omega); rw [ite_eq_left (by omega)] at hm0
        obtain ⟨k, hk, rfl⟩ := hc.exists_lt_eq_of_card_eq hcard i
        have hmk := hm k hk; split_ifs at hmk <;> omega
  · obtain ⟨w, m, _, _, ⟨hw, hwb, hm, hmb, -⟩ | ⟨hw, hwb, hm, hmb, -⟩⟩ :=
      isGenusOneLongForkShape_iff.mp hfork
    · refine close b b (fun i ↦ ?_) (fun i ↦ ?_)
      · rcases hf.eq_or_exists_lt_eq_of_card_eq hcard i with rfl | ⟨k, hk, rfl⟩
        · omega
        · have hwk := hw k hk; split_ifs at hwk <;> omega
      · rcases hf.eq_or_exists_lt_eq_of_card_eq hcard i with rfl | ⟨k, hk, rfl⟩
        · omega
        · have hmk := hm k hk; split_ifs at hmk <;> omega
    · refine close (c 0) b (fun i ↦ ?_) (fun i ↦ ?_)
      · have hw0 := hw 0 (by omega); simp only [↓reduceIte] at hw0
        rcases hf.eq_or_exists_lt_eq_of_card_eq hcard i with rfl | ⟨k, hk, rfl⟩
        · omega
        · have hwk := hw k hk; split_ifs at hwk <;> omega
      · rcases hf.eq_or_exists_lt_eq_of_card_eq hcard i with rfl | ⟨k, hk, rfl⟩
        · omega
        · have hmk := hm k hk; split_ifs at hmk <;> omega
  · obtain ⟨w, m, _, _, hw, hwl, hwr, hm, hml, hmr, -⟩ := isGenusOneAffineDShape_iff.mp hD
    refine close left left (fun i ↦ ?_) (fun i ↦ ?_)
    · rcases hr.eq_or_eq_or_exists_lt_eq_of_card_eq hl ht hcard i with rfl | rfl | ⟨k, hk, rfl⟩ <;>
        [omega; omega; (have hwk := hw k hk; omega)]
    · rcases hr.eq_or_eq_or_exists_lt_eq_of_card_eq hl ht hcard i with rfl | rfl | ⟨k, hk, rfl⟩ <;>
        [omega; omega; (have hmk := hm k hk; split_ifs at hmk <;> omega)]
  · refine close (e 0) (e 2) (fun i ↦ ?_) (fun i ↦ ?_)
    · rw [← e.apply_symm_apply i, hw (e.symm i)]; omega
    · rw [← e.apply_symm_apply i, hm (e.symm i)]
      generalize e.symm i = k; fin_cases k <;> simp [mul_comm]
  · refine close (e 0) (e 4) (fun i ↦ ?_) (fun i ↦ ?_)
    · rw [← e.apply_symm_apply i, hw (e.symm i)]; omega
    · rw [← e.apply_symm_apply i, hm (e.symm i)]
      generalize e.symm i = k; fin_cases k <;> simp
  · refine close (e 0) (e 8) (fun i ↦ ?_) (fun i ↦ ?_)
    · rw [← e.apply_symm_apply i, hw (e.symm i)]; omega
    · rw [← e.apply_symm_apply i, hm (e.symm i)]
      generalize e.symm i = k; fin_cases k <;> simp

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
