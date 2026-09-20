/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.IntersectionForm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Proper subgraphs of `(-2)`-indices in a numerical type

A `(-2)`-index of a numerical type is a component `i` with `gᵢ = 0` and `aᵢᵢ = -2wᵢ`. The
connected configurations of `(-2)`-indices that can occur as proper subsets of the components
of a numerical type form a short explicit list, of Dynkin-diagram shape
([Stacks, Section 0C7L](https://stacks.math.columbia.edu/tag/0C7L)). This classification is
what bounds the multiplicities along chains of `(-2)`-indices in a minimal numerical type, and
hence its Picard group.

This file classifies the configurations on two, three, four, and five components. If a numerical
type has
more than two components and two `(-2)`-indices `i` and `j` meet, then up to swapping `i` and `j`,

`(wᵢ, wⱼ, aᵢⱼ) = (w, w, w)`, `(w, 2w, 2w)` or `(w, 3w, 3w)`

for some positive integer `w` ([Stacks, Tag 0C7M](https://stacks.math.columbia.edu/tag/0C7M)). If
a numerical type has more than three components and two distinct `(-2)`-indices `i` and `k` both
meet a `(-2)`-index `j`, then `i` and `k` do not meet, so that the configuration is a chain, and
up to reversing it

`(wᵢ, wⱼ, wₖ, aᵢⱼ, aⱼₖ) = (w, w, w, w, w)`, `(w, w, 2w, w, 2w)` or `(2w, 2w, w, 2w, 2w)`

([Stacks, Tag 0C7R](https://stacks.math.columbia.edu/tag/0C7R)).

On four components, a chain has four possible unoriented weight patterns, and a component meeting
three others has the simply-laced star pattern. In both cases all intersections not displayed in
the graph vanish ([Stacks, Tags 0C7V and 0C80](https://stacks.math.columbia.edu/tag/0C7V)).

On five components a chain has only three unoriented weight patterns: all five weights equal, or
four equal weights together with, at one end of the chain, their double or their half
([Stacks, Tag 0C82](https://stacks.math.columbia.edu/tag/0C82)). In particular a double edge can
occur only at an end, so the two middle edges are simply laced, and again no intersection outside
the chain is nonzero: five `(-2)`-indices never form a pentagon. Likewise, a component meeting
three other `(-2)`-indices cannot meet a fourth one
([Stacks, Lemma 55.5.6](https://stacks.math.columbia.edu/tag/0C86)).

The remaining five-component tree has a chain of length three ending in a fork. All five weights
and all four displayed intersections are equal, and every other intersection vanishes
([Stacks, Lemma 55.5.7](https://stacks.math.columbia.edu/tag/0C87)).

On six components, a chain again has equal weights and simple edges except possibly at one end,
where the endpoint may have twice or half the common interior weight. This is the base case for
the arbitrary-length chain classification of
[Stacks, Lemma 55.5.8](https://stacks.math.columbia.edu/tag/0C89).

These arguments use only the self-intersections `aᵢᵢ = -2wᵢ`, not the genera. For a pair, negative
definiteness of the principal `2 × 2` submatrix gives `aᵢⱼ² < 4wᵢwⱼ`, and `lcm(wᵢ, wⱼ) ∣ aᵢⱼ`
leaves only the three solutions above. For a triple, negative definiteness of the principal
`3 × 3` submatrix says that

`p₁q₁ + p₂q₂ + p₃q₃ + q₁q₂p₃ < 4`

where `aᵢⱼ = wᵢp₁ = wⱼq₁`, `aⱼₖ = wⱼp₂ = wₖq₂` and `aᵢₖ = wᵢp₃ = wₖq₃` are the factorisations
supplied by the divisibility axiom. All four summands are nonnegative integers and the first two
are positive, so the last two vanish; in particular `aᵢₖ = 0` and `p₁q₁ + p₂q₂ ≤ 3`. The constraints
`aᵢⱼ mⱼ ≤ 2wᵢ mᵢ` and `aᵢⱼ mᵢ ≤ 2wⱼ mⱼ` on the multiplicities listed alongside the Stacks
statements are instances of `TauCeti.NumericalType.multiplicity_mul_intersection_le`.

Beyond four components the principal determinants become unwieldy, and the five-component
classification instead evaluates the intersection form at an explicit positive integral vector.
Each ratio pattern excluded there is the diagram of an affine generalized Cartan matrix, so the
form vanishes at the vector spanning its kernel; this is what negative definiteness of the
intersection form on the vectors supported on a proper subset of the components forbids.

## Main results

* `TauCeti.NumericalType.exists_weight_intersection_triple_mem`: the classification of the
  weights and the intersection number of two meeting `(-2)`-indices.
* `TauCeti.NumericalType.intersection_eq_zero_of_intersection_pos_of_intersection_pos`: two
  `(-2)`-indices meeting a common third one do not meet each other.
* `TauCeti.NumericalType.exists_weight_intersection_quintuple_mem`: the classification of the
  weights and the intersection numbers of a chain of three `(-2)`-indices.
* `TauCeti.NumericalType.exists_intersection_ratio_chain_four_mem`: the classification of a chain
  of four `(-2)`-indices by its normalized adjacent intersection ratios.
* `TauCeti.NumericalType.exists_weight_intersection_star_four_eq`: the classification of the
  four-component star.
* `TauCeti.NumericalType.exists_intersection_ratio_chain_five_mem`: the classification of a chain
  of five `(-2)`-indices by its normalized adjacent intersection ratios.
* `TauCeti.NumericalType.intersection_eq_weight_of_chain_five`: the two middle edges of a chain of
  five `(-2)`-indices are simply laced.
* `TauCeti.NumericalType.intersection_eq_zero_of_chain_five`: a chain of five `(-2)`-indices does
  not close up into a pentagon.
* `TauCeti.NumericalType.intersection_eq_zero_of_star_five`: a `(-2)`-index meeting three others
  meets no fourth one.
* `TauCeti.NumericalType.exists_weight_intersection_fork_five_eq`: the five-component fork is
  simply laced, with equal weights and no additional edges.
* `TauCeti.NumericalType.intersection_eq_zero_of_chain_six`: a chain of six `(-2)`-indices has no
  intersections outside its five displayed edges.
* `TauCeti.NumericalType.exists_intersection_ratio_chain_six_mem`: a six-component chain has at
  most one nonsimple edge, and only at an end.
-/

public section

namespace TauCeti

namespace NumericalType

universe u

variable (T : NumericalType.{u})

/-- Two meeting components `i` and `j` of self-intersections `aᵢᵢ = -2wᵢ` and `aⱼⱼ = -2wⱼ`, such
as two `(-2)`-indices, in a numerical type with more than two components have
`(wᵢ, wⱼ, aᵢⱼ)` equal to `(w, w, w)`, `(w, 2w, 2w)`, `(2w, w, 2w)`, `(w, 3w, 3w)` or
`(3w, w, 3w)` for some positive integer `w`
([Stacks, Tag 0C7M](https://stacks.math.columbia.edu/tag/0C7M)). -/
theorem exists_weight_intersection_triple_mem (hcard : 2 < Fintype.card T.Component)
    {i j : T.Component} (hi : T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hj : T.intersection j j = -(2 * (T.weight j : ℤ))) (hij : 0 < T.intersection i j) :
    ∃ w : ℕ+, ((T.weight i : ℤ), (T.weight j : ℤ), T.intersection i j) ∈
      ({((w : ℤ), (w : ℤ), (w : ℤ)), ((w : ℤ), 2 * (w : ℤ), 2 * (w : ℤ)),
        (2 * (w : ℤ), (w : ℤ), 2 * (w : ℤ)), ((w : ℤ), 3 * (w : ℤ), 3 * (w : ℤ)),
        (3 * (w : ℤ), (w : ℤ), 3 * (w : ℤ))} : Set (ℤ × ℤ × ℤ)) := by
  have hwi : (0 : ℤ) < T.weight i := by simp
  have hwj : (0 : ℤ) < T.weight j := by simp
  have hne : i ≠ j := by
    rintro rfl
    linarith
  -- Negative definiteness on `{i, j}` gives `aᵢⱼ² < 4 wᵢ wⱼ`.
  have hlt := T.intersection_sq_lt_intersection_mul_intersection hcard hne
  rw [hi, hj] at hlt
  -- Both weights divide `aᵢⱼ`, say `aᵢⱼ = wᵢ p = wⱼ q`; then `p q < 4`.
  obtain ⟨p, hp⟩ := T.weight_dvd i j
  obtain ⟨q, hq⟩ : (T.weight j : ℤ) ∣ T.intersection i j :=
    T.intersection_comm j i ▸ T.weight_dvd j i
  have hp0 : 0 < p := pos_of_mul_pos_right (hp ▸ hij) hwi.le
  have hq0 : 0 < q := pos_of_mul_pos_right (hq ▸ hij) hwj.le
  have hpq : p * q < 4 := by
    have hww : 0 < (T.weight i : ℤ) * T.weight j := mul_pos hwi hwj
    have : (T.weight i : ℤ) * T.weight j * (p * q) < T.weight i * T.weight j * 4 := by
      nlinarith
    exact lt_of_mul_lt_mul_left this hww.le
  have hp3 : p ≤ 3 := by nlinarith
  have hq3 : q ≤ 3 := by nlinarith
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  interval_cases p <;> interval_cases q <;>
    first
    | omega
    | (refine ⟨T.weight i, ?_⟩; omega)
    | (refine ⟨T.weight j, ?_⟩; omega)

/-! ### Three components -/

/-- The determinant inequality for three distinct components with `aᵢᵢ = -2wᵢ`, divided by
`2wᵢwⱼwₖ` and written in terms of factorisations `aᵢⱼ = wᵢp₁ = wⱼq₁`, `aⱼₖ = wⱼp₂ = wₖq₂` and
`aᵢₖ = wᵢp₃ = wₖq₃` of the three intersection numbers. -/
private lemma sum_lt_four (hcard : 3 < Fintype.card T.Component) {i j k : T.Component}
    (hi : T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hj : T.intersection j j = -(2 * (T.weight j : ℤ)))
    (hk : T.intersection k k = -(2 * (T.weight k : ℤ)))
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) {p₁ q₁ p₂ q₂ p₃ q₃ : ℤ}
    (hp₁ : T.intersection i j = (T.weight i : ℤ) * p₁)
    (hq₁ : T.intersection i j = (T.weight j : ℤ) * q₁)
    (hp₂ : T.intersection j k = (T.weight j : ℤ) * p₂)
    (hq₂ : T.intersection j k = (T.weight k : ℤ) * q₂)
    (hp₃ : T.intersection i k = (T.weight i : ℤ) * p₃)
    (hq₃ : T.intersection i k = (T.weight k : ℤ) * q₃) :
    p₁ * q₁ + p₂ * q₂ + p₃ * q₃ + q₁ * q₂ * p₃ < 4 := by
  have hwi : (0 : ℤ) < T.weight i := by simp
  have hwj : (0 : ℤ) < T.weight j := by simp
  have hwk : (0 : ℤ) < T.weight k := by simp
  have hdet := T.intersection_det_triple_neg hcard hij hik hjk
  rw [hi, hj, hk] at hdet
  have hkey : (T.weight i : ℤ) * T.intersection j k ^ 2 +
      (T.weight j : ℤ) * T.intersection i k ^ 2 + (T.weight k : ℤ) * T.intersection i j ^ 2 +
        T.intersection i j * T.intersection i k * T.intersection j k <
      ((T.weight i : ℤ) * T.weight j * T.weight k) * 4 := by linarith
  have hsq₁ : T.intersection i j ^ 2 =
      (T.weight i : ℤ) * p₁ * ((T.weight j : ℤ) * q₁) := by rw [← hp₁, ← hq₁, sq]
  have hsq₂ : T.intersection j k ^ 2 =
      (T.weight j : ℤ) * p₂ * ((T.weight k : ℤ) * q₂) := by rw [← hp₂, ← hq₂, sq]
  have hsq₃ : T.intersection i k ^ 2 =
      (T.weight i : ℤ) * p₃ * ((T.weight k : ℤ) * q₃) := by rw [← hp₃, ← hq₃, sq]
  have hprod : T.intersection i j * T.intersection i k * T.intersection j k =
      (T.weight j : ℤ) * q₁ * ((T.weight i : ℤ) * p₃) * ((T.weight k : ℤ) * q₂) := by
    rw [← hq₁, ← hp₃, ← hq₂]
  rw [hsq₁, hsq₂, hsq₃, hprod] at hkey
  refine lt_of_mul_lt_mul_left (a := (T.weight i : ℤ) * T.weight j * T.weight k) ?_
    (mul_pos (mul_pos hwi hwj) hwk).le
  linarith

/-- Two components of a numerical type with more than three components whose self-intersections
are `aᵢᵢ = -2wᵢ` and `aₖₖ = -2wₖ`, and which both meet a third component `j` with `aⱼⱼ = -2wⱼ`, do
not meet each other, and the two factorisations of the two positive intersection numbers satisfy
`p₁q₁ + p₂q₂ < 4`.

Both conclusions come from the four-summand inequality above: its first two summands are positive,
so its last two vanish, which forces `aᵢₖ = 0`. -/
private lemma intersection_eq_zero_and_exists_factors (hcard : 3 < Fintype.card T.Component)
    {i j k : T.Component}
    (hi : T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hj : T.intersection j j = -(2 * (T.weight j : ℤ)))
    (hk : T.intersection k k = -(2 * (T.weight k : ℤ)))
    (hik : i ≠ k) (hij : 0 < T.intersection i j) (hjk : 0 < T.intersection j k) :
    T.intersection i k = 0 ∧ ∃ p₁ q₁ p₂ q₂ : ℤ, 1 ≤ p₁ ∧ 1 ≤ q₁ ∧ 1 ≤ p₂ ∧ 1 ≤ q₂ ∧
      T.intersection i j = (T.weight i : ℤ) * p₁ ∧ T.intersection i j = (T.weight j : ℤ) * q₁ ∧
      T.intersection j k = (T.weight j : ℤ) * p₂ ∧ T.intersection j k = (T.weight k : ℤ) * q₂ ∧
      p₁ * q₁ + p₂ * q₂ < 4 := by
  have hwi : (0 : ℤ) < T.weight i := by simp
  have hwj : (0 : ℤ) < T.weight j := by simp
  have hwk : (0 : ℤ) < T.weight k := by simp
  have hij' : i ≠ j := by rintro rfl; linarith
  have hjk' : j ≠ k := by rintro rfl; linarith
  obtain ⟨p₁, hp₁⟩ := T.weight_dvd i j
  obtain ⟨q₁, hq₁⟩ : (T.weight j : ℤ) ∣ T.intersection i j :=
    T.intersection_comm j i ▸ T.weight_dvd j i
  obtain ⟨p₂, hp₂⟩ := T.weight_dvd j k
  obtain ⟨q₂, hq₂⟩ : (T.weight k : ℤ) ∣ T.intersection j k :=
    T.intersection_comm k j ▸ T.weight_dvd k j
  obtain ⟨p₃, hp₃⟩ := T.weight_dvd i k
  obtain ⟨q₃, hq₃⟩ : (T.weight k : ℤ) ∣ T.intersection i k :=
    T.intersection_comm k i ▸ T.weight_dvd k i
  have hS := T.sum_lt_four hcard hi hj hk hij' hik hjk' hp₁ hq₁ hp₂ hq₂ hp₃ hq₃
  have hp₁1 : 1 ≤ p₁ := by have := pos_of_mul_pos_right (hp₁ ▸ hij) hwi.le; omega
  have hq₁1 : 1 ≤ q₁ := by have := pos_of_mul_pos_right (hq₁ ▸ hij) hwj.le; omega
  have hp₂1 : 1 ≤ p₂ := by have := pos_of_mul_pos_right (hp₂ ▸ hjk) hwj.le; omega
  have hq₂1 : 1 ≤ q₂ := by have := pos_of_mul_pos_right (hq₂ ▸ hjk) hwk.le; omega
  have h₁ : 1 ≤ p₁ * q₁ := by nlinarith
  have h₂ : 1 ≤ p₂ * q₂ := by nlinarith
  have haik : T.intersection i k = 0 := by
    rcases (T.offDiagonal_nonneg i k hik).lt_or_eq with hpos | h0
    · -- Were `i` and `k` to meet, each of the four summands would be at least one.
      exfalso
      have hp₃1 : 1 ≤ p₃ := by have := pos_of_mul_pos_right (hp₃ ▸ hpos) hwi.le; omega
      have hq₃1 : 1 ≤ q₃ := by have := pos_of_mul_pos_right (hq₃ ▸ hpos) hwk.le; omega
      have h₃ : 1 ≤ p₃ * q₃ := by nlinarith
      have h₄ : 1 ≤ q₁ * q₂ := by nlinarith
      have h₅ : 1 ≤ q₁ * q₂ * p₃ := by nlinarith
      linarith
    · exact h0.symm
  have hp₃0 : p₃ = 0 := by
    rw [haik] at hp₃
    exact (mul_eq_zero.mp hp₃.symm).resolve_left hwi.ne'
  rw [hp₃0] at hS
  exact ⟨haik, p₁, q₁, p₂, q₂, hp₁1, hq₁1, hp₂1, hq₂1, hp₁, hq₁, hp₂, hq₂, by linarith⟩

/-- Two components `i` and `k` of a numerical type with more than three components whose
self-intersections are `aᵢᵢ = -2wᵢ` and `aₖₖ = -2wₖ`, such as two `(-2)`-indices, and which both
meet a third component `j` with `aⱼⱼ = -2wⱼ`, do not meet each other: such a configuration is a
chain, never a triangle ([Stacks, Tag 0C7R](https://stacks.math.columbia.edu/tag/0C7R)). -/
theorem intersection_eq_zero_of_intersection_pos_of_intersection_pos
    (hcard : 3 < Fintype.card T.Component) {i j k : T.Component}
    (hi : T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hj : T.intersection j j = -(2 * (T.weight j : ℤ)))
    (hk : T.intersection k k = -(2 * (T.weight k : ℤ)))
    (hik : i ≠ k) (hij : 0 < T.intersection i j) (hjk : 0 < T.intersection j k) :
    T.intersection i k = 0 :=
  (T.intersection_eq_zero_and_exists_factors hcard hi hj hk hik hij hjk).1

/-- Three components `i`, `j`, `k` of self-intersections `aᵢᵢ = -2wᵢ`, `aⱼⱼ = -2wⱼ` and
`aₖₖ = -2wₖ`, such as three `(-2)`-indices, in a numerical type with more than three components,
with `i` and `k` distinct and both meeting `j`, have `(wᵢ, wⱼ, wₖ, aᵢⱼ, aⱼₖ)` equal to
`(w, w, w, w, w)`, `(w, w, 2w, w, 2w)`, `(2w, w, w, 2w, w)`, `(2w, 2w, w, 2w, 2w)` or
`(w, 2w, 2w, 2w, 2w)` for some positive integer `w`. The first, second and fourth of these are the
three chains of [Stacks, Tag 0C7R](https://stacks.math.columbia.edu/tag/0C7R), the remaining two
their reverses. The intersection number `aᵢₖ` of the two ends vanishes by
`TauCeti.NumericalType.intersection_eq_zero_of_intersection_pos_of_intersection_pos`. -/
theorem exists_weight_intersection_quintuple_mem (hcard : 3 < Fintype.card T.Component)
    {i j k : T.Component}
    (hi : T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hj : T.intersection j j = -(2 * (T.weight j : ℤ)))
    (hk : T.intersection k k = -(2 * (T.weight k : ℤ)))
    (hik : i ≠ k) (hij : 0 < T.intersection i j) (hjk : 0 < T.intersection j k) :
    ∃ w : ℕ+, ((T.weight i : ℤ), (T.weight j : ℤ), (T.weight k : ℤ), T.intersection i j,
        T.intersection j k) ∈
      ({((w : ℤ), (w : ℤ), (w : ℤ), (w : ℤ), (w : ℤ)),
        ((w : ℤ), (w : ℤ), 2 * (w : ℤ), (w : ℤ), 2 * (w : ℤ)),
        (2 * (w : ℤ), (w : ℤ), (w : ℤ), 2 * (w : ℤ), (w : ℤ)),
        (2 * (w : ℤ), 2 * (w : ℤ), (w : ℤ), 2 * (w : ℤ), 2 * (w : ℤ)),
        ((w : ℤ), 2 * (w : ℤ), 2 * (w : ℤ), 2 * (w : ℤ), 2 * (w : ℤ))} :
        Set (ℤ × ℤ × ℤ × ℤ × ℤ)) := by
  obtain ⟨-, p₁, q₁, p₂, q₂, hp₁1, hq₁1, hp₂1, hq₂1, hp₁, hq₁, hp₂, hq₂, hS⟩ :=
    T.intersection_eq_zero_and_exists_factors hcard hi hj hk hik hij hjk
  -- Both products are positive, so each of `p₁`, `q₁`, `p₂`, `q₂` is at most two.
  have h₁ : 1 ≤ p₁ * q₁ := by nlinarith
  have h₂ : 1 ≤ p₂ * q₂ := by nlinarith
  have hb₁ : p₁ ≤ 2 := by nlinarith
  have hb₂ : q₁ ≤ 2 := by nlinarith
  have hb₃ : p₂ ≤ 2 := by nlinarith
  have hb₄ : q₂ ≤ 2 := by nlinarith
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  interval_cases p₁ <;> interval_cases q₁ <;> interval_cases p₂ <;> interval_cases q₂ <;>
    first
      | omega
      | (refine ⟨T.weight i, ?_⟩; omega)
      | (refine ⟨T.weight j, ?_⟩; omega)
      | (refine ⟨T.weight k, ?_⟩; omega)

/-! ### Four components -/

/-- The positive determinant inequality for four distinct components in a cyclic ordering,
divided by `wᵢwⱼwₖwₗ`. The opposite intersections `aᵢₖ` and `aⱼₗ` vanish, while the four
remaining off-diagonal intersections are expressed using the divisibility of each row by its
weight. -/
private lemma chain_sum_lt_sixteen (hcard : 4 < Fintype.card T.Component)
    {i j k l : T.Component}
    (hi : T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hj : T.intersection j j = -(2 * (T.weight j : ℤ)))
    (hk : T.intersection k k = -(2 * (T.weight k : ℤ)))
    (hl : T.intersection l l = -(2 * (T.weight l : ℤ)))
    (hij : i ≠ j) (hik : i ≠ k) (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l)
    (hkl : k ≠ l) (hik0 : T.intersection i k = 0) (hjl0 : T.intersection j l = 0)
    {p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ : ℤ}
    (hp₁ : T.intersection i j = (T.weight i : ℤ) * p₁)
    (hq₁ : T.intersection i j = (T.weight j : ℤ) * q₁)
    (hp₂ : T.intersection j k = (T.weight j : ℤ) * p₂)
    (hq₂ : T.intersection j k = (T.weight k : ℤ) * q₂)
    (hp₃ : T.intersection k l = (T.weight k : ℤ) * p₃)
    (hq₃ : T.intersection k l = (T.weight l : ℤ) * q₃)
    (hp₄ : T.intersection i l = (T.weight i : ℤ) * p₄)
    (hq₄ : T.intersection i l = (T.weight l : ℤ) * q₄) :
    4 * (p₁ * q₁ + p₂ * q₂ + p₃ * q₃ + p₄ * q₄) +
        2 * q₁ * q₂ * q₃ * p₄ <
      16 + p₁ * q₁ * p₃ * q₃ + p₂ * q₂ * p₄ * q₄ := by
  have hwi : (0 : ℤ) < T.weight i := by simp
  have hwj : (0 : ℤ) < T.weight j := by simp
  have hwk : (0 : ℤ) < T.weight k := by simp
  have hwl : (0 : ℤ) < T.weight l := by simp
  have hdet := T.intersection_det_four_pos hcard hij hik hil hjk hjl hkl
  rw [hi, hj, hk, hl, hik0, hjl0] at hdet
  have hsq₁ : T.intersection i j ^ 2 =
      (T.weight i : ℤ) * p₁ * ((T.weight j : ℤ) * q₁) := by rw [← hp₁, ← hq₁, sq]
  have hsq₂ : T.intersection j k ^ 2 =
      (T.weight j : ℤ) * p₂ * ((T.weight k : ℤ) * q₂) := by rw [← hp₂, ← hq₂, sq]
  have hsq₃ : T.intersection k l ^ 2 =
      (T.weight k : ℤ) * p₃ * ((T.weight l : ℤ) * q₃) := by rw [← hp₃, ← hq₃, sq]
  have hsq₄ : T.intersection i l ^ 2 =
      (T.weight i : ℤ) * p₄ * ((T.weight l : ℤ) * q₄) := by rw [← hp₄, ← hq₄, sq]
  rw [hsq₁, hsq₂, hsq₃, hsq₄, hq₁, hp₄, hq₂, hq₃] at hdet
  refine lt_of_mul_lt_mul_left
    (a := (T.weight i : ℤ) * T.weight j * T.weight k * T.weight l) ?_
    (mul_pos (mul_pos (mul_pos hwi hwj) hwk) hwl).le
  ring_nf at hdet ⊢
  omega

/-- The factor data used to classify a chain of four components. Besides proving that all three
nonconsecutive intersections vanish, this bounds every divisibility factor by two and records the
normalized determinant inequality. -/
private lemma chain_four_factors (hcard : 4 < Fintype.card T.Component)
    {i j k l : T.Component}
    (hi : T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hj : T.intersection j j = -(2 * (T.weight j : ℤ)))
    (hk : T.intersection k k = -(2 * (T.weight k : ℤ)))
    (hl : T.intersection l l = -(2 * (T.weight l : ℤ)))
    (hik : i ≠ k) (hil : i ≠ l) (hjl : j ≠ l)
    (hij : 0 < T.intersection i j) (hjk : 0 < T.intersection j k)
    (hkl : 0 < T.intersection k l) :
    T.intersection i k = 0 ∧ T.intersection j l = 0 ∧ T.intersection i l = 0 ∧
      ∃ p₁ q₁ p₂ q₂ p₃ q₃ : ℤ,
        1 ≤ p₁ ∧ p₁ ≤ 2 ∧ 1 ≤ q₁ ∧ q₁ ≤ 2 ∧
        1 ≤ p₂ ∧ p₂ ≤ 2 ∧ 1 ≤ q₂ ∧ q₂ ≤ 2 ∧
        1 ≤ p₃ ∧ p₃ ≤ 2 ∧ 1 ≤ q₃ ∧ q₃ ≤ 2 ∧
        T.intersection i j = (T.weight i : ℤ) * p₁ ∧
        T.intersection i j = (T.weight j : ℤ) * q₁ ∧
        T.intersection j k = (T.weight j : ℤ) * p₂ ∧
        T.intersection j k = (T.weight k : ℤ) * q₂ ∧
        T.intersection k l = (T.weight k : ℤ) * p₃ ∧
        T.intersection k l = (T.weight l : ℤ) * q₃ ∧
        4 * (p₁ * q₁ + p₂ * q₂ + p₃ * q₃) <
          16 + p₁ * q₁ * p₃ * q₃ := by
  have hij' : i ≠ j := by rintro rfl; linarith
  have hjk' : j ≠ k := by rintro rfl; linarith
  have hkl' : k ≠ l := by rintro rfl; linarith
  have hik0 := T.intersection_eq_zero_of_intersection_pos_of_intersection_pos
    (by omega) hi hj hk hik hij hjk
  have hjl0 := T.intersection_eq_zero_of_intersection_pos_of_intersection_pos
    (by omega) hj hk hl hjl hjk hkl
  -- Factor each adjacent intersection by the weights at both ends. The two overlapping
  -- three-component classifications bound every factor by two.
  obtain ⟨p₁, hp₁⟩ := T.weight_dvd i j
  obtain ⟨q₁, hq₁⟩ : (T.weight j : ℤ) ∣ T.intersection i j :=
    T.intersection_comm j i ▸ T.weight_dvd j i
  obtain ⟨p₂, hp₂⟩ := T.weight_dvd j k
  obtain ⟨q₂, hq₂⟩ : (T.weight k : ℤ) ∣ T.intersection j k :=
    T.intersection_comm k j ▸ T.weight_dvd k j
  obtain ⟨p₃, hp₃⟩ := T.weight_dvd k l
  obtain ⟨q₃, hq₃⟩ : (T.weight l : ℤ) ∣ T.intersection k l :=
    T.intersection_comm l k ▸ T.weight_dvd l k
  obtain ⟨p₄, hp₄⟩ := T.weight_dvd i l
  obtain ⟨q₄, hq₄⟩ : (T.weight l : ℤ) ∣ T.intersection i l :=
    T.intersection_comm l i ▸ T.weight_dvd l i
  have hp₁1 : 1 ≤ p₁ := by
    have := pos_of_mul_pos_right (hp₁ ▸ hij) (by positivity : (0 : ℤ) ≤ T.weight i)
    omega
  have hq₁1 : 1 ≤ q₁ := by
    have := pos_of_mul_pos_right (hq₁ ▸ hij) (by positivity : (0 : ℤ) ≤ T.weight j)
    omega
  have hp₂1 : 1 ≤ p₂ := by
    have := pos_of_mul_pos_right (hp₂ ▸ hjk) (by positivity : (0 : ℤ) ≤ T.weight j)
    omega
  have hq₂1 : 1 ≤ q₂ := by
    have := pos_of_mul_pos_right (hq₂ ▸ hjk) (by positivity : (0 : ℤ) ≤ T.weight k)
    omega
  have hp₃1 : 1 ≤ p₃ := by
    have := pos_of_mul_pos_right (hp₃ ▸ hkl) (by positivity : (0 : ℤ) ≤ T.weight k)
    omega
  have hq₃1 : 1 ≤ q₃ := by
    have := pos_of_mul_pos_right (hq₃ ▸ hkl) (by positivity : (0 : ℤ) ≤ T.weight l)
    omega
  have hsum₁₂ := T.sum_lt_four (p₃ := 0) (q₃ := 0) (by omega) hi hj hk hij' hik hjk'
    hp₁ hq₁ hp₂ hq₂ (by simp [hik0]) (by simp [hik0])
  have hsum₂₃ := T.sum_lt_four (p₃ := 0) (q₃ := 0) (by omega) hj hk hl hjk' hjl hkl'
    hp₂ hq₂ hp₃ hq₃ (by simp [hjl0]) (by simp [hjl0])
  simp only [mul_zero, add_zero] at hsum₁₂ hsum₂₃
  have hpq₁pos : 0 < p₁ * q₁ := mul_pos (by omega) (by omega)
  have hpq₂pos : 0 < p₂ * q₂ := mul_pos (by omega) (by omega)
  have hpq₃pos : 0 < p₃ * q₃ := mul_pos (by omega) (by omega)
  have hpq₁2 : p₁ * q₁ ≤ 2 := by omega
  have hpq₂2 : p₂ * q₂ ≤ 2 := by omega
  have hpq₃2 : p₃ * q₃ ≤ 2 := by omega
  have hp₁2 : p₁ ≤ 2 := (le_mul_of_one_le_right (by omega) hq₁1).trans hpq₁2
  have hq₁2 : q₁ ≤ 2 := (le_mul_of_one_le_left (by omega) hp₁1).trans hpq₁2
  have hp₂2 : p₂ ≤ 2 := (le_mul_of_one_le_right (by omega) hq₂1).trans hpq₂2
  have hq₂2 : q₂ ≤ 2 := (le_mul_of_one_le_left (by omega) hp₂1).trans hpq₂2
  have hp₃2 : p₃ ≤ 2 := (le_mul_of_one_le_right (by omega) hq₃1).trans hpq₃2
  have hq₃2 : q₃ ≤ 2 := (le_mul_of_one_le_left (by omega) hp₃1).trans hpq₃2
  have hquad := T.chain_sum_lt_sixteen hcard hi hj hk hl hij' hik hil hjk' hjl hkl'
    hik0 hjl0 hp₁ hq₁ hp₂ hq₂ hp₃ hq₃ hp₄ hq₄
  -- A positive closing intersection would make all eight factors equal to one or two. The
  -- strict four-component determinant inequality rules out every such cycle.
  have hil0 : T.intersection i l = 0 := by
    rcases (T.offDiagonal_nonneg i l hil).lt_or_eq with hilpos | hilzero
    · have hp₄1 : 1 ≤ p₄ := by
        have := pos_of_mul_pos_right (hp₄ ▸ hilpos) (by positivity : (0 : ℤ) ≤ T.weight i)
        omega
      have hq₄1 : 1 ≤ q₄ := by
        have := pos_of_mul_pos_right (hq₄ ▸ hilpos) (by positivity : (0 : ℤ) ≤ T.weight l)
        omega
      have hp₃' : T.intersection l k = (T.weight l : ℤ) * q₃ := by
        rw [T.intersection_comm l k]
        exact hq₃
      have hq₃' : T.intersection l k = (T.weight k : ℤ) * p₃ := by
        rw [T.intersection_comm l k]
        exact hp₃
      have hsum₃₄ := T.sum_lt_four (p₃ := 0) (q₃ := 0) (by omega) hi hl hk hil hik hkl'.symm
        hp₄ hq₄ hp₃' hq₃' (by simp [hik0]) (by simp [hik0])
      simp only [mul_zero, add_zero] at hsum₃₄
      rw [mul_comm q₃ p₃] at hsum₃₄
      have hpq₄pos : 0 < p₄ * q₄ := mul_pos (by omega) (by omega)
      have hpq₄2 : p₄ * q₄ ≤ 2 := by omega
      have hp₄2 : p₄ ≤ 2 := (le_mul_of_one_le_right (by omega) hq₄1).trans hpq₄2
      have hq₄2 : q₄ ≤ 2 := (le_mul_of_one_le_left (by omega) hp₄1).trans hpq₄2
      interval_cases p₁ <;> interval_cases q₁ <;> interval_cases p₂ <;> interval_cases q₂ <;>
        interval_cases p₃ <;> interval_cases q₃ <;> interval_cases p₄ <;> interval_cases q₄ <;>
        norm_num at hquad
    · exact hilzero.symm
  have hquad0 := T.chain_sum_lt_sixteen (p₄ := 0) (q₄ := 0) hcard hi hj hk hl hij' hik hil
    hjk' hjl hkl' hik0 hjl0 hp₁ hq₁ hp₂ hq₂ hp₃ hq₃ (by simp [hil0]) (by simp [hil0])
  simp only [mul_zero, add_zero] at hquad0
  exact ⟨hik0, hjl0, hil0, p₁, q₁, p₂, q₂, p₃, q₃, hp₁1, hp₁2, hq₁1, hq₁2,
    hp₂1, hp₂2, hq₂1, hq₂2, hp₃1, hp₃2, hq₃1, hq₃2, hp₁, hq₁, hp₂, hq₂,
    hp₃, hq₃, hquad0⟩

/-- In a chain of four components of self-intersection `-2w`, every nonconsecutive intersection
vanishes. This is the graph-shape part of
[Stacks, Lemma 55.5.3](https://stacks.math.columbia.edu/tag/0C7V). -/
theorem intersection_eq_zero_of_chain_four (hcard : 4 < Fintype.card T.Component)
    {i j k l : T.Component}
    (hi : T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hj : T.intersection j j = -(2 * (T.weight j : ℤ)))
    (hk : T.intersection k k = -(2 * (T.weight k : ℤ)))
    (hl : T.intersection l l = -(2 * (T.weight l : ℤ)))
    (hik : i ≠ k) (hil : i ≠ l) (hjl : j ≠ l)
    (hij : 0 < T.intersection i j) (hjk : 0 < T.intersection j k)
    (hkl : 0 < T.intersection k l) :
    T.intersection i k = 0 ∧ T.intersection j l = 0 ∧ T.intersection i l = 0 := by
  have h := T.chain_four_factors hcard hi hj hk hl hik hil hjl hij hjk hkl
  exact ⟨h.1, h.2.1, h.2.2.1⟩

/-- For four components in a chain, all of self-intersection `-2w`, the three normalized adjacent
intersection ratios are `(1, 1, 1)`, `(1, 1, 2)`, `(1, 2, 1)`, or `(2, 1, 1)`. The factors in
the statement express `aᵢⱼ²/(wᵢwⱼ)` without division and recover the four unoriented weight
patterns of [Stacks, Lemma 55.5.3](https://stacks.math.columbia.edu/tag/0C7V). -/
theorem exists_intersection_ratio_chain_four_mem (hcard : 4 < Fintype.card T.Component)
    {i j k l : T.Component}
    (hi : T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hj : T.intersection j j = -(2 * (T.weight j : ℤ)))
    (hk : T.intersection k k = -(2 * (T.weight k : ℤ)))
    (hl : T.intersection l l = -(2 * (T.weight l : ℤ)))
    (hik : i ≠ k) (hil : i ≠ l) (hjl : j ≠ l)
    (hij : 0 < T.intersection i j) (hjk : 0 < T.intersection j k)
    (hkl : 0 < T.intersection k l) :
    ∃ p₁ q₁ p₂ q₂ p₃ q₃ : ℤ,
      T.intersection i j = (T.weight i : ℤ) * p₁ ∧
      T.intersection i j = (T.weight j : ℤ) * q₁ ∧
      T.intersection j k = (T.weight j : ℤ) * p₂ ∧
      T.intersection j k = (T.weight k : ℤ) * q₂ ∧
      T.intersection k l = (T.weight k : ℤ) * p₃ ∧
      T.intersection k l = (T.weight l : ℤ) * q₃ ∧
      (p₁ * q₁, p₂ * q₂, p₃ * q₃) ∈
        ({(1, 1, 1), (1, 1, 2), (1, 2, 1), (2, 1, 1)} : Set (ℤ × ℤ × ℤ)) := by
  obtain ⟨-, -, -, p₁, q₁, p₂, q₂, p₃, q₃, hp₁1, hp₁2, hq₁1, hq₁2, hp₂1, hp₂2,
      hq₂1, hq₂2, hp₃1, hp₃2, hq₃1, hq₃2, hp₁, hq₁, hp₂, hq₂, hp₃, hq₃, hdet⟩ :=
    T.chain_four_factors hcard hi hj hk hl hik hil hjl hij hjk hkl
  refine ⟨p₁, q₁, p₂, q₂, p₃, q₃, hp₁, hq₁, hp₂, hq₂, hp₃, hq₃, ?_⟩
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  interval_cases p₁ <;> interval_cases q₁ <;> interval_cases p₂ <;> interval_cases q₂ <;>
    interval_cases p₃ <;> interval_cases q₃ <;> norm_num at hdet
  all_goals norm_num

/-- Four components of self-intersection `-2w` forming a three-legged star all have the same
weight, and every displayed intersection equals that weight
([Stacks, Lemma 55.5.4](https://stacks.math.columbia.edu/tag/0C80)). -/
theorem exists_weight_intersection_star_four_eq (hcard : 4 < Fintype.card T.Component)
    {i j k l : T.Component}
    (hi : T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hj : T.intersection j j = -(2 * (T.weight j : ℤ)))
    (hk : T.intersection k k = -(2 * (T.weight k : ℤ)))
    (hl : T.intersection l l = -(2 * (T.weight l : ℤ)))
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hij : 0 < T.intersection i j) (hik : 0 < T.intersection i k)
    (hil : 0 < T.intersection i l) :
    ∃ w : ℕ+, (T.weight i : ℤ) = w ∧ (T.weight j : ℤ) = w ∧
      (T.weight k : ℤ) = w ∧ (T.weight l : ℤ) = w ∧
      T.intersection i j = w ∧ T.intersection i k = w ∧ T.intersection i l = w ∧
      T.intersection j k = 0 ∧ T.intersection j l = 0 ∧ T.intersection k l = 0 := by
  have hij' : i ≠ j := by rintro rfl; linarith
  have hik' : i ≠ k := by rintro rfl; linarith
  have hil' : i ≠ l := by rintro rfl; linarith
  have hjk0 := T.intersection_eq_zero_of_intersection_pos_of_intersection_pos
    (by omega) hj hi hk hjk (T.intersection_comm i j ▸ hij) hik
  have hjl0 := T.intersection_eq_zero_of_intersection_pos_of_intersection_pos
    (by omega) hj hi hl hjl (T.intersection_comm i j ▸ hij) hil
  have hkl0 := T.intersection_eq_zero_of_intersection_pos_of_intersection_pos
    (by omega) hk hi hl hkl (T.intersection_comm i k ▸ hik) hil
  obtain ⟨p₁, hp₁⟩ := T.weight_dvd i j
  obtain ⟨q₁, hq₁⟩ : (T.weight j : ℤ) ∣ T.intersection i j :=
    T.intersection_comm j i ▸ T.weight_dvd j i
  obtain ⟨p₂, hp₂⟩ := T.weight_dvd i k
  obtain ⟨q₂, hq₂⟩ : (T.weight k : ℤ) ∣ T.intersection i k :=
    T.intersection_comm k i ▸ T.weight_dvd k i
  obtain ⟨p₃, hp₃⟩ := T.weight_dvd i l
  obtain ⟨q₃, hq₃⟩ : (T.weight l : ℤ) ∣ T.intersection i l :=
    T.intersection_comm l i ▸ T.weight_dvd l i
  have hp₁1 : 1 ≤ p₁ := by
    have := pos_of_mul_pos_right (hp₁ ▸ hij) (by positivity : (0 : ℤ) ≤ T.weight i)
    omega
  have hq₁1 : 1 ≤ q₁ := by
    have := pos_of_mul_pos_right (hq₁ ▸ hij) (by positivity : (0 : ℤ) ≤ T.weight j)
    omega
  have hp₂1 : 1 ≤ p₂ := by
    have := pos_of_mul_pos_right (hp₂ ▸ hik) (by positivity : (0 : ℤ) ≤ T.weight i)
    omega
  have hq₂1 : 1 ≤ q₂ := by
    have := pos_of_mul_pos_right (hq₂ ▸ hik) (by positivity : (0 : ℤ) ≤ T.weight k)
    omega
  have hp₃1 : 1 ≤ p₃ := by
    have := pos_of_mul_pos_right (hp₃ ▸ hil) (by positivity : (0 : ℤ) ≤ T.weight i)
    omega
  have hq₃1 : 1 ≤ q₃ := by
    have := pos_of_mul_pos_right (hq₃ ▸ hil) (by positivity : (0 : ℤ) ≤ T.weight l)
    omega
  have hdet := T.intersection_det_four_pos hcard hij' hik' hil' hjk hjl hkl
  -- With the three leaf-to-leaf intersections zero, positivity of the determinant says that
  -- the sum of the three positive integral normalized edge ratios is less than four.
  rw [hi, hj, hk, hl, hjk0, hjl0, hkl0] at hdet
  have hsq₁ : T.intersection i j ^ 2 =
      (T.weight i : ℤ) * p₁ * ((T.weight j : ℤ) * q₁) := by rw [← hp₁, ← hq₁, sq]
  have hsq₂ : T.intersection i k ^ 2 =
      (T.weight i : ℤ) * p₂ * ((T.weight k : ℤ) * q₂) := by rw [← hp₂, ← hq₂, sq]
  have hsq₃ : T.intersection i l ^ 2 =
      (T.weight i : ℤ) * p₃ * ((T.weight l : ℤ) * q₃) := by rw [← hp₃, ← hq₃, sq]
  rw [hsq₁, hsq₂, hsq₃] at hdet
  have hweights : p₁ * q₁ + p₂ * q₂ + p₃ * q₃ < 4 := by
    have hwi : (0 : ℤ) < T.weight i := by simp
    have hwj : (0 : ℤ) < T.weight j := by simp
    have hwk : (0 : ℤ) < T.weight k := by simp
    have hwl : (0 : ℤ) < T.weight l := by simp
    refine lt_of_mul_lt_mul_left
      (a := (T.weight i : ℤ) * T.weight j * T.weight k * T.weight l) ?_
      (mul_pos (mul_pos (mul_pos hwi hwj) hwk) hwl).le
    ring_nf at hdet ⊢
    omega
  have hpq₁pos : 0 < p₁ * q₁ := mul_pos (by omega) (by omega)
  have hpq₂pos : 0 < p₂ * q₂ := mul_pos (by omega) (by omega)
  have hpq₃pos : 0 < p₃ * q₃ := mul_pos (by omega) (by omega)
  have hpq₁ : p₁ * q₁ = 1 := by omega
  have hpq₂ : p₂ * q₂ = 1 := by omega
  have hpq₃ : p₃ * q₃ = 1 := by omega
  have hp₁le : p₁ ≤ p₁ * q₁ := le_mul_of_one_le_right (by omega) hq₁1
  have hq₁le : q₁ ≤ p₁ * q₁ := le_mul_of_one_le_left (by omega) hp₁1
  have hp₂le : p₂ ≤ p₂ * q₂ := le_mul_of_one_le_right (by omega) hq₂1
  have hq₂le : q₂ ≤ p₂ * q₂ := le_mul_of_one_le_left (by omega) hp₂1
  have hp₃le : p₃ ≤ p₃ * q₃ := le_mul_of_one_le_right (by omega) hq₃1
  have hq₃le : q₃ ≤ p₃ * q₃ := le_mul_of_one_le_left (by omega) hp₃1
  have hp₁eq : p₁ = 1 := by omega
  have hq₁eq : q₁ = 1 := by omega
  have hp₂eq : p₂ = 1 := by omega
  have hq₂eq : q₂ = 1 := by omega
  have hp₃eq : p₃ = 1 := by omega
  have hq₃eq : q₃ = 1 := by omega
  simp only [hp₁eq, hq₁eq, hp₂eq, hq₂eq, hp₃eq, hq₃eq, mul_one] at hp₁ hq₁ hp₂ hq₂ hp₃ hq₃
  refine ⟨T.weight i, ?_⟩
  omega

/-! ### Five components -/

/-- The intersection form of a numerical type at an integral vector supported on five distinct
components `h`, `i`, `j`, `k`, `l` whose intersection numbers vanish on all nonconsecutive pairs
of the chain `h - i - j - k - l` except possibly the pair of ends. Retaining the intersection
number of the two ends lets the statement cover a chain that closes up into a pentagon. The form
is negative as soon as the first entry is nonzero, since the vector is then nonzero and vanishes
at a sixth component. -/
private lemma chain_five_form_neg (hcard : 5 < Fintype.card T.Component)
    {h i j k l : T.Component}
    (hhi : h ≠ i) (hhj : h ≠ j) (hhk : h ≠ k) (hhl : h ≠ l) (hij : i ≠ j) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hhj0 : T.intersection h j = 0) (hhk0 : T.intersection h k = 0)
    (hik0 : T.intersection i k = 0) (hil0 : T.intersection i l = 0)
    (hjl0 : T.intersection j l = 0) (y₁ y₂ y₃ y₄ y₅ : ℤ) (hy₁ : y₁ ≠ 0) :
    T.intersection h h * y₁ ^ 2 + T.intersection i i * y₂ ^ 2 + T.intersection j j * y₃ ^ 2 +
        T.intersection k k * y₄ ^ 2 + T.intersection l l * y₅ ^ 2 +
      2 * (T.intersection h i * y₁ * y₂ + T.intersection i j * y₂ * y₃ +
        T.intersection j k * y₃ * y₄ + T.intersection k l * y₄ * y₅ +
        T.intersection h l * y₁ * y₅) < 0 := by
  have hneg := T.intersection_five_neg hcard hhi hhj hhk hhl hij hik hil hjk hjl hkl
    (y₁ := y₁) (y₂ := y₂) (y₃ := y₃) (y₄ := y₄) (y₅ := y₅)
    (fun hy ↦ hy₁ hy.1)
  rw [hhj0, hhk0, hik0, hil0, hjl0] at hneg
  ring_nf at hneg ⊢
  exact hneg

/-- The intersection form of a numerical type at an integral vector supported on five distinct
components forming the fork with edges `h - i - j - k` and `j - l` is negative when its first
entry is nonzero and the fork is a proper subgraph. -/
private lemma fork_five_form_neg (hcard : 5 < Fintype.card T.Component)
    {h i j k l : T.Component}
    (hhi : h ≠ i) (hhj : h ≠ j) (hhk : h ≠ k) (hhl : h ≠ l) (hij : i ≠ j) (hik : i ≠ k)
    (hil : i ≠ l) (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l)
    (hhj0 : T.intersection h j = 0) (hhk0 : T.intersection h k = 0)
    (hhl0 : T.intersection h l = 0) (hik0 : T.intersection i k = 0)
    (hil0 : T.intersection i l = 0) (hkl0 : T.intersection k l = 0)
    (y₁ y₂ y₃ y₄ y₅ : ℤ) (hy₁ : y₁ ≠ 0) :
    T.intersection h h * y₁ ^ 2 + T.intersection i i * y₂ ^ 2 + T.intersection j j * y₃ ^ 2 +
        T.intersection k k * y₄ ^ 2 + T.intersection l l * y₅ ^ 2 +
      2 * (T.intersection h i * y₁ * y₂ + T.intersection i j * y₂ * y₃ +
        T.intersection j k * y₃ * y₄ + T.intersection j l * y₃ * y₅) < 0 := by
  have hneg := T.intersection_five_neg hcard hhi hhj hhk hhl hij hik hil hjk hjl hkl
    (y₁ := y₁) (y₂ := y₂) (y₃ := y₃) (y₄ := y₄) (y₅ := y₅)
    (fun hy ↦ hy₁ hy.1)
  rw [hhj0, hhk0, hhl0, hik0, hil0, hkl0] at hneg
  ring_nf at hneg ⊢
  exact hneg

/-- The factor data used to classify a chain of five components. The four-component analysis of
the two overlapping windows of the chain shows that every intersection number of two
nonconsecutive components other than that of the two ends vanishes, bounds each of the eight
divisibility factors of the four edges by two, and supplies the two determinant inequalities. -/
private lemma chain_five_factors (hcard : 5 < Fintype.card T.Component)
    {h i j k l : T.Component}
    (hh : T.intersection h h = -(2 * (T.weight h : ℤ)))
    (hi : T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hj : T.intersection j j = -(2 * (T.weight j : ℤ)))
    (hk : T.intersection k k = -(2 * (T.weight k : ℤ)))
    (hl : T.intersection l l = -(2 * (T.weight l : ℤ)))
    (hhj : h ≠ j) (hhk : h ≠ k) (hik : i ≠ k) (hil : i ≠ l) (hjl : j ≠ l)
    (hhi : 0 < T.intersection h i) (hij : 0 < T.intersection i j)
    (hjk : 0 < T.intersection j k) (hkl : 0 < T.intersection k l) :
    T.intersection h j = 0 ∧ T.intersection h k = 0 ∧ T.intersection i k = 0 ∧
      T.intersection i l = 0 ∧ T.intersection j l = 0 ∧
      ∃ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ : ℤ,
        1 ≤ p₁ ∧ p₁ ≤ 2 ∧ 1 ≤ q₁ ∧ q₁ ≤ 2 ∧
        1 ≤ p₂ ∧ p₂ ≤ 2 ∧ 1 ≤ q₂ ∧ q₂ ≤ 2 ∧
        1 ≤ p₃ ∧ p₃ ≤ 2 ∧ 1 ≤ q₃ ∧ q₃ ≤ 2 ∧
        1 ≤ p₄ ∧ p₄ ≤ 2 ∧ 1 ≤ q₄ ∧ q₄ ≤ 2 ∧
        T.intersection h i = (T.weight h : ℤ) * p₁ ∧
        T.intersection h i = (T.weight i : ℤ) * q₁ ∧
        T.intersection i j = (T.weight i : ℤ) * p₂ ∧
        T.intersection i j = (T.weight j : ℤ) * q₂ ∧
        T.intersection j k = (T.weight j : ℤ) * p₃ ∧
        T.intersection j k = (T.weight k : ℤ) * q₃ ∧
        T.intersection k l = (T.weight k : ℤ) * p₄ ∧
        T.intersection k l = (T.weight l : ℤ) * q₄ ∧
        4 * (p₁ * q₁ + p₂ * q₂ + p₃ * q₃) < 16 + p₁ * q₁ * p₃ * q₃ ∧
        4 * (p₂ * q₂ + p₃ * q₃ + p₄ * q₄) < 16 + p₂ * q₂ * p₄ * q₄ := by
  obtain ⟨hhj0, hik0, hhk0, p₁, q₁, p₂, q₂, p₃, q₃, hp₁1, hp₁2, hq₁1, hq₁2, hp₂1, hp₂2,
      hq₂1, hq₂2, hp₃1, hp₃2, hq₃1, hq₃2, hp₁, hq₁, hp₂, hq₂, hp₃, hq₃, hdet₁⟩ :=
    T.chain_four_factors (by omega) hh hi hj hk hhj hhk hik hhi hij hjk
  obtain ⟨-, hjl0, hil0, p₂', q₂', p₃', q₃', p₄, q₄, -, -, -, -, -, -, -, -,
      hp₄1, hp₄2, hq₄1, hq₄2, hp₂', hq₂', hp₃', hq₃', hp₄, hq₄, hdet₂⟩ :=
    T.chain_four_factors (by omega) hi hj hk hl hik hil hjl hij hjk hkl
  have hwi : (0 : ℤ) < T.weight i := by simp
  have hwj : (0 : ℤ) < T.weight j := by simp
  have hwk : (0 : ℤ) < T.weight k := by simp
  -- The two windows factor the two shared edges by the same weights, hence identically.
  have e₂p : p₂' = p₂ := mul_left_cancel₀ hwi.ne' (hp₂'.symm.trans hp₂)
  have e₂q : q₂' = q₂ := mul_left_cancel₀ hwj.ne' (hq₂'.symm.trans hq₂)
  have e₃p : p₃' = p₃ := mul_left_cancel₀ hwj.ne' (hp₃'.symm.trans hp₃)
  have e₃q : q₃' = q₃ := mul_left_cancel₀ hwk.ne' (hq₃'.symm.trans hq₃)
  rw [e₂p, e₂q, e₃p, e₃q] at hdet₂
  exact ⟨hhj0, hhk0, hik0, hil0, hjl0, p₁, q₁, p₂, q₂, p₃, q₃, p₄, q₄, hp₁1, hp₁2, hq₁1, hq₁2,
    hp₂1, hp₂2, hq₂1, hq₂2, hp₃1, hp₃2, hq₃1, hq₃2, hp₄1, hp₄2, hq₄1, hq₄2, hp₁, hq₁, hp₂, hq₂,
    hp₃, hq₃, hp₄, hq₄, hdet₁, hdet₂⟩

/-- For five components in a chain, all of self-intersection `-2w`, the four normalized adjacent
intersection ratios are `(1, 1, 1, 1)`, `(1, 1, 1, 2)` or `(2, 1, 1, 1)`: a double edge occurs
only at one of the two ends of the chain, and a triple edge not at all. The factors in the
statement express `aᵢⱼ²/(wᵢwⱼ)` without division, and together with the divisibility of each row
by its weight they give the weight patterns of
[Stacks, Lemma 55.5.5](https://stacks.math.columbia.edu/tag/0C82): all five weights equal, or
four equal weights together with, at one end, their double or their half.

The two windows of four consecutive components leave three further ratio patterns, carrying a
double edge in the middle of the chain or double edges at both of its ends. Each is ruled out by
an explicit positive vector at which the intersection form vanishes, which negative definiteness
on the vectors supported on a proper subset of the components forbids. -/
theorem exists_intersection_ratio_chain_five_mem (hcard : 5 < Fintype.card T.Component)
    {h i j k l : T.Component}
    (hh : T.intersection h h = -(2 * (T.weight h : ℤ)))
    (hi : T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hj : T.intersection j j = -(2 * (T.weight j : ℤ)))
    (hk : T.intersection k k = -(2 * (T.weight k : ℤ)))
    (hl : T.intersection l l = -(2 * (T.weight l : ℤ)))
    (hhj : h ≠ j) (hhk : h ≠ k) (hhl : h ≠ l) (hik : i ≠ k) (hil : i ≠ l) (hjl : j ≠ l)
    (hhi : 0 < T.intersection h i) (hij : 0 < T.intersection i j)
    (hjk : 0 < T.intersection j k) (hkl : 0 < T.intersection k l) :
    ∃ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ : ℤ,
      T.intersection h i = (T.weight h : ℤ) * p₁ ∧
      T.intersection h i = (T.weight i : ℤ) * q₁ ∧
      T.intersection i j = (T.weight i : ℤ) * p₂ ∧
      T.intersection i j = (T.weight j : ℤ) * q₂ ∧
      T.intersection j k = (T.weight j : ℤ) * p₃ ∧
      T.intersection j k = (T.weight k : ℤ) * q₃ ∧
      T.intersection k l = (T.weight k : ℤ) * p₄ ∧
      T.intersection k l = (T.weight l : ℤ) * q₄ ∧
      (p₁ * q₁, p₂ * q₂, p₃ * q₃, p₄ * q₄) ∈
        ({(1, 1, 1, 1), (1, 1, 1, 2), (2, 1, 1, 1)} : Set (ℤ × ℤ × ℤ × ℤ)) := by
  obtain ⟨hhj0, hhk0, hik0, hil0, hjl0, p₁, q₁, p₂, q₂, p₃, q₃, p₄, q₄, hp₁1, hp₁2, hq₁1, hq₁2,
      hp₂1, hp₂2, hq₂1, hq₂2, hp₃1, hp₃2, hq₃1, hq₃2, hp₄1, hp₄2, hq₄1, hq₄2, hp₁, hq₁, hp₂, hq₂,
      hp₃, hq₃, hp₄, hq₄, hdet₁, hdet₂⟩ :=
    T.chain_five_factors hcard hh hi hj hk hl hhj hhk hik hil hjl hhi hij hjk hkl
  refine ⟨p₁, q₁, p₂, q₂, p₃, q₃, p₄, q₄, hp₁, hq₁, hp₂, hq₂, hp₃, hq₃, hp₄, hq₄, ?_⟩
  have hhi' : h ≠ i := by rintro rfl; linarith
  have hij' : i ≠ j := by rintro rfl; linarith
  have hjk' : j ≠ k := by rintro rfl; linarith
  have hkl' : k ≠ l := by rintro rfl; linarith
  have hhl0 : 0 ≤ T.intersection h l := T.offDiagonal_nonneg h l hhl
  have key := T.chain_five_form_neg hcard hhi' hhj hhk hhl hij' hik hil hjk' hjl hkl'
    hhj0 hhk0 hik0 hil0 hjl0
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq]
  -- The eight remaining orientations of the three excluded ratio patterns are affine; the seven
  -- vectors below span the kernels of their Cartan matrices, so the form vanishes there.
  interval_cases p₁ <;> interval_cases q₁ <;> interval_cases p₂ <;> interval_cases q₂ <;>
    interval_cases p₃ <;> interval_cases q₃ <;> interval_cases p₄ <;> interval_cases q₄ <;>
    first
      | omega
      | (exfalso; linarith [key 1 2 3 4 2 one_ne_zero])
      | (exfalso; linarith [key 1 2 3 2 1 one_ne_zero])
      | (exfalso; linarith [key 2 4 3 2 1 (by norm_num)])
      | (exfalso; linarith [key 1 1 1 1 1 one_ne_zero])
      | (exfalso; linarith [key 1 2 2 2 1 one_ne_zero])
      | (exfalso; linarith [key 2 2 2 2 1 (by norm_num)])
      | (exfalso; linarith [key 1 2 2 2 2 one_ne_zero])

/-- In a chain of five components of self-intersection `-2w`, the two middle edges are simply
laced: the three middle components share a weight, and it is the intersection number of both
middle pairs. This is the part of
[Stacks, Lemma 55.5.5](https://stacks.math.columbia.edu/tag/0C82) common to its three cases, in
all of which a double edge can only occur at one of the two ends of the chain. -/
theorem intersection_eq_weight_of_chain_five (hcard : 5 < Fintype.card T.Component)
    {h i j k l : T.Component}
    (hh : T.intersection h h = -(2 * (T.weight h : ℤ)))
    (hi : T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hj : T.intersection j j = -(2 * (T.weight j : ℤ)))
    (hk : T.intersection k k = -(2 * (T.weight k : ℤ)))
    (hl : T.intersection l l = -(2 * (T.weight l : ℤ)))
    (hhj : h ≠ j) (hhk : h ≠ k) (hhl : h ≠ l) (hik : i ≠ k) (hil : i ≠ l) (hjl : j ≠ l)
    (hhi : 0 < T.intersection h i) (hij : 0 < T.intersection i j)
    (hjk : 0 < T.intersection j k) (hkl : 0 < T.intersection k l) :
    T.intersection i j = (T.weight i : ℤ) ∧ T.intersection i j = (T.weight j : ℤ) ∧
      T.intersection j k = (T.weight j : ℤ) ∧ T.intersection j k = (T.weight k : ℤ) := by
  obtain ⟨p₁, q₁, p₂, q₂, p₃, q₃, p₄, q₄, -, -, hp₂, hq₂, hp₃, hq₃, -, -, hmem⟩ :=
    T.exists_intersection_ratio_chain_five_mem hcard hh hi hj hk hl hhj hhk hhl hik hil hjl
      hhi hij hjk hkl
  have hwi : (0 : ℤ) < T.weight i := by simp
  have hwj : (0 : ℤ) < T.weight j := by simp
  have hwk : (0 : ℤ) < T.weight k := by simp
  have hp₂0 : 0 < p₂ := pos_of_mul_pos_right (hp₂ ▸ hij) hwi.le
  have hq₂0 : 0 < q₂ := pos_of_mul_pos_right (hq₂ ▸ hij) hwj.le
  have hp₃0 : 0 < p₃ := pos_of_mul_pos_right (hp₃ ▸ hjk) hwj.le
  have hq₃0 : 0 < q₃ := pos_of_mul_pos_right (hq₃ ▸ hjk) hwk.le
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hmem
  -- In each of the three patterns the two middle ratios are one.
  obtain ⟨h₂, h₃⟩ : p₂ * q₂ = 1 ∧ p₃ * q₃ = 1 := by
    rcases hmem with hm | hm | hm <;> exact ⟨hm.2.1, hm.2.2.1⟩
  have hp₂le : p₂ ≤ p₂ * q₂ := le_mul_of_one_le_right hp₂0.le hq₂0
  have hq₂le : q₂ ≤ p₂ * q₂ := le_mul_of_one_le_left hq₂0.le hp₂0
  have hp₃le : p₃ ≤ p₃ * q₃ := le_mul_of_one_le_right hp₃0.le hq₃0
  have hq₃le : q₃ ≤ p₃ * q₃ := le_mul_of_one_le_left hq₃0.le hp₃0
  have hp₂1 : p₂ = 1 := by linarith
  have hq₂1 : q₂ = 1 := by linarith
  have hp₃1 : p₃ = 1 := by linarith
  have hq₃1 : q₃ = 1 := by linarith
  rw [hp₂1, mul_one] at hp₂
  rw [hq₂1, mul_one] at hq₂
  rw [hp₃1, mul_one] at hp₃
  rw [hq₃1, mul_one] at hq₃
  exact ⟨hp₂, hq₂, hp₃, hq₃⟩

/-- In a chain of five components of self-intersection `-2w`, every nonconsecutive intersection
vanishes: in particular the chain does not close up into a pentagon. This is the graph-shape part
of [Stacks, Lemma 55.5.5](https://stacks.math.columbia.edu/tag/0C82). -/
theorem intersection_eq_zero_of_chain_five (hcard : 5 < Fintype.card T.Component)
    {h i j k l : T.Component}
    (hh : T.intersection h h = -(2 * (T.weight h : ℤ)))
    (hi : T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hj : T.intersection j j = -(2 * (T.weight j : ℤ)))
    (hk : T.intersection k k = -(2 * (T.weight k : ℤ)))
    (hl : T.intersection l l = -(2 * (T.weight l : ℤ)))
    (hhj : h ≠ j) (hhk : h ≠ k) (hhl : h ≠ l) (hik : i ≠ k) (hil : i ≠ l) (hjl : j ≠ l)
    (hhi : 0 < T.intersection h i) (hij : 0 < T.intersection i j)
    (hjk : 0 < T.intersection j k) (hkl : 0 < T.intersection k l) :
    T.intersection h j = 0 ∧ T.intersection h k = 0 ∧ T.intersection h l = 0 ∧
      T.intersection i k = 0 ∧ T.intersection i l = 0 ∧ T.intersection j l = 0 := by
  obtain ⟨hhj0, hhk0, hik0, hil0, hjl0, -⟩ :=
    T.chain_five_factors hcard hh hi hj hk hl hhj hhk hik hil hjl hhi hij hjk hkl
  refine ⟨hhj0, hhk0, ?_, hik0, hil0, hjl0⟩
  by_contra hne
  have hhl0 : 0 < T.intersection h l := (T.offDiagonal_nonneg h l hhl).lt_of_ne (Ne.symm hne)
  have hlh0 : 0 < T.intersection l h := T.intersection_comm h l ▸ hhl0
  have hhi' : h ≠ i := by rintro rfl; linarith
  have hij' : i ≠ j := by rintro rfl; linarith
  have hjk' : j ≠ k := by rintro rfl; linarith
  have hkl' : k ≠ l := by rintro rfl; linarith
  -- The chain now closes up into a pentagon. Reading the simply-laced middle of three rotations
  -- of it shows that all five weights agree and that each of its five edges has that weight.
  obtain ⟨e₂i, e₂j, e₃j, e₃k⟩ := T.intersection_eq_weight_of_chain_five hcard hh hi hj hk hl
    hhj hhk hhl hik hil hjl hhi hij hjk hkl
  obtain ⟨e₄k, e₄l, e₅l, e₅h⟩ := T.intersection_eq_weight_of_chain_five hcard hj hk hl hh hi
    hjl hhj.symm hij'.symm hhk.symm hik.symm hil.symm hjk hkl hlh0 hhi
  obtain ⟨e₁h, e₁i, -, -⟩ := T.intersection_eq_weight_of_chain_five hcard hl hh hi hj hk
    hil.symm hjl.symm hkl'.symm hhj hhk hik hlh0 hhi hij hjk
  have hcomm : T.intersection h l = T.intersection l h := T.intersection_comm h l
  linarith [T.chain_five_form_neg hcard hhi' hhj hhk hhl hij' hik hil hjk' hjl hkl'
    hhj0 hhk0 hik0 hil0 hjl0 1 1 1 1 1 one_ne_zero]

/-- A component of self-intersection `-2w` meeting three others of self-intersection `-2w` meets
no fourth such component, in a numerical type with more than five components. In particular, the
four-legged star does not occur as a proper subgraph of `(-2)`-indices
([Stacks, Lemma 55.5.6](https://stacks.math.columbia.edu/tag/0C86)). -/
theorem intersection_eq_zero_of_star_five (hcard : 5 < Fintype.card T.Component)
    {c₁ c₂ c₃ c₄ c₅ : T.Component}
    (h₁ : T.intersection c₁ c₁ = -(2 * (T.weight c₁ : ℤ)))
    (h₂ : T.intersection c₂ c₂ = -(2 * (T.weight c₂ : ℤ)))
    (h₃ : T.intersection c₃ c₃ = -(2 * (T.weight c₃ : ℤ)))
    (h₄ : T.intersection c₄ c₄ = -(2 * (T.weight c₄ : ℤ)))
    (h₅ : T.intersection c₅ c₅ = -(2 * (T.weight c₅ : ℤ)))
    (h₁₅ : c₁ ≠ c₅) (h₂₃ : c₂ ≠ c₃) (h₂₄ : c₂ ≠ c₄) (h₂₅ : c₂ ≠ c₅) (h₃₄ : c₃ ≠ c₄)
    (h₃₅ : c₃ ≠ c₅) (h₄₅ : c₄ ≠ c₅) (e₁₂ : 0 < T.intersection c₁ c₂)
    (e₁₃ : 0 < T.intersection c₁ c₃) (e₁₄ : 0 < T.intersection c₁ c₄) :
    T.intersection c₁ c₅ = 0 := by
  classical
  have h₁₂ : c₁ ≠ c₂ := by rintro rfl; linarith
  have h₁₃ : c₁ ≠ c₃ := by rintro rfl; linarith
  have h₁₄ : c₁ ≠ c₄ := by rintro rfl; linarith
  by_contra hne
  have e₁₅ : 0 < T.intersection c₁ c₅ :=
    ((T.offDiagonal_nonneg c₁ c₅ h₁₅).lt_or_eq).resolve_right fun hzero ↦ hne hzero.symm
  -- Each of the four legs, taken three at a time, is a three-legged star: all weights agree, all
  -- displayed intersection numbers equal that weight, and the legs are pairwise disjoint.
  obtain ⟨w, hw, hw₂, hw₃, hw₄, a₁₂, a₁₃, a₁₄, z₂₃, z₂₄, z₃₄⟩ :=
    T.exists_weight_intersection_star_four_eq (by omega) h₁ h₂ h₃ h₄ h₂₃ h₂₄ h₃₄ e₁₂ e₁₃ e₁₄
  obtain ⟨w', hw', -, -, hw₅, -, -, a₁₅, -, z₂₅, z₃₅⟩ :=
    T.exists_weight_intersection_star_four_eq (by omega) h₁ h₂ h₃ h₅ h₂₃ h₂₅ h₃₅ e₁₂ e₁₃ e₁₅
  obtain ⟨-, -, -, -, -, -, -, -, -, -, z₄₅⟩ :=
    T.exists_weight_intersection_star_four_eq (by omega) h₁ h₂ h₄ h₅ h₂₄ h₂₅ h₄₅ e₁₂ e₁₄ e₁₅
  have hww : (w : ℤ) = w' := by omega
  -- The vector taking the value two at the centre and one at each leg is isotropic.
  have hneg := T.intersection_five_neg hcard h₁₂ h₁₃ h₁₄ h₁₅ h₂₃ h₂₄ h₂₅ h₃₄ h₃₅ h₄₅
    (y₁ := 2) (y₂ := 1) (y₃ := 1) (y₄ := 1) (y₅ := 1) (by omega)
  rw [h₁, h₂, h₃, h₄, h₅, a₁₂, a₁₃, a₁₄, a₁₅, z₂₃, z₂₄, z₂₅, z₃₄, z₃₅, z₄₅] at hneg
  simp only [one_pow, mul_one] at hneg
  rw [hw, hw₂, hw₃, hw₄, hw₅] at hneg
  linarith

/-- Five components of self-intersection `-2w` in a numerical type with more than five components
forming the fork

`h - i - j - k`, with a second leaf `l` at `j`,

all have the same weight, every displayed intersection equals that weight, and every other
intersection vanishes. This is the classification of
[Stacks, Lemma 55.5.7](https://stacks.math.columbia.edu/tag/0C87). The corresponding inequalities
on the multiplicities follow from `TauCeti.NumericalType.multiplicity_mul_intersection_le`. -/
theorem exists_weight_intersection_fork_five_eq (hcard : 5 < Fintype.card T.Component)
    {h i j k l : T.Component}
    (hh : T.intersection h h = -(2 * (T.weight h : ℤ)))
    (hi : T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hj : T.intersection j j = -(2 * (T.weight j : ℤ)))
    (hk : T.intersection k k = -(2 * (T.weight k : ℤ)))
    (hl : T.intersection l l = -(2 * (T.weight l : ℤ)))
    (hhj : h ≠ j) (hhk : h ≠ k) (hhl : h ≠ l) (hik : i ≠ k) (hil : i ≠ l)
    (hkl : k ≠ l) (hhi : 0 < T.intersection h i) (hij : 0 < T.intersection i j)
    (hjk : 0 < T.intersection j k) (hjl : 0 < T.intersection j l) :
    ∃ w : ℕ+, (T.weight h : ℤ) = w ∧ (T.weight i : ℤ) = w ∧
      (T.weight j : ℤ) = w ∧ (T.weight k : ℤ) = w ∧ (T.weight l : ℤ) = w ∧
      T.intersection h i = w ∧ T.intersection i j = w ∧ T.intersection j k = w ∧
      T.intersection j l = w ∧ T.intersection h j = 0 ∧ T.intersection h k = 0 ∧
      T.intersection h l = 0 ∧ T.intersection i k = 0 ∧ T.intersection i l = 0 ∧
      T.intersection k l = 0 := by
  have hhi' : h ≠ i := by rintro rfl; linarith
  have hij' : i ≠ j := by rintro rfl; linarith
  have hjk' : j ≠ k := by rintro rfl; linarith
  have hjl' : j ≠ l := by rintro rfl; linarith
  -- The three-legged star at `j` fixes four weights and its three edges. The chain from `h` to `k`
  -- shows that no additional edge can meet `h` and bounds the divisibility factors of `h - i`.
  obtain ⟨w, hwj, hwi, hwk, hwl, aji, ajk, ajl, zik, zil, zkl⟩ :=
    T.exists_weight_intersection_star_four_eq (by omega) hj hi hk hl hik hil hkl
      (T.intersection_comm i j ▸ hij) hjk hjl
  have aij : T.intersection i j = w := T.intersection_comm j i ▸ aji
  obtain ⟨zhj, -, zhk, p₁, q₁, p₂, q₂, p₃, q₃, hp₁1, hp₁2, hq₁1, hq₁2, -, -, -, -, -, -, -, -,
      ap₁, aq₁, ap₂, aq₂, ap₃, aq₃, hdet⟩ :=
    T.chain_four_factors (by omega) hh hi hj hk hhj hhk hik hhi hij hjk
  obtain ⟨-, -, zhl⟩ := T.intersection_eq_zero_of_chain_four (by omega) hh hi hj hl
    hhj hhl hil hhi hij hjl
  have hw0 : (w : ℤ) ≠ 0 := by positivity
  have factor_eq_one (a : ℤ) (ha : (w : ℤ) = w * a) : a = 1 := by
    exact (mul_left_cancel₀ hw0 (by rw [mul_one]; exact ha)).symm
  have hp₂1 : p₂ = 1 := by
    rw [hwi, aij] at ap₂
    exact factor_eq_one p₂ ap₂
  have hq₂1 : q₂ = 1 := by
    rw [hwj, aij] at aq₂
    exact factor_eq_one q₂ aq₂
  have hp₃1 : p₃ = 1 := by
    rw [hwj, ajk] at ap₃
    exact factor_eq_one p₃ ap₃
  have hq₃1 : q₃ = 1 := by
    rw [hwk, ajk] at aq₃
    exact factor_eq_one q₃ aq₃
  have hpqle : p₁ * q₁ ≤ 2 := by
    rw [hp₂1, hq₂1, hp₃1, hq₃1] at hdet
    norm_num at hdet
    omega
  have hpq1 : p₁ * q₁ = 1 := by
    rcases eq_or_lt_of_le hpqle with hpq | hpq
    · have hp₁_cases : p₁ = 1 ∨ p₁ = 2 := by omega
      have hpq_cases : (p₁ = 1 ∧ q₁ = 2) ∨ (p₁ = 2 ∧ q₁ = 1) := by
        rcases hp₁_cases with rfl | rfl <;> simp_all
      -- The two orientations of ratio two are affine. Their displayed vectors span the kernels
      -- of the corresponding intersection matrices, contradicting negative definiteness.
      rcases hpq_cases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · have hwh : (T.weight h : ℤ) = 2 * w := by
          rw [hwi] at aq₁
          omega
        have ahi : T.intersection h i = 2 * w := by
          rw [hwi] at aq₁
          rw [mul_comm]
          exact aq₁
        linarith [T.fork_five_form_neg hcard hhi' hhj hhk hhl hij' hik hil hjk' hjl' hkl
          zhj zhk zhl zik zil zkl 1 2 2 1 1 one_ne_zero]
      · have hwh : 2 * (T.weight h : ℤ) = w := by
          rw [hwi] at aq₁
          omega
        have ahi : T.intersection h i = w := by
          rw [hwi, mul_one] at aq₁
          exact aq₁
        linarith [T.fork_five_form_neg hcard hhi' hhj hhk hhl hij' hik hil hjk' hjl' hkl
          zhj zhk zhl zik zil zkl 2 2 2 1 1 (by omega)]
    · have hpqpos : 0 < p₁ * q₁ := mul_pos (by omega) (by omega)
      omega
  have hp₁le : p₁ ≤ p₁ * q₁ := le_mul_of_one_le_right (by omega) hq₁1
  have hq₁le : q₁ ≤ p₁ * q₁ := le_mul_of_one_le_left (by omega) hp₁1
  have hp₁1 : p₁ = 1 := by omega
  have hq₁1 : q₁ = 1 := by omega
  have ahi : T.intersection h i = w := by rw [hwi, hq₁1, mul_one] at aq₁; exact aq₁
  have hwh : (T.weight h : ℤ) = w := by rw [hp₁1, mul_one, ahi] at ap₁; exact ap₁.symm
  exact ⟨w, hwh, hwi, hwj, hwk, hwl, ahi, aij, ajk, ajl, zhj, zhk, zhl, zik, zil, zkl⟩

/-! ### Six components -/

/-- The factor data used to classify a chain of six components. -/
private theorem chain_six_factors (hcard : 6 < Fintype.card T.Component)
    {g h i j k l : T.Component}
    (hg : T.intersection g g = -(2 * (T.weight g : ℤ)))
    (hh : T.intersection h h = -(2 * (T.weight h : ℤ)))
    (hi : T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hj : T.intersection j j = -(2 * (T.weight j : ℤ)))
    (hk : T.intersection k k = -(2 * (T.weight k : ℤ)))
    (hl : T.intersection l l = -(2 * (T.weight l : ℤ)))
    (hgi : g ≠ i) (hgj : g ≠ j) (hgk : g ≠ k) (hgl : g ≠ l)
    (hhj : h ≠ j) (hhk : h ≠ k) (hhl : h ≠ l) (hik : i ≠ k) (hil : i ≠ l)
    (hjl : j ≠ l) (egh : 0 < T.intersection g h) (ehi : 0 < T.intersection h i)
    (eij : 0 < T.intersection i j) (ejk : 0 < T.intersection j k)
    (ekl : 0 < T.intersection k l) :
    T.intersection g i = 0 ∧ T.intersection g j = 0 ∧ T.intersection g k = 0 ∧
      T.intersection g l = 0 ∧ T.intersection h j = 0 ∧ T.intersection h k = 0 ∧
      T.intersection h l = 0 ∧ T.intersection i k = 0 ∧ T.intersection i l = 0 ∧
      T.intersection j l = 0 ∧
      ∃ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ p₅ q₅ : ℤ,
        T.intersection g h = (T.weight g : ℤ) * p₁ ∧
        T.intersection g h = (T.weight h : ℤ) * q₁ ∧
        T.intersection h i = (T.weight h : ℤ) * p₂ ∧
        T.intersection h i = (T.weight i : ℤ) * q₂ ∧
        T.intersection i j = (T.weight i : ℤ) * p₃ ∧
        T.intersection i j = (T.weight j : ℤ) * q₃ ∧
        T.intersection j k = (T.weight j : ℤ) * p₄ ∧
        T.intersection j k = (T.weight k : ℤ) * q₄ ∧
        T.intersection k l = (T.weight k : ℤ) * p₅ ∧
        T.intersection k l = (T.weight l : ℤ) * q₅ ∧
        (p₁ * q₁, p₂ * q₂, p₃ * q₃, p₄ * q₄, p₅ * q₅) ∈
          ({(1, 1, 1, 1, 1), (2, 1, 1, 1, 1), (1, 1, 1, 1, 2)} :
            Set (ℤ × ℤ × ℤ × ℤ × ℤ)) := by
  have hgh : g ≠ h := by rintro rfl; linarith
  have hhi : h ≠ i := by rintro rfl; linarith
  have hij : i ≠ j := by rintro rfl; linarith
  have hjk : j ≠ k := by rintro rfl; linarith
  have hkl : k ≠ l := by rintro rfl; linarith
  obtain ⟨zgi, zgj, zgk, zhj, zhk, zik⟩ :=
    T.intersection_eq_zero_of_chain_five (by omega) hg hh hi hj hk hgi hgj hgk hhj hhk hik
      egh ehi eij ejk
  obtain ⟨zhj', zhk', zhl, zik', zil, zjl⟩ :=
    T.intersection_eq_zero_of_chain_five (by omega) hh hi hj hk hl hhj hhk hhl hik hil hjl
      ehi eij ejk ekl
  have zgl : T.intersection g l = 0 := by
    by_contra hne
    have egl : 0 < T.intersection g l := (T.offDiagonal_nonneg g l hgl).lt_of_ne (Ne.symm hne)
    have elg : 0 < T.intersection l g := T.intersection_comm g l ▸ egl
    obtain ⟨ahi, wh, aij, wi⟩ := T.intersection_eq_weight_of_chain_five (by omega)
      hg hh hi hj hk hgi hgj hgk hhj hhk hik egh ehi eij ejk
    obtain ⟨aij', wi', ajk, wj⟩ := T.intersection_eq_weight_of_chain_five (by omega)
      hh hi hj hk hl hhj hhk hhl hik hil hjl ehi eij ejk ekl
    obtain ⟨akl, wk, alg, wl⟩ := T.intersection_eq_weight_of_chain_five (by omega)
      hj hk hl hg hh hjl hgj.symm hhj.symm hgk.symm hhk.symm hhl.symm ejk ekl elg egh
    obtain ⟨alg', wl', agh, wg⟩ := T.intersection_eq_weight_of_chain_five (by omega)
      hk hl hg hh hi hgk.symm hhk.symm hik.symm hhl.symm hil.symm hgi ekl elg egh ehi
    have agl : T.intersection g l = (T.weight l : ℤ) := T.intersection_comm l g ▸ alg
    have hform := T.intersection_six_neg hcard hgh hgi hgj hgk hgl hhi hhj hhk hhl hij hik
      hil hjk hjl hkl (y₁ := 1) (y₂ := 1) (y₃ := 1) (y₄ := 1) (y₅ := 1) (y₆ := 1)
      (by norm_num)
    rw [hg, hh, hi, hj, hk, hl, zgi, zgj, zgk, zhj, zhk, zhl, zik, zil, zjl,
      agh, ahi, aij, ajk, akl, agl] at hform
    simp only [one_pow, mul_one] at hform
    linarith
  obtain ⟨p₁, q₁, p₂, q₂, p₃, q₃, p₄, q₄, ap₁, aq₁, ap₂, aq₂, ap₃, aq₃,
      ap₄, aq₄, hm₁⟩ := T.exists_intersection_ratio_chain_five_mem (by omega)
    hg hh hi hj hk hgi hgj hgk hhj hhk hik egh ehi eij ejk
  obtain ⟨r₂, s₂, r₃, s₃, r₄, s₄, p₅, q₅, bp₂, bq₂, bp₃, bq₃, bp₄, bq₄,
      ap₅, aq₅, hm₂⟩ := T.exists_intersection_ratio_chain_five_mem (by omega)
    hh hi hj hk hl hhj hhk hhl hik hil hjl ehi eij ejk ekl
  have hp₂ : p₂ = r₂ := mul_left_cancel₀ (by positivity : (T.weight h : ℤ) ≠ 0) (ap₂.symm.trans bp₂)
  have hq₂ : q₂ = s₂ := mul_left_cancel₀ (by positivity : (T.weight i : ℤ) ≠ 0) (aq₂.symm.trans bq₂)
  have hp₃ : p₃ = r₃ := mul_left_cancel₀ (by positivity : (T.weight i : ℤ) ≠ 0) (ap₃.symm.trans bp₃)
  have hq₃ : q₃ = s₃ := mul_left_cancel₀ (by positivity : (T.weight j : ℤ) ≠ 0) (aq₃.symm.trans bq₃)
  have hp₄ : p₄ = r₄ := mul_left_cancel₀ (by positivity : (T.weight j : ℤ) ≠ 0) (ap₄.symm.trans bp₄)
  have hq₄ : q₄ = s₄ := mul_left_cancel₀ (by positivity : (T.weight k : ℤ) ≠ 0) (aq₄.symm.trans bq₄)
  subst r₂; subst s₂; subst r₃; subst s₃; subst r₄; subst s₄
  have factor_pos {a w e : ℤ} (hw : 0 < w) (he : 0 < e) (ha : e = w * a) : 0 < a :=
    pos_of_mul_pos_right (ha ▸ he) hw.le
  have hp₁pos := factor_pos (by simp : (0 : ℤ) < T.weight g) egh ap₁
  have hq₁pos := factor_pos (by simp : (0 : ℤ) < T.weight h) egh aq₁
  have hp₂pos := factor_pos (by simp : (0 : ℤ) < T.weight h) ehi ap₂
  have hq₂pos := factor_pos (by simp : (0 : ℤ) < T.weight i) ehi aq₂
  have hp₃pos := factor_pos (by simp : (0 : ℤ) < T.weight i) eij ap₃
  have hq₃pos := factor_pos (by simp : (0 : ℤ) < T.weight j) eij aq₃
  have hp₄pos := factor_pos (by simp : (0 : ℤ) < T.weight j) ejk ap₄
  have hq₄pos := factor_pos (by simp : (0 : ℤ) < T.weight k) ejk aq₄
  have hp₅pos := factor_pos (by simp : (0 : ℤ) < T.weight k) ekl ap₅
  have hq₅pos := factor_pos (by simp : (0 : ℤ) < T.weight l) ekl aq₅
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Prod.mk.injEq] at hm₁ hm₂ ⊢
  refine ⟨zgi, zgj, zgk, zgl, zhj, zhk, zhl, zik, zil, zjl, p₁, q₁, p₂, q₂, p₃, q₃, p₄,
    q₄, p₅, q₅, ap₁, aq₁, ap₂, aq₂, ap₃, aq₃, ap₄, aq₄, ap₅, aq₅, ?_⟩
  by_cases hbad : p₁ * q₁ = 2 ∧ p₅ * q₅ = 2
  · exfalso
    have hmids : p₂ * q₂ = 1 ∧ p₃ * q₃ = 1 ∧ p₄ * q₄ = 1 := by
      rcases hm₁ with h | h | h <;> omega
    have eq_one_of_mul_eq_one {a b : ℤ} (ha : 0 < a) (hb : 0 < b) (hab : a * b = 1) :
        a = 1 ∧ b = 1 := by
      have ha_le : a ≤ a * b := le_mul_of_one_le_right ha.le (by omega)
      have hb_le : b ≤ a * b := le_mul_of_one_le_left hb.le (by omega)
      omega
    obtain ⟨hp₂, hq₂⟩ := eq_one_of_mul_eq_one hp₂pos hq₂pos hmids.1
    obtain ⟨hp₃, hq₃⟩ := eq_one_of_mul_eq_one hp₃pos hq₃pos hmids.2.1
    obtain ⟨hp₄, hq₄⟩ := eq_one_of_mul_eq_one hp₄pos hq₄pos hmids.2.2
    have factors_of_mul_eq_two {a b : ℤ} (ha : 0 < a) (hb : 0 < b) (hab : a * b = 2) :
        (a = 1 ∧ b = 2) ∨ (a = 2 ∧ b = 1) := by
      have ha_le : a ≤ a * b := le_mul_of_one_le_right ha.le (by omega)
      have hb_le : b ≤ a * b := le_mul_of_one_le_left hb.le (by omega)
      have ha_two : a ≤ 2 := by omega
      have hb_two : b ≤ 2 := by omega
      interval_cases a <;> interval_cases b <;> omega
    rcases factors_of_mul_eq_two hp₁pos hq₁pos hbad.1 with
      ⟨hp₁, hq₁⟩ | ⟨hp₁, hq₁⟩ <;>
      rcases factors_of_mul_eq_two hp₅pos hq₅pos hbad.2 with
        ⟨hp₅, hq₅⟩ | ⟨hp₅, hq₅⟩
    all_goals subst_vars
    all_goals first
      | have key := T.intersection_six_neg hcard hgh hgi hgj hgk hgl hhi hhj hhk hhl hij hik
          hil hjk hjl hkl (y₁ := 1) (y₂ := 2) (y₃ := 2) (y₄ := 2) (y₅ := 2) (y₆ := 2)
          (by norm_num)
        rw [zgi, zgj, zgk, zgl, zhj, zhk, zhl, zik, zil, zjl] at key
        ring_nf at key
        linarith
      | have key := T.intersection_six_neg hcard hgh hgi hgj hgk hgl hhi hhj hhk hhl hij hik
          hil hjk hjl hkl (y₁ := 1) (y₂ := 2) (y₃ := 2) (y₄ := 2) (y₅ := 2) (y₆ := 1)
          (by norm_num)
        rw [zgi, zgj, zgk, zgl, zhj, zhk, zhl, zik, zil, zjl] at key
        ring_nf at key
        linarith
      | have key := T.intersection_six_neg hcard hgh hgi hgj hgk hgl hhi hhj hhk hhl hij hik
          hil hjk hjl hkl (y₁ := 1) (y₂ := 1) (y₃ := 1) (y₄ := 1) (y₅ := 1) (y₆ := 1)
          (by norm_num)
        rw [zgi, zgj, zgk, zgl, zhj, zhk, zhl, zik, zil, zjl] at key
        ring_nf at key
        linarith
      | have key := T.intersection_six_neg hcard hgh hgi hgj hgk hgl hhi hhj hhk hhl hij hik
          hil hjk hjl hkl (y₁ := 2) (y₂ := 2) (y₃ := 2) (y₄ := 2) (y₅ := 2) (y₆ := 1)
          (by norm_num)
        rw [zgi, zgj, zgk, zgl, zhj, zhk, zhl, zik, zil, zjl] at key
        ring_nf at key
        linarith
  · rcases hm₁ with h₁ | h₁ | h₁ <;> rcases hm₂ with h₂ | h₂ | h₂ <;> omega

/-- Six components of self-intersection `-2w` forming a chain in a numerical type with more than
six components have no additional intersections. This is the graph-shape part of the
six-component base case for
[Stacks, Lemma 55.5.8](https://stacks.math.columbia.edu/tag/0C89). -/
theorem intersection_eq_zero_of_chain_six (hcard : 6 < Fintype.card T.Component)
    {g h i j k l : T.Component}
    (hg : T.intersection g g = -(2 * (T.weight g : ℤ)))
    (hh : T.intersection h h = -(2 * (T.weight h : ℤ)))
    (hi : T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hj : T.intersection j j = -(2 * (T.weight j : ℤ)))
    (hk : T.intersection k k = -(2 * (T.weight k : ℤ)))
    (hl : T.intersection l l = -(2 * (T.weight l : ℤ)))
    (hgi : g ≠ i) (hgj : g ≠ j) (hgk : g ≠ k) (hgl : g ≠ l)
    (hhj : h ≠ j) (hhk : h ≠ k) (hhl : h ≠ l) (hik : i ≠ k) (hil : i ≠ l)
    (hjl : j ≠ l) (egh : 0 < T.intersection g h) (ehi : 0 < T.intersection h i)
    (eij : 0 < T.intersection i j) (ejk : 0 < T.intersection j k)
    (ekl : 0 < T.intersection k l) :
    T.intersection g i = 0 ∧ T.intersection g j = 0 ∧ T.intersection g k = 0 ∧
      T.intersection g l = 0 ∧ T.intersection h j = 0 ∧ T.intersection h k = 0 ∧
      T.intersection h l = 0 ∧ T.intersection i k = 0 ∧ T.intersection i l = 0 ∧
      T.intersection j l = 0 := by
  obtain ⟨zgi, zgj, zgk, zgl, zhj, zhk, zhl, zik, zil, zjl, -⟩ := T.chain_six_factors
    hcard hg hh hi hj hk hl hgi hgj hgk hgl hhj hhk hhl hik hil hjl egh ehi eij ejk ekl
  exact ⟨zgi, zgj, zgk, zgl, zhj, zhk, zhl, zik, zil, zjl⟩

/-- In a chain of six components of self-intersection `-2w`, all adjacent normalized intersection
ratios are one except possibly a ratio two at one end. Equivalently, their ratio pattern is
`(1,1,1,1,1)`, `(2,1,1,1,1)`, or `(1,1,1,1,2)`. This is the numerical classification in the
six-component base case for
[Stacks, Lemma 55.5.8](https://stacks.math.columbia.edu/tag/0C89). -/
theorem exists_intersection_ratio_chain_six_mem (hcard : 6 < Fintype.card T.Component)
    {g h i j k l : T.Component}
    (hg : T.intersection g g = -(2 * (T.weight g : ℤ)))
    (hh : T.intersection h h = -(2 * (T.weight h : ℤ)))
    (hi : T.intersection i i = -(2 * (T.weight i : ℤ)))
    (hj : T.intersection j j = -(2 * (T.weight j : ℤ)))
    (hk : T.intersection k k = -(2 * (T.weight k : ℤ)))
    (hl : T.intersection l l = -(2 * (T.weight l : ℤ)))
    (hgi : g ≠ i) (hgj : g ≠ j) (hgk : g ≠ k) (hgl : g ≠ l)
    (hhj : h ≠ j) (hhk : h ≠ k) (hhl : h ≠ l) (hik : i ≠ k) (hil : i ≠ l)
    (hjl : j ≠ l) (egh : 0 < T.intersection g h) (ehi : 0 < T.intersection h i)
    (eij : 0 < T.intersection i j) (ejk : 0 < T.intersection j k)
    (ekl : 0 < T.intersection k l) :
    ∃ p₁ q₁ p₂ q₂ p₃ q₃ p₄ q₄ p₅ q₅ : ℤ,
      T.intersection g h = (T.weight g : ℤ) * p₁ ∧
      T.intersection g h = (T.weight h : ℤ) * q₁ ∧
      T.intersection h i = (T.weight h : ℤ) * p₂ ∧
      T.intersection h i = (T.weight i : ℤ) * q₂ ∧
      T.intersection i j = (T.weight i : ℤ) * p₃ ∧
      T.intersection i j = (T.weight j : ℤ) * q₃ ∧
      T.intersection j k = (T.weight j : ℤ) * p₄ ∧
      T.intersection j k = (T.weight k : ℤ) * q₄ ∧
      T.intersection k l = (T.weight k : ℤ) * p₅ ∧
      T.intersection k l = (T.weight l : ℤ) * q₅ ∧
      (p₁ * q₁, p₂ * q₂, p₃ * q₃, p₄ * q₄, p₅ * q₅) ∈
        ({(1, 1, 1, 1, 1), (2, 1, 1, 1, 1), (1, 1, 1, 1, 2)} :
          Set (ℤ × ℤ × ℤ × ℤ × ℤ)) := by
  obtain ⟨-, -, -, -, -, -, -, -, -, -, p₁, q₁, p₂, q₂, p₃, q₃, p₄, q₄, p₅, q₅,
      ap₁, aq₁, ap₂, aq₂, ap₃, aq₃, ap₄, aq₄, ap₅, aq₅, hm⟩ := T.chain_six_factors
    hcard hg hh hi hj hk hl hgi hgj hgk hgl hhj hhk hhl hik hil hjl egh ehi eij ejk ekl
  exact ⟨p₁, q₁, p₂, q₂, p₃, q₃, p₄, q₄, p₅, q₅, ap₁, aq₁, ap₂, aq₂, ap₃, aq₃, ap₄,
    aq₄, ap₅, aq₅, hm⟩

end NumericalType

end TauCeti
