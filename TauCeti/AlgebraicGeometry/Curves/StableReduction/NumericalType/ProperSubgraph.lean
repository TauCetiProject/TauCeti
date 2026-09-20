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
* `TauCeti.NumericalType.intersection_eq_zero_of_star_four`: a `(-2)`-index meeting three others
  meets no fourth one.
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
  classical
  obtain ⟨m, hm⟩ :
      (((((Finset.univ.erase h).erase i).erase j).erase k).erase l).Nonempty := by
    rw [← Finset.card_pos,
      Finset.card_erase_of_mem (by simp [hhl.symm, hil.symm, hjl.symm, hkl.symm]),
      Finset.card_erase_of_mem (by simp [hhk.symm, hik.symm, hjk.symm]),
      Finset.card_erase_of_mem (by simp [hhj.symm, hij.symm]),
      Finset.card_erase_of_mem (by simp [hhi.symm]),
      Finset.card_erase_of_mem (Finset.mem_univ h), Finset.card_univ]
    omega
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hm
  obtain ⟨hml, hmk, hmj, hmi, hmh⟩ := hm
  -- Spread the five entries over the five components and zero elsewhere.
  let x : T.Component → ℤ := fun c ↦
    if c = h then y₁ else if c = i then y₂ else if c = j then y₃ else
      if c = k then y₄ else if c = l then y₅ else 0
  have hxh : x h = y₁ := by simp [x]
  have hxi : x i = y₂ := by simp [x, hhi.symm]
  have hxj : x j = y₃ := by simp [x, hhj.symm, hij.symm]
  have hxk : x k = y₄ := by simp [x, hhk.symm, hik.symm, hjk.symm]
  have hxl : x l = y₅ := by simp [x, hhl.symm, hil.symm, hjl.symm, hkl.symm]
  have hsupp : ∀ c ∉ ({h, i, j, k, l} : Finset T.Component), x c = 0 := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    simp [x, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2]
  have hne : x ≠ 0 := fun hc ↦ hy₁ (by simpa [hxh] using congrFun hc h)
  have hxm : x m = 0 := by simp [x, hmh, hmi, hmj, hmk, hml]
  -- Only the five diagonal entries and the five retained off-diagonal pairs survive.
  have hform : T.intersection h h * y₁ ^ 2 + T.intersection i i * y₂ ^ 2 +
        T.intersection j j * y₃ ^ 2 + T.intersection k k * y₄ ^ 2 +
        T.intersection l l * y₅ ^ 2 +
      2 * (T.intersection h i * y₁ * y₂ + T.intersection i j * y₂ * y₃ +
        T.intersection j k * y₃ * y₄ + T.intersection k l * y₄ * y₅ +
        T.intersection h l * y₁ * y₅) = x ⬝ᵥ T.intersection.mulVec x := by
    rw [T.dotProduct_intersection_mulVec_of_support_subset hsupp]
    simp only [Finset.sum_insert (by simp [hhi, hhj, hhk, hhl] :
        h ∉ ({i, j, k, l} : Finset T.Component)),
      Finset.sum_insert (by simp [hij, hik, hil] : i ∉ ({j, k, l} : Finset T.Component)),
      Finset.sum_insert (by simp [hjk, hjl] : j ∉ ({k, l} : Finset T.Component)),
      Finset.sum_pair hkl, hxh, hxi, hxj, hxk, hxl, T.intersection_comm i h,
      T.intersection_comm j h, T.intersection_comm k h, T.intersection_comm l h,
      T.intersection_comm j i, T.intersection_comm k i, T.intersection_comm l i,
      T.intersection_comm k j, T.intersection_comm l j, T.intersection_comm l k,
      hhj0, hhk0, hik0, hil0, hjl0]
    ring
  rw [hform]
  exact T.dotProduct_intersection_mulVec_neg hne hxm

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
no fourth such component, in a numerical type with more than five components. Equivalently, the
four-legged star does not occur as a proper subgraph of `(-2)`-indices
([Stacks, Lemma 55.5.6](https://stacks.math.columbia.edu/tag/0C86)). -/
theorem intersection_eq_zero_of_star_four (hcard : 5 < Fintype.card T.Component)
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
  let x : T.Component → ℤ := fun c ↦
    if c = c₁ then 2 else if c = c₂ then 1 else if c = c₃ then 1 else
      if c = c₄ then 1 else if c = c₅ then 1 else 0
  have hx₁ : x c₁ = 2 := by simp [x]
  have hx₂ : x c₂ = 1 := by simp [x, h₁₂.symm]
  have hx₃ : x c₃ = 1 := by simp [x, h₁₃.symm, h₂₃.symm]
  have hx₄ : x c₄ = 1 := by simp [x, h₁₄.symm, h₂₄.symm, h₃₄.symm]
  have hx₅ : x c₅ = 1 := by
    simp [x, h₁₅.symm, h₂₅.symm, h₃₅.symm, h₄₅.symm]
  have hsupp : ∀ c ∉ ({c₁, c₂, c₃, c₄, c₅} : Finset T.Component), x c = 0 := by
    intro c hc
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    simp [x, hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2]
  obtain ⟨m, hm⟩ :
      (((((Finset.univ.erase c₁).erase c₂).erase c₃).erase c₄).erase c₅).Nonempty := by
    rw [← Finset.card_pos,
      Finset.card_erase_of_mem (by simp [h₁₅.symm, h₂₅.symm, h₃₅.symm, h₄₅.symm]),
      Finset.card_erase_of_mem (by simp [h₁₄.symm, h₂₄.symm, h₃₄.symm]),
      Finset.card_erase_of_mem (by simp [h₁₃.symm, h₂₃.symm]),
      Finset.card_erase_of_mem (by simp [h₁₂.symm]),
      Finset.card_erase_of_mem (Finset.mem_univ c₁), Finset.card_univ]
    omega
  simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hm
  obtain ⟨hmc₅, hmc₄, hmc₃, hmc₂, hmc₁⟩ := hm
  have hm' : m ∉ ({c₁, c₂, c₃, c₄, c₅} : Finset T.Component) := by
    simp [hmc₁, hmc₂, hmc₃, hmc₄, hmc₅]
  have hxne : x ≠ 0 := by
    intro heq
    have hxzero := congrFun heq c₁
    rw [hx₁] at hxzero
    norm_num at hxzero
  have hneg := T.dotProduct_intersection_mulVec_neg
    (x := x) hxne (hsupp m hm')
  rw [T.dotProduct_intersection_mulVec_of_support_subset hsupp] at hneg
  simp only [Finset.sum_insert (by simp [h₁₂, h₁₃, h₁₄, h₁₅] :
      c₁ ∉ ({c₂, c₃, c₄, c₅} : Finset T.Component)),
    Finset.sum_insert (by simp [h₂₃, h₂₄, h₂₅] :
      c₂ ∉ ({c₃, c₄, c₅} : Finset T.Component)),
    Finset.sum_insert (by simp [h₃₄, h₃₅] : c₃ ∉ ({c₄, c₅} : Finset T.Component)),
    Finset.sum_pair h₄₅, hx₁, hx₂, hx₃, hx₄, hx₅, T.intersection_comm c₂ c₁,
    T.intersection_comm c₃ c₁, T.intersection_comm c₄ c₁, T.intersection_comm c₅ c₁,
    T.intersection_comm c₃ c₂, T.intersection_comm c₄ c₂, T.intersection_comm c₅ c₂,
    T.intersection_comm c₄ c₃, T.intersection_comm c₅ c₃, T.intersection_comm c₅ c₄,
    h₁, h₂, h₃, h₄, h₅, a₁₂, a₁₃, a₁₄, a₁₅, z₂₃, z₂₄, z₂₅, z₃₄, z₃₅, z₄₅,
    hw, hw₂, hw₃, hw₄, hw₅, mul_one] at hneg
  linarith

end NumericalType

end TauCeti
