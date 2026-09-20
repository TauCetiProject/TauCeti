/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Curves.StableReduction.NumericalType.IntersectionForm
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith

/-!
# Proper subgraphs of `(-2)`-indices in a numerical type

A `(-2)`-index of a numerical type is a component `i` with `gᵢ = 0` and `aᵢᵢ = -2wᵢ`. The
connected configurations of `(-2)`-indices that can occur as proper subsets of the components
of a numerical type form a short explicit list, of Dynkin-diagram shape
([Stacks, Section 0C7L](https://stacks.math.columbia.edu/tag/0C7L)). This classification is
what bounds the multiplicities along chains of `(-2)`-indices in a minimal numerical type, and
hence its Picard group.

This file classifies the configurations on two and on three components. If a numerical type has
more than two components and two `(-2)`-indices `i` and `j` meet, then up to swapping `i` and `j`,

`(wᵢ, wⱼ, aᵢⱼ) = (w, w, w)`, `(w, 2w, 2w)` or `(w, 3w, 3w)`

for some positive integer `w` ([Stacks, Tag 0C7M](https://stacks.math.columbia.edu/tag/0C7M)). If
a numerical type has more than three components and two distinct `(-2)`-indices `i` and `k` both
meet a `(-2)`-index `j`, then `i` and `k` do not meet, so that the configuration is a chain, and
up to reversing it

`(wᵢ, wⱼ, wₖ, aᵢⱼ, aⱼₖ) = (w, w, w, w, w)`, `(w, w, 2w, w, 2w)` or `(2w, 2w, w, 2w, 2w)`

([Stacks, Tag 0C7R](https://stacks.math.columbia.edu/tag/0C7R)).

Both arguments use only the self-intersections `aᵢᵢ = -2wᵢ`, not the genera. For a pair, negative
definiteness of the principal `2 × 2` submatrix gives `aᵢⱼ² < 4wᵢwⱼ`, and `lcm(wᵢ, wⱼ) ∣ aᵢⱼ`
leaves only the three solutions above. For a triple, negative definiteness of the principal
`3 × 3` submatrix says that

`p₁q₁ + p₂q₂ + p₃q₃ + q₁q₂p₃ < 4`

where `aᵢⱼ = wᵢp₁ = wⱼq₁`, `aⱼₖ = wⱼp₂ = wₖq₂` and `aᵢₖ = wᵢp₃ = wₖq₃` are the factorisations
supplied by the divisibility axiom. All four summands are nonnegative integers and the first two
are positive, so the last two vanish; in particular `aᵢₖ = 0` and `p₁q₁ + p₂q₂ ≤ 3`. The constraints
`aᵢⱼ mⱼ ≤ 2wᵢ mᵢ` and `aᵢⱼ mᵢ ≤ 2wⱼ mⱼ` on the multiplicities listed alongside the Stacks
statements are instances of `TauCeti.NumericalType.multiplicity_mul_intersection_le`.

## Main results

* `TauCeti.NumericalType.exists_weight_intersection_triple_mem`: the classification of the
  weights and the intersection number of two meeting `(-2)`-indices.
* `TauCeti.NumericalType.intersection_eq_zero_of_intersection_pos_of_intersection_pos`: two
  `(-2)`-indices meeting a common third one do not meet each other.
* `TauCeti.NumericalType.exists_weight_intersection_quintuple_mem`: the classification of the
  weights and the intersection numbers of a chain of three `(-2)`-indices.
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

end NumericalType

end TauCeti
