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

This file starts the classification with pairs of meeting `(-2)`-indices
([Stacks, Tag 0C7M](https://stacks.math.columbia.edu/tag/0C7M)). If a numerical type has more
than two components and two `(-2)`-indices `i` and `j` meet, then up to swapping `i` and `j`,

`(wᵢ, wⱼ, aᵢⱼ) = (w, w, w)`, `(w, 2w, 2w)` or `(w, 3w, 3w)`

for some positive integer `w`. The argument uses only the self-intersections `aᵢᵢ = -2wᵢ`,
not the genera: negative definiteness of the principal `2 × 2` submatrix gives
`aᵢⱼ² < 4wᵢwⱼ`, and `lcm(wᵢ, wⱼ) ∣ aᵢⱼ` leaves only these solutions. The constraints
`aᵢⱼ mⱼ ≤ 2wᵢ mᵢ` and `aᵢⱼ mᵢ ≤ 2wⱼ mⱼ` on the multiplicities listed alongside the Stacks
statement are instances of `TauCeti.NumericalType.multiplicity_mul_intersection_le`.

## Main results

* `TauCeti.NumericalType.exists_weight_intersection_triple_mem`: the classification of the
  weights and the intersection number of two meeting `(-2)`-indices.
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

end NumericalType

end TauCeti
