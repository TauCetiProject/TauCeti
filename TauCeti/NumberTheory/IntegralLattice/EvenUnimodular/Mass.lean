/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.Bernoulli.Values
public import TauCeti.NumberTheory.IntegralLattice.E8Genus
import TauCeti.NumberTheory.IntegralLattice.EvenUnimodular.Genus

/-!
# The Bernoulli product for the mass of even unimodular lattices

The positive definite even unimodular lattices of rank `n = 2m > 0` form a single genus, and
`8 ∣ n`. The Minkowski–Siegel mass formula evaluates the mass of this genus, the sum of
`1 / |O(L)|` over its classes, as the rational number

`M_n = |B_m / (2m)| · ∏_{j=1}^{m-1} |B_{2j} / (4j)|`,

where `B_k` are the Bernoulli numbers. This file defines that product,
`TauCeti.bernoulliFullMass m`, for every natural number `m`, proves that it is positive for every
positive even `m`, and evaluates it exactly in ranks `8`, `16` and `24`, with two-sided bounds for
`2 M_n` in ranks `32` and `40`. These are the values that turn the mass into class counts: a
lattice of positive rank has at least the two automorphisms `±1`, so `2 M_n` bounds the number of
classes from below, and a list of distinct classes whose reciprocal automorphism orders sum to
`M_n` is the complete list.

The identification of `TauCeti.bernoulliFullMass (n / 2)` with `TauCeti.IntegralLattice.mass` is
proved here only in rank eight, where the genus is the single class of `E₈`
(`TauCeti.IntegralLattice.mass_typeE₈RootLattice`).

At `m = 0` the division by zero makes the product `0`; it is not the mass `1` of the genus of the
zero lattice.

## Main results

* `TauCeti.bernoulliFullMass`: the product `|B_m / (2m)| · ∏_{j=1}^{m-1} |B_{2j} / (4j)|`.
* `TauCeti.bernoulliFullMass_pos`: the product is positive for positive even `m`.
* `TauCeti.bernoulliFullMass_four`, `TauCeti.bernoulliFullMass_eight`,
  `TauCeti.bernoulliFullMass_twelve`: `M₈ = 1 / 696729600`,
  `M₁₆ = 691 / 277667181515243520000` and the exact value of `M₂₄`.
* `TauCeti.two_mul_bernoulliFullMass_sixteen_mem_Ioo`,
  `TauCeti.two_mul_bernoulliFullMass_twenty_mem_Ioo`: `80618465 < 2 M₃₂ < 80618466` and
  `8 · 10⁵¹ < 2 M₄₀ < 9 · 10⁵¹`.
* `TauCeti.IntegralLattice.IsPosDef.mass_eq_bernoulliFullMass_four`: the mass of the genus of a
  positive definite even unimodular lattice of rank eight is `M₈`.

## References

* J. H. Conway and N. J. A. Sloane, *Low-dimensional lattices. IV. The mass formula*,
  Proc. Roy. Soc. London A 419 (1988), §9(iv), p.274, for the mass of even unimodular lattices.
* M. Belolipetsky and W. T. Gan, *The mass of unimodular lattices*, J. Number Theory 114 (2005),
  Theorem 3.1, whose proper mass is twice this full mass in positive rank.
-/

public section

open Finset

namespace TauCeti

/-- The rational product `|B_m / (2m)| · ∏_{j=1}^{m-1} |B_{2j} / (4j)|` of Bernoulli numbers
`bernoulli` (with `B₁ = -1/2`). For `m = n / 2` with `n > 0` divisible by eight it is the mass of
the genus of positive definite even unimodular lattices of rank `n`; at `m = 0` the division by
zero makes it `0`. -/
def bernoulliFullMass (m : ℕ) : ℚ :=
  |bernoulli m / (2 * (m : ℚ))| * ∏ j ∈ Ico 1 m, |bernoulli (2 * j) / (4 * (j : ℚ))|

theorem bernoulliFullMass_def (m : ℕ) :
    bernoulliFullMass m =
      |bernoulli m / (2 * (m : ℚ))| * ∏ j ∈ Ico 1 m, |bernoulli (2 * j) / (4 * (j : ℚ))| :=
  (rfl)

@[simp]
theorem bernoulliFullMass_zero : bernoulliFullMass 0 = 0 := by
  simp [bernoulliFullMass_def]

/-- The Bernoulli product is positive for positive even `m`, since no even Bernoulli number
vanishes. -/
theorem bernoulliFullMass_pos {m : ℕ} (hm : m ≠ 0) (he : Even m) : 0 < bernoulliFullMass m := by
  obtain ⟨k, rfl⟩ := he
  rw [bernoulliFullMass_def, ← two_mul]
  refine mul_pos (abs_pos.mpr (div_ne_zero (bernoulli_two_mul_ne_zero k) ?_))
    (prod_pos fun j hj => abs_pos.mpr (div_ne_zero (bernoulli_two_mul_ne_zero j) ?_))
  · exact_mod_cast (by omega : 2 * (2 * k) ≠ 0)
  · exact_mod_cast (by grind : 4 * j ≠ 0)

/-- **The mass in rank eight**: `M₈ = |B₄/8| · |B₂/4| · |B₄/8| · |B₆/12| = 1 / 696729600`. -/
@[simp]
theorem bernoulliFullMass_four : bernoulliFullMass 4 = 696729600⁻¹ := by
  simp only [bernoulliFullMass_def, prod_Ico_eq_prod_range, prod_range_succ, prod_range_zero,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, bernoulli_two, bernoulli_four, bernoulli_six]
  decide +kernel

/-- **The mass in rank sixteen**: `M₁₆ = 691 / 277667181515243520000`. -/
@[simp]
theorem bernoulliFullMass_eight : bernoulliFullMass 8 = 691 / 277667181515243520000 := by
  simp only [bernoulliFullMass_def, prod_Ico_eq_prod_range, prod_range_succ, prod_range_zero,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, bernoulli_two, bernoulli_four, bernoulli_six,
    bernoulli_eight, bernoulli_ten, bernoulli_twelve, bernoulli_fourteen]
  decide +kernel

/-- **The mass in rank twenty-four**, `M₂₄ ≈ 7.937 · 10⁻¹⁵`. -/
@[simp]
theorem bernoulliFullMass_twelve :
    bernoulliFullMass 12 =
      1027637932586061520960267 / 129477933340026851560636148613120000000 := by
  simp only [bernoulliFullMass_def, prod_Ico_eq_prod_range, prod_range_succ, prod_range_zero,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, bernoulli_two, bernoulli_four, bernoulli_six,
    bernoulli_eight, bernoulli_ten, bernoulli_twelve, bernoulli_fourteen, bernoulli_sixteen,
    bernoulli_eighteen, bernoulli_twenty, bernoulli_twentyTwo]
  decide +kernel

/-- **Twice the mass in rank thirty-two** lies strictly between `80618465` and `80618466`. -/
theorem two_mul_bernoulliFullMass_sixteen_mem_Ioo :
    2 * bernoulliFullMass 16 ∈ Set.Ioo 80618465 80618466 := by
  simp only [bernoulliFullMass_def, prod_Ico_eq_prod_range, prod_range_succ, prod_range_zero,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, bernoulli_two, bernoulli_four, bernoulli_six,
    bernoulli_eight, bernoulli_ten, bernoulli_twelve, bernoulli_fourteen, bernoulli_sixteen,
    bernoulli_eighteen, bernoulli_twenty, bernoulli_twentyTwo, bernoulli_twentyFour,
    bernoulli_twentySix, bernoulli_twentyEight, bernoulli_thirty]
  decide +kernel

/-- **Twice the mass in rank forty** lies strictly between `8 · 10⁵¹` and `9 · 10⁵¹`. -/
theorem two_mul_bernoulliFullMass_twenty_mem_Ioo :
    2 * bernoulliFullMass 20 ∈ Set.Ioo (8 * 10 ^ 51) (9 * 10 ^ 51) := by
  simp only [bernoulliFullMass_def, prod_Ico_eq_prod_range, prod_range_succ, prod_range_zero,
    Nat.reduceAdd, Nat.reduceMul, Nat.reduceSub, bernoulli_two, bernoulli_four, bernoulli_six,
    bernoulli_eight, bernoulli_ten, bernoulli_twelve, bernoulli_fourteen, bernoulli_sixteen,
    bernoulli_eighteen, bernoulli_twenty, bernoulli_twentyTwo, bernoulli_twentyFour,
    bernoulli_twentySix, bernoulli_twentyEight, bernoulli_thirty, bernoulli_thirtyTwo,
    bernoulli_thirtyFour, bernoulli_thirtySix, bernoulli_thirtyEight]
  decide +kernel

namespace IntegralLattice

open Module

variable {V : Type*} [AddCommGroup V] [Module ℚ V] {L : IntegralLattice V}

/-- **The mass of even unimodular lattices in rank eight**: a positive definite even unimodular
lattice of rank eight lies in the genus of `E₈`, whose mass `1 / 696729600` is the Bernoulli
product `M₈`. -/
theorem IsPosDef.mass_eq_bernoulliFullMass_four (hL : L.IsPosDef) (hLe : L.IsEven)
    (hLu : L.IsUnimodular) (hn : finrank ℤ L = 8) : L.mass = bernoulliFullMass 4 := by
  have h : L.SameGenus typeE₈RootLattice :=
    hL.sameGenus_of_isEven_of_isUnimodular isPosDef_typeE₈RootLattice hLe isEven_typeE₈RootLattice
      hLu isUnimodular_typeE₈RootLattice
      (by rw [hn, finrank_carrier, finrank_fin_fun])
  rw [h.mass_eq, mass_typeE₈RootLattice, bernoulliFullMass_four]

end IntegralLattice

end TauCeti
