/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.NumberField.Quadratic.Radicand
public import Mathlib.NumberTheory.NumberField.Units.DirichletTheorem
import TauCeti.Algebra.Squarefree
import TauCeti.Data.Nat.Totient
import TauCeti.NumberTheory.EffectiveBounds.Regulator
import TauCeti.NumberTheory.NumberField.Units.Torsion
import TauCeti.NumberTheory.NumberField.WorkedExamples.GaussianRationals.Units
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# Roots of unity and units of quadratic fields

A quadratic field `K` contains the roots of unity `±1`, and further roots of unity only in two
cases. If `K = ℚ(√d)` with `d` squarefree, the torsion subgroup of the units of `K` has order `4`
when `d = -1`, order `6` when `d = -3`, and order `2` otherwise. In terms of the field
discriminant `D`, there are four roots of unity for `D = -4`, six for `D = -3`, and two otherwise.
For an imaginary quadratic field the unit rank is zero, so these roots of unity are all the units
of the ring of integers.

A primitive root of unity of order `n` in `K` has degree `φ(n) ≤ 2` over `ℚ`, so `n` divides
`4` or `6`. A primitive fourth root of unity is a square root of `-1`, and a primitive sixth
root `ζ` gives the square root `2ζ - 1` of `-3`. Since the squarefree radicand is the only
squarefree integer other than `1` with a square root in `K`
(`NumberField.eq_of_sq_eq_intCast_of_squarefree`), these force `d = -1` and `d = -3`. Conversely
`θ = √-1` is a primitive fourth root of unity, and `(1 + √-3)/2` is a primitive sixth root of
unity; these generate the exceptional torsion subgroups.

## Main results

* `TauCeti.NumberField.Units.torsionOrder_eq_two_or_four_or_six`: a field of degree at most `2`
  has two, four or six roots of unity.
* `TauCeti.NumberField.isPrimitiveRoot_one_add_gen_div_two`: for `θ² = -3`, `(1 + θ)/2` is a
  primitive sixth root of unity.
* `TauCeti.NumberField.Units.torsionOrder_eq_of_minpoly_eq_X_sq_sub_C`: the torsion order of
  `ℚ(√d)` for squarefree `d` is `4` if `d = -1`, `6` if `d = -3`, and `2` otherwise.
* `TauCeti.NumberField.Units.torsion_eq_top_of_isTotallyComplex`: every unit of an imaginary
  quadratic field is a root of unity.
* `TauCeti.NumberField.Units.card_units_of_isTotallyComplex`: the number of units of an
  imaginary quadratic field.
-/

public section

open Polynomial NumberField NumberField.Units Module
open scoped NumberField

namespace TauCeti.NumberField

variable {K : Type*} [Field K] [NumberField K] {θ : 𝓞 K} {d : ℤ}

/-- **The exceptional sixth root of unity.** If `θ² = -3`, then `(1 + θ)/2` is a primitive sixth
root of unity: it is a root of `Φ₆ = X² - X + 1`. -/
theorem isPrimitiveRoot_one_add_gen_div_two (hmin : minpoly ℤ θ = X ^ 2 - C (-3)) :
    IsPrimitiveRoot ((1 + θ) / 2 : K) 6 := by
  have h : (θ : K) ^ 2 = -3 := by
    rw [coe_gen_sq hmin]
    norm_num
  rw [← isRoot_cyclotomic_iff_charZero (by norm_num), cyclotomic_six]
  simp only [IsRoot.def, eval_add, eval_sub, eval_pow, eval_X, eval_one]
  linear_combination h / 4

namespace Units

/-- **A field of degree at most two has two, four or six roots of unity.** A primitive root of
unity of order `n = torsionOrder K` has degree `φ(n) ≤ 2`, so `n ∈ {1, 2, 3, 4, 6}`, and `n` is
even since `-1` is a root of unity. -/
theorem torsionOrder_eq_two_or_four_or_six (hK : finrank ℚ K ≤ 2) :
    torsionOrder K = 2 ∨ torsionOrder K = 4 ∨ torsionOrder K = 6 := by
  have h := TauCeti.Nat.totient_le_two_iff.1
    ((totient_torsionOrder_le_finrank (K := K)).trans hK)
  obtain ⟨k, hk⟩ := even_torsionOrder K
  have := torsionOrder_ne_zero K
  omega

/-- A primitive fourth root of unity in a quadratic field forces the radicand `-1`: it squares
to `-1`. -/
private theorem eq_neg_one_of_isPrimitiveRoot_four (hK : finrank ℚ K = 2)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hd : Squarefree d) {μ : K} (hμ : IsPrimitiveRoot μ 4) :
    d = -1 := by
  have hμ2 : μ ^ 2 = ((-1 : ℤ) : K) := by
    rw [(hμ.pow (by norm_num) (show 4 = 2 * 2 by rfl)).eq_neg_one_of_two_right]
    norm_num
  exact (eq_of_sq_eq_intCast_of_squarefree hK hmin hd hμ2 squarefree_one.neg
    (by norm_num)).symm

/-- A primitive sixth root of unity `μ` in a quadratic field forces the radicand `-3`: since
`μ² - μ + 1 = 0`, the element `2μ - 1` squares to `-3`. -/
private theorem eq_neg_three_of_isPrimitiveRoot_six (hK : finrank ℚ K = 2)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hd : Squarefree d) {μ : K} (hμ : IsPrimitiveRoot μ 6) :
    d = -3 := by
  have h := (isRoot_cyclotomic_iff_charZero (by norm_num)).2 hμ
  rw [cyclotomic_six] at h
  simp only [IsRoot.def, eval_add, eval_sub, eval_pow, eval_X, eval_one] at h
  have hz : (2 * μ - 1) ^ 2 = ((-3 : ℤ) : K) := by
    push_cast
    linear_combination 4 * h
  exact (eq_of_sq_eq_intCast_of_squarefree hK hmin hd hz Int.prime_three.squarefree.neg
    (by norm_num)).symm

/-- **The roots of unity in a quadratic field.** If `K = ℚ(θ)` with `θ² = d` squarefree, the
torsion subgroup of the units of `K` has order `4` if `d = -1`, order `6` if `d = -3`, and order
`2` otherwise. -/
theorem torsionOrder_eq_of_minpoly_eq_X_sq_sub_C (hK : finrank ℚ K = 2)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hd : Squarefree d) :
    torsionOrder K = if d = -1 then 4 else if d = -3 then 6 else 2 := by
  obtain ⟨μ, hμ⟩ := exists_isPrimitiveRoot_torsionOrder (K := K)
  rcases torsionOrder_eq_two_or_four_or_six hK.le with h | h | h <;> rw [h] at hμ ⊢
  · -- Only two roots of unity: the exceptional radicands would supply more.
    split_ifs with h1 h3
    · subst h1
      have := dvd_torsionOrder_of_isPrimitiveRoot
        (GaussianRationals.isPrimitiveRoot_four (K := K)
          (by simpa using hmin))
      omega
    · subst h3
      have := dvd_torsionOrder_of_isPrimitiveRoot (isPrimitiveRoot_one_add_gen_div_two hmin)
      omega
    · rfl
  · simp [eq_neg_one_of_isPrimitiveRoot_four hK hmin hd hμ]
  · simp [eq_neg_three_of_isPrimitiveRoot_six hK hmin hd hμ]

/-- **The units of an imaginary quadratic field are roots of unity.** The unit rank of a totally
complex quadratic field is `0 + 1 - 1 = 0`. -/
theorem torsion_eq_top_of_isTotallyComplex [IsTotallyComplex K] (hK : finrank ℚ K = 2) :
    torsion K = ⊤ :=
  torsion_eq_top_of_rank_eq_zero
    (rank_eq_zero_of_isTotallyComplex_of_finrank_eq_two K hK)

/-- **The number of units of an imaginary quadratic field.** If `K = ℚ(θ)` is imaginary
quadratic with `θ² = d` squarefree, the ring of integers of `K` has four units if `d = -1`, six
units if `d = -3`, and two units otherwise. -/
theorem card_units_of_isTotallyComplex [IsTotallyComplex K] (hK : finrank ℚ K = 2)
    (hmin : minpoly ℤ θ = X ^ 2 - C d) (hd : Squarefree d) :
    Nat.card (𝓞 K)ˣ = if d = -1 then 4 else if d = -3 then 6 else 2 := by
  rw [← torsionOrder_eq_of_minpoly_eq_X_sq_sub_C hK hmin hd, torsionOrder,
    torsion_eq_top_of_isTotallyComplex hK, Subgroup.card_top]

end Units

end TauCeti.NumberField
