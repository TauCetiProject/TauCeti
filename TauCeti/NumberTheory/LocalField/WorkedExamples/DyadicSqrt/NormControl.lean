/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.NumberTheory.LocalField.WorkedExamples.DyadicSqrt.Two
public import TauCeti.NumberTheory.LocalField.Eisenstein.Quadratic
public import TauCeti.NumberTheory.LocalField.QuadraticForm.UnramifiedClass

/-!
# A unit norm over `ℚ₂(√2)` without integral square-root coordinates

Put `π = √2`. The unit `1 + π` is the norm of `(π + 1/2) + (1/2)√5`, but has no representation
`x² - 5y²` with both `x` and `y` integral. Consequently the two naive families
`u²(1 - 5t²)` and `-5u²(1 - 5t²)` with integral `u,t` miss a unit norm. The obstruction is the
coefficient of `π` in the Eisenstein integral basis `(1, π)`: it is divisible by `2` in every
such integral norm, whereas that coefficient in `1 + π` is `1`.
-/

public section
noncomputable section

open ValuativeRel IsLocalRing

namespace TauCeti.DyadicSqrtTwo

@[simp]
private theorem coe_two_integerRing : ((2 : 𝒪[DyadicSqrtTwo]) : DyadicSqrtTwo) = 2 :=
  map_ofNat (Subring.subtype 𝒪[DyadicSqrtTwo]) 2

@[simp]
private theorem coe_five_integerRing : ((5 : 𝒪[DyadicSqrtTwo]) : DyadicSqrtTwo) = 5 :=
  map_ofNat (Subring.subtype 𝒪[DyadicSqrtTwo]) 5

@[simp]
private theorem coe_two_padicIntegerRing : ((2 : 𝒪[ℚ_[2]]) : ℚ_[2]) = 2 :=
  map_ofNat (Subring.subtype 𝒪[ℚ_[2]]) 2

/-- Over the ramified base `ℚ₂(√2)`, radicand `5` is still the unramified quadratic
class: its norms are exactly the elements of even normalized valuation. -/
theorem exists_norm_five_iff_even (b : DyadicSqrtTwoˣ) :
    (∃ x y : DyadicSqrtTwo, (b : DyadicSqrtTwo) = x ^ 2 - 5 * y ^ 2) ↔
      Even (normalizedValuation DyadicSqrtTwo b).toAdd := by
  let : Fintype 𝓀[DyadicSqrtTwo] := Fintype.ofFinite _
  have hcard : Fintype.card 𝓀[DyadicSqrtTwo] = 2 := by
    rw [← Nat.card_eq_fintype_card, natCard_residueField]
  have htwo : (2 : 𝓀[DyadicSqrtTwo]) = 0 := by
    simpa only [hcard, Nat.cast_ofNat] using FiniteField.cast_card_eq_zero 𝓀[DyadicSqrtTwo]
  have hc (t : 𝓀[DyadicSqrtTwo]) :
      t ^ 2 + t ≠ residue 𝒪[DyadicSqrtTwo] 1 := by
    have ht : t ^ 2 = t := by simpa only [hcard] using FiniteField.pow_card t
    rw [ht, ← two_mul, htwo, zero_mul, map_one]
    exact zero_ne_one
  have hrad : (1 : DyadicSqrtTwo) + 4 * ((1 : 𝒪[DyadicSqrtTwo]) : DyadicSqrtTwo) = 5 := by
    norm_num
  simpa only [hrad] using exists_eq_sq_sub_one_add_four_mul_mul_sq_iff_even
    (K := DyadicSqrtTwo) two_ne_zero hc b

/-- The control norm is a unit of the integer ring of the ramified base. -/
theorem isUnit_one_add_integerSqrtTwo : IsUnit (1 + integerSqrtTwo) := by
  have hn : ¬ IsUnit (-integerSqrtTwo) := by
    simpa using irreducible_integerSqrtTwo.not_isUnit
  simpa using (isUnit_or_isUnit_one_sub_self (-integerSqrtTwo)).resolve_left hn

/-- Rational square-root coordinates exhibit the unit `1 + √2` as a norm for radicand `5`. -/
theorem one_add_sqrtTwo_eq_norm :
    1 + sqrtTwo = (sqrtTwo + 1 / 2) ^ 2 - 5 * (1 / 2 : DyadicSqrtTwo) ^ 2 := by
  linear_combination -sqrtTwo_sq

/-- The unit norm `1 + √2` has no integral representation in the square-root basis for
radicand `5`. The maximal order of that quadratic extension is essential. -/
theorem not_exists_integral_norm_one_add_sqrtTwo :
    ¬ ∃ x y : 𝒪[DyadicSqrtTwo], (x : DyadicSqrtTwo) ^ 2 - 5 * (y : DyadicSqrtTwo) ^ 2 =
      1 + sqrtTwo := by
  obtain ⟨B, hB0, hB1, -, -⟩ := exists_basis_integerRing_of_sq_eq_of_irreducible
    (K := ℚ_[2]) (L := DyadicSqrtTwo) (a := 2) (Padic.irreducible_natCast_self 2)
    (x := sqrtTwo) (by simpa only [coe_two_padicIntegerRing, map_ofNat] using sqrtTwo_sq)
  have hB1' : B 1 = integerSqrtTwo := Subtype.ext (hB1.trans coe_integerSqrtTwo.symm)
  have hπ : integerSqrtTwo ^ 2 = (2 : 𝒪[DyadicSqrtTwo]) := by
    apply Subtype.ext
    simpa only [SubmonoidClass.coe_pow, coe_integerSqrtTwo, coe_two_integerRing] using sqrtTwo_sq
  have hr (z : 𝒪[DyadicSqrtTwo]) :
      z = B.repr z 0 • (1 : 𝒪[DyadicSqrtTwo]) + B.repr z 1 • integerSqrtTwo := by
    simpa only [Fin.sum_univ_two, hB0, hB1'] using (B.sum_repr z).symm
  rintro ⟨x, y, hxy⟩
  have h : x ^ 2 - 5 * y ^ 2 = 1 + integerSqrtTwo := by
    apply Subtype.ext
    simpa only [SubmonoidClass.coe_pow, AddSubgroupClass.coe_sub, Subring.coe_mul,
      Subring.coe_add, Subring.coe_one, coe_five_integerRing,
      coe_integerSqrtTwo] using hxy
  have hc :
      (B.repr x 0 ^ 2 + 2 * B.repr x 1 ^ 2 -
        5 * (B.repr y 0 ^ 2 + 2 * B.repr y 1 ^ 2)) • B 0 +
      (2 * (B.repr x 0 * B.repr x 1 - 5 * B.repr y 0 * B.repr y 1)) • B 1 =
        1 + integerSqrtTwo := by
    rw [hB0, hB1']
    calc
      _ = x ^ 2 - 5 * y ^ 2 := by
        conv_rhs => rw [hr x, hr y]
        simp only [Algebra.smul_def, map_sub, map_add, map_mul, map_pow, map_ofNat]
        linear_combination
          -(algebraMap 𝒪[ℚ_[2]] 𝒪[DyadicSqrtTwo] (B.repr x 1) ^ 2 -
            5 * algebraMap 𝒪[ℚ_[2]] 𝒪[DyadicSqrtTwo] (B.repr y 1) ^ 2) * hπ
      _ = _ := h
  rw [← hB0, ← hB1'] at hc
  have hcoeff := congrArg (fun z => B.repr z 1) hc
  simp at hcoeff
  exact (show Irreducible (2 : 𝒪[ℚ_[2]]) from
    by simpa using Padic.irreducible_natCast_self 2).not_isUnit
    (isUnit_of_dvd_one ⟨_, hcoeff.symm⟩)

/-- Neither of the square-root-coordinate families with integral parameters contains the
unit norm `1 + √2`. In particular restricting `u` to units cannot repair these families. -/
theorem not_mem_naive_integral_norm_families (u t : 𝒪[DyadicSqrtTwo]) :
    (u : DyadicSqrtTwo) ^ 2 * (1 - 5 * (t : DyadicSqrtTwo) ^ 2) ≠ 1 + sqrtTwo ∧
      -5 * (u : DyadicSqrtTwo) ^ 2 * (1 - 5 * (t : DyadicSqrtTwo) ^ 2) ≠ 1 + sqrtTwo := by
  constructor
  · intro h
    apply not_exists_integral_norm_one_add_sqrtTwo
    refine ⟨u, u * t, ?_⟩
    simp only [Subring.coe_mul]
    linear_combination h
  · intro h
    apply not_exists_integral_norm_one_add_sqrtTwo
    refine ⟨5 * u * t, u, ?_⟩
    simp only [Subring.coe_mul, coe_five_integerRing]
    linear_combination h

end TauCeti.DyadicSqrtTwo
