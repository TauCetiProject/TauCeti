/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import TauCeti.NumberTheory.NumberField.Quadratic.Norm
public import TauCeti.NumberTheory.NumberField.WorkedExamples.GaussianRationals.Invariants
public import TauCeti.RingTheory.RootsOfUnity.Basic

/-!
# Basic facts about the Gaussian integers as a ring of integers

Let `K = ℚ(i)` be given as a number field with `IsCyclotomicExtension {4} ℚ K`, so that
`𝓞 K = ℤ[i]` for a primitive fourth root of unity `i`. This file records the elementary facts
about `ℤ[i]` that the primary normalisation of quartic reciprocity is computed with. The
coordinates of `ℤ[i]` in the basis `1, i` are described for every quadratic cyclotomic field in
`TauCeti.NumberTheory.NumberField.Cyclotomic.Quadratic`.

* `TauCeti.one_add_pow_four_of_sq_eq_neg_one`: for a square root `x` of `-1` in a commutative
  ring, `(1 + x)⁴ = -4`;
* `TauCeti.associated_one_add_of_sq_eq_neg_one`: in a domain, `1 + x` does not depend on the
  choice of the square root `x` of `-1` up to a unit;
* `TauCeti.one_add_pow_three_dvd_iff_four_dvd_mul`: in a domain with `2 ≠ 0`, divisibility by
  `(1 + x)³` is divisibility of the product with `1 + x` by `4`;
* `IsPrimitiveRoot.minpoly_toInteger_eq_X_sq_add_one`: the minimal polynomial of `i` is
  `X² + 1`, the hypothesis of the `GaussianRationals` API, which
  `GaussianRationals.minpoly_eq_X_sq_sub_C` converts to the `X² - C d` form of the
  quadratic-field API;
* `IsPrimitiveRoot.norm_intCast_add_intCast_mul_toInteger_of_four`: the norm of `a + b i` is
  `a² + b²`;
* `IsPrimitiveRoot.odd_norm_intCast_add_intCast_mul_toInteger_iff_of_four`: the norm of `a + b i`
  is odd exactly when `a + b` is;
* `IsPrimitiveRoot.isUnit_intCast_add_intCast_mul_toInteger_iff_of_four`: `a + b i` is a unit
  exactly when `a² + b² = 1`;
* `TauCeti.isPrincipalIdealRing_ringOfIntegers_four`: `ℤ[i]` is a principal ideal domain.
-/

public section

open NumberField Polynomial TauCeti.NumberField

namespace TauCeti

variable {R : Type*} [CommRing R]

/-- A square root `x` of `-1` satisfies `(1 + x)⁴ = -4`. -/
theorem one_add_pow_four_of_sq_eq_neg_one {x : R} (hx : x ^ 2 = -1) : (1 + x) ^ 4 = -4 := by
  linear_combination (x ^ 2 + 4 * x + 5) * hx

/-- In a domain, `1 + x` and `1 + y` are associated for any two square roots `x` and `y` of `-1`:
either `y = x`, or `y = -x` and `1 - x = (1 + x) (-x)` with `-x` a unit. -/
theorem associated_one_add_of_sq_eq_neg_one [IsDomain R] {x y : R} (hx : x ^ 2 = -1)
    (hy : y ^ 2 = -1) : Associated (1 + x) (1 + y) := by
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp (hy.trans hx.symm) with rfl | rfl
  · rfl
  · have hu : IsUnit (-x) := IsUnit.of_mul_eq_one x (by linear_combination -hx)
    exact ⟨hu.unit, by rw [IsUnit.unit_spec]; linear_combination -hx⟩

/-- For a square root `x` of `-1` in a domain in which `2 ≠ 0`, `(1 + x)³ ∣ y` if and only if
`4 ∣ y (1 + x)`, since `(1 + x)⁴ = -4`. This trades divisibility by `(1 + x)³` for divisibility
by an integer. -/
theorem one_add_pow_three_dvd_iff_four_dvd_mul [IsDomain R] (h2 : (2 : R) ≠ 0) {x y : R}
    (hx : x ^ 2 = -1) : (1 + x) ^ 3 ∣ y ↔ (4 : R) ∣ y * (1 + x) := by
  have hne : 1 + x ≠ 0 := fun h ↦ h2 (by linear_combination (1 - x) * h + hx)
  constructor
  · rintro ⟨c, rfl⟩
    exact ⟨-c, by linear_combination c * one_add_pow_four_of_sq_eq_neg_one hx⟩
  · rintro ⟨c, hc⟩
    refine ⟨-c, mul_right_cancel₀ hne ?_⟩
    linear_combination hc + c * one_add_pow_four_of_sq_eq_neg_one hx

end TauCeti

namespace IsPrimitiveRoot

variable {K : Type*} [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 4)
include hζ

/-- The minimal polynomial over `ℤ` of a primitive fourth root of unity `i ∈ 𝓞 K` is `X² + 1`.
This is the minimal-polynomial hypothesis of the `GaussianRationals` API;
`GaussianRationals.minpoly_eq_X_sq_sub_C` converts it to the `X² - C d` form taken by the
quadratic-field lemmas such as `TauCeti.NumberField.norm_int_add_mul_gen`. -/
theorem minpoly_toInteger_eq_X_sq_add_one : minpoly ℤ hζ.toInteger = X ^ 2 + 1 := by
  have h : minpoly ℤ ζ = X ^ 2 + 1 := by
    rw [← cyclotomic_eq_minpoly hζ (by norm_num), show (4 : ℕ) = 2 ^ (1 + 1) by norm_num,
      cyclotomic_prime_pow_eq_geom_sum Nat.prime_two]
    simp [Finset.sum_range_succ, add_comm]
  -- The image of `hζ.toInteger` in `K` is `ζ` by definition (`IsPrimitiveRoot.coe_toInteger`).
  rw [← RingOfIntegers.minpoly_coe]
  exact h

variable [IsCyclotomicExtension {4} ℚ K]

private theorem adjoin_toInteger_four : Algebra.adjoin ℚ {(hζ.toInteger : K)} = ⊤ :=
  IsCyclotomicExtension.adjoin_primitive_root_eq_top hζ

/-- The norm of `a + b i` in `𝓞 K = ℤ[i]` is `a² + b²`. -/
@[simp]
theorem norm_intCast_add_intCast_mul_toInteger_of_four (a b : ℤ) :
    Algebra.norm ℤ ((a : 𝓞 K) + b * hζ.toInteger) = a ^ 2 + b ^ 2 := by
  rw [TauCeti.NumberField.norm_int_add_mul_gen
    (GaussianRationals.minpoly_eq_X_sq_sub_C hζ.minpoly_toInteger_eq_X_sq_add_one)
    (adjoin_toInteger_four hζ)]
  ring

/-- The norm of `a + b i` in `𝓞 K = ℤ[i]` is odd exactly when `a + b` is odd. -/
theorem odd_norm_intCast_add_intCast_mul_toInteger_iff_of_four {a b : ℤ} :
    Odd (Algebra.norm ℤ ((a : 𝓞 K) + b * hζ.toInteger)) ↔ Odd (a + b) := by
  rw [norm_intCast_add_intCast_mul_toInteger_of_four]
  simp [Int.odd_add, parity_simps]

/-- An element `a + b i` of `𝓞 K = ℤ[i]` is a unit exactly when `a² + b² = 1`, that is, when it is
one of `±1, ±i`. -/
theorem isUnit_intCast_add_intCast_mul_toInteger_iff_of_four {a b : ℤ} :
    IsUnit ((a : 𝓞 K) + b * hζ.toInteger) ↔ a ^ 2 + b ^ 2 = 1 := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hn := h.map (Algebra.norm ℤ)
    rw [norm_intCast_add_intCast_mul_toInteger_of_four, Int.isUnit_iff] at hn
    rcases hn with hn | hn
    · exact hn
    · nlinarith [sq_nonneg a, sq_nonneg b]
  · refine IsUnit.of_mul_eq_one ((a : 𝓞 K) - b * hζ.toInteger) ?_
    have hsq := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
    have h' : ((a : 𝓞 K)) ^ 2 + (b : 𝓞 K) ^ 2 = 1 := by exact_mod_cast h
    linear_combination (-(b : 𝓞 K) ^ 2) * hsq + h'

end IsPrimitiveRoot

namespace TauCeti

variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

/-- **`ℤ[i]` is a principal ideal domain.** This is
`TauCeti.NumberField.GaussianRationals.isPrincipalIdealRing` at a primitive fourth root of
unity. -/
theorem isPrincipalIdealRing_ringOfIntegers_four : IsPrincipalIdealRing (𝓞 K) :=
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  NumberField.GaussianRationals.isPrincipalIdealRing hζ.minpoly_toInteger_eq_X_sq_add_one
    hζ.adjoin_toInteger_four

end TauCeti
