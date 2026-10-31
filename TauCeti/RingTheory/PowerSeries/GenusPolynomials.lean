/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Cartier
public import TauCeti.RingTheory.PowerSeries.CharacteristicSeries
public import TauCeti.RingTheory.PowerSeries.MultiplicativeSequence

/-!
# The Todd, L and Â polynomials in low degree

Hirzebruch's multiplicative sequences of the Todd, L and Â genera are the universal polynomials
expressing the Todd class in the Chern classes, and the L and Â classes in the Pontryagin
classes. This file identifies their first terms over a `ℚ`-algebra `A`:

* `Td = 1 + c₁/2 + (c₁² + c₂)/12 + c₁c₂/24 + …`;
* `L = 1 + p₁/3 + (7p₂ - p₁²)/45 + …`;
* `Â = 1 - p₁/24 + (7p₁² - 4p₂)/5760 + …`.

The Todd polynomials are the multiplicative sequence of the Todd series
`Td(X) = X / (1 - e^{-X})`, applied to the Chern roots, so the variable `j` stands for `c_{j+1}`.
The series `L(X) = X / tanh X` and `Â(X) = (X / 2) / sinh (X / 2)` are even. They are applied to
one degree-two root `xⱼ` for each oriented real 2-plane, and their products are expressed in the
elementary symmetric polynomials `pᵢ` of the `xⱼ²`. So the L and Â polynomials are the
multiplicative sequences of the series `P` with `P(X²) = L(X)`, respectively `P(X²) = Â(X)`. Here
`P` is the residue-zero Cartier component `PowerSeries.cartier A 2 0`, which keeps the even
coefficients, and the variable `j` stands for `p_{j+1}`.

## Main results

* `TauCeti.multiplicativeSequence_bernoulli'PowerSeries_one`,
  `TauCeti.multiplicativeSequence_bernoulli'PowerSeries_two`,
  `TauCeti.multiplicativeSequence_bernoulli'PowerSeries_three`: `Td₁ = c₁/2`,
  `Td₂ = (c₁² + c₂)/12` and `Td₃ = c₁c₂/24`.
* `TauCeti.expand_cartier_hirzebruchLSeries`, `TauCeti.expand_cartier_aHatSeries`: the L and Â
  series are the series of their even coefficients, evaluated at `X²`.
* `TauCeti.multiplicativeSequence_cartier_hirzebruchLSeries_one`,
  `TauCeti.multiplicativeSequence_cartier_hirzebruchLSeries_two`: `L₁ = p₁/3` and
  `L₂ = (7p₂ - p₁²)/45`.
* `TauCeti.multiplicativeSequence_cartier_aHatSeries_one`,
  `TauCeti.multiplicativeSequence_cartier_aHatSeries_two`: `Â₁ = -p₁/24` and
  `Â₂ = (7p₁² - 4p₂)/5760`.

## References

* F. Hirzebruch, *Topological Methods in Algebraic Geometry*, Springer (1966), §1.
* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §19 and Appendix B.
-/

public section

open PowerSeries

namespace TauCeti

variable (A : Type*) [CommRing A] [Algebra ℚ A] (n : ℕ)

/-! ### The Todd polynomials -/

/-- The first Todd polynomial, in rank at least one: `Td₁ = c₁/2`. -/
theorem multiplicativeSequence_bernoulli'PowerSeries_one :
    (bernoulli'PowerSeries A).multiplicativeSequence (n + 1) 1 =
      MvPolynomial.C (algebraMap ℚ A (1 / 2)) * MvPolynomial.X 0 := by
  rw [multiplicativeSequence_one_right n (constantCoeff_bernoulli'PowerSeries A),
    coeff_one_bernoulli'PowerSeries]

/-- The second Todd polynomial, in rank at least two: `Td₂ = (c₁² + c₂)/12`. -/
theorem multiplicativeSequence_bernoulli'PowerSeries_two :
    (bernoulli'PowerSeries A).multiplicativeSequence (n + 2) 2 =
      MvPolynomial.C (algebraMap ℚ A (1 / 12)) * (MvPolynomial.X 0 ^ 2 + MvPolynomial.X 1) := by
  have h : algebraMap ℚ A (1 / 2) ^ 2 - 2 * algebraMap ℚ A (1 / 12) =
      algebraMap ℚ A (1 / 12) := by
    rw [← map_pow, ← map_ofNat (algebraMap ℚ A) 2, ← map_mul, ← map_sub]
    norm_num
  rw [multiplicativeSequence_two_right n (constantCoeff_bernoulli'PowerSeries A),
    coeff_one_bernoulli'PowerSeries, coeff_two_bernoulli'PowerSeries, h, mul_add]

/-- The third Todd polynomial, in rank at least three: `Td₃ = c₁c₂/24`. -/
theorem multiplicativeSequence_bernoulli'PowerSeries_three :
    (bernoulli'PowerSeries A).multiplicativeSequence (n + 3) 3 =
      MvPolynomial.C (algebraMap ℚ A (1 / 24)) * MvPolynomial.X 0 * MvPolynomial.X 1 := by
  have h₁ : algebraMap ℚ A (1 / 2) * algebraMap ℚ A (1 / 12) - 3 * 0 =
      algebraMap ℚ A (1 / 24) := by
    rw [← map_mul, mul_zero, sub_zero]
    norm_num
  have h₂ : algebraMap ℚ A (1 / 2) ^ 3 -
      3 * algebraMap ℚ A (1 / 2) * algebraMap ℚ A (1 / 12) + 3 * 0 = 0 := by
    rw [← map_pow, ← map_ofNat (algebraMap ℚ A) 3, ← map_mul, ← map_mul, ← map_sub, mul_zero,
      add_zero]
    norm_num
  rw [multiplicativeSequence_three_right n (constantCoeff_bernoulli'PowerSeries A),
    coeff_one_bernoulli'PowerSeries, coeff_two_bernoulli'PowerSeries,
    coeff_three_bernoulli'PowerSeries, h₁, h₂, map_zero, zero_mul, zero_mul, zero_add, add_zero]

/-! ### The L polynomials -/

/-- **The L series is even**: it is the series `P` of its even coefficients evaluated at `X²`,
`L(X) = P(X²)`. -/
theorem expand_cartier_hirzebruchLSeries :
    expand 2 two_ne_zero (cartier A 2 0 (hirzebruchLSeries A)) = hirzebruchLSeries A :=
  expand_cartier_zero_of_coeff_eq_zero _ _ fun _ hn ↦
    coeff_hirzebruchLSeries_of_odd A (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hn))

/-- The series of even coefficients of the L series has constant coefficient `1`. -/
@[simp]
theorem constantCoeff_cartier_hirzebruchLSeries :
    constantCoeff (cartier A 2 0 (hirzebruchLSeries A)) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_cartier]
  simp

/-- The first L polynomial, for at least one root: `L₁ = p₁/3`. -/
theorem multiplicativeSequence_cartier_hirzebruchLSeries_one :
    (cartier A 2 0 (hirzebruchLSeries A)).multiplicativeSequence (n + 1) 1 =
      MvPolynomial.C (algebraMap ℚ A (1 / 3)) * MvPolynomial.X 0 := by
  rw [multiplicativeSequence_one_right n (constantCoeff_cartier_hirzebruchLSeries A),
    coeff_cartier, coeff_two_hirzebruchLSeries]

/-- The second L polynomial, for at least two roots: `L₂ = (7p₂ - p₁²)/45`. -/
theorem multiplicativeSequence_cartier_hirzebruchLSeries_two :
    (cartier A 2 0 (hirzebruchLSeries A)).multiplicativeSequence (n + 2) 2 =
      MvPolynomial.C (algebraMap ℚ A (1 / 45)) * (7 * MvPolynomial.X 1 - MvPolynomial.X 0 ^ 2) := by
  have h₁ : algebraMap ℚ A (-1 / 45) = -algebraMap ℚ A (1 / 45) := by
    rw [← map_neg]
    norm_num
  have h₂ : algebraMap ℚ A (1 / 3) ^ 2 - 2 * -algebraMap ℚ A (1 / 45) =
      7 * algebraMap ℚ A (1 / 45) := by
    rw [← map_pow, ← map_ofNat (algebraMap ℚ A) 2, ← map_ofNat (algebraMap ℚ A) 7, ← map_neg,
      ← map_mul, ← map_mul, ← map_sub]
    norm_num
  rw [multiplicativeSequence_two_right n (constantCoeff_cartier_hirzebruchLSeries A),
    coeff_cartier, coeff_cartier, coeff_two_hirzebruchLSeries, coeff_four_hirzebruchLSeries, h₁,
    h₂, map_neg, map_mul, map_ofNat]
  ring

/-! ### The Â polynomials -/

/-- **The Â series is even**: it is the series `P` of its even coefficients evaluated at `X²`,
`Â(X) = P(X²)`. -/
theorem expand_cartier_aHatSeries :
    expand 2 two_ne_zero (cartier A 2 0 (aHatSeries A)) = aHatSeries A :=
  expand_cartier_zero_of_coeff_eq_zero _ _ fun _ hn ↦
    coeff_aHatSeries_of_odd A (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hn))

/-- The series of even coefficients of the Â series has constant coefficient `1`. -/
@[simp]
theorem constantCoeff_cartier_aHatSeries :
    constantCoeff (cartier A 2 0 (aHatSeries A)) = 1 := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_cartier]
  simp

/-- The first Â polynomial, for at least one root: `Â₁ = -p₁/24`. -/
theorem multiplicativeSequence_cartier_aHatSeries_one :
    (cartier A 2 0 (aHatSeries A)).multiplicativeSequence (n + 1) 1 =
      MvPolynomial.C (algebraMap ℚ A (-1 / 24)) * MvPolynomial.X 0 := by
  rw [multiplicativeSequence_one_right n (constantCoeff_cartier_aHatSeries A), coeff_cartier,
    coeff_two_aHatSeries]

/-- The second Â polynomial, for at least two roots: `Â₂ = (7p₁² - 4p₂)/5760`. -/
theorem multiplicativeSequence_cartier_aHatSeries_two :
    (cartier A 2 0 (aHatSeries A)).multiplicativeSequence (n + 2) 2 =
      MvPolynomial.C (algebraMap ℚ A (1 / 5760)) *
        (7 * MvPolynomial.X 0 ^ 2 - 4 * MvPolynomial.X 1) := by
  have h₁ : algebraMap ℚ A (7 / 5760) = 7 * algebraMap ℚ A (1 / 5760) := by
    rw [← map_ofNat (algebraMap ℚ A) 7, ← map_mul]
    norm_num
  have h₂ : algebraMap ℚ A (-1 / 24) ^ 2 - 2 * (7 * algebraMap ℚ A (1 / 5760)) =
      -(4 * algebraMap ℚ A (1 / 5760)) := by
    rw [← map_pow, ← map_ofNat (algebraMap ℚ A) 2, ← map_ofNat (algebraMap ℚ A) 7,
      ← map_ofNat (algebraMap ℚ A) 4, ← map_mul, ← map_mul, ← map_mul, ← map_sub, ← map_neg]
    norm_num
  rw [multiplicativeSequence_two_right n (constantCoeff_cartier_aHatSeries A),
    coeff_cartier, coeff_cartier, coeff_two_aHatSeries, coeff_four_aHatSeries, h₁, h₂, map_neg,
    map_mul, map_mul, map_ofNat, map_ofNat]
  ring

end TauCeti
