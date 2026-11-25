/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Cartier
public import TauCeti.RingTheory.PowerSeries.CharacteristicSeries
public import TauCeti.RingTheory.PowerSeries.MultiplicativeSequence

import TauCeti.RingTheory.PowerSeries.Derivative

/-!
# Coefficients of the Todd, L and Â polynomials

Hirzebruch's multiplicative sequences of the Todd, L and Â genera are the universal polynomials
expressing the Todd class in the Chern classes, and the L and Â classes in the Pontryagin
classes. This file identifies their first terms over a `ℚ`-algebra `A`:

* `Td = 1 + c₁/2 + (c₁² + c₂)/12 + c₁c₂/24 + …`;
* `L = 1 + p₁/3 + (7p₂ - p₁²)/45 + (62p₃ - 13p₁p₂ + 2p₁³)/945 + …`;
* `Â = 1 - p₁/24 + (7p₁² - 4p₂)/5760 + …`.

In every degree `k` it also computes the coefficient of the top Pontryagin class in `Lₖ`:
modulo products of lower Pontryagin classes, `Lₖ = sₖ pₖ` with
`sₖ = (-1)ᵏ⁻¹ 2²ᵏ (2²ᵏ⁻¹ - 1) B₂ₖ / (2k)!`, from the logarithmic derivative of `L`.

The Todd polynomials are the multiplicative sequence of the Todd series
`Td(X) = X / (1 - e^{-X})`, applied to the Chern roots, so the variable `j` stands for `c_{j+1}`.
The series `L(X) = X / tanh X` and `Â(X) = (X / 2) / sinh (X / 2)` are even. They are applied to
one degree-two root `xⱼ` for each oriented real 2-plane, and their products are expressed in the
elementary symmetric polynomials `pᵢ` of the `xⱼ²`. So the L and Â polynomials are the
multiplicative sequences of the series `P` with `P(X²) = L(X)`, respectively `P(X²) = Â(X)`. Here
`P` is the residue-zero Cartier component `PowerSeries.cartier A 2 0`, which keeps the even
coefficients, and the variable `j` stands for `p_{j+1}`.

The index-theoretic form of the signature theorem uses the half-argument series
`X / tanh (X / 2) = 2 L(X / 2)` in place of `L`. On `n` roots the two products agree in degree `n`,
the component that is paired with the fundamental class of a closed oriented manifold of
dimension `2n`.

## Main results

* `TauCeti.multiplicativeSequence_bernoulli'PowerSeries_one`,
  `TauCeti.multiplicativeSequence_bernoulli'PowerSeries_two`,
  `TauCeti.multiplicativeSequence_bernoulli'PowerSeries_three`: `Td₁ = c₁/2`,
  `Td₂ = (c₁² + c₂)/12` and `Td₃ = c₁c₂/24`.
* `TauCeti.expand_cartier_hirzebruchLSeries`, `TauCeti.expand_cartier_aHatSeries`: the L and Â
  series are the series of their even coefficients, evaluated at `X²`.
* `TauCeti.multiplicativeSequence_cartier_hirzebruchLSeries_one`,
  `TauCeti.multiplicativeSequence_cartier_hirzebruchLSeries_two`,
  `TauCeti.multiplicativeSequence_cartier_hirzebruchLSeries_three`: `L₁ = p₁/3`,
  `L₂ = (7p₂ - p₁²)/45` and `L₃ = (62p₃ - 13p₁p₂ + 2p₁³)/945`.
* `TauCeti.coeff_six_multiset_prod_rescale_hirzebruchLSeries`: the same formula for `L₃` in terms
  of the roots, for any number of roots.
* `TauCeti.coeff_single_multiplicativeSequence_cartier_hirzebruchLSeries`: in every degree `k`, the
  coefficient of `pₖ` in `Lₖ` is `sₖ = (-1)ᵏ⁻¹ 2²ᵏ (2²ᵏ⁻¹ - 1) B₂ₖ / (2k)!`.
* `TauCeti.coeff_multiset_prod_rescale_two_mul_rescale_half_hirzebruchLSeries`: for `n` roots,
  the half-argument products `∏ xⱼ / tanh (xⱼ / 2)` and `∏ L(xⱼ)` agree in degree `n`.
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
  have h : algebraMap ℚ A (1 / 2) ^ 2 = 3 * algebraMap ℚ A (1 / 12) := by
    simp only [← map_ofNat (algebraMap ℚ A), ← map_pow, ← map_mul]
    norm_num
  rw [multiplicativeSequence_two_right n (constantCoeff_bernoulli'PowerSeries A),
    coeff_one_bernoulli'PowerSeries, coeff_two_bernoulli'PowerSeries, h]
  simp only [map_sub, map_mul, map_ofNat]
  ring

/-- The third Todd polynomial, in rank at least three: `Td₃ = c₁c₂/24`. -/
theorem multiplicativeSequence_bernoulli'PowerSeries_three :
    (bernoulli'PowerSeries A).multiplicativeSequence (n + 3) 3 =
      MvPolynomial.C (algebraMap ℚ A (1 / 24)) * MvPolynomial.X 0 * MvPolynomial.X 1 := by
  have h₁ : algebraMap ℚ A (1 / 2) * algebraMap ℚ A (1 / 12) = algebraMap ℚ A (1 / 24) := by
    simp only [← map_mul]
    norm_num
  have h₂ : algebraMap ℚ A (1 / 2) ^ 3 - 3 * algebraMap ℚ A (1 / 2) * algebraMap ℚ A (1 / 12) =
      0 := by
    simp only [← map_ofNat (algebraMap ℚ A), ← map_pow, ← map_mul, ← map_sub]
    norm_num
  rw [multiplicativeSequence_three_right n (constantCoeff_bernoulli'PowerSeries A),
    coeff_one_bernoulli'PowerSeries, coeff_two_bernoulli'PowerSeries,
    coeff_three_bernoulli'PowerSeries]
  simp only [mul_zero, sub_zero, add_zero, map_zero, zero_mul, zero_add, h₁, h₂]

/-! ### The L polynomials -/

/-- **The L series is even**: it is the series `P` of its even coefficients evaluated at `X²`,
`L(X) = P(X²)`. -/
theorem expand_cartier_hirzebruchLSeries :
    expand 2 two_ne_zero (cartier A 2 0 (hirzebruchLSeries A)) = hirzebruchLSeries A :=
  expand_cartier_zero_of_coeff_eq_zero _ _ fun _ hn ↦
    coeff_hirzebruchLSeries_of_odd A (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hn))

/-- The series of even coefficients of the L series has constant coefficient `1`. -/
theorem constantCoeff_cartier_hirzebruchLSeries :
    constantCoeff (cartier A 2 0 (hirzebruchLSeries A)) = 1 := by
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
    simp only [← map_neg]
    norm_num
  have h₂ : algebraMap ℚ A (1 / 3) ^ 2 = 5 * algebraMap ℚ A (1 / 45) := by
    simp only [← map_ofNat (algebraMap ℚ A), ← map_pow, ← map_mul]
    norm_num
  rw [multiplicativeSequence_two_right n (constantCoeff_cartier_hirzebruchLSeries A),
    coeff_cartier, coeff_cartier, coeff_two_hirzebruchLSeries, coeff_four_hirzebruchLSeries, h₁,
    h₂]
  simp only [map_neg, map_sub, map_mul, map_ofNat]
  ring

/-- The third L polynomial, for at least three roots: `L₃ = (62p₃ - 13p₁p₂ + 2p₁³)/945`. -/
theorem multiplicativeSequence_cartier_hirzebruchLSeries_three :
    (cartier A 2 0 (hirzebruchLSeries A)).multiplicativeSequence (n + 3) 3 =
      MvPolynomial.C (algebraMap ℚ A (1 / 945)) *
        (62 * MvPolynomial.X 2 - 13 * MvPolynomial.X 0 * MvPolynomial.X 1 +
          2 * MvPolynomial.X 0 ^ 3) := by
  have h₁ : algebraMap ℚ A (2 / 945) = 2 * algebraMap ℚ A (1 / 945) := by
    simp only [← map_ofNat (algebraMap ℚ A), ← map_mul]
    norm_num
  have h₂ : algebraMap ℚ A (1 / 3) * algebraMap ℚ A (-1 / 45) - 3 * algebraMap ℚ A (2 / 945) =
      -13 * algebraMap ℚ A (1 / 945) := by
    simp only [← map_ofNat (algebraMap ℚ A), ← map_mul, ← map_sub, ← map_neg]
    norm_num
  have h₃ : algebraMap ℚ A (1 / 3) ^ 3 - 3 * algebraMap ℚ A (1 / 3) * algebraMap ℚ A (-1 / 45) +
      3 * algebraMap ℚ A (2 / 945) = 62 * algebraMap ℚ A (1 / 945) := by
    simp only [← map_ofNat (algebraMap ℚ A), ← map_pow, ← map_mul, ← map_sub, ← map_add]
    norm_num
  rw [multiplicativeSequence_three_right n (constantCoeff_cartier_hirzebruchLSeries A),
    coeff_cartier, coeff_cartier, coeff_cartier, coeff_two_hirzebruchLSeries,
    coeff_four_hirzebruchLSeries, coeff_six_hirzebruchLSeries, h₂, h₃, h₁]
  simp only [map_mul, map_neg, map_ofNat]
  ring

/-- **The degree-twelve L class in roots**: for any multiset `s` of roots `xⱼ` in a commutative
`ℚ`-algebra, the coefficient of `t⁶` in `∏ⱼ L(xⱼ t)` is `(62p₃ - 13p₁p₂ + 2p₁³)/945`, where
`pᵢ = eᵢ(x₁², x₂², …)` is the `i`-th elementary symmetric function of the squares of the roots.
There is no lower bound on the number of roots: with fewer than three roots, the absent `pᵢ`
vanish. -/
theorem coeff_six_multiset_prod_rescale_hirzebruchLSeries (s : Multiset A) :
    coeff 6 (s.map fun x ↦ rescale x (hirzebruchLSeries A)).prod =
      algebraMap ℚ A (1 / 945) * (62 * (s.map (· ^ 2)).esymm 3 -
        13 * (s.map (· ^ 2)).esymm 1 * (s.map (· ^ 2)).esymm 2 +
          2 * (s.map (· ^ 2)).esymm 1 ^ 3) := by
  -- Pad `s` with three zero roots, which change neither side, and apply `L₃`.
  have h := aeval_multiset_esymm_sq_multiplicativeSequence (cartier A 2 0 (hirzebruchLSeries A))
    (s.card + 3) 3 (0 ::ₘ 0 ::ₘ 0 ::ₘ s) (by simp)
  rw [multiplicativeSequence_cartier_hirzebruchLSeries_three, expand_cartier_hirzebruchLSeries,
    Algebra.algebraMap_self, PowerSeries.map_id] at h
  have h0 : rescale (0 : A) (hirzebruchLSeries A) = 1 := by simp [rescale_zero]
  simp only [map_mul, map_sub, map_add, map_pow, map_ofNat, MvPolynomial.aeval_C,
    MvPolynomial.aeval_X, Multiset.map_cons, Multiset.prod_cons, id, h0, one_mul,
    Algebra.algebraMap_self, RingHom.id_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, Multiset.esymm_cons_zero, Fin.val_zero, Fin.val_one, Fin.val_two,
    Nat.reduceAdd, Nat.reduceMul] at h
  exact h.symm

/-- **The half-argument form of the L class**: the series `X / tanh (X / 2)` is `2 L(X / 2)`.
For a multiset `s` of `n` roots `xⱼ`, the products `∏ⱼ xⱼt / tanh (xⱼt / 2)` and `∏ⱼ L(xⱼ t)` have
the same coefficient of `tⁿ`. For `n = 2k` roots of a real bundle of rank `4k`, this is the
equality of the degree-`4k` components of the two characteristic classes. The full products
differ: their constant coefficients are `2ⁿ` and `1`. -/
theorem coeff_multiset_prod_rescale_two_mul_rescale_half_hirzebruchLSeries (s : Multiset A)
    (hs : s.card = n) :
    coeff n (s.map fun x ↦
        rescale x (2 * rescale (algebraMap ℚ A 2⁻¹) (hirzebruchLSeries A))).prod =
      coeff n (s.map fun x ↦ rescale x (hirzebruchLSeries A)).prod := by
  rw [← map_ofNat C 2, coeff_multiset_prod_rescale_C_mul_rescale, hs, ← mul_pow,
    ← map_ofNat (algebraMap ℚ A) 2, ← map_mul, mul_inv_cancel₀ (two_ne_zero' ℚ), map_one, one_pow,
    one_mul]

variable {n} in
/-- **The indecomposable coefficient of the L polynomials**: for `k = i + 1 ≤ n`, the coefficient
of the top Pontryagin class `pₖ` in `Lₖ` is
`sₖ = (-1)ᵏ⁻¹ 2²ᵏ (2²ᵏ⁻¹ - 1) B₂ₖ / (2k)!`. For instance `s₁ = 1/3`, `s₂ = 7/45` and
`s₃ = 62/945`. Modulo products of lower Pontryagin classes, `Lₖ` is therefore `sₖ pₖ`. Here the
Cartier component `cartier A 2 0 (hirzebruchLSeries A)` is the series `P` with `P(X²) = L(X)`, and
the variable `i` of its multiplicative sequence stands for the Pontryagin class `pₖ`. -/
theorem coeff_single_multiplicativeSequence_cartier_hirzebruchLSeries (i : Fin n) :
    ((cartier A 2 0 (hirzebruchLSeries A)).multiplicativeSequence n (i + 1)).coeff
        (Finsupp.single i 1) =
      algebraMap ℚ A ((-1) ^ (i : ℕ) * 2 ^ (2 * ((i : ℕ) + 1)) * (2 ^ (2 * (i : ℕ) + 1) - 1) *
        bernoulli (2 * ((i : ℕ) + 1)) / (2 * ((i : ℕ) + 1)).factorial) := by
  set L := hirzebruchLSeries A
  set M := 1 + rescale 2 L - 2 * L
  -- `M` is even, since `L` is.
  have hM : expand 2 two_ne_zero (cartier A 2 0 M) = M := by
    refine expand_cartier_zero_of_coeff_eq_zero _ _ fun m hm ↦ ?_
    have hL : coeff m L = 0 := coeff_hirzebruchLSeries_of_odd A (Nat.odd_iff.2
      (Nat.two_dvd_ne_zero.1 hm))
    have hm0 : m ≠ 0 := by rintro rfl; exact hm (dvd_zero 2)
    simp [M, ← map_ofNat C 2, coeff_rescale, hL, coeff_one, hm0]
  -- The logarithmic derivative of `P` with `P(X²) = L(X)` is `M(√X) / 2`.
  have h2 : C (algebraMap ℚ A 2⁻¹) * 2 = (1 : A⟦X⟧) := by
    simpa only [map_mul, map_ofNat, map_one, RingHom.comp_apply] using
      congrArg ((C : A →+* A⟦X⟧).comp (algebraMap ℚ A)) (inv_mul_cancel₀ (two_ne_zero' ℚ))
  have hG : cartier A 2 0 L * (C (algebraMap ℚ A 2⁻¹) * cartier A 2 0 M) =
      X * d⁄dX (cartier A 2 0 L) := by
    refine expand_injective 2 two_ne_zero ?_
    have hd := X_mul_derivative_expand 2 two_ne_zero (cartier A 2 0 L)
    rw [expand_cartier_hirzebruchLSeries, X_mul_derivative_hirzebruchLSeries] at hd
    rw [map_mul, map_mul, expand_cartier_hirzebruchLSeries, expand_C, hM]
    linear_combination C (algebraMap ℚ A 2⁻¹) * hd +
      expand 2 two_ne_zero (X * d⁄dX (cartier A 2 0 L)) * h2
  -- The coefficient of `X²ᵏ` in `M` is `(2²ᵏ - 2) 2²ᵏ B₂ₖ / (2k)!`.
  have hk : 2 * ((i : ℕ) + 1) ≠ 1 := by omega
  have hk0 : 2 * ((i : ℕ) + 1) ≠ 0 := by omega
  have hc : coeff (2 * ((i : ℕ) + 1)) M = algebraMap ℚ A ((2 ^ (2 * ((i : ℕ) + 1)) - 2) *
      (2 ^ (2 * ((i : ℕ) + 1)) * bernoulli (2 * ((i : ℕ) + 1)) /
        (2 * ((i : ℕ) + 1)).factorial)) := by
    have hL : coeff (2 * ((i : ℕ) + 1)) L = algebraMap ℚ A (2 ^ (2 * ((i : ℕ) + 1)) *
        bernoulli (2 * ((i : ℕ) + 1)) / (2 * ((i : ℕ) + 1)).factorial) :=
      coeff_hirzebruchLSeries A hk
    simp only [M, map_add, map_sub, coeff_one, hk0, ite_false, coeff_rescale, ← map_ofNat C 2,
      coeff_C_mul, hL, zero_add]
    simp only [← map_ofNat (algebraMap ℚ A), ← map_pow, ← map_mul, ← map_sub]
    congr 1
    ring
  rw [coeff_single_multiplicativeSequence (constantCoeff_cartier_hirzebruchLSeries A) hG,
    coeff_C_mul, coeff_cartier, add_zero, hc]
  -- In `ℚ`, `sₖ` is `(-1)ᵏ⁻¹ / 2` times the coefficient `hc` of `X²ᵏ` in `M`.
  have hs : ((-1) ^ (i : ℕ) * 2 ^ (2 * ((i : ℕ) + 1)) * (2 ^ (2 * (i : ℕ) + 1) - 1) *
      bernoulli (2 * ((i : ℕ) + 1)) / (2 * ((i : ℕ) + 1)).factorial : ℚ) =
      (-1) ^ (i : ℕ) * (2⁻¹ * ((2 ^ (2 * ((i : ℕ) + 1)) - 2) * (2 ^ (2 * ((i : ℕ) + 1)) *
        bernoulli (2 * ((i : ℕ) + 1)) / (2 * ((i : ℕ) + 1)).factorial))) := by
    ring
  rw [hs]
  simp only [map_mul, map_pow, map_neg, map_one]

/-! ### The Â polynomials -/

/-- **The Â series is even**: it is the series `P` of its even coefficients evaluated at `X²`,
`Â(X) = P(X²)`. -/
theorem expand_cartier_aHatSeries :
    expand 2 two_ne_zero (cartier A 2 0 (aHatSeries A)) = aHatSeries A :=
  expand_cartier_zero_of_coeff_eq_zero _ _ fun _ hn ↦
    coeff_aHatSeries_of_odd A (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hn))

/-- The series of even coefficients of the Â series has constant coefficient `1`. -/
theorem constantCoeff_cartier_aHatSeries :
    constantCoeff (cartier A 2 0 (aHatSeries A)) = 1 := by
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
    simp only [← map_ofNat (algebraMap ℚ A), ← map_mul]
    norm_num
  have h₂ : algebraMap ℚ A (-1 / 24) ^ 2 = 10 * algebraMap ℚ A (1 / 5760) := by
    simp only [← map_ofNat (algebraMap ℚ A), ← map_pow, ← map_mul]
    norm_num
  rw [multiplicativeSequence_two_right n (constantCoeff_cartier_aHatSeries A),
    coeff_cartier, coeff_cartier, coeff_two_aHatSeries, coeff_four_aHatSeries, h₁, h₂]
  simp only [map_sub, map_mul, map_ofNat]
  ring

end TauCeti
