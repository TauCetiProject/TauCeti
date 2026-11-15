/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.PowerSeries.Cartier
import TauCeti.RingTheory.PowerSeries.Expand
import TauCeti.RingTheory.PowerSeries.Rescale

/-!
# The formal Pontryagin series and its Whitney correction

The Pontryagin classes of a real vector bundle `E` are defined from the Chern classes of its
complexification by `pₖ(E) = (-1)ᵏ c₂ₖ(E ⊗ ℂ)`. Over a commutative ring `R`, this file isolates
the formal algebra behind that definition. For a power series `C = ∑ cᵢ Xⁱ`, standing for the
total Chern class of `E ⊗ ℂ`, the *Pontryagin series* is `∑ₖ (-1)ᵏ c₂ₖ Xᵏ`.

Since `(E ⊕ F) ⊗ ℂ = (E ⊗ ℂ) ⊕ (F ⊗ ℂ)`, the Whitney sum formula for Chern classes reduces the
Pontryagin classes of a direct sum to the Pontryagin series of a product. Writing
`C(X) = C₀(X²) + X C₁(X²)` for the even and odd parts, the product formula for even parts gives
the exact integral Whitney formula
`pₖ(E ⊕ F) = ∑_{a+b=k} pₐ(E) p_b(F) + (-1)ᵏ ∑_{a+b=k-1} c_{2a+1}(E ⊗ ℂ) c_{2b+1}(F ⊗ ℂ)` for
`k ≥ 1`.
The odd Chern classes of a complexification are annihilated by `2`, so the correction term is
`2`-torsion, and the Pontryagin series is multiplicative once `2` is a non-zero-divisor, for
instance over `ℤ[1/2]` or `ℚ`.

For a complex bundle `E` with formal Chern roots `xⱼ`, the complexification of the underlying
real bundle is `E ⊕ Ē` and `c(Ē)(X) = c(E)(-X)`. The product `C(-X) C(X)` is even, which gives
Milnor–Stasheff's formula `1 - p₁ + p₂ - ⋯ = (1 - c₁ + c₂ - ⋯)(1 + c₁ + c₂ + ⋯)` and, in terms
of roots, `p(E_ℝ) = ∏ⱼ (1 + xⱼ²)`.

The even and odd parts are the Cartier components `PowerSeries.cartier R 2 0` and
`PowerSeries.cartier R 2 1`; their product formulas are `PowerSeries.cartier_two_zero_mul` and
`PowerSeries.cartier_two_one_mul`.

## Main definitions

* `PowerSeries.pontryaginSeries R C`: the series `∑ₖ (-1)ᵏ c₂ₖ Xᵏ` of a series `C = ∑ cᵢ Xⁱ`.

## Main results

* `PowerSeries.pontryaginSeries_mul`, `PowerSeries.coeff_succ_pontryaginSeries_mul`: the exact
  Whitney formula with its odd-times-odd correction, as series and coefficientwise.
* `PowerSeries.twice_even_product_correction_eq_zero`: if the odd coefficients of `P` are
  annihilated by `2`, then twice the difference between an even coefficient of `P * Q` and the
  convolution of the even coefficients of `P` and `Q` vanishes.
* `PowerSeries.pontryaginSeries_mul_of_isLeftRegular_two`: the Pontryagin series is
  multiplicative when `2` is a non-zero-divisor and the odd coefficients of one factor are
  annihilated by `2`.
* `PowerSeries.expand_rescale_pontryaginSeries_rescale_neg_one_mul_self`: Milnor–Stasheff's formula
  for the Pontryagin series of `C(-X) C(X)`.
* `PowerSeries.pontryaginSeries_rescale_neg_one_prod_mul_prod`: on formal roots,
  `C = ∏ⱼ (1 + xⱼ X)` gives the Pontryagin series `∏ⱼ (1 + xⱼ² X)`.

## References

* J. W. Milnor and J. D. Stasheff, *Characteristic classes*, §15: the Whitney product formula
  for Pontryagin classes modulo `2`-torsion, and Corollary 15.5 for complex bundles.
-/

public section

namespace PowerSeries

variable {R : Type*} [CommRing R]

variable (R) in
/-- The *Pontryagin series* of a power series `C = ∑ cᵢ Xⁱ` is `∑ₖ (-1)ᵏ c₂ₖ Xᵏ`. When `C` is
the total Chern class of the complexification `E ⊗ ℂ` of a real vector bundle, its coefficients
are the Pontryagin classes `pₖ(E) = (-1)ᵏ c₂ₖ(E ⊗ ℂ)`. -/
noncomputable def pontryaginSeries : R⟦X⟧ →ₗ[R] R⟦X⟧ where
  toFun C := rescale (-1) (cartier R 2 0 C)
  map_add' C D := by simp
  map_smul' a C := by
    ext k
    simp only [coeff_rescale, coeff_cartier, map_smul, smul_eq_mul, RingHom.id_apply]
    ring

/-- The Pontryagin series is the even part of the series, evaluated at `-X`. -/
theorem pontryaginSeries_apply (C : R⟦X⟧) :
    pontryaginSeries R C = rescale (-1) (cartier R 2 0 C) := (rfl)

/-- The coefficients of the Pontryagin series: `pₖ = (-1)ᵏ c₂ₖ`. -/
@[simp]
theorem coeff_pontryaginSeries (C : R⟦X⟧) (k : ℕ) :
    coeff k (pontryaginSeries R C) = (-1) ^ k * coeff (2 * k) C := by
  simp [pontryaginSeries_apply]

/-- The constant coefficient of the Pontryagin series is the constant coefficient of the
series. -/
@[simp]
theorem constantCoeff_pontryaginSeries (C : R⟦X⟧) :
    constantCoeff (pontryaginSeries R C) = constantCoeff C := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← coeff_zero_eq_constantCoeff_apply,
    coeff_pontryaginSeries, pow_zero, one_mul, mul_zero]

/-- The trivial total Chern class has trivial Pontryagin series. -/
@[simp]
theorem pontryaginSeries_one : pontryaginSeries R (1 : R⟦X⟧) = 1 := by
  simp [pontryaginSeries_apply]

/-- The Pontryagin series is natural for coefficient ring homomorphisms. -/
theorem map_pontryaginSeries {S : Type*} [CommRing S] (f : R →+* S) (C : R⟦X⟧) :
    map f (pontryaginSeries R C) = pontryaginSeries S (map f C) := by
  ext k
  simp

/-- **The exact Whitney formula for Pontryagin series.** The Pontryagin series of a product is
the product of the Pontryagin series, corrected by the product of the odd parts:
`p(P Q) = p(P) p(Q) - X P₁(-X) Q₁(-X)`, where `P(X) = P₀(X²) + X P₁(X²)` and similarly for
`Q`. -/
theorem pontryaginSeries_mul (P Q : R⟦X⟧) :
    pontryaginSeries R (P * Q) = pontryaginSeries R P * pontryaginSeries R Q -
      X * rescale (-1) (cartier R 2 1 P * cartier R 2 1 Q) := by
  simp only [pontryaginSeries_apply, cartier_two_zero_mul, map_add, map_mul (rescale (-1 : R)),
    rescale_neg_one_X]
  ring

/-- **The exact integral Whitney formula, coefficientwise.** The coefficient of `X ^ (k + 1)` in
the Pontryagin series of `P * Q` is the convolution of the coefficients of the Pontryagin series
of `P` and `Q`, plus the correction `(-1) ^ (k + 1) ∑_{a+b=k} P_{2a+1} Q_{2b+1}`. -/
theorem coeff_succ_pontryaginSeries_mul (P Q : R⟦X⟧) (k : ℕ) :
    coeff (k + 1) (pontryaginSeries R (P * Q)) =
      ∑ p ∈ Finset.antidiagonal (k + 1),
        coeff p.1 (pontryaginSeries R P) * coeff p.2 (pontryaginSeries R Q) +
      (-1) ^ (k + 1) * ∑ p ∈ Finset.antidiagonal k,
        coeff (2 * p.1 + 1) P * coeff (2 * p.2 + 1) Q := by
  rw [pontryaginSeries_mul, map_sub, coeff_mul, coeff_succ_X_mul, coeff_rescale, coeff_mul,
    sub_eq_add_neg, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib]
  refine congrArg _ (Finset.sum_congr rfl fun p _ ↦ ?_)
  simp only [coeff_cartier, pow_succ]
  ring

/-- **The `2`-torsion of the Pontryagin Whitney correction.** If the odd coefficients of `P` are
annihilated by `2`, then twice the difference between an even coefficient of `P * Q` and the
convolution of the even coefficients of `P` and `Q` vanishes. The difference itself need not
vanish, so the even parts multiply cleanly only after inverting `2`. -/
theorem twice_even_product_correction_eq_zero (P Q : R⟦X⟧)
    (hodd : ∀ j : ℕ, 2 * coeff (2 * j + 1) P = 0) (k : ℕ) :
    2 * (coeff (2 * k) (P * Q) -
      ∑ i ∈ Finset.range (k + 1), coeff (2 * i) P * coeff (2 * (k - i)) Q) = 0 := by
  have h := congrArg (coeff k) (cartier_two_zero_mul P Q)
  rw [coeff_cartier, add_zero, map_add] at h
  rw [h, coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_cartier, add_zero, Nat.succ_eq_add_one, add_sub_cancel_left]
  rcases k with _ | k
  · simp
  · rw [coeff_succ_X_mul, coeff_mul, Finset.mul_sum]
    refine Finset.sum_eq_zero fun p _ ↦ ?_
    simp only [coeff_cartier, ← mul_assoc, hodd, zero_mul]

/-- **Multiplicativity of the Pontryagin series away from `2`.** If `2` is a non-zero-divisor in
`R` and the odd coefficients of `P` are annihilated by `2`, then the Pontryagin series of
`P * Q` is the product of the Pontryagin series of `P` and `Q`. -/
theorem pontryaginSeries_mul_of_isLeftRegular_two (h2 : IsLeftRegular (2 : R)) (P Q : R⟦X⟧)
    (hodd : ∀ j : ℕ, 2 * coeff (2 * j + 1) P = 0) :
    pontryaginSeries R (P * Q) = pontryaginSeries R P * pontryaginSeries R Q := by
  have hP : cartier R 2 1 P = 0 := by
    ext j
    exact h2 (by simpa using hodd j)
  simp [pontryaginSeries_mul, hP]

/-- The product `C(-X) C(X)` is even: its odd part vanishes. -/
theorem cartier_two_one_rescale_neg_one_mul_self (C : R⟦X⟧) :
    cartier R 2 1 (rescale (-1) C * C) = 0 := by
  ext n
  simp only [coeff_cartier, coeff_mul, coeff_rescale, map_zero]
  -- The involution `(i, j) ↦ (j, i)` of the antidiagonal of the odd number `2n + 1` reverses the
  -- parity of the first index, so it pairs each term with its negative.
  refine Finset.sum_involution (fun p _ ↦ p.swap) (fun p hp ↦ ?_) (fun p hp _ h ↦ ?_)
    (fun p hp ↦ by simp only [Finset.mem_antidiagonal, Prod.fst_swap, Prod.snd_swap] at hp ⊢; omega)
    (fun p _ ↦ p.swap_swap)
  · have hsum := Finset.mem_antidiagonal.1 hp
    have hpar : (-1 : R) ^ p.2 = -(-1) ^ p.1 := by
      rcases Nat.even_or_odd p.1 with h | h
      · rw [h.neg_one_pow, (show Odd p.2 by grind).neg_one_pow]
      · rw [h.neg_one_pow, (show Even p.2 by grind).neg_one_pow, neg_neg]
    simp only [Prod.fst_swap, Prod.snd_swap, hpar]
    ring
  · have hsum := Finset.mem_antidiagonal.1 hp
    exact absurd (Prod.ext_iff.1 h) (by grind)

/-- **Milnor–Stasheff's formula for a complex bundle.** For a series `C`, standing for the total
Chern class of a complex bundle `E`, the series `C(-X) C(X)` is the total Chern class of the
complexification `E ⊕ Ē` of its underlying real bundle, and its Pontryagin series `p`
satisfies `p(-X²) = C(-X) C(X)`, that is, `1 - p₁ + p₂ - ⋯ = (1 - c₁ + c₂ - ⋯)(1 + c₁ + c₂ + ⋯)`.
-/
theorem expand_rescale_pontryaginSeries_rescale_neg_one_mul_self (C : R⟦X⟧) :
    expand 2 two_ne_zero (rescale (-1) (pontryaginSeries R (rescale (-1) C * C))) =
      rescale (-1) C * C := by
  rw [pontryaginSeries_apply, rescale_rescale, neg_one_mul, neg_neg, rescale_one,
    RingHom.id_apply]
  refine expand_cartier_zero_of_coeff_eq_zero 2 two_ne_zero fun n hn ↦ ?_
  obtain ⟨m, rfl⟩ := Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hn)
  simpa using congrArg (coeff m) (cartier_two_one_rescale_neg_one_mul_self C)

/-- **The Pontryagin series on formal roots.** For `C = ∏ⱼ (1 + xⱼ X)`, standing for the total
Chern class of a complex bundle with Chern roots `xⱼ`, the Pontryagin series of `C(-X) C(X)` is
`∏ⱼ (1 + xⱼ² X)`; that is, `p(E_ℝ) = ∏ⱼ (1 + xⱼ²)`. -/
theorem pontryaginSeries_rescale_neg_one_prod_mul_prod (s : Multiset R) :
    pontryaginSeries R (rescale (-1) (s.map fun x ↦ 1 + C x * X).prod *
      (s.map fun x ↦ 1 + C x * X).prod) = (s.map fun x ↦ 1 + C (x ^ 2) * X).prod := by
  set c := (s.map fun x ↦ 1 + C x * X).prod
  have hc : rescale (-1) c * c =
      expand 2 two_ne_zero (rescale (-1) (s.map fun x ↦ 1 + C (x ^ 2) * X).prod) := by
    simp only [c, map_multiset_prod, Multiset.map_map, Function.comp_def, ← Multiset.prod_map_mul,
      map_add, map_one, map_mul, rescale_C, rescale_neg_one_X, expand_C]
    congr 1
    refine Multiset.map_congr rfl fun x _ ↦ ?_
    rw [map_neg, expand_X, map_pow]
    ring
  have h' := congrArg (rescale (-1 : R)) (expand_injective 2 two_ne_zero
    ((expand_rescale_pontryaginSeries_rescale_neg_one_mul_self c).trans hc))
  simpa only [rescale_rescale, neg_one_mul, neg_neg, rescale_one, RingHom.id_apply] using h'

end PowerSeries
