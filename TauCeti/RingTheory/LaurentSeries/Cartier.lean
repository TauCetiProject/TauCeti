/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Ramified
public import TauCeti.RingTheory.PowerSeries.Cartier

/-!
# Cartier operators on Laurent series

For a positive modulus `d` and a residue `r < d`, the exponent-congruence component
`LaurentSeries.contract d f r` of a Laurent series `f = ∑ aₙ Xⁿ` is `∑ a_{d n + r} Xⁿ`: this is
the Cartier operator `Λ_r` of modulus `d` on Laurent series. This file relates it to the Cartier
operators `PowerSeries.cartier` of power series, and proves the Frobenius identities that make
these operators useful over a finite field `K` with `q` elements:

* `Λ_r (g ^ q * h) = g * Λ_r h`, because `g ^ q` is the expansion `X ↦ X ^ q` of `g`;
* `f = ∑_{r < q} X ^ r * (Λ_r f) ^ q`.

Through `LaurentSeries.contract_coe`, `PowerSeries.exists_cartier_coe_polynomial_eq` shows that
these operators send a polynomial of degree at most `N` to a polynomial of degree at most `N / d`.
These are the operations used in Christol's theorem to pass from an algebraic power series over
`K` to its Ore relation and to the finite set of series spanned by its Cartier iterates.

## Main results

* `LaurentSeries.contract_coe`: on power series, `contract` is `PowerSeries.cartier`.
* `LaurentSeries.contract_expand_mul`: `contract d (expand d g * h) r = g * contract d h r`.
* `FiniteField.LaurentSeries.expand_card`: over a finite field with `q` elements, the expansion
  `X ↦ X ^ q` of a Laurent series is its `q`-th power.
* `LaurentSeries.contract_pow_card_mul` and `LaurentSeries.sum_single_mul_contract_pow_card`: the
  two Frobenius identities above.

## References

* G. Christol, T. Kamae, M. Mendès France, G. Rauzy, *Suites algébriques, automates et
  substitutions*, Bull. Soc. Math. France 108 (1980), Sections 6 and 7.
* E. Rowland, M. Stipulanti, R. Yassawi, *An elementary proof of Bridy's theorem*, Section 3,
  Proposition 4.
-/

public section

open HahnSeries
open scoped LaurentSeries PowerSeries

namespace LaurentSeries

section Semiring

variable {R : Type*} [Semiring R]

/-- On power series, the exponent-congruence components of Laurent series are the Cartier
operators of power series. -/
theorem contract_coe (d : ℕ+) (F : R⟦X⟧) (r : Fin d) :
    contract d (F : R⸨X⸩) r = (PowerSeries.cartier R d r F : R⸨X⸩) := by
  ext k
  have hd : (0 : ℤ) < d := by exact_mod_cast d.pos
  have hr : (0 : ℤ) ≤ r := Int.natCast_nonneg _
  rw [coeff_contract, PowerSeries.coeff_coe, PowerSeries.coeff_coe, PowerSeries.coeff_cartier]
  by_cases hk : k < 0
  · have : (r : ℤ) < d := by exact_mod_cast r.isLt
    rw [ite_eq_left hk, ite_eq_left (by nlinarith)]
  · rw [ite_eq_right hk, ite_eq_right (by nlinarith)]
    lift k to ℕ using not_lt.mp hk
    norm_cast

end Semiring

section CommSemiring

variable {A : Type*} [CommSemiring A]

/-- Multiplication by an expanded series passes through the exponent-congruence components. -/
theorem contract_expand_mul (d : ℕ+) (g h : A⸨X⸩) (r : Fin d) :
    contract d (expand A d g * h) r = g * contract d h r := by
  refine contract_eq_of_sum_eq d (fun s ↦ g * contract d h s) _ ?_ r
  conv_rhs => rw [← sum_single_mul_expand_contract d h]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ ↦ ?_
  rw [map_mul, mul_left_comm]

end CommSemiring

end LaurentSeries

namespace FiniteField.LaurentSeries

open _root_.LaurentSeries

variable {K : Type*} [Field K] [Fintype K]

/-- Over a finite field with `q` elements, the expansion `X ↦ X ^ q` of a Laurent series is its
`q`-th power. The modulus is given as a positive natural number `d` with `d = q`. -/
theorem expand_card (d : ℕ+) (hd : (d : ℕ) = Fintype.card K) (f : K⸨X⸩) :
    expand K d f = f ^ Fintype.card K := by
  have hexp : PowerSeries.expand (d : ℕ) d.ne_zero f.powerSeriesPart =
      f.powerSeriesPart ^ (d : ℕ) := by
    simp only [hd]
    exact FiniteField.PowerSeries.expand_card _
  rw [← single_order_mul_powerSeriesPart f, map_mul, expand_single, expand_coe, hexp,
    PowerSeries.coe_pow, mul_pow, single_pow, one_pow, nsmul_eq_mul, hd]

end FiniteField.LaurentSeries

namespace LaurentSeries

section FiniteField

variable {K : Type*} [Field K] [Fintype K]

/-- Over a finite field with `q` elements, multiplication by a `q`-th power passes through the
Cartier operators of modulus `q`. The modulus is given as a positive natural number `d` with
`d = q`. -/
theorem contract_pow_card_mul (d : ℕ+) (hd : (d : ℕ) = Fintype.card K) (g h : K⸨X⸩) (r : Fin d) :
    contract d (g ^ Fintype.card K * h) r = g * contract d h r := by
  rw [← FiniteField.LaurentSeries.expand_card d hd, contract_expand_mul]

/-- Over a finite field with `q` elements, a Laurent series `f` is `∑_{r < q} X ^ r * (Λ_r f) ^ q`,
where `Λ_r` is the Cartier operator of modulus `q`. The modulus is given as a positive natural
number `d` with `d = q`. -/
theorem sum_single_mul_contract_pow_card (d : ℕ+) (hd : (d : ℕ) = Fintype.card K) (f : K⸨X⸩) :
    ∑ r : Fin d, single (r : ℤ) 1 * contract d f r ^ Fintype.card K = f := by
  conv_rhs => rw [← sum_single_mul_expand_contract d f]
  simp only [FiniteField.LaurentSeries.expand_card d hd]

end FiniteField

/-! The examples check monomials with negative exponents, the residue restriction and the
Frobenius identity at a power. -/

example : contract 2 (single (-3) (1 : ℤ)) 1 = single (-2) 1 ∧
    contract 2 (single (-3) (1 : ℤ)) 0 = 0 := by
  constructor <;> rw [contract_single] <;> norm_num

example (g : (ZMod 3)⸨X⸩) : contract 3 (g ^ 3) 0 = g := by
  have h := contract_pow_card_mul 3 (ZMod.card 3).symm g 1 0
  rwa [ZMod.card, mul_one, contract_one, ite_eq_left rfl, mul_one] at h

end LaurentSeries
