/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Exp
public import TauCeti.RingTheory.MvPolynomial.Symmetric.PowerSum.NewtonPolynomial

/-!
# The Chern character polynomials

The Chern character of a complex vector bundle `E` of rank `n` with Chern roots `x₁, …, xₙ` is
`ch(E) = ∑ᵢ exp(xᵢ)`. Its degree-`2k` component `(x₁ᵏ + ⋯ + xₙᵏ) / k!` is a symmetric function of
the roots, hence a polynomial `chₖ(c₁, …, cₙ)` in the Chern classes, which are the elementary
symmetric functions of the roots. Following Milnor and Stasheff (§16), `chₖ = sₖ / k!`, where
`sₖ` is the integral Newton polynomial `TauCeti.newtonMvPolynomial`. This file defines these
universal rational polynomials and proves, for formal roots in any commutative `ℚ`-algebra, the
identities the Chern character inherits from the exponential: `ch₀` is the rank, the generating
function is the sum of the exponentials of the roots, and the root forms of
`ch(E ⊕ F) = ch(E) + ch(F)`, `ch(E ⊗ F) = ch(E) ch(F)`, `ch(E ⊗ L) = ch(E) exp(c₁(L))` and
`chₖ(E*) = (-1)ᵏ chₖ(E)`. By the splitting principle these root identities give the corresponding
identities for the Chern character of vector bundles.

## Main definitions

* `TauCeti.chernCharacterPolynomial n k`: the polynomial `chₖ = sₖ / k!` in `n` variables over
  `ℚ`, where the variable `j : Fin n` stands for the Chern class `c_{j+1}`.

## Main results

* `TauCeti.chernCharacterPolynomial_eq_C_mul_newtonMvPolynomial`,
  `TauCeti.C_factorial_mul_chernCharacterPolynomial`: `chₖ` is the rational Newton polynomial
  divided by `k!`, and `k! chₖ` is the integral Newton polynomial.
* `Multiset.aeval_esymm_chernCharacterPolynomial`: for a multiset `s` of `n` roots,
  `chₖ(e₁(s), …, eₙ(s)) = (∑_{x ∈ s} xᵏ) / k!`.
* `Multiset.mk_aeval_esymm_chernCharacterPolynomial`: the generating function
  `∑ₖ chₖ(e₁(s), …, eₙ(s)) tᵏ = ∑_{x ∈ s} exp(x t)`.
* `Multiset.aeval_esymm_add_chernCharacterPolynomial`: additivity on a union of roots.
* `Multiset.aeval_esymm_product_chernCharacterPolynomial`: multiplicativity on the
  pairwise sums of two families of roots.
* `Multiset.aeval_esymm_map_add_chernCharacterPolynomial`: twisting by the root of a line.
* `TauCeti.aeval_neg_one_pow_mul_chernCharacterPolynomial`: replacing `cⱼ` by `(-1)ʲ cⱼ`
  multiplies `chₖ` by `(-1)ᵏ`.
* `TauCeti.chernCharacterPolynomial_zero_right`, `TauCeti.chernCharacterPolynomial_one_right`,
  `TauCeti.chernCharacterPolynomial_two_right`, `TauCeti.chernCharacterPolynomial_three_right`:
  `ch₀ = n`, `ch₁ = c₁`, `ch₂ = (c₁² - 2c₂) / 2` and `ch₃ = (c₁³ - 3c₁c₂ + 3c₃) / 6`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §16 and Problem 16-A.
* F. Hirzebruch, *Topological Methods in Algebraic Geometry*, Springer (1966), §10.1.
-/

public section

open Finset MvPolynomial
open PowerSeries (exp rescale)
open scoped Nat

namespace TauCeti

variable (n k : ℕ)

/-- The **Chern character polynomial** `chₖ` in `n` variables: the integral Newton polynomial
`sₖ`, viewed over `ℚ` and divided by `k!`. Evaluated at the Chern classes `c₁, …, cₙ` of a
complex vector bundle of rank `n`, it gives the degree-`2k` component of the Chern character.
The variable `j : Fin n` stands for `c_{j+1}`. -/
noncomputable def chernCharacterPolynomial : MvPolynomial (Fin n) ℚ :=
  C (k ! : ℚ)⁻¹ * map (Int.castRingHom ℚ) (newtonMvPolynomial ℤ n k)

/-- The definition of `TauCeti.chernCharacterPolynomial`: `chₖ = sₖ / k!` with `sₖ` the integral
Newton polynomial. -/
theorem chernCharacterPolynomial_def :
    chernCharacterPolynomial n k =
      C (k ! : ℚ)⁻¹ * map (Int.castRingHom ℚ) (newtonMvPolynomial ℤ n k) :=
  (rfl)

/-- The Chern character polynomial `chₖ` is the rational Newton polynomial divided by `k!`. -/
theorem chernCharacterPolynomial_eq_C_mul_newtonMvPolynomial :
    chernCharacterPolynomial n k = C (k ! : ℚ)⁻¹ * newtonMvPolynomial ℚ n k := by
  rw [chernCharacterPolynomial_def, map_newtonMvPolynomial]

/-- **Integrality of the Chern character**: `k! chₖ` is the integral Newton polynomial `sₖ`. -/
theorem C_factorial_mul_chernCharacterPolynomial :
    C (k ! : ℚ) * chernCharacterPolynomial n k =
      map (Int.castRingHom ℚ) (newtonMvPolynomial ℤ n k) := by
  rw [chernCharacterPolynomial_def, ← mul_assoc, ← C_mul,
    mul_inv_cancel₀ (Nat.cast_ne_zero.2 (Nat.factorial_ne_zero k)), C_1, one_mul]

/-- **The degree-zero Chern character is the rank**: `ch₀ = n`. -/
@[simp]
theorem chernCharacterPolynomial_zero_right : chernCharacterPolynomial n 0 = n := by
  simp [chernCharacterPolynomial_eq_C_mul_newtonMvPolynomial]

/-- **The linear Chern character**: `ch₁ = c₁`. -/
@[simp]
theorem chernCharacterPolynomial_one_right : chernCharacterPolynomial (n + 1) 1 = X 0 := by
  simp [chernCharacterPolynomial_eq_C_mul_newtonMvPolynomial, newtonMvPolynomial_one_right]

/-- **The quadratic Chern character**: in at least two variables, `ch₂ = (c₁² - 2c₂) / 2`. -/
theorem chernCharacterPolynomial_two_right :
    chernCharacterPolynomial (n + 2) 2 = C (1 / 2 : ℚ) * (X 0 ^ 2 - 2 * X 1) := by
  rw [chernCharacterPolynomial_eq_C_mul_newtonMvPolynomial, newtonMvPolynomial_two_right]
  norm_num [Nat.factorial]

/-- **The cubic Chern character**: in at least three variables,
`ch₃ = (c₁³ - 3c₁c₂ + 3c₃) / 6`. -/
theorem chernCharacterPolynomial_three_right :
    chernCharacterPolynomial (n + 3) 3 =
      C (1 / 6 : ℚ) * (X 0 ^ 3 - 3 * X 0 * X 1 + 3 * X 2) := by
  rw [chernCharacterPolynomial_eq_C_mul_newtonMvPolynomial, newtonMvPolynomial_three_right]
  norm_num [Nat.factorial]

variable {n k}

section CommSemiring

variable {S : Type*} [CommSemiring S] [Algebra ℚ S]

/-- **Root description of the Chern character polynomial**: for a multiset `s` of `n` roots in a
commutative `ℚ`-algebra, `chₖ(e₁(s), …, eₙ(s)) = (∑_{x ∈ s} xᵏ) / k!`. -/
theorem _root_.Multiset.aeval_esymm_chernCharacterPolynomial (s : Multiset S) (hs : s.card = n) :
    aeval (fun j : Fin n => s.esymm (j + 1)) (chernCharacterPolynomial n k) =
      algebraMap ℚ S (k ! : ℚ)⁻¹ * (s.map (· ^ k)).sum := by
  rw [chernCharacterPolynomial_eq_C_mul_newtonMvPolynomial, map_mul, aeval_C,
    Multiset.aeval_esymm_newtonMvPolynomial s hs]

/-- **Additivity of the Chern character**: on the union of a family `s` of `n` roots and a family
`t` of `m` roots, the Chern character polynomial is the sum of its values on `s` and on `t`. This
is the root form of `ch(E ⊕ F) = ch(E) + ch(F)`. -/
theorem _root_.Multiset.aeval_esymm_add_chernCharacterPolynomial {m : ℕ} (s t : Multiset S)
    (hs : s.card = n) (ht : t.card = m) :
    aeval (fun j : Fin (n + m) => (s + t).esymm (j + 1)) (chernCharacterPolynomial (n + m) k) =
      aeval (fun j : Fin n => s.esymm (j + 1)) (chernCharacterPolynomial n k) +
        aeval (fun j : Fin m => t.esymm (j + 1)) (chernCharacterPolynomial m k) := by
  rw [Multiset.aeval_esymm_chernCharacterPolynomial _ (by simp [hs, ht]),
    Multiset.aeval_esymm_chernCharacterPolynomial s hs,
    Multiset.aeval_esymm_chernCharacterPolynomial t ht, Multiset.map_add, Multiset.sum_add,
    mul_add]

/-- **Stability of the Chern character**: in positive degree, setting `cₙ₊₁ = 0` in the Chern
character polynomial for `n + 1` variables gives the one for `n` variables. -/
@[simp]
theorem aeval_snoc_zero_chernCharacterPolynomial (hk : k ≠ 0) (c : Fin n → S) :
    aeval (Fin.snoc c 0) (chernCharacterPolynomial (n + 1) k) =
      aeval c (chernCharacterPolynomial n k) := by
  simp [chernCharacterPolynomial_eq_C_mul_newtonMvPolynomial, hk]

end CommSemiring

section CommRing

variable {S : Type*} [CommRing S] [Algebra ℚ S]

/-- **The Chern character is the sum of the exponentials of the roots**: for a multiset `s` of
`n` roots in a commutative `ℚ`-algebra, `∑ₖ chₖ(e₁(s), …, eₙ(s)) tᵏ = ∑_{x ∈ s} exp(x t)`. -/
theorem _root_.Multiset.mk_aeval_esymm_chernCharacterPolynomial (s : Multiset S) (hs : s.card = n) :
    PowerSeries.mk (fun k =>
        aeval (fun j : Fin n => s.esymm (j + 1)) (chernCharacterPolynomial n k)) =
      (s.map fun x => rescale x (exp S)).sum := by
  ext k
  rw [PowerSeries.coeff_mk, Multiset.aeval_esymm_chernCharacterPolynomial s hs, map_multiset_sum,
    Multiset.map_map, ← Multiset.sum_map_mul_left]
  refine congrArg Multiset.sum (Multiset.map_congr rfl fun x _ => ?_)
  simp [PowerSeries.coeff_rescale, PowerSeries.coeff_exp, mul_comm]

/-- **Multiplicativity of the Chern character**: for a family `s` of `n` roots and a family `t` of
`m` roots, the Chern character polynomial on the `n * m` pairwise sums `x + y`, `x ∈ s`, `y ∈ t`,
is the convolution of its values on `s` and on `t`. The Chern roots of a tensor product `E ⊗ F`
are these pairwise sums, so this is the root form of `ch(E ⊗ F) = ch(E) ch(F)`. -/
theorem _root_.Multiset.aeval_esymm_product_chernCharacterPolynomial {m : ℕ} (s t : Multiset S)
    (hs : s.card = n) (ht : t.card = m) :
    aeval (fun j : Fin (n * m) => ((s ×ˢ t).map fun p => p.1 + p.2).esymm (j + 1))
        (chernCharacterPolynomial (n * m) k) =
      ∑ p ∈ antidiagonal k,
        aeval (fun j : Fin n => s.esymm (j + 1)) (chernCharacterPolynomial n p.1) *
          aeval (fun j : Fin m => t.esymm (j + 1)) (chernCharacterPolynomial m p.2) := by
  have h := congrArg (PowerSeries.coeff k) (Multiset.mk_aeval_esymm_chernCharacterPolynomial
    (n := n * m) ((s ×ˢ t).map fun p => p.1 + p.2) (by simp [hs, ht]))
  rw [PowerSeries.coeff_mk] at h
  rw [h]
  -- `∑_{(x, y)} exp((x + y) t)` factors as `(∑_x exp(x t)) (∑_y exp(y t))`.
  simp only [SProd.sprod, Multiset.product, Multiset.map_bind, Multiset.sum_bind,
    Multiset.map_map, Function.comp_def, ← PowerSeries.exp_mul_exp_eq_exp_add,
    Multiset.sum_map_mul_left, Multiset.sum_map_mul_right]
  rw [← Multiset.mk_aeval_esymm_chernCharacterPolynomial s hs,
    ← Multiset.mk_aeval_esymm_chernCharacterPolynomial t ht, PowerSeries.coeff_mul]
  simp only [PowerSeries.coeff_mk]

/-- **The Chern character of a line twist**: for a family `s` of `n` roots and the root `y` of a
line bundle, the Chern character polynomial on the shifted roots `x + y` is the convolution of
its values on `s` with the coefficients `yʲ / j!` of `exp y`. This is the root form of
`ch(E ⊗ L) = ch(E) exp(c₁(L))`. -/
theorem _root_.Multiset.aeval_esymm_map_add_chernCharacterPolynomial (s : Multiset S)
    (hs : s.card = n) (y : S) :
    aeval (fun j : Fin n => (s.map (· + y)).esymm (j + 1)) (chernCharacterPolynomial n k) =
      ∑ p ∈ antidiagonal k,
        aeval (fun j : Fin n => s.esymm (j + 1)) (chernCharacterPolynomial n p.1) *
          (algebraMap ℚ S (p.2 ! : ℚ)⁻¹ * y ^ p.2) := by
  -- This is multiplicativity with the single root `y` as the second family.
  have h := s.aeval_esymm_product_chernCharacterPolynomial (k := k) (m := 1) {y} hs rfl
  rw [mul_one] at h
  have hs' : ((s ×ˢ {y}).map fun p => p.1 + p.2) = s.map (· + y) := by
    simp [SProd.sprod, Multiset.product]
  rw [← hs', h]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Multiset.aeval_esymm_chernCharacterPolynomial (n := 1) {y} rfl]
  simp

/-- **The Chern character of the dual**: replacing each Chern class `cⱼ` by `(-1)ʲ cⱼ`, as
passing to the dual bundle does, multiplies `chₖ` by `(-1)ᵏ`. -/
theorem aeval_neg_one_pow_mul_chernCharacterPolynomial (c : Fin n → S) :
    aeval (fun j : Fin n => (-1) ^ (j.val + 1) * c j) (chernCharacterPolynomial n k) =
      (-1) ^ k * aeval c (chernCharacterPolynomial n k) := by
  rw [chernCharacterPolynomial_eq_C_mul_newtonMvPolynomial, map_mul, map_mul, aeval_C, aeval_C,
    aeval_neg_one_pow_mul_newtonMvPolynomial, mul_left_comm]

end CommRing

end TauCeti
