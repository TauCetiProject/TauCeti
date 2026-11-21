/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Derivative
public import Mathlib.RingTheory.PowerSeries.Exp
public import TauCeti.RingTheory.MvPolynomial.Symmetric.PowerSum.NewtonPolynomial
import Mathlib.Algebra.Module.Rat
import TauCeti.RingTheory.MvPolynomial.Symmetric.FundamentalTheorem
import TauCeti.RingTheory.MvPolynomial.Symmetric.PowerSum.Elementary
import TauCeti.RingTheory.PowerSeries.Derivative

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

Conversely, the Chern character determines the Chern classes. In terms of the total Chern series
`c(t) = 1 + c₁ t + ⋯ + cₙ tⁿ` (`TauCeti.chernSeries`), Newton's identities say that its
logarithmic derivative is the generating function of the Newton power sums `sₖ = k! chₖ`:

`t c'(t) = c(t) ∑_{k ≥ 1} (-1)^(k-1) sₖ tᵏ`

(`TauCeti.X_mul_derivative_chernSeries`), for arbitrary Chern classes in any commutative ring.
This identity is additive along `c(K ⊕ W) = c(K) c(W)`, so it determines the total Chern class
`c(I) = c(K) / c(W)` of a virtual bundle `I = K - W` from the power sums `sₖ(I) = sₖ(K) - sₖ(W)`,
in any ring with unique division by positive integers. In particular, if the Chern character of
`I` is concentrated in degrees `0` and `2`, `ch(I) = rank I + u`, then `c(I) = exp(u)` and the
Segre class is `s(I) = c(I)⁻¹ = exp(-u)`. Over the integers the exponential is replaced by a
sequence `γₖ` of divided powers `uᵏ / k!`, characterized by `γ₀ = 1` and `(k + 1) γ_{k+1} = u γₖ`,
which exist without denominators for the quadratic classes `u` of
`TauCeti.Algebra.Algebra.PairingDividedPower`. This is the algebra by which the Chern and Segre
classes of the index bundle of the family of Dirac operators over the Picard torus of a
four-manifold with `b₂⁺ = 1` are read off from its Chern character, which has no components of
degree above two; these Segre classes enter the wall-crossing formula for Seiberg–Witten
invariants.

## Main definitions

* `TauCeti.chernCharacterPolynomial n k`: the polynomial `chₖ = sₖ / k!` in `n` variables over
  `ℚ`, where the variable `j : Fin n` stands for the Chern class `c_{j+1}`.
* `TauCeti.chernSeries c`: the total Chern series `1 + c₁ t + ⋯ + cₙ tⁿ`.

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
* `TauCeti.chernSeries_esymm`: for Chern roots `s`, the total Chern series is `∑ₖ eₖ(s) tᵏ`.
* `TauCeti.X_mul_derivative_chernSeries`: Newton's identities `t c'(t) = c(t) ∑ (-1)^(k-1) sₖ tᵏ`.
* `TauCeti.chernSeries_eq_chernSeries_mul_mk`,
  `TauCeti.chernSeries_eq_chernSeries_mul_mk_neg_one_pow_mul`: a virtual bundle `I = K - W` with
  `s₁(I) = u` and `sₖ(I) = 0` for `k ≥ 2` has `c(K) = c(W) ∑ γₖ tᵏ` and `c(W) = c(K) ∑ (-1)ᵏ γₖ tᵏ`
  for the divided powers `γₖ` of `u`.
* `TauCeti.chernSeries_eq_chernSeries_mul_rescale_exp`: over `ℚ`, `ch(I) = rank I + x` gives
  `c(K) = c(W) exp(x t)`.

## References

* J. W. Milnor, J. D. Stasheff, *Characteristic Classes*, Annals of Mathematics Studies 76,
  Princeton (1974), §16 and Problem 16-A.
* F. Hirzebruch, *Topological Methods in Algebraic Geometry*, Springer (1966), §10.1.
* C. Okonek and A. Teleman, *Seiberg–Witten invariants for manifolds with `b₊ = 1` and the
  universal wall crossing formula*, Internat. J. Math. 7 (1996), 811–832.
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

/-! ### The total Chern series and Newton's identities -/

section ChernSeries

section CommSemiring

variable {A : Type*} [CommSemiring A] {n : ℕ}

/-- The **total Chern series** `1 + c₁ t + ⋯ + cₙ tⁿ` of Chern classes `c₁, …, cₙ`, where
`c j` stands for `c_{j+1}`. For a complex vector bundle of rank `n` it is the generating function
of its Chern classes. -/
noncomputable def chernSeries (c : Fin n → A) : PowerSeries A :=
  PowerSeries.mk fun k => if k = 0 then 1 else if h : k - 1 < n then c ⟨k - 1, h⟩ else 0

/-- The coefficients of the total Chern series: `1`, then `c₁, …, cₙ`, then `0`. -/
theorem coeff_chernSeries (c : Fin n → A) (k : ℕ) :
    PowerSeries.coeff k (chernSeries c) =
      if k = 0 then 1 else if h : k - 1 < n then c ⟨k - 1, h⟩ else 0 :=
  PowerSeries.coeff_mk _ _

/-- The total Chern series has constant coefficient `c₀ = 1`. -/
@[simp]
theorem constantCoeff_chernSeries (c : Fin n → A) :
    PowerSeries.constantCoeff (chernSeries c) = 1 := by
  simp [← PowerSeries.coeff_zero_eq_constantCoeff_apply, coeff_chernSeries]

/-- The coefficient of `t^(j+1)` in the total Chern series is the Chern class `c_{j+1}`. -/
@[simp]
theorem coeff_succ_chernSeries (c : Fin n → A) (j : Fin n) :
    PowerSeries.coeff (j + 1) (chernSeries c) = c j := by
  simp [coeff_chernSeries]

/-- The total Chern series of a bundle of rank `n` has no terms of degree above `n`. -/
theorem coeff_chernSeries_of_lt (c : Fin n → A) {k : ℕ} (hk : n < k) :
    PowerSeries.coeff k (chernSeries c) = 0 := by
  rw [coeff_chernSeries]
  split_ifs <;> first | rfl | omega

/-- The total Chern series is natural in the coefficient ring. -/
@[simp]
theorem map_chernSeries {B : Type*} [CommSemiring B] (f : A →+* B) (c : Fin n → A) :
    PowerSeries.map f (chernSeries c) = chernSeries (f ∘ c) := by
  ext k
  simp only [PowerSeries.coeff_map, coeff_chernSeries, Function.comp_apply]
  split_ifs <;> simp

open PowerSeries in
/-- Changing coefficients along a ring hom commutes with the Euler operator `t d/dt` applied to
the total Chern series. -/
private theorem map_X_mul_derivative_chernSeries {B : Type*} [CommSemiring B] (f : A →+* B)
    (c : Fin n → A) :
    PowerSeries.map f (PowerSeries.X * d⁄dX (chernSeries c)) =
      PowerSeries.X * d⁄dX (chernSeries (f ∘ c)) := by
  rw [map_mul, PowerSeries.map_X, ← PowerSeries.derivative_map, map_chernSeries]

/-- **The splitting principle for the total Chern series**: if the Chern classes are the elementary
symmetric functions of a multiset `s` of `n` Chern roots, the total Chern series is the generating
function `∑ₖ eₖ(s) tᵏ = ∏_{x ∈ s} (1 + x t)` of these functions. -/
theorem chernSeries_esymm (s : Multiset A) (hs : s.card = n) :
    chernSeries (fun j : Fin n => s.esymm (j + 1)) = PowerSeries.mk s.esymm := by
  ext (_ | k)
  · simp
  · rw [PowerSeries.coeff_mk, coeff_chernSeries, Nat.add_sub_cancel]
    simp only [Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte]
    split_ifs with h
    · rfl
    · exact (Multiset.esymm_of_card_lt (by omega)).symm

end CommSemiring

section CommRing

variable {A : Type*} [CommRing A] {n : ℕ}

open PowerSeries in
/-- **Newton's identities for Chern classes.** The total Chern series `c(t)` of Chern classes
`c₁, …, cₙ` has logarithmic derivative

`t c'(t) = c(t) ∑_{k ≥ 1} (-1)^(k-1) sₖ(c₁, …, cₙ) tᵏ`,

where `sₖ = k! chₖ` is the Newton polynomial `TauCeti.newtonMvPolynomial`. For Chern roots `xᵢ`
this is `t (log ∏ᵢ (1 + xᵢ t))' = ∑ᵢ xᵢ t / (1 + xᵢ t)`. The coefficients of `R` are arbitrary;
the Newton polynomial over `R` is the image of the integral one. -/
theorem X_mul_derivative_chernSeries (R : Type*) [CommRing R] [Algebra R A] (c : Fin n → A) :
    PowerSeries.X * d⁄dX (chernSeries c) = chernSeries c *
      mk fun k => if k = 0 then 0 else (-1) ^ (k + 1) * aeval c (newtonMvPolynomial R n k) := by
  -- The universal case: the Chern classes are the variables of `MvPolynomial (Fin n) R`.
  -- Substituting the elementary symmetric polynomials for the variables is injective and turns
  -- the identity into Newton's identities for the elementary symmetric polynomials.
  have huniv :
      PowerSeries.X * d⁄dX (chernSeries (MvPolynomial.X : Fin n → MvPolynomial (Fin n) R)) =
        chernSeries MvPolynomial.X * mk fun k =>
        if k = 0 then 0 else (-1) ^ (k + 1) * newtonMvPolynomial R n k := by
    set ψ := aeval (R := R) fun j : Fin n =>
      (univ.val.map (MvPolynomial.X (R := R) (σ := Fin n))).esymm (j + 1)
    have hψ : Function.Injective ψ :=
      aeval_multiset_esymm_X_injective R (Fintype.card_fin n).ge
    have hesymm : chernSeries (ψ ∘ MvPolynomial.X) = mk fun k => esymm (Fin n) R k := by
      rw [esymm_eq_multiset_esymm, ← chernSeries_esymm (n := n) _ (by simp)]
      exact congrArg chernSeries (funext fun j => aeval_X _ j)
    refine PowerSeries.map_injective ψ.toRingHom hψ ?_
    rw [map_X_mul_derivative_chernSeries, map_mul, map_chernSeries]
    simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at hesymm ⊢
    rw [hesymm, X_mul_derivative_mk_esymm]
    congr 1
    ext k
    simp only [PowerSeries.coeff_map, coeff_mk]
    split_ifs
    · simp
    · simp only [ψ, ← esymm_eq_multiset_esymm]
      simp [aeval_esymm_newtonMvPolynomial]
  -- Specialize the universal identity along `aeval c`.
  have h := congrArg (PowerSeries.map (aeval (R := R) c).toRingHom) huniv
  rw [map_X_mul_derivative_chernSeries, map_mul, map_chernSeries] at h
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h
  have hc : (aeval (R := R) c) ∘ MvPolynomial.X = c := funext fun j => aeval_X c j
  rw [hc] at h
  rw [h]
  congr 1
  ext k
  simp only [PowerSeries.coeff_map, coeff_mk]
  split_ifs <;> simp

/-- **The total Chern class of a virtual bundle whose Chern character is concentrated in degrees
`0` and `2`.** Let `cK` and `cW` be the Chern classes of complex vector bundles `K` and `W` of ranks
`n` and `m`, in a commutative ring with unique division by positive integers, such as the integral
cohomology of a torus in even degrees. Suppose the virtual bundle `I = K - W` has Newton power sums
`s₁(I) = s₁(K) - s₁(W) = u` and `sₖ(I) = sₖ(K) - sₖ(W) = 0` for `k ≥ 2`; rationally, its Chern
character is `ch(I) = rank I + u`. If `γ` satisfies `γ₀ = 1` and `(k + 1) γ_{k+1} = u γₖ`, the
recursion of the divided powers `γₖ = uᵏ / k!`, then the total Chern class `c(I) = c(K) / c(W)` is
the divided-power exponential `∑ₖ γₖ tᵏ` of `u`:

`c(K) = c(W) ∑ₖ γₖ tᵏ`. -/
theorem chernSeries_eq_chernSeries_mul_mk [HasUniqueDiv A] (R : Type*) [CommRing R] [Algebra R A]
    {m : ℕ} (cK : Fin n → A) (cW : Fin m → A) {u : A} {γ : ℕ → A} (hγ₀ : γ 0 = 1)
    (hγ : ∀ k, (k + 1) • γ (k + 1) = u * γ k)
    (h₁ : aeval cK (newtonMvPolynomial R n 1) = aeval cW (newtonMvPolynomial R m 1) + u)
    (h : ∀ k, 2 ≤ k →
      aeval cK (newtonMvPolynomial R n k) = aeval cW (newtonMvPolynomial R m k)) :
    chernSeries cK = chernSeries cW * PowerSeries.mk γ := by
  have hG := PowerSeries.X_mul_derivative_mk_eq_mul_C_mul_X_iff.2 hγ
  have hW := X_mul_derivative_chernSeries R cW
  -- The logarithmic derivative of `c(K)` is that of `c(W)` plus `u t`, that of `∑ₖ γₖ tᵏ`.
  have hP : (PowerSeries.mk fun k =>
        if k = 0 then 0 else (-1) ^ (k + 1) * aeval cK (newtonMvPolynomial R n k)) =
      (PowerSeries.mk fun k =>
        if k = 0 then 0 else (-1) ^ (k + 1) * aeval cW (newtonMvPolynomial R m k)) +
        PowerSeries.C u * PowerSeries.X := by
    ext (_ | _ | k)
    · simp
    · simp [h₁]
    · simp [h (k + 2) (by omega)]
  refine PowerSeries.eq_of_X_mul_derivative_eq_mul (by simp) (X_mul_derivative_chernSeries R cK)
    ?_ (by simp [hγ₀])
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul, hP]
  linear_combination chernSeries cW * hG + PowerSeries.mk γ * hW

/-- **The total Segre class of a virtual bundle whose Chern character is concentrated in degrees
`0` and `2`.** Under the hypotheses of `TauCeti.chernSeries_eq_chernSeries_mul_mk`, the Segre class
`s(I) = c(I)⁻¹ = c(W) / c(K)` of `I = K - W` is `∑ₖ (-1)ᵏ γₖ tᵏ`, the divided-power exponential of
`-u`:

`c(W) = c(K) ∑ₖ (-1)ᵏ γₖ tᵏ`. -/
theorem chernSeries_eq_chernSeries_mul_mk_neg_one_pow_mul [HasUniqueDiv A] (R : Type*) [CommRing R]
    [Algebra R A] {m : ℕ} (cK : Fin n → A) (cW : Fin m → A) {u : A} {γ : ℕ → A} (hγ₀ : γ 0 = 1)
    (hγ : ∀ k, (k + 1) • γ (k + 1) = u * γ k)
    (h₁ : aeval cK (newtonMvPolynomial R n 1) = aeval cW (newtonMvPolynomial R m 1) + u)
    (h : ∀ k, 2 ≤ k →
      aeval cK (newtonMvPolynomial R n k) = aeval cW (newtonMvPolynomial R m k)) :
    chernSeries cW = chernSeries cK * PowerSeries.mk fun k => (-1) ^ k * γ k :=
  chernSeries_eq_chernSeries_mul_mk R cW cK (u := -u) (by simp [hγ₀])
    (fun k => by rw [← mul_smul_comm, hγ, pow_succ]; ring) (by rw [h₁]; ring)
    fun k hk => (h k hk).symm

open PowerSeries in
/-- **The total Chern class of a virtual bundle whose Chern character is concentrated in degrees
`0` and `2`, over `ℚ`.** Let `cK` and `cW` be the Chern classes of complex vector bundles `K` and
`W` of ranks `n` and `m`, in a commutative `ℚ`-algebra. If the virtual bundle `I = K - W` has
Chern character components `ch₁(I) = ch₁(K) - ch₁(W) = x` and `chₖ(I) = 0` for `k ≥ 2`, that is
`ch(I) = rank I + x`, then its total Chern class is `c(I) = exp(x)`:

`c(K) = c(W) exp(x t)`.

Exchanging `K` and `W` gives the Segre class `s(I) = c(W) / c(K) = exp(-x)`. -/
theorem chernSeries_eq_chernSeries_mul_rescale_exp [Algebra ℚ A] {m : ℕ} (cK : Fin n → A)
    (cW : Fin m → A) (x : A)
    (h₁ : aeval cK (chernCharacterPolynomial n 1) = aeval cW (chernCharacterPolynomial m 1) + x)
    (h : ∀ k, 2 ≤ k →
      aeval cK (chernCharacterPolynomial n k) = aeval cW (chernCharacterPolynomial m k)) :
    chernSeries cK = chernSeries cW * rescale x (exp A) := by
  have := HasUniqueDiv.of_module_rat (M := A)
  have hch (l : ℕ) {N : ℕ} (c : Fin N → A) : aeval c (chernCharacterPolynomial N l) =
      algebraMap ℚ A (l ! : ℚ)⁻¹ * aeval c (newtonMvPolynomial ℚ N l) := by
    rw [chernCharacterPolynomial_eq_C_mul_newtonMvPolynomial, map_mul, aeval_C]
  -- `exp' = exp` makes the coefficients of `exp(x t)` satisfy the divided-power recursion.
  have hd : PowerSeries.X * d⁄dX (rescale x (exp A)) =
      rescale x (exp A) * (PowerSeries.C x * PowerSeries.X) := by
    rw [PowerSeries.derivative_rescale, derivative_exp]
    ring
  have hexp : rescale x (exp A) = PowerSeries.mk fun k => PowerSeries.coeff k (rescale x (exp A)) :=
    PowerSeries.ext fun k => by rw [coeff_mk]
  rw [hexp] at hd ⊢
  refine chernSeries_eq_chernSeries_mul_mk ℚ cK cW (by simp)
    (PowerSeries.X_mul_derivative_mk_eq_mul_C_mul_X_iff.1 hd) ?_ fun k hk => ?_
  · simpa [hch] using h₁
  · have hk' := h k hk
    rw [hch, hch] at hk'
    exact (IsUnit.map (algebraMap ℚ A) (isUnit_iff_ne_zero.2 (by positivity))).mul_left_cancel hk'

end CommRing

end ChernSeries

end TauCeti
