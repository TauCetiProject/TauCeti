/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.GCDMonoid.Finset
public import Mathlib.Algebra.GCDMonoid.Nat
public import Mathlib.Data.Nat.Choose.Lucas
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.MvPolynomial.Symmetric.Defs
-- Proof-only: coefficients of `(X + Y)ⁿ` and of differences.
import Mathlib.Algebra.MvPolynomial.Coeff
import Mathlib.Algebra.MvPolynomial.CommRing
-- Proof-only: substitution commutes with change of coefficients.
import Mathlib.Algebra.MvPolynomial.Monad
import Mathlib.Tactic.LinearCombination
-- Proof-only: Bézout's identity and faithfulness of scalars, for uniqueness of the multiple.
import TauCeti.Algebra.GCDMonoid.Finset
import TauCeti.Algebra.MvPolynomial.Coeff
-- Proof-only: the coefficients of `C_n` sum to `(2ⁿ - 2) / d_n`.
import TauCeti.Data.Nat.Choose.Basic
-- Proof-only: the coefficients of the four terms of the cocycle identity.
import TauCeti.Algebra.MvPolynomial.Fin.Three

/-!
# The Lazard symmetric 2-cocycles `C_n(X, Y)`

A two-variable polynomial `f(X, Y)` over a commutative ring `R` is an *additive 2-cocycle* if

  `f(X, Y) + f(X + Y, Z) = f(X, Y + Z) + f(Y, Z)`.

Symmetric additive 2-cocycles are the first-order deformations of the additive formal group law
`X + Y`: if `F(X, Y) ≡ X + Y + f(X, Y)` modulo terms of degree `> n` and `f` is homogeneous of
degree `n`, then commutativity and associativity of `F` modulo terms of degree `> n` say exactly
that `f` is a symmetric additive 2-cocycle. This is why they govern the degree-by-degree
construction of formal group laws and Lazard's theorem that the Lazard ring is polynomial.

For `n ≥ 2` the basic example is `(X + Y)ⁿ - Xⁿ - Yⁿ`. Its coefficients `n.choose i`,
`0 < i < n`, have greatest common divisor `d_n`, which is the prime `p` when `n` is a power of `p`
and `1` otherwise (`Choose.gcd_choose_eq_minFac_of_isPrimePow`,
`Choose.gcd_choose_eq_one_of_not_isPrimePow`). Dividing by it gives the integral polynomial
`C_n(X, Y)` with `d_n • C_n = (X + Y)ⁿ - Xⁿ - Yⁿ`, defined here over every commutative ring by
casting its natural-number coefficients `n.choose i / d_n`. It is a homogeneous symmetric
additive 2-cocycle of degree `n`, compatible with every change of coefficients, and its
coefficients generate the unit ideal of `ℤ`. Consequently `r • C_n = 0` forces `r = 0` in *every*
commutative ring `R`, including rings with torsion: the multiple of `C_n` representing a cocycle
is unique. The converse, existence, is the symmetric 2-cocycle lemma: every homogeneous symmetric
additive 2-cocycle of degree `n` is a multiple of `C_n`
(`TauCeti.exists_eq_smul_lazardCocycle`, in
`TauCeti.RingTheory.FormalGroup.SymmetricCocycle.Classification`).

## Main definitions

* `MvPolynomial.IsAddCocycle₂`: `f(X, Y) + f(X + Y, Z) = f(X, Y + Z) + f(Y, Z)`.
* `TauCeti.lazardGcd n`: the greatest common divisor `d_n` of the `n.choose i`, `0 < i < n`.
* `TauCeti.lazardCocycle n R`: the polynomial `C_n(X, Y)` over `R`.

## Main results

* `MvPolynomial.IsAddCocycle₂.coeff_eq`: the cocycle identity at the coefficient of `XⁱYʲZᵏ`,
  `[k = 0] c_{i,j} + (i + j).choose i * c_{i+j,k} = (j + k).choose j * c_{i,j+k} + [i = 0] c_{j,k}`
  where `c_{a,b}` is the coefficient of `XᵃYᵇ` in `f`.
* `MvPolynomial.IsAddCocycle₂.coeff_single_one_eq_zero`: the coefficient of `Yⁿ` in an additive
  2-cocycle vanishes for `n ≠ 0`.
* `TauCeti.lazardGcd_eq_minFac_of_isPrimePow`, `TauCeti.lazardGcd_eq_one_of_not_isPrimePow`:
  `d_n` is `p` for `n = pᵏ`, and `1` for `n ≥ 2` not a prime power.
* `TauCeti.prime_dvd_lazardGcd_iff`: for `n ≠ 0` and a prime `p`, `p ∣ d_n` exactly when `n` is a
  power of `p`. In particular `d_n` is odd unless `n` is a power of two.
* `Nat.Prime.exists_not_dvd_choose`: if `n ≠ 0` is not a power of the prime `p`, then `p` does not
  divide some `n.choose i` with `0 < i < n`.
* `TauCeti.gcd_choose_div_lazardGcd_eq_one`: for `n ≥ 2`, the coefficients `n.choose i / d_n`
  have greatest common divisor `1`.
* `TauCeti.coeff_lazardCocycle`: the coefficient of `XⁱYʲ` in `C_n` is
  `n.choose i / d_n` when `i + j = n` and `i, j ≠ 0`, and `0` otherwise.
* `TauCeti.lazardGcd_nsmul_lazardCocycle`: `d_n • C_n = (X + Y)ⁿ - Xⁿ - Yⁿ` for `n ≠ 0`.
* `TauCeti.aeval_diag_lazardCocycle`: the diagonal `C_n(a, a)` is `((2ⁿ - 2) / d_n) • aⁿ`.
* `TauCeti.map_lazardCocycle`: `C_n` is compatible with ring homomorphisms.
* `TauCeti.isHomogeneous_lazardCocycle`, `TauCeti.isSymmetric_lazardCocycle`,
  `TauCeti.isAddCocycle₂_lazardCocycle`: `C_n` is a homogeneous symmetric additive 2-cocycle
  of degree `n`.
* `TauCeti.smul_lazardCocycle_eq_zero_iff`: for `n ≥ 2`, `r • C_n = 0 ↔ r = 0`.

## References

* M. Lazard, *Sur les groupes de Lie formels à un paramètre*, Bull. Soc. Math. France 83 (1955).
* D. C. Ravenel, *Complex Cobordism and Stable Homotopy Groups of Spheres*, Appendix A2.1
  (the symmetric 2-cocycle lemma).
-/

public section

open Finset

namespace MvPolynomial

variable {R S : Type*} [CommRing R] [CommRing S]

section IsAddCocycle₂

/-- A two-variable polynomial `f(X, Y)` is an *additive 2-cocycle* if
`f(X, Y) + f(X + Y, Z) = f(X, Y + Z) + f(Y, Z)` in `R[X, Y, Z]`. -/
def IsAddCocycle₂ (f : MvPolynomial (Fin 2) R) : Prop :=
  (aeval ![X 0, X 1] f + aeval ![X 0 + X 1, X 2] f : MvPolynomial (Fin 3) R) =
    aeval ![X 0, X 1 + X 2] f + aeval ![X 1, X 2] f

/-- Unfolding `MvPolynomial.IsAddCocycle₂`. -/
theorem isAddCocycle₂_iff {f : MvPolynomial (Fin 2) R} :
    f.IsAddCocycle₂ ↔
      (aeval ![X 0, X 1] f + aeval ![X 0 + X 1, X 2] f : MvPolynomial (Fin 3) R) =
        aeval ![X 0, X 1 + X 2] f + aeval ![X 1, X 2] f :=
  Iff.rfl

namespace IsAddCocycle₂

variable {f g : MvPolynomial (Fin 2) R}

/-- The zero polynomial is an additive 2-cocycle. -/
@[simp]
theorem zero : (0 : MvPolynomial (Fin 2) R).IsAddCocycle₂ := by
  simp [isAddCocycle₂_iff]

/-- Additive 2-cocycles are closed under addition. -/
theorem add (hf : f.IsAddCocycle₂) (hg : g.IsAddCocycle₂) : (f + g).IsAddCocycle₂ := by
  rw [isAddCocycle₂_iff] at *
  simp only [map_add]
  linear_combination hf + hg

/-- Additive 2-cocycles are closed under scalar multiplication. -/
theorem smul (r : R) (hf : f.IsAddCocycle₂) : (r • f).IsAddCocycle₂ := by
  rw [isAddCocycle₂_iff] at *
  simp only [map_smul, ← smul_add, hf]

/-- Additive 2-cocycles are preserved by a change of coefficients. -/
theorem map (hf : f.IsAddCocycle₂) (φ : R →+* S) : (MvPolynomial.map φ f).IsAddCocycle₂ := by
  -- `map φ (aeval g f) = aeval (map φ ∘ g) (map φ f)`, by `aeval_eq_bind₁` and `map_bind₁`.
  have hmap (a b : MvPolynomial (Fin 3) R) :
      MvPolynomial.map φ (aeval ![a, b] f) =
        aeval ![MvPolynomial.map φ a, MvPolynomial.map φ b] (MvPolynomial.map φ f) := by
    rw [aeval_eq_bind₁, aeval_eq_bind₁, map_bind₁]
    congr 2
    funext i
    fin_cases i <;> simp
  have h := congrArg (MvPolynomial.map φ) hf
  rw [isAddCocycle₂_iff]
  simpa only [map_add, hmap, map_X] using h

/-- The cocycle identity at the coefficient of `XⁱYʲZᵏ`. -/
theorem coeff_eq (hf : f.IsAddCocycle₂) (i j k : ℕ) :
    (if k = 0 then f.coeff (Finsupp.single 0 i + Finsupp.single 1 j) else 0) +
        (i + j).choose i * f.coeff (Finsupp.single 0 (i + j) + Finsupp.single 1 k) =
      (j + k).choose j * f.coeff (Finsupp.single 0 i + Finsupp.single 1 (j + k)) +
        if i = 0 then f.coeff (Finsupp.single 0 j + Finsupp.single 1 k) else 0 := by
  have h := congrArg (fun p : MvPolynomial (Fin 3) R =>
    p.coeff (Finsupp.single 0 i + Finsupp.single 1 j + Finsupp.single 2 k)) (isAddCocycle₂_iff.1 hf)
  -- `aeval_eq_bind₁` would turn the four substitutions into `bind₁` before they are computed.
  simpa [-aeval_eq_bind₁, coeff_aeval_X_add_X_X, coeff_aeval_X_X_add_X, coeff_aeval_X_zero_X_one,
    coeff_aeval_X_one_X_two, Finsupp.single_apply] using h

/-- The coefficient of `Yⁿ` in an additive 2-cocycle vanishes for `n ≠ 0`. -/
theorem coeff_single_one_eq_zero (hf : f.IsAddCocycle₂) {n : ℕ} (hn : n ≠ 0) :
    f.coeff (Finsupp.single 1 n) = 0 := by
  simpa [hn] using hf.coeff_eq 0 0 n

end IsAddCocycle₂

end IsAddCocycle₂

end MvPolynomial

namespace TauCeti

open MvPolynomial

variable {R S : Type*} [CommRing R] [CommRing S]

section lazardGcd

/-- The greatest common divisor `d_n` of the binomial coefficients `n.choose i`, `0 < i < n`.
For `n ≥ 2` it is the prime `p` if `n` is a power of `p`, and `1` otherwise
(`lazardGcd_eq_minFac_of_isPrimePow`, `lazardGcd_eq_one_of_not_isPrimePow`); for `n < 2` the
range is empty and `d_n = 0` (`lazardGcd_eq_zero_of_lt_two`). -/
def lazardGcd (n : ℕ) : ℕ :=
  (Icc 1 (n - 1)).gcd n.choose

/-- If `n = pᵏ` with `k ≥ 1`, then `d_n = p`. -/
theorem lazardGcd_eq_minFac_of_isPrimePow {n : ℕ} (h : IsPrimePow n) : lazardGcd n = n.minFac :=
  Choose.gcd_choose_eq_minFac_of_isPrimePow h

/-- If `n ≥ 2` is not a prime power, then `d_n = 1`. -/
theorem lazardGcd_eq_one_of_not_isPrimePow {n : ℕ} (hn : 1 < n) (h : ¬IsPrimePow n) :
    lazardGcd n = 1 :=
  Choose.gcd_choose_eq_one_of_not_isPrimePow hn h

/-- `d_0 = d_1 = 0`: the range `0 < i < n` is empty. -/
theorem lazardGcd_eq_zero_of_lt_two {n : ℕ} (hn : n < 2) : lazardGcd n = 0 := by
  rw [lazardGcd, Finset.Icc_eq_empty (by omega), Finset.gcd_empty]

/-- For a prime `p` and `k ≠ 0`, `d_{pᵏ} = p`. -/
theorem lazardGcd_prime_pow {p k : ℕ} (hp : p.Prime) (hk : k ≠ 0) : lazardGcd (p ^ k) = p := by
  rw [lazardGcd_eq_minFac_of_isPrimePow (hp.isPrimePow.pow hk), hp.pow_minFac hk]

/-- For `n ≠ 0` and a prime `p`, `p` divides `d_n` exactly when `n` is a power of `p`. -/
theorem prime_dvd_lazardGcd_iff {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) :
    p ∣ lazardGcd n ↔ ∃ k, n = p ^ k := by
  -- For `n = 1`, both sides hold: `d_1 = 0` and `1 = p⁰`.
  rcases eq_or_ne n 1 with rfl | hn1
  · exact iff_of_true (by simp [lazardGcd_eq_zero_of_lt_two]) ⟨0, (pow_zero p).symm⟩
  refine ⟨fun h => ?_, ?_⟩
  · by_cases hpp : IsPrimePow n
    · obtain ⟨q, k, hq, hk, rfl⟩ := (isPrimePow_nat_iff n).1 hpp
      rw [lazardGcd_prime_pow hq hk.ne', Nat.prime_dvd_prime_iff_eq hp hq] at h
      exact ⟨k, h ▸ rfl⟩
    · rw [lazardGcd_eq_one_of_not_isPrimePow (by omega) hpp, Nat.dvd_one] at h
      exact absurd h hp.one_lt.ne'
  · rintro ⟨k, rfl⟩
    rw [lazardGcd_prime_pow hp]
    rintro rfl
    simp at hn1

/-- `d ∣ d_n` if and only if `d` divides every `n.choose i`, `0 < i < n`. -/
theorem dvd_lazardGcd_iff {n d : ℕ} :
    d ∣ lazardGcd n ↔ ∀ i, 0 < i → i < n → d ∣ n.choose i := by
  rw [lazardGcd, Finset.dvd_gcd_iff]
  refine ⟨fun h i hi hin => h i (mem_Icc.2 ⟨hi, by omega⟩), fun h i hi => ?_⟩
  rw [mem_Icc] at hi
  exact h i (by omega) (by omega)

/-- If `n ≠ 0` is not a power of the prime `p`, some binomial coefficient `n.choose i` with
`0 < i < n` is not divisible by `p`. This is the converse of `Nat.Prime.dvd_choose_pow`. -/
theorem _root_.Nat.Prime.exists_not_dvd_choose {p n : ℕ} (hp : p.Prime) (hn0 : n ≠ 0)
    (hn : ∀ k, n ≠ p ^ k) : ∃ i, 0 < i ∧ i < n ∧ ¬p ∣ n.choose i := by
  by_contra! H
  obtain ⟨k, hk⟩ := (prime_dvd_lazardGcd_iff hp hn0).1 (dvd_lazardGcd_iff.2 H)
  exact hn k hk

/-- `d_n` divides `n.choose i` for `0 < i < n`. -/
theorem lazardGcd_dvd_choose {n i : ℕ} (hi : 0 < i) (hin : i < n) : lazardGcd n ∣ n.choose i :=
  gcd_dvd (mem_Icc.2 ⟨hi, by omega⟩)

/-- `d_n * (n.choose i / d_n) = n.choose i` for `0 < i < n`. -/
theorem lazardGcd_mul_choose_div_lazardGcd {n i : ℕ} (hi : 0 < i) (hin : i < n) :
    lazardGcd n * (n.choose i / lazardGcd n) = n.choose i :=
  Nat.mul_div_cancel' (lazardGcd_dvd_choose hi hin)

/-- `d_n ≠ 0` for `n ≥ 2`. -/
theorem lazardGcd_ne_zero {n : ℕ} (hn : 2 ≤ n) : lazardGcd n ≠ 0 :=
  Finset.gcd_ne_zero_iff.2 ⟨1, mem_Icc.2 ⟨le_rfl, by omega⟩, by simp; omega⟩

/-- For `n ≥ 2`, the numbers `n.choose i / d_n`, `0 < i < n`, have greatest common divisor `1`. -/
theorem gcd_choose_div_lazardGcd_eq_one {n : ℕ} (hn : 2 ≤ n) :
    (Icc 1 (n - 1)).gcd (fun i => n.choose i / lazardGcd n) = 1 :=
  Finset.gcd_div_eq_one (i := 1) (mem_Icc.2 ⟨le_rfl, by omega⟩) (by simp; omega)

end lazardGcd

section lazardCocycle

/-- The monomial `XⁱYʲ` has exponent `d` exactly when `d 0 = i` and `d 1 = j`. -/
private theorem single_add_single_eq_iff {i j : ℕ} {d : Fin 2 →₀ ℕ} :
    Finsupp.single 0 i + Finsupp.single 1 j = d ↔ d 0 = i ∧ d 1 = j := by
  simp [Finsupp.ext_iff, Fin.forall_fin_two, eq_comm]

/-- The **Lazard 2-cocycle** `C_n(X, Y)`, whose coefficient of `XⁱYⁿ⁻ⁱ` is `n.choose i / d_n` for
`0 < i < n`, where `d_n = lazardGcd n`; thus `d_n • C_n = (X + Y)ⁿ - Xⁿ - Yⁿ` for `n ≠ 0`
(`lazardGcd_nsmul_lazardCocycle`). Its coefficients are natural numbers, cast into `R`. For
`n < 2` it is `0`. -/
noncomputable def lazardCocycle (n : ℕ) (R : Type*) [CommRing R] : MvPolynomial (Fin 2) R :=
  ∑ i ∈ Icc 1 (n - 1), monomial (Finsupp.single 0 i + Finsupp.single 1 (n - i))
    ((n.choose i / lazardGcd n : ℕ) : R)

/-- The coefficient of `XⁱYʲ` in `C_n` is `n.choose i / d_n` if `i + j = n` and `i, j ≠ 0`, and
`0` otherwise. -/
theorem coeff_lazardCocycle (n : ℕ) (d : Fin 2 →₀ ℕ) :
    (lazardCocycle n R).coeff d =
      if d 0 + d 1 = n ∧ d 0 ≠ 0 ∧ d 1 ≠ 0 then ((n.choose (d 0) / lazardGcd n : ℕ) : R)
      else 0 := by
  classical
  rw [lazardCocycle, coeff_sum]
  simp only [coeff_monomial, single_add_single_eq_iff]
  split_ifs with h
  · rw [Finset.sum_eq_single (d 0)]
    · rw [ite_eq_left ⟨rfl, by omega⟩]
    · intro i _ hi
      rw [ite_eq_right (by omega)]
    · intro hd
      exact absurd (mem_Icc.2 ⟨by omega, by omega⟩) hd
  · refine Finset.sum_eq_zero fun i hi => ite_eq_right ?_
    rw [mem_Icc] at hi
    omega

/-- `C_n` is compatible with every change of coefficients. -/
@[simp]
theorem map_lazardCocycle (φ : R →+* S) (n : ℕ) :
    MvPolynomial.map φ (lazardCocycle n R) = lazardCocycle n S := by
  simp [lazardCocycle, map_monomial]

/-- `C_0 = C_1 = 0`. -/
theorem lazardCocycle_eq_zero_of_lt_two {n : ℕ} (hn : n < 2) : lazardCocycle n R = 0 := by
  rw [lazardCocycle, Finset.Icc_eq_empty (by omega), Finset.sum_empty]

/-- For `n ≠ 0`, `d_n • C_n = (X + Y)ⁿ - Xⁿ - Yⁿ`, where `d_n = lazardGcd n` is the greatest common
divisor of the `n.choose i`, `0 < i < n`. -/
theorem lazardGcd_nsmul_lazardCocycle {n : ℕ} (hn : n ≠ 0) :
    lazardGcd n • lazardCocycle n R = (X 0 + X 1) ^ n - X 0 ^ n - X 1 ^ n := by
  classical
  ext d
  have h0 : Finsupp.single 0 n = d ↔ d 0 = n ∧ d 1 = 0 := by
    simpa using single_add_single_eq_iff (i := n) (j := 0) (d := d)
  have h1 : Finsupp.single 1 n = d ↔ d 0 = 0 ∧ d 1 = n := by
    simpa using single_add_single_eq_iff (i := 0) (j := n) (d := d)
  rw [coeff_smul, coeff_lazardCocycle, coeff_sub, coeff_sub, coeff_add_pow, coeff_X_pow,
    coeff_X_pow]
  simp only [h0, h1, mem_antidiagonal]
  by_cases h : d 0 + d 1 = n ∧ d 0 ≠ 0 ∧ d 1 ≠ 0
  · -- At `XⁱYʲ` with `i + j = n` and `i, j ≠ 0`, both sides are `n.choose i`, as `d_n` divides it.
    obtain ⟨hd, ha, hb⟩ := h
    have hcast : ((lazardGcd n : ℕ) : R) * ((n.choose (d 0) / lazardGcd n : ℕ) : R) =
        n.choose (d 0) := by
      rw [← Nat.cast_mul, lazardGcd_mul_choose_div_lazardGcd (by omega) (by omega)]
    simp [hd, ha, hb, nsmul_eq_mul, hcast]
  · -- At `Xⁿ` and `Yⁿ` the binomial coefficient `1` cancels; all other coefficients vanish.
    rw [ite_eq_right h, smul_zero]
    obtain ⟨ha, hb⟩ | ⟨ha, hb⟩ | hd :
        (d 0 = 0 ∧ d 1 = n) ∨ (d 0 = n ∧ d 1 = 0) ∨ d 0 + d 1 ≠ n := by omega
    · simp [ha, hb, Ne.symm hn]
    · simp [ha, hb, hn]
    · simp [hd, show ¬(d 0 = n ∧ d 1 = 0) by omega, show ¬(d 0 = 0 ∧ d 1 = n) by omega]

/-- `d_n • C_n(a, b) = (a + b)ⁿ - aⁿ - bⁿ` for elements `a, b` of any commutative `R`-algebra. -/
theorem lazardGcd_nsmul_aeval_lazardCocycle {A : Type*} [CommRing A] [Algebra R A] {n : ℕ}
    (hn : n ≠ 0) (a b : A) :
    lazardGcd n • aeval ![a, b] (lazardCocycle n R) = (a + b) ^ n - a ^ n - b ^ n := by
  rw [← map_nsmul, lazardGcd_nsmul_lazardCocycle hn]
  simp

/-- The diagonal `C_n(a, a)` of the Lazard cocycle, for an element `a` of any commutative
`R`-algebra, is `((2ⁿ - 2) / d_n) • aⁿ`: the coefficients `n.choose i`, `0 < i < n`, of
`(X + Y)ⁿ - Xⁿ - Yⁿ` sum to `2ⁿ - 2`. For `n < 2` both sides vanish. -/
@[simp]
theorem aeval_diag_lazardCocycle {A : Type*} [CommRing A] [Algebra R A] (n : ℕ) (a : A) :
    aeval ![a, a] (lazardCocycle n R) = ((2 ^ n - 2) / lazardGcd n) • a ^ n := by
  -- The coefficient is the sum of the coefficients `n.choose i / d_n` of `C_n`.
  have hsum : (2 ^ n - 2) / lazardGcd n = ∑ i ∈ Icc 1 (n - 1), n.choose i / lazardGcd n := by
    rw [← Nat.sum_Icc_choose_eq_two_pow_sub_two]
    refine Nat.sum_div fun i hi => ?_
    rw [mem_Icc] at hi
    exact lazardGcd_dvd_choose (by omega) (by omega)
  rw [hsum, Finset.sum_smul, lazardCocycle, map_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mem_Icc] at hi
  simp [aeval_monomial, Finsupp.prod_add_index', ← pow_add, Nat.add_sub_cancel' (by omega : i ≤ n)]

/-- `C_n` is homogeneous of degree `n`. -/
theorem isHomogeneous_lazardCocycle (n : ℕ) : (lazardCocycle n R).IsHomogeneous n :=
  IsHomogeneous.sum _ _ _ fun i hi => isHomogeneous_monomial _ <| by
    rw [mem_Icc] at hi
    simp only [map_add, Finsupp.degree_single]
    omega

-- Over `ℤ`, multiplication by `d_n ≠ 0` is injective, so identities for `C_n` follow from the
-- corresponding identities for `(X + Y)ⁿ - Xⁿ - Yⁿ`; they then hold over every ring by base change.
private theorem isSymmetric_lazardCocycle_int (n : ℕ) : (lazardCocycle n ℤ).IsSymmetric := by
  obtain hn | hn := lt_or_ge n 2
  · rw [lazardCocycle_eq_zero_of_lt_two hn]
    exact IsSymmetric.zero
  intro e
  apply smul_right_injective _ (lazardGcd_ne_zero hn)
  dsimp only
  rw [← map_nsmul, lazardGcd_nsmul_lazardCocycle (by omega)]
  have hP : (X 0 + X 1) ^ n - X 0 ^ n - X 1 ^ n =
      ((∑ i, X i) ^ n - ∑ i, X i ^ n : MvPolynomial (Fin 2) ℤ) := by
    simp only [Fin.sum_univ_two]
    ring
  rw [hP]
  simp only [map_sub, map_pow, map_sum, rename_X]
  rw [Equiv.sum_comp e (fun i => (X i : MvPolynomial (Fin 2) ℤ)),
    Equiv.sum_comp e (fun i => (X i : MvPolynomial (Fin 2) ℤ) ^ n)]

private theorem isAddCocycle₂_lazardCocycle_int (n : ℕ) : (lazardCocycle n ℤ).IsAddCocycle₂ := by
  obtain hn | hn := lt_or_ge n 2
  · rw [lazardCocycle_eq_zero_of_lt_two hn]
    exact IsAddCocycle₂.zero
  rw [isAddCocycle₂_iff]
  apply smul_right_injective _ (lazardGcd_ne_zero hn)
  dsimp only
  simp only [smul_add, lazardGcd_nsmul_aeval_lazardCocycle (by omega : n ≠ 0)]
  ring

/-- `C_n(X, Y) = C_n(Y, X)`. -/
theorem isSymmetric_lazardCocycle (n : ℕ) : (lazardCocycle n R).IsSymmetric := by
  rw [← map_lazardCocycle (Int.castRingHom R)]
  exact (isSymmetric_lazardCocycle_int n).map _

/-- `C_n` is an additive 2-cocycle. -/
theorem isAddCocycle₂_lazardCocycle (n : ℕ) : (lazardCocycle n R).IsAddCocycle₂ := by
  rw [← map_lazardCocycle (Int.castRingHom R)]
  exact (isAddCocycle₂_lazardCocycle_int n).map _

/-- For `n ≥ 2`, `r • C_n = 0 ↔ r = 0` in every commutative ring `R`, including rings with
torsion. -/
@[simp]
theorem smul_lazardCocycle_eq_zero_iff {n : ℕ} (hn : 2 ≤ n) {r : R} :
    r • lazardCocycle n R = 0 ↔ r = 0 := by
  refine ⟨fun h => ?_, fun h => by rw [h, zero_smul]⟩
  obtain ⟨c, hc⟩ :=
    Finset.exists_sum_natCast_mul_eq_one_of_gcd_eq_one (gcd_choose_div_lazardGcd_eq_one hn)
  refine eq_zero_of_smul_eq_zero_of_sum_coeff_mul_eq_one (Icc 1 (n - 1))
    (fun i => Finsupp.single 0 i + Finsupp.single 1 (n - i)) (fun i => (c i : R)) ?_ h
  rw [← Int.cast_one, ← hc, Int.cast_sum]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [mem_Icc] at hi
  rw [Int.cast_mul, Int.cast_natCast]
  simp [coeff_lazardCocycle, show i ≠ 0 by omega, show n - i ≠ 0 by omega,
    show i + (n - i) = n by omega]

/-- For `n ≥ 2`, `r ↦ r • C_n` is injective. -/
theorem smul_lazardCocycle_injective {n : ℕ} (hn : 2 ≤ n) :
    Function.Injective fun r : R => r • lazardCocycle n R := fun r s h => by
  rw [← sub_eq_zero, ← smul_lazardCocycle_eq_zero_iff hn, sub_smul]
  exact sub_eq_zero.2 h

end lazardCocycle

end TauCeti
