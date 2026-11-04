/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Cyclotomic.Basic
public import Mathlib.NumberTheory.NumberField.Cyclotomic.Galois
public import TauCeti.NumberTheory.NumberField.Cyclotomic.Quadratic
public import TauCeti.NumberTheory.NumberField.Ideal.RootsOfUnity
public import TauCeti.NumberTheory.NumberField.Quadratic.Norm
public import TauCeti.NumberTheory.NumberField.WorkedExamples.GaussianRationals.Invariants
public import TauCeti.RingTheory.RootsOfUnity.Basic
import TauCeti.NumberTheory.NumberField.RingOfIntegers.Norm

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
* `IsPrimitiveRoot.apply_intCast_add_intCast_mul_toInteger_of_four`: any ring-homomorphism-like
  map `σ` of `ℤ[i]` cubing the fourth roots of unity sends `a + b i` to `a - b i`;
* `IsPrimitiveRoot.norm_intCast_add_intCast_mul_toInteger_of_four`: the norm of `a + b i` is
  `a² + b²`;
* `IsPrimitiveRoot.odd_norm_intCast_add_intCast_mul_toInteger_iff_of_four`: the norm of `a + b i`
  is odd exactly when `a + b` is;
* `IsPrimitiveRoot.isUnit_intCast_add_intCast_mul_toInteger_iff_of_four`: `a + b i` is a unit
  exactly when `a² + b² = 1`;
* `TauCeti.finrank_four`: `[K : ℚ] = 2`;
* `TauCeti.isPrincipalIdealRing_ringOfIntegers_four`: `ℤ[i]` is a principal ideal domain;
* `TauCeti.exists_ringHom_apply_eq_pow_three_of_four`,
  `TauCeti.exists_ringEquiv_apply_eq_pow_three_of_four`: complex conjugation of `ℤ[i]` (as a ring
  endomorphism or ring automorphism) cubes every fourth root of unity;
* `TauCeti.intCast_norm_eq_mul_of_four`: the norm of `x` is `x σ(x)` for such a conjugation `σ`,
  and `TauCeti.apply_apply_eq_self_of_four` records that `σ` is an involution;
* `TauCeti.absNorm_span_natCast_four`: the absolute norm of `q ℤ[i]` is `q²`;
* `NumberField.RingOfIntegers.natCast_absNorm_span_singleton_of_four`: the absolute norm of
  `x ℤ[i]` is the norm of `x`;
* `TauCeti.prime_natCast_of_mod_four_eq_three`: a rational prime `q ≡ 3 (mod 4)` stays prime in
  `ℤ[i]`, and `TauCeti.mk_pow_eq_mk_apply_of_mod_four_eq_three` identifies the `q`-th power map on
  `ℤ[i] ⧸ q ℤ[i]` with complex conjugation.

The conjugation argument follows the cubic case in
[TauCetiProject/TauCeti#21047](https://github.com/TauCetiProject/TauCeti/pull/21047).
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

omit [NumberField K] in
/-- Any ring-homomorphism-like map `σ` of `𝓞 K = ℤ[i]` that cubes the fourth roots of unity sends
`a + b i` to `a - b i`. -/
theorem apply_intCast_add_intCast_mul_toInteger_of_four
    {F : Type*} [FunLike F (𝓞 K) (𝓞 K)] [RingHomClass F (𝓞 K) (𝓞 K)] {σ : F}
    (hσ : ∀ x : 𝓞 K, x ^ 4 = 1 → σ x = x ^ 3) (a b : ℤ) :
    σ ((a : 𝓞 K) + b * hζ.toInteger) = (a : 𝓞 K) - b * hζ.toInteger := by
  have hsq := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  rw [map_add, map_mul, map_intCast, map_intCast, hσ _ hζ.toInteger_isPrimitiveRoot.pow_eq_one]
  linear_combination ((b : 𝓞 K) * hζ.toInteger) * hsq

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

/-- The fourth cyclotomic field `ℚ(i)` has degree `2` over `ℚ`. -/
theorem finrank_four {K : Type*} [Field K] [CharZero K] [IsCyclotomicExtension {4} ℚ K] :
    Module.finrank ℚ K = 2 := by
  rw [IsCyclotomicExtension.Rat.finrank 4 K]
  decide

variable (K : Type*) [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

/-- **`ℤ[i]` is a principal ideal domain.** This is
`TauCeti.NumberField.GaussianRationals.isPrincipalIdealRing` at a primitive fourth root of
unity. -/
theorem isPrincipalIdealRing_ringOfIntegers_four : IsPrincipalIdealRing (𝓞 K) :=
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  NumberField.GaussianRationals.isPrincipalIdealRing hζ.minpoly_toInteger_eq_X_sq_add_one
    hζ.adjoin_toInteger_four

end TauCeti

namespace TauCeti

open IsCyclotomicExtension.Rat

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

/-- Complex conjugation of `𝓞 K = ℤ[i]`, the automorphism corresponding to `-1 ∈ (ZMod 4)ˣ`, cubes
every fourth root of unity. -/
theorem exists_ringHom_apply_eq_pow_three_of_four :
    ∃ σ : 𝓞 K →+* 𝓞 K, ∀ x : 𝓞 K, x ^ 4 = 1 → σ x = x ^ 3 := by
  refine ⟨MulSemiringAction.toRingHom Gal(K/ℚ) (𝓞 K) ((galEquivZMod 4 K).symm (-1)),
    fun x hx ↦ ?_⟩
  rw [MulSemiringAction.toRingHom_apply, galEquivZMod_smul_of_pow_eq 4 K _ hx,
    MulEquiv.apply_symm_apply]
  -- The representative of `-1` in `ZMod 4` is `3`.
  rfl

/-- If `σ` cubes the fourth roots of unity of `𝓞 K = ℤ[i]`, then the norm of `x` is `x σ(x)`. -/
theorem intCast_norm_eq_mul_of_four
    {F : Type*} [FunLike F (𝓞 K) (𝓞 K)] [RingHomClass F (𝓞 K) (𝓞 K)] {σ : F}
    (hσ : ∀ x : 𝓞 K, x ^ 4 = 1 → σ x = x ^ 3) (x : 𝓞 K) :
    (Algebra.norm ℤ x : 𝓞 K) = x * σ x := by
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  have hsq := hζ.toInteger_isPrimitiveRoot.sq_eq_neg_one
  obtain ⟨a, b, rfl⟩ := hζ.exists_intCast_add_intCast_mul_toInteger_eq (by decide) x
  rw [hζ.norm_intCast_add_intCast_mul_toInteger_of_four,
    hζ.apply_intCast_add_intCast_mul_toInteger_of_four hσ]
  push_cast
  linear_combination (b : 𝓞 K) ^ 2 * hsq

/-- Any ring-homomorphism-like map `σ` of `𝓞 K = ℤ[i]` that cubes the fourth roots of unity is an
involution. -/
theorem apply_apply_eq_self_of_four
    {F : Type*} [FunLike F (𝓞 K) (𝓞 K)] [RingHomClass F (𝓞 K) (𝓞 K)] {σ : F}
    (hσ : ∀ x : 𝓞 K, x ^ 4 = 1 → σ x = x ^ 3) (x : 𝓞 K) :
    σ (σ x) = x := by
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  obtain ⟨a, b, rfl⟩ := hζ.exists_intCast_add_intCast_mul_toInteger_eq (by decide) x
  have hsub : (a : 𝓞 K) - b * hζ.toInteger = (a : 𝓞 K) + (-b : ℤ) * hζ.toInteger := by
    push_cast; ring
  rw [hζ.apply_intCast_add_intCast_mul_toInteger_of_four hσ, hsub,
    hζ.apply_intCast_add_intCast_mul_toInteger_of_four hσ]
  push_cast
  ring

/-- Complex conjugation of `𝓞 K = ℤ[i]` as a ring automorphism, cubing every fourth root of
unity. -/
theorem exists_ringEquiv_apply_eq_pow_three_of_four :
    ∃ τ : 𝓞 K ≃+* 𝓞 K, ∀ x : 𝓞 K, x ^ 4 = 1 → τ x = x ^ 3 := by
  obtain ⟨σ, hσ⟩ := exists_ringHom_apply_eq_pow_three_of_four (K := K)
  refine ⟨{
    toFun := σ
    invFun := σ
    left_inv := apply_apply_eq_self_of_four hσ
    right_inv := apply_apply_eq_self_of_four hσ
    map_mul' := map_mul σ
    map_add' := map_add σ
  }, hσ⟩

end TauCeti

namespace TauCeti

open Ideal

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

/-- The absolute norm of `q 𝓞 K` is `q²`, since `𝓞 K` has rank two. -/
theorem absNorm_span_natCast_four (q : ℕ) : absNorm (span {(q : 𝓞 K)}) = q ^ 2 := by
  rw [absNorm_span_natCast, RingOfIntegers.rank, finrank_four]

end TauCeti

namespace NumberField.RingOfIntegers

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

/-- The absolute norm of `x 𝓞 K` is the norm of `x`, which is nonnegative in `𝓞 K = ℤ[i]` as a
sum of two squares. -/
theorem natCast_absNorm_span_singleton_of_four (x : 𝓞 K) :
    (Ideal.absNorm (Ideal.span {x}) : ℤ) = Algebra.norm ℤ x := by
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  rw [Ideal.absNorm_span_singleton, Int.natCast_natAbs, abs_eq_self]
  obtain ⟨a, b, rfl⟩ := hζ.exists_intCast_add_intCast_mul_toInteger_eq (by decide) x
  rw [hζ.norm_intCast_add_intCast_mul_toInteger_of_four]
  positivity

end NumberField.RingOfIntegers

namespace TauCeti

open Ideal

variable {K : Type*} [Field K] [NumberField K] [IsCyclotomicExtension {4} ℚ K]

/-- **Rational primes `q ≡ 3 (mod 4)` are inert in `𝓞 K = ℤ[i]`.** This is the analogue for the
ring of integers of the fourth cyclotomic field of one direction of Mathlib's
`GaussianInt.prime_iff_mod_four_eq_three_of_nat_prime`. -/
theorem prime_natCast_of_mod_four_eq_three [HasEnoughRootsOfUnity (𝓞 K) 4] {q : ℕ}
    (hq : q.Prime) (hq3 : q % 4 = 3) : Prime (q : 𝓞 K) := by
  have hN := absNorm_span_natCast_four (K := K) q
  have hne : span {(q : 𝓞 K)} ≠ ⊤ := by
    rintro htop
    rw [htop, absNorm_top] at hN
    nlinarith [hq.two_le]
  obtain ⟨P, hP, hle⟩ := exists_le_maximal _ hne
  -- `N P ∣ q²`, and `N P ≠ q` since `4 ∣ N P - 1`, so `N P = q²` and `P = q 𝓞 K`.
  have hPN : absNorm P = q ^ 2 := by
    obtain ⟨k, hk, hPk⟩ := (Nat.dvd_prime_pow hq).mp (hN ▸ absNorm_dvd_absNorm_of_le hle)
    interval_cases k
    · exact absurd (absNorm_eq_one_iff.mp (by rw [hPk, pow_zero])) hP.ne_top
    · rw [pow_one] at hPk
      have h4 := NumberField.dvd_absNorm_sub_one (n := 4) (P := P) (by
        rw [hPk, Nat.Coprime, Nat.gcd_comm, Nat.gcd_rec, hq3]
        rfl)
      omega
    · exact hPk
  obtain ⟨C, hC⟩ := dvd_iff_le.mpr hle
  have hC1 : absNorm C = 1 := by
    rw [hC, map_mul, hPN] at hN
    exact (Nat.mul_eq_left (pow_ne_zero 2 hq.ne_zero)).mp hN
  rw [absNorm_eq_one_iff.mp hC1, mul_top] at hC
  exact (span_singleton_prime (by exact_mod_cast hq.ne_zero)).mp (hC ▸ hP.isPrime)

/-- Modulo an inert prime `Q = q 𝓞 K` with `q ≡ 3 (mod 4)`, the `q`-th power map on `𝓞 K ⧸ Q`
agrees with complex conjugation `σ`. -/
theorem mk_pow_eq_mk_apply_of_mod_four_eq_three {q : ℕ} (hq : q.Prime) (hq3 : q % 4 = 3)
    {F : Type*} [FunLike F (𝓞 K) (𝓞 K)] [RingHomClass F (𝓞 K) (𝓞 K)] {σ : F}
    (hσ : ∀ x : 𝓞 K, x ^ 4 = 1 → σ x = x ^ 3) (x : 𝓞 K) :
    (Ideal.Quotient.mk (span {(q : 𝓞 K)}) x) ^ q =
      Ideal.Quotient.mk (span {(q : 𝓞 K)}) (σ x) := by
  have : Fact q.Prime := ⟨hq⟩
  set Q := span {(q : 𝓞 K)}
  have hζ := IsCyclotomicExtension.zeta_spec 4 ℚ K
  obtain ⟨a, b, rfl⟩ := hζ.exists_intCast_add_intCast_mul_toInteger_eq (by decide) x
  have hint (c : ℤ) : (c : 𝓞 K ⧸ Q) ^ q = (c : 𝓞 K ⧸ Q) := by
    let φ : ZMod q →+* 𝓞 K ⧸ Q := ZMod.castHom dvd_rfl (𝓞 K ⧸ Q)
    have hc : (c : 𝓞 K ⧸ Q) = φ (c : ZMod q) := by simp [φ]
    rw [hc, ← map_pow, ZMod.pow_card]
  have hiq : (Ideal.Quotient.mk Q hζ.toInteger) ^ q =
      Ideal.Quotient.mk Q (σ hζ.toInteger) := by
    have h4 : (Ideal.Quotient.mk Q hζ.toInteger) ^ 4 = 1 := by
      rw [← map_pow, hζ.toInteger_isPrimitiveRoot.pow_eq_one, map_one]
    obtain ⟨k, hk⟩ : ∃ k, q = 4 * k + 3 := ⟨q / 4, by omega⟩
    rw [hσ _ hζ.toInteger_isPrimitiveRoot.pow_eq_one, map_pow, hk, pow_add, pow_mul, h4,
      one_pow, one_mul]
  simp only [map_add, map_mul, map_intCast, add_pow_char, mul_pow, hint, hiq]

end TauCeti
