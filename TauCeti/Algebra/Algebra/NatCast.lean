/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Field.Defs

/-!
# Natural numbers invertible in algebras

A natural number that is a unit in `K` stays nonzero in every nontrivial `K`-algebra `L`. Results
stated over an extension, such as the separable closure `Kˢ`, often need `(m : L) ≠ 0`, while the
hypothesis available is `IsUnit (m : K)`, which holds for every `m ≠ 0` in an algebra over a
characteristic-zero semifield, such as a `ℚ`-algebra.

In an algebra over a characteristic-zero semifield `K` (for instance `K = ℚ`) every positive
natural number is invertible. Over any semifield `K`, the natural multiple `m • ·` and the scalar
`m⁻¹`, taken in `K`, cancel in every module over a `K`-algebra whenever `(m : K) ≠ 0`. Over a
characteristic-zero semifield every `k + 1` is nonzero, so in an algebra over it, choosing the
termwise integral of a power series to have zero constant coefficient gives a right inverse of
differentiation; integrating a derivative recovers only the terms of positive degree.

The hypotheses `[Semifield K] [CharZero K] [Algebra K A]` of the three unit lemmas, and their
explicit base argument `K`, follow Mathlib's `IsUnit.natCast_factorial_of_algebra`.

## Main results

* `IsUnit.ofNat_of_algebra`: if a numeral is a unit in `K` then it is a unit in `L`.
* `IsUnit.natCast_ne_zero_of_algebra`: if `(m : K)` is a unit then `(m : L) ≠ 0`.
* `TauCeti.isUnit_natCast_of_ne_zero`, `TauCeti.isUnit_natCast_add_of_ne_zero`,
  `TauCeti.isUnit_natCast_add_one`: every nonzero natural number (in particular `(m : A) + k` for
  `k ≠ 0` and `(m : A) + 1`) is a unit in an algebra `A` over a characteristic-zero semifield `K`.

The remaining results hold over any semifield `K` (the first `k + 1` cancellation even over any
division semiring); in each, the inverse is taken in `K` and then mapped into the algebra or used
as a scalar.

* `TauCeti.natCast_mul_algebraMap_inv`, `TauCeti.ofNat_mul_algebraMap_inv`: `m · (1 / m) = 1` in a
  `K`-algebra, for a natural number or a numeral `m` with `(m : K) ≠ 0`;
  `TauCeti.algebraMap_inv_mul_ofNat` is the numeral form `(1 / m) · m = 1`.
* `TauCeti.algebraMap_mul_algebraMap_inv`: `a · (1 / a) = 1` in `A` for `a` in the base `R` of a
  scalar tower `R → K → A`, when `a` is nonzero in `K`.
* `TauCeti.nsmul_algebraMap_inv_natCast_smul`, `TauCeti.algebraMap_inv_natCast_smul_nsmul`:
  `m • (1 / m) • a = a` and `(1 / m) • m • a = a` in a module over a `K`-algebra, when
  `(m : K) ≠ 0`.
* `TauCeti.inv_natCast_add_one_smul_mul_natCast_add_one`: `(k + 1)⁻¹ • (a * (k + 1)) = a` in a
  semiring that is a module over a division semiring `K`, when `(k : K) + 1 ≠ 0`.
* `TauCeti.algebraMap_inv_natCast_add_one_smul_natCast_add_one_mul`:
  `(1 / (k + 1)) • ((k + 1) * a) = a` in a semiring that is a module over a `K`-algebra, when
  `(k : K) + 1 ≠ 0`.
-/

public section

/-- A numeral invertible in `K` is invertible in every `K`-algebra `L`; for instance `2` is
invertible in every real algebra. -/
theorem IsUnit.ofNat_of_algebra {K L : Type*} [CommSemiring K] [Semiring L] [Algebra K L]
    {m : ℕ} [m.AtLeastTwo] (hm : IsUnit (ofNat(m) : K)) : IsUnit (ofNat(m) : L) := by
  simpa only [map_ofNat] using hm.map (algebraMap K L)

/-- A natural number invertible in `K` is nonzero in every nontrivial `K`-algebra `L`. -/
theorem IsUnit.natCast_ne_zero_of_algebra {K L : Type*} [CommSemiring K] [Semiring L]
    [Nontrivial L] [Algebra K L] {m : ℕ} (hm : IsUnit (m : K)) : (m : L) ≠ 0 := by
  simpa using (hm.map (algebraMap K L)).ne_zero

namespace TauCeti

/-- Every nonzero natural number is a unit in an algebra over a characteristic-zero semifield `K`,
for instance in every `ℚ`-algebra. -/
theorem isUnit_natCast_of_ne_zero (K : Type*) {A : Type*} [Semifield K] [CharZero K] [Semiring A]
    [Algebra K A] {m : ℕ} (hm : m ≠ 0) : IsUnit (m : A) := by
  simpa using (Nat.cast_ne_zero.2 hm : (m : K) ≠ 0).isUnit.map (algebraMap K A)

/-- Adding a nonzero natural number to a natural number gives a unit in an algebra over a
characteristic-zero semifield `K`. -/
theorem isUnit_natCast_add_of_ne_zero (K : Type*) {A : Type*} [Semifield K] [CharZero K]
    [Semiring A] [Algebra K A] (m : ℕ) {k : ℕ} (hk : k ≠ 0) : IsUnit ((m : A) + k) := by
  simpa only [Nat.cast_add] using isUnit_natCast_of_ne_zero K (A := A) (m := m + k) (by omega)

/-- For every natural number `m`, `(m : A) + 1` is a unit in an algebra over a characteristic-zero
semifield `K`. -/
theorem isUnit_natCast_add_one (K : Type*) {A : Type*} [Semifield K] [CharZero K] [Semiring A]
    [Algebra K A] (m : ℕ) : IsUnit ((m : A) + 1) := by
  simpa only [Nat.cast_one] using isUnit_natCast_add_of_ne_zero K (A := A) m one_ne_zero

/-- In a scalar tower `R → K → A` over a semifield `K`, multiplying by the image of `a : R` and by
the image of `a⁻¹ : K` cancel, provided `a` is nonzero in `K`; `natCast_mul_algebraMap_inv` is the
case of a natural number. -/
@[simp]
theorem algebraMap_mul_algebraMap_inv {R K A : Type*} [CommSemiring R] [Semifield K] [Semiring A]
    [Algebra R K] [Algebra K A] [Algebra R A] [IsScalarTower R K A] {a : R}
    (ha : algebraMap R K a ≠ 0) : algebraMap R A a * algebraMap K A (algebraMap R K a)⁻¹ = 1 := by
  have h : algebraMap R A a = algebraMap K A (algebraMap R K a) := by
    simp only [Algebra.algebraMap_eq_smul_one, smul_one_smul]
  rw [h, ← map_mul, mul_inv_cancel₀ ha, map_one]

/-- Multiplying by a natural number `m` and by the image of `m⁻¹ : K` cancel in an algebra over a
semifield `K`, provided `m` is nonzero in `K`. -/
@[simp]
theorem natCast_mul_algebraMap_inv {K A : Type*} [Semifield K] [Semiring A] [Algebra K A] {m : ℕ}
    (hm : (m : K) ≠ 0) : (m : A) * algebraMap K A (m : K)⁻¹ = 1 := by
  simpa using algebraMap_mul_algebraMap_inv (R := ℕ) (A := A) (by simpa using hm)

/-- Multiplying by a numeral `n` and by the image of `n⁻¹ : K` cancel in an algebra over a
semifield `K`, provided `n` is nonzero in `K`; for instance `2 · (1 / 2) = 1` in a `ℚ`-algebra. -/
@[simp]
theorem ofNat_mul_algebraMap_inv {K A : Type*} [Semifield K] [Semiring A] [Algebra K A] {n : ℕ}
    [n.AtLeastTwo] (hn : (ofNat(n) : K) ≠ 0) :
    (ofNat(n) : A) * algebraMap K A (ofNat(n) : K)⁻¹ = 1 :=
  natCast_mul_algebraMap_inv (A := A) hn

/-- Multiplying by the image of `n⁻¹ : K` and by a numeral `n` cancel in an algebra over a
semifield `K`, provided `n` is nonzero in `K`; for instance `(1 / 2) · 2 = 1` in a `ℚ`-algebra. -/
@[simp]
theorem algebraMap_inv_mul_ofNat {K A : Type*} [Semifield K] [Semiring A] [Algebra K A] {n : ℕ}
    [n.AtLeastTwo] (hn : (ofNat(n) : K) ≠ 0) :
    algebraMap K A (ofNat(n) : K)⁻¹ * (ofNat(n) : A) = 1 :=
  (Algebra.commutes _ _).trans (ofNat_mul_algebraMap_inv hn)

/-- In a module over a `K`-algebra `R`, the natural multiple `m • ·` cancels the scalar
`algebraMap K R m⁻¹` applied first, provided `m` is nonzero in the semifield `K`. -/
@[simp]
theorem nsmul_algebraMap_inv_natCast_smul {K R M : Type*} [Semifield K] [Semiring R] [Algebra K R]
    [AddCommMonoid M] [Module R M] {m : ℕ} (hm : (m : K) ≠ 0) (a : M) :
    m • algebraMap K R (m : K)⁻¹ • a = a := by
  rw [← Nat.cast_smul_eq_nsmul R, smul_smul, natCast_mul_algebraMap_inv hm, one_smul]

/-- In a module over a `K`-algebra `R`, the scalar `algebraMap K R m⁻¹` cancels the natural
multiple `m • ·` applied first, provided `m` is nonzero in the semifield `K`. -/
@[simp]
theorem algebraMap_inv_natCast_smul_nsmul {K R M : Type*} [Semifield K] [Semiring R] [Algebra K R]
    [AddCommMonoid M] [Module R M] {m : ℕ} (hm : (m : K) ≠ 0) (a : M) :
    algebraMap K R (m : K)⁻¹ • m • a = a := by
  rw [smul_comm (algebraMap K R (m : K)⁻¹) m]
  exact nsmul_algebraMap_inv_natCast_smul hm a

/-- Multiplying on the right by `k + 1` and then dividing by `k + 1` cancel in a semiring that is
a module over a division semiring `K`, for instance an algebra over a semifield `K`, provided
`k + 1` is nonzero in `K`. In a `K`-algebra this is the simp-normal form of
`(k + 1)⁻¹ • a * (k + 1)`. -/
@[simp]
theorem inv_natCast_add_one_smul_mul_natCast_add_one {K R : Type*} [DivisionSemiring K] [Semiring R]
    [Module K R] (a : R) (k : ℕ) (hk : (k : K) + 1 ≠ 0) :
    ((k : K) + 1)⁻¹ • (a * ((k : R) + 1)) = a := by
  have h : a * ((k : R) + 1) = ((k : K) + 1) • a := by
    rw [← Nat.cast_add_one, ← nsmul_eq_mul', ← Nat.cast_smul_eq_nsmul K, Nat.cast_add_one]
  rw [h, inv_smul_smul₀ hk]

/-- Multiplying by `k + 1` and then applying the scalar `1 / (k + 1)` of a semifield `K`, acting
through a `K`-algebra `R` on a semiring `A` that is an `R`-module, cancel, provided `k + 1` is
nonzero in `K`. This is the simp-normal form of `(k + 1) * ((1 / (k + 1)) • a)` in an `R`-algebra
`A`. -/
@[simp]
theorem algebraMap_inv_natCast_add_one_smul_natCast_add_one_mul {K R A : Type*} [Semifield K]
    [Semiring R] [Algebra K R] [Semiring A] [Module R A] (k : ℕ) (hk : (k : K) + 1 ≠ 0) (a : A) :
    algebraMap K R ((k : K) + 1)⁻¹ • (((k : A) + 1) * a) = a := by
  simpa [nsmul_eq_mul] using
    algebraMap_inv_natCast_smul_nsmul (R := R) (m := k + 1) (by simpa using hk) a

end TauCeti
