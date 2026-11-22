/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic

/-!
# Natural numbers invertible in algebras

A natural number that is a unit in `K` stays nonzero in every nontrivial `K`-algebra `L`. Results
stated over an extension, such as the separable closure `Kˢ`, often need `(m : L) ≠ 0`, while the
hypothesis available is `IsUnit (m : K)`, which holds for every `m ≠ 0` in an algebra over a
characteristic-zero semifield, such as a `ℚ`-algebra.
Likewise a subalgebra over `K` is closed under division by such a natural number.

In an algebra over a characteristic-zero semifield `K` (for instance `K = ℚ`) every positive
natural number is invertible. Over any semifield `K`, multiplying by a natural number `m` cancels
the inverse `m⁻¹`, taken in `K`, whenever `(m : K) ≠ 0`. With `m = k + 1` this is how termwise
integration of power series with zero constant term is a right inverse of differentiation:
differentiating the integral returns the series, while integrating a derivative recovers only the
terms of positive degree.

The hypotheses `[Semifield K] [CharZero K] [Algebra K A]` of the three unit lemmas, and their
explicit base argument `K`, follow Mathlib's `IsUnit.natCast_factorial_of_algebra`.

## Main results

* `IsUnit.ofNat_of_algebra`: if a numeral is a unit in `K` then it is a unit in `L`.
* `IsUnit.natCast_ne_zero_of_algebra`: if `(m : K)` is a unit then `(m : L) ≠ 0`.
* `Subalgebra.natCast_mul_mem_iff`: if `(m : K)` is a unit, a `K`-subalgebra contains `m * t`
  exactly when it contains `t`.
* `TauCeti.isUnit_natCast_of_ne_zero`, `TauCeti.isUnit_natCast_add_of_ne_zero`,
  `TauCeti.isUnit_natCast_add_one`: every nonzero natural number (in particular `(m : A) + k` for
  `k ≠ 0` and `(m : A) + 1`) is a unit in an algebra `A` over a characteristic-zero semifield `K`.

The remaining results hold for an algebra over any semifield `K`; in each, the inverse is taken in
`K` and then mapped into the algebra or used as a scalar.

* `TauCeti.natCast_mul_algebraMap_inv`: `m · (1 / m) = 1` in a `K`-algebra, when `(m : K) ≠ 0`.
* `TauCeti.inv_natCast_add_one_smul_mul_natCast_add_one`: `(k + 1)⁻¹ • a * (k + 1) = a` in a
  `K`-algebra, when `(k : K) + 1 ≠ 0`.
* `TauCeti.natCast_add_one_mul_algebraMap_inv_smul`: `(k + 1) * ((1 / (k + 1)) • a) = a` in an
  algebra over a `K`-algebra, the scalar `1 / (k + 1)` coming from `K`, when `(k : K) + 1 ≠ 0`.
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

/-- A subalgebra over `K` contains `m * t` exactly when it contains `t`, provided the natural
number `m` is invertible in `K`. -/
theorem Subalgebra.natCast_mul_mem_iff {K L : Type*} [CommSemiring K] [Semiring L] [Algebra K L]
    (T : Subalgebra K L) {m : ℕ} (hm : IsUnit (m : K)) {t : L} : (m : L) * t ∈ T ↔ t ∈ T := by
  rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul K]
  exact Submodule.smul_mem_iff_of_isUnit (Subalgebra.toSubmodule T) hm

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

/-- Multiplying by a natural number `m` and by the image of `m⁻¹ : K` cancel in an algebra over a
semifield `K`, provided `m` is nonzero in `K`. -/
@[simp]
theorem natCast_mul_algebraMap_inv {K A : Type*} [Semifield K] [Semiring A] [Algebra K A] {m : ℕ}
    (hm : (m : K) ≠ 0) : (m : A) * algebraMap K A (m : K)⁻¹ = 1 := by
  simpa using congrArg (algebraMap K A) (mul_inv_cancel₀ hm)

/-- Dividing by `k + 1` and multiplying by `k + 1` cancel in an algebra over a semifield `K`,
provided `k + 1` is nonzero in `K`. -/
theorem inv_natCast_add_one_smul_mul_natCast_add_one {K R : Type*} [Semifield K] [Semiring R]
    [Algebra K R] (a : R) (k : ℕ) (hk : (k : K) + 1 ≠ 0) :
    ((k : K) + 1)⁻¹ • a * ((k : R) + 1) = a := by
  have hcast : (k : R) + 1 = algebraMap K R ((k : K) + 1) := by simp
  rw [hcast, ← Algebra.commutes, ← Algebra.smul_def, smul_smul, mul_inv_cancel₀ hk, one_smul]

/-- Multiplying by `k + 1` cancels the scalar `1 / (k + 1)` of a semifield `K` acting, through a
`K`-algebra `R`, on an `R`-algebra `A`, provided `k + 1` is nonzero in `K`. -/
theorem natCast_add_one_mul_algebraMap_inv_smul {K R A : Type*} [Semifield K] [CommSemiring R]
    [Algebra K R] [Semiring A] [Algebra R A] (k : ℕ) (hk : (k : K) + 1 ≠ 0) (a : A) :
    ((k : A) + 1) * (algebraMap K R ((k : K) + 1)⁻¹ • a) = a := by
  have h : ((k : R) + 1) * algebraMap K R ((k : K) + 1)⁻¹ = 1 := by
    simpa using natCast_mul_algebraMap_inv (A := R) (m := k + 1) (by rwa [Nat.cast_add_one])
  have hcast : (k : A) + 1 = algebraMap R A ((k : R) + 1) := by simp
  rw [Algebra.smul_def, ← mul_assoc, hcast, ← map_mul]
  simp [h]

end TauCeti
