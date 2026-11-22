/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.Algebra.Field.Rat
public import Mathlib.Data.Nat.Prime.Defs

/-!
# Natural numbers invertible in semirings and algebras

A natural number that is a unit in `K` stays nonzero in every nontrivial `K`-algebra `L`. Results
stated over an extension, such as the separable closure `Kˢ`, often need `(m : L) ≠ 0`, while the
hypothesis available is `IsUnit (m : K)`, which holds for every `m ≠ 0` in an algebra over a
characteristic-zero semifield, such as a `ℚ`-algebra.
Likewise a subalgebra over `K` is closed under division by such a natural number.

Because natural-number casts commute with every element of a semiring, any divisor of an invertible
natural cast is again a unit, and a nonzero natural number casts to a unit if and only if each of
its prime factors does.

In an algebra over a characteristic-zero semifield `K` (for instance `K = ℚ`) every positive
natural number is invertible, so dividing by `k + 1` and multiplying by `k + 1` cancel. This is
how termwise integration of power series inverts differentiation.

## Main results

* `IsUnit.ofNat_of_algebra`: if a numeral is a unit in `K` then it is a unit in `L`.
* `IsUnit.natCast_ne_zero_of_algebra`: if `(m : K)` is a unit then `(m : L) ≠ 0`.
* `IsUnit.neZero_natCast`: a natural number invertible in a nontrivial semiring is nonzero.
* `IsUnit.natCast_of_dvd`: a divisor of a natural number casting to a unit also casts to a unit.
* `Subalgebra.natCast_mul_mem_iff`: if `(m : K)` is a unit, a `K`-subalgebra contains `m * t`
  exactly when it contains `t`.
* `TauCeti.isUnit_natCast_of_forall_prime_dvd`, `TauCeti.isUnit_natCast_iff_forall_prime_dvd`: a
  nonzero natural number casts to a unit in a semiring if and only if all of its prime divisors do.
* `TauCeti.isUnit_natCast_of_ne_zero`, `TauCeti.isUnit_natCast_add_of_ne_zero`,
  `TauCeti.isUnit_natCast_add_one`: every nonzero natural number (in particular `(m : A) + k` for
  `k ≠ 0` and `(m : A) + 1`) is a unit in an algebra `A` over a characteristic-zero semifield `K`.
* `TauCeti.natCast_mul_algebraMap_inv`: `m · (1 / m) = 1` in a `K`-algebra, for `m ≠ 0`.
* `TauCeti.inv_natCast_add_one_smul_mul_natCast_add_one`: `(k + 1)⁻¹ • a * (k + 1) = a` in a
  `K`-algebra.
* `TauCeti.natCast_add_one_mul_algebraMap_inv_smul`: `(k + 1) * ((1 / (k + 1)) • a) = a` in an
  algebra over a `K`-algebra, the scalar `1 / (k + 1)` coming from `K`.
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

/-- A natural number invertible in a nontrivial semiring is nonzero as a natural number. -/
theorem IsUnit.neZero_natCast {R : Type*} [Semiring R] [Nontrivial R] {m : ℕ}
    (hm : IsUnit (m : R)) : NeZero m :=
  ⟨fun h ↦ hm.ne_zero (by rw [h, Nat.cast_zero])⟩

/-- A divisor of a natural number casting to a unit in a semiring also casts to a unit. -/
theorem IsUnit.natCast_of_dvd {R : Type*} [Semiring R] {m n : ℕ}
    (hn : IsUnit (n : R)) (hmn : m ∣ n) : IsUnit (m : R) := by
  obtain ⟨k, rfl⟩ := hmn
  rw [Nat.cast_mul, (Nat.cast_commute m (k : R)).isUnit_mul_iff] at hn
  exact hn.1

/-- A subalgebra over `K` contains `m * t` exactly when it contains `t`, provided the natural
number `m` is invertible in `K`. -/
theorem Subalgebra.natCast_mul_mem_iff {K L : Type*} [CommSemiring K] [Semiring L] [Algebra K L]
    (T : Subalgebra K L) {m : ℕ} (hm : IsUnit (m : K)) {t : L} : (m : L) * t ∈ T ↔ t ∈ T := by
  rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul K]
  exact Submodule.smul_mem_iff_of_isUnit (Subalgebra.toSubmodule T) hm

namespace TauCeti

/-- A nonzero natural number casts to a unit in a semiring whenever all of its prime divisors do. -/
theorem isUnit_natCast_of_forall_prime_dvd {R : Type*} [Semiring R] {n : ℕ} (hn : n ≠ 0)
    (hp : ∀ p : ℕ, p.Prime → p ∣ n → IsUnit (p : R)) : IsUnit (n : R) := by
  induction n using Nat.strongRecOn with | ind n ih => ?_
  rcases eq_or_ne n 1 with rfl | hn1
  · simp
  -- Split off the least prime factor `n.minFac` and recurse on the cofactor `m < n`.
  obtain ⟨m, hm⟩ := n.minFac_dvd
  have hm0 : m ≠ 0 := by rintro rfl; exact hn hm
  have hmn : m < n := hm ▸ (Nat.lt_mul_iff_one_lt_left hm0.bot_lt).2 (Nat.minFac_prime hn1).one_lt
  rw [hm, Nat.cast_mul]
  exact (hp _ (Nat.minFac_prime hn1) n.minFac_dvd).mul
    (ih m hmn hm0 fun q hq hqm ↦ hp q hq (hqm.trans (Dvd.intro_left _ hm.symm)))

/-- A nonzero natural number casts to a unit in a semiring if and only if all of its prime divisors
cast to units. -/
theorem isUnit_natCast_iff_forall_prime_dvd {R : Type*} [Semiring R] {n : ℕ} (hn : n ≠ 0) :
    IsUnit (n : R) ↔ ∀ p : ℕ, p.Prime → p ∣ n → IsUnit (p : R) :=
  ⟨fun hu _ _ hpn ↦ hu.natCast_of_dvd hpn, isUnit_natCast_of_forall_prime_dvd hn⟩

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

/-- Multiplying by a nonzero natural number `m` and by the image of `m⁻¹ : K` cancel in an algebra
over a characteristic-zero semifield `K`. -/
theorem natCast_mul_algebraMap_inv {K A : Type*} [Semifield K] [CharZero K] [Semiring A]
    [Algebra K A] {m : ℕ} (hm : m ≠ 0) : (m : A) * algebraMap K A (m : K)⁻¹ = 1 := by
  rw [← map_natCast (algebraMap K A), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hm), map_one]

/-- Dividing by `k + 1` and multiplying by `k + 1` cancel in an algebra over a characteristic-zero
semifield `K`. -/
theorem inv_natCast_add_one_smul_mul_natCast_add_one {K R : Type*} [Semifield K] [CharZero K]
    [Semiring R] [Algebra K R] (a : R) (k : ℕ) : ((k : K) + 1)⁻¹ • a * ((k : R) + 1) = a := by
  have hcast : (k : R) + 1 = algebraMap K R ((k : K) + 1) := by simp
  rw [hcast, ← Algebra.commutes, ← Algebra.smul_def, smul_smul]
  simp [Nat.cast_add_one_ne_zero]

/-- Multiplying by `k + 1` cancels the scalar `1 / (k + 1)` of a characteristic-zero semifield `K`
acting, through a `K`-algebra `R`, on an `R`-algebra `A`. -/
theorem natCast_add_one_mul_algebraMap_inv_smul {K R A : Type*} [Semifield K] [CharZero K]
    [CommSemiring R] [Algebra K R] [Semiring A] [Algebra R A] (k : ℕ) (a : A) :
    ((k : A) + 1) * (algebraMap K R ((k : K) + 1)⁻¹ • a) = a := by
  have h := natCast_mul_algebraMap_inv (K := K) (A := R) k.succ_ne_zero
  push_cast at h
  have hcast : (k : A) + 1 = algebraMap R A ((k : R) + 1) := by simp
  rw [Algebra.smul_def, ← mul_assoc, hcast, ← map_mul, h, map_one, one_mul]

end TauCeti
