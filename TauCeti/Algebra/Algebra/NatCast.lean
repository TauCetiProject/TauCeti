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
hypothesis available is `IsUnit (m : K)`, which holds for every `m ≠ 0` in a `ℚ`-algebra.
Likewise a subalgebra over `K` is closed under division by such a natural number.

Because natural-number casts commute with every element of a semiring, any divisor of an invertible
natural cast is again a unit, and a nonzero natural number casts to a unit if and only if each of
its prime factors does.

In a `ℚ`-algebra every positive natural number is invertible, so dividing by `k + 1` and
multiplying by `k + 1` cancel. This is how termwise integration of power series inverts
differentiation.

## Main results

* `IsUnit.natCast_ne_zero_of_algebra`: if `(m : K)` is a unit then `(m : L) ≠ 0`.
* `IsUnit.neZero_natCast`: a natural number invertible in a nontrivial semiring is nonzero.
* `IsUnit.natCast_of_dvd`: a divisor of a natural number casting to a unit also casts to a unit.
* `Subalgebra.natCast_mul_mem_iff`: if `(m : K)` is a unit, a `K`-subalgebra contains `m * t`
  exactly when it contains `t`.
* `TauCeti.isUnit_natCast_of_forall_prime_dvd`, `TauCeti.isUnit_natCast_iff_forall_prime_dvd`: a
  nonzero natural number casts to a unit in a semiring if and only if all of its prime divisors do.
* `TauCeti.isUnit_natCast_of_ne_zero`, `TauCeti.isUnit_natCast_add_of_ne_zero`,
  `TauCeti.isUnit_natCast_add_one`: every nonzero natural number (in particular `(m : K) + k` for
  `k ≠ 0` and `(m : K) + 1`) is a unit in a `ℚ`-algebra.
* `TauCeti.natCast_mul_algebraMap_inv`: `m · (1 / m) = 1` in a `ℚ`-algebra, for `m ≠ 0`.
* `TauCeti.inv_natCast_add_one_smul_mul_natCast_add_one`: `(k + 1)⁻¹ • a * (k + 1) = a` in a
  `ℚ`-algebra.
-/

public section

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
  induction n using Nat.strongRecOn with
  | ind n ih =>
    rcases eq_or_ne n 1 with rfl | hn1
    · rw [Nat.cast_one]
      exact isUnit_one
    · have hp_prime : n.minFac.Prime := Nat.minFac_prime hn1
      have hp_dvd : n.minFac ∣ n := n.minFac_dvd
      have hdiv_pos : 0 < n / n.minFac := Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hp_dvd)
        hp_prime.pos
      have hdiv_lt : n / n.minFac < n := Nat.div_lt_self (Nat.pos_of_ne_zero hn) hp_prime.one_lt
      have heq : n = n.minFac * (n / n.minFac) := (Nat.mul_div_cancel' hp_dvd).symm
      rw [heq, Nat.cast_mul]
      exact (hp n.minFac hp_prime hp_dvd).mul
        (ih (n / n.minFac) hdiv_lt hdiv_pos.ne' fun q hq hqd ↦
          hp q hq (hqd.trans ⟨n.minFac, by rw [mul_comm]; exact heq⟩))

/-- A nonzero natural number casts to a unit in a semiring if and only if all of its prime divisors
cast to units. -/
theorem isUnit_natCast_iff_forall_prime_dvd {R : Type*} [Semiring R] {n : ℕ} (hn : n ≠ 0) :
    IsUnit (n : R) ↔ ∀ p : ℕ, p.Prime → p ∣ n → IsUnit (p : R) :=
  ⟨fun hu _ _ hpn ↦ hu.natCast_of_dvd hpn, isUnit_natCast_of_forall_prime_dvd hn⟩

/-- Every nonzero natural number is a unit in a `ℚ`-algebra. -/
theorem isUnit_natCast_of_ne_zero {K : Type*} [Semiring K] [Algebra ℚ K] {m : ℕ}
    (hm : m ≠ 0) : IsUnit (m : K) := by
  simpa using (Nat.cast_ne_zero.2 hm : (m : ℚ) ≠ 0).isUnit.map (algebraMap ℚ K)

/-- Adding a nonzero natural number to a natural number gives a unit in a `ℚ`-algebra. -/
theorem isUnit_natCast_add_of_ne_zero {K : Type*} [Semiring K] [Algebra ℚ K] (m : ℕ) {k : ℕ}
    (hk : k ≠ 0) : IsUnit ((m : K) + k) := by
  simpa only [Nat.cast_add] using isUnit_natCast_of_ne_zero (K := K) (m := m + k) (by omega)

/-- For every natural number `m`, `(m : K) + 1` is a unit in a `ℚ`-algebra. -/
theorem isUnit_natCast_add_one {K : Type*} [Semiring K] [Algebra ℚ K] (m : ℕ) :
    IsUnit ((m : K) + 1) := by
  simpa only [Nat.cast_one] using isUnit_natCast_add_of_ne_zero (K := K) m one_ne_zero

/-- Multiplying by a nonzero natural number `m` and by the image of `m⁻¹ : ℚ` cancel in a
`ℚ`-algebra. -/
theorem natCast_mul_algebraMap_inv {K : Type*} [Semiring K] [Algebra ℚ K] {m : ℕ}
    (hm : m ≠ 0) : (m : K) * algebraMap ℚ K (m : ℚ)⁻¹ = 1 := by
  rw [← map_natCast (algebraMap ℚ K), ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.2 hm), map_one]

/-- Dividing by `k + 1` and multiplying by `k + 1` cancel in a `ℚ`-algebra. -/
theorem inv_natCast_add_one_smul_mul_natCast_add_one {R : Type*} [Semiring R] [Algebra ℚ R]
    (a : R) (k : ℕ) : ((k : ℚ) + 1)⁻¹ • a * ((k : R) + 1) = a := by
  have hcast : (k : R) + 1 = algebraMap ℚ R ((k : ℚ) + 1) := by simp
  rw [hcast, ← Algebra.commutes, ← Algebra.smul_def, smul_smul]
  simp [Nat.cast_add_one_ne_zero]

end TauCeti
