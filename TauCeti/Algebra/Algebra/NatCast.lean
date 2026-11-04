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

In a `ℚ`-algebra every positive natural number is invertible, so dividing by `k + 1` and
multiplying by `k + 1` cancel. This is how termwise integration of power series inverts
differentiation.

## Main results

* `IsUnit.natCast_ne_zero_of_algebra`: if `(m : K)` is a unit then `(m : L) ≠ 0`.
* `IsUnit.neZero_natCast`: a natural number invertible in a nontrivial semiring is nonzero.
* `Nat.Coprime.isUnit_natCast_of_prime`: if every prime distinct from `n` is a unit in `R`, then
  every nonzero natural number coprime to `n` is a unit in `R`.
* `Subalgebra.natCast_mul_mem_iff`: if `(m : K)` is a unit, a `K`-subalgebra contains `m * t`
  exactly when it contains `t`.
* `TauCeti.isUnit_natCast_of_ne_zero`: every nonzero natural number is a unit in a `ℚ`-algebra.
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

/-- If every prime distinct from `n` is a unit in a semiring `R`, then every nonzero natural number
coprime to `n` is a unit in `R`, as a product of prime factors distinct from `n`. -/
theorem Nat.Coprime.isUnit_natCast_of_prime {R : Type*} [Semiring R] {m n : ℕ}
    (h : m.Coprime n) (hm : m ≠ 0) (hunit : ∀ q : ℕ, q.Prime → q ≠ n → IsUnit (q : R)) :
    IsUnit (m : R) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rcases eq_or_ne m 1 with rfl | hm1
    · simp
    set q := m.minFac
    have hq : q.Prime := Nat.minFac_prime hm1
    have hqm : m = q * (m / q) := (Nat.mul_div_cancel' (Nat.minFac_dvd m)).symm
    have hmul : (q * (m / q)).Coprime n := hqm ▸ h
    have hq_cop : q.Coprime n := (Nat.coprime_mul_iff_left.mp hmul).1
    have hk_cop : (m / q).Coprime n := (Nat.coprime_mul_iff_left.mp hmul).2
    have hqn : q ≠ n := fun hqn ↦ hq.ne_one (by simpa [← hqn, Nat.gcd_self] using hq_cop.gcd_eq_one)
    have hk_lt : m / q < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm) hq.one_lt
    have hk0 : m / q ≠ 0 := right_ne_zero_of_mul (hqm ▸ hm)
    rw [hqm, Nat.cast_mul]
    exact (hunit q hq hqn).mul (ih (m / q) hk_lt hk_cop hk0)

/-- A subalgebra over `K` contains `m * t` exactly when it contains `t`, provided the natural
number `m` is invertible in `K`. -/
theorem Subalgebra.natCast_mul_mem_iff {K L : Type*} [CommSemiring K] [Semiring L] [Algebra K L]
    (T : Subalgebra K L) {m : ℕ} (hm : IsUnit (m : K)) {t : L} : (m : L) * t ∈ T ↔ t ∈ T := by
  rw [← nsmul_eq_mul, ← Nat.cast_smul_eq_nsmul K]
  exact Submodule.smul_mem_iff_of_isUnit (Subalgebra.toSubmodule T) hm

namespace TauCeti

/-- Every nonzero natural number is a unit in a `ℚ`-algebra. -/
theorem isUnit_natCast_of_ne_zero {K : Type*} [Semiring K] [Algebra ℚ K] {m : ℕ}
    (hm : m ≠ 0) : IsUnit (m : K) := by
  simpa using (Nat.cast_ne_zero.2 hm : (m : ℚ) ≠ 0).isUnit.map (algebraMap ℚ K)

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
