/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RingTheory.LaurentSeries.Ramified

/-!
# Combined Adams dilation on `(R⸨X⸩)⟦X⟧`

This file defines the combined Adams substitution `PowerSeries.adamsExpand R n` (`ψ ^ n`) on formal
power series with Laurent-series coefficients `(R⸨X⸩)⟦X⟧`, dilating both the inner Laurent
variable `q ↦ q ^ n` (via `LaurentSeries.expand`) and the outer power-series variable `t ↦ t ^ n`
(via `PowerSeries.expand`), over any commutative ring `R`.

## Main definitions

* `PowerSeries.adamsExpand R n`: `R`-algebra endomorphism `ψ ^ n` of `(R⸨X⸩)⟦X⟧`.

## Main results

* `PowerSeries.coeff_adamsExpand_mul`, `PowerSeries.coeff_adamsExpand_of_not_dvd`: outer
  `t`-coefficients of `ψ ^ n (F)`.
* `PowerSeries.coeff_coeff_adamsExpand`: double-coefficient formula for `[q ^ i t ^ k] ψ ^ n (F)`.
* `PowerSeries.adamsExpand_one`, `PowerSeries.adamsExpand_comp_adamsExpand`,
  `PowerSeries.adamsExpand_adamsExpand`: identity and functoriality `ψ ^ m ∘ ψ ^ n = ψ ^ (m * n)`.
* `PowerSeries.map_adamsExpand`: compatibility with coefficientwise ring homomorphisms.
-/

public section

open HahnSeries
open scoped LaurentSeries PowerSeries

namespace PowerSeries

section AdamsExpand

variable (R : Type*) [CommRing R]

/-- The **combined Adams substitution** `ψ ^ n` on `(R⸨X⸩)⟦X⟧`, dilating both the Laurent variable
`q ↦ q ^ n` (via `LaurentSeries.expand`) and the power-series variable `t ↦ t ^ n` (via
`PowerSeries.expand`). -/
noncomputable def adamsExpand (n : ℕ+) : (R⸨X⸩)⟦X⟧ →ₐ[R] (R⸨X⸩)⟦X⟧ :=
  ((PowerSeries.expand (n : ℕ) n.ne_zero).restrictScalars R).comp
    (PowerSeries.mapAlgHom (LaurentSeries.expand R n))

variable {R}

/-- Unfolding formula for `PowerSeries.adamsExpand`. -/
theorem adamsExpand_apply (n : ℕ+) (F : (R⸨X⸩)⟦X⟧) :
    adamsExpand R n F =
      PowerSeries.expand (n : ℕ) n.ne_zero
        (PowerSeries.map (LaurentSeries.expand R n).toRingHom F) :=
  (rfl)

/-- The `t ^ (n * k)` coefficient of `ψ ^ n (F)` is `LaurentSeries.expand R n (coeff k F)`. -/
@[simp] theorem coeff_adamsExpand_mul (n : ℕ+) (F : (R⸨X⸩)⟦X⟧) (k : ℕ) :
    coeff ((n : ℕ) * k) (adamsExpand R n F) = LaurentSeries.expand R n (coeff k F) := by
  rw [adamsExpand_apply, coeff_expand_mul, coeff_map, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]

/-- Coefficients of `ψ ^ n (F)` at `t`-exponents not divisible by `n` vanish. -/
theorem coeff_adamsExpand_of_not_dvd (n : ℕ+) (F : (R⸨X⸩)⟦X⟧) {k : ℕ} (hk : ¬ (n : ℕ) ∣ k) :
    coeff k (adamsExpand R n F) = 0 :=
  coeff_expand_of_not_dvd (n : ℕ) n.ne_zero _ hk

/-- The `[q ^ (n * i) t ^ (n * k)]` coefficient of `ψ ^ n (F)` equals `[q ^ i t ^ k] F`. -/
theorem coeff_coeff_adamsExpand_mul (n : ℕ+) (F : (R⸨X⸩)⟦X⟧) (k : ℕ) (i : ℤ) :
    (coeff ((n : ℕ) * k) (adamsExpand R n F)).coeff ((n : ℤ) * i) = (coeff k F).coeff i := by
  rw [coeff_adamsExpand_mul, LaurentSeries.coeff_expand_mul]

/-- Double-coefficient formula for `adamsExpand`: `[q ^ i t ^ k] ψ ^ n (F)` equals
`[q ^ (i / n) t ^ (k / n)] F` when `n` divides both `k` and `i`, and `0` otherwise. -/
theorem coeff_coeff_adamsExpand (n : ℕ+) (F : (R⸨X⸩)⟦X⟧) (k : ℕ) (i : ℤ) :
    (coeff k (adamsExpand R n F)).coeff i =
      if (n : ℕ) ∣ k ∧ (n : ℤ) ∣ i then (coeff (k / (n : ℕ)) F).coeff (i / (n : ℤ)) else 0 := by
  by_cases hk : (n : ℕ) ∣ k
  · obtain ⟨d, rfl⟩ := hk
    by_cases hi : (n : ℤ) ∣ i
    · obtain ⟨u, rfl⟩ := hi
      rw [ite_eq_left ⟨dvd_mul_right _ _, dvd_mul_right _ _⟩, coeff_coeff_adamsExpand_mul,
        Nat.mul_div_cancel_left _ n.pos,
        Int.mul_ediv_cancel_left _ (Int.natCast_ne_zero.mpr n.ne_zero)]
    · simp [hi, coeff_adamsExpand_mul, LaurentSeries.coeff_expand_of_not_dvd n _ hi]
  · simp [hk, coeff_adamsExpand_of_not_dvd n F hk]

/-- `ψ ^ n` acts on `t`-constants by `LaurentSeries.expand R n`. -/
@[simp] theorem adamsExpand_C (n : ℕ+) (c : R⸨X⸩) :
    adamsExpand R n (C c) = C (LaurentSeries.expand R n c) := by
  rw [adamsExpand_apply, map_C, expand_C, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]

/-- `ψ ^ n` fixes scalar constants `C (HahnSeries.C r)`. -/
theorem adamsExpand_C_const (n : ℕ+) (r : R) :
    adamsExpand R n (C (HahnSeries.C r)) = C (HahnSeries.C r) := by
  rw [adamsExpand_C, HahnSeries.C_apply, LaurentSeries.expand_single, mul_zero]

/-- `ψ ^ n` sends `t` to `t ^ n`. -/
@[simp] theorem adamsExpand_X (n : ℕ+) :
    adamsExpand R n (X : (R⸨X⸩)⟦X⟧) = X ^ (n : ℕ) := by
  rw [adamsExpand_apply, map_X, expand_X]

/-- `ψ ^ n` sends the monomial `r q ^ i t ^ j` to `r q ^ (n i) t ^ (n j)`. -/
@[simp] theorem adamsExpand_C_single_mul_X_pow (n : ℕ+) (i : ℤ) (r : R) (j : ℕ) :
    adamsExpand R n (C (single i r) * X ^ j) =
      C (single ((n : ℤ) * i) r) * X ^ ((n : ℕ) * j) := by
  rw [map_mul, adamsExpand_C, LaurentSeries.expand_single, map_pow, adamsExpand_X, ← pow_mul]

/-- The `t`-constant term of `ψ ^ n (F)` is `LaurentSeries.expand R n (constantCoeff F)`. -/
@[simp] theorem constantCoeff_adamsExpand (n : ℕ+) (F : (R⸨X⸩)⟦X⟧) :
    constantCoeff (adamsExpand R n F) = LaurentSeries.expand R n (constantCoeff F) := by
  rw [← coeff_zero_eq_constantCoeff_apply, ← mul_zero (n : ℕ), coeff_adamsExpand_mul,
    coeff_zero_eq_constantCoeff_apply]

variable (R) in
/-- `ψ ^ 1` is the identity algebra homomorphism. -/
@[simp] theorem adamsExpand_one : adamsExpand R 1 = AlgHom.id R (R⸨X⸩)⟦X⟧ := by
  ext F k i; simpa using coeff_coeff_adamsExpand_mul 1 F k i

variable (R) in
/-- Functoriality of combined Adams dilation as algebra endomorphisms:
`ψ ^ m ∘ ψ ^ n = ψ ^ (m * n)`. -/
@[simp] theorem adamsExpand_comp_adamsExpand (m n : ℕ+) :
    (adamsExpand R m).comp (adamsExpand R n) = adamsExpand R (m * n) := by
  apply AlgHom.ext; intro F
  have hcomp :
      (LaurentSeries.expand R m).toRingHom.comp (LaurentSeries.expand R n).toRingHom =
        (LaurentSeries.expand R (m * n)).toRingHom :=
    RingHom.ext (LaurentSeries.expand_expand m n)
  rw [AlgHom.comp_apply, adamsExpand_apply, adamsExpand_apply, adamsExpand_apply,
    map_expand (n : ℕ) n.ne_zero (LaurentSeries.expand R m).toRingHom,
    ← expand_mul (m : ℕ) m.ne_zero (n : ℕ) n.ne_zero, ← RingHom.comp_apply,
    ← PowerSeries.map_comp, hcomp]
  simp only [PNat.mul_coe]

/-- Functoriality of combined Adams dilation: `ψ ^ m (ψ ^ n (F)) = ψ ^ (m * n) (F)`. -/
@[simp] theorem adamsExpand_adamsExpand (m n : ℕ+) (F : (R⸨X⸩)⟦X⟧) :
    adamsExpand R m (adamsExpand R n F) = adamsExpand R (m * n) F :=
  AlgHom.congr_fun (adamsExpand_comp_adamsExpand R m n) F

/-- Coefficientwise ring homomorphisms commute with `PowerSeries.adamsExpand`. -/
theorem map_adamsExpand {S : Type*} [CommRing S] (φ : R →+* S) (n : ℕ+) (F : (R⸨X⸩)⟦X⟧) :
    PowerSeries.map (HahnSeries.mapRingHom φ) (adamsExpand R n F) =
      adamsExpand S n (PowerSeries.map (HahnSeries.mapRingHom φ) F) := by
  have hcomp :
      (HahnSeries.mapRingHom φ).comp (LaurentSeries.expand R n).toRingHom =
        (LaurentSeries.expand S n).toRingHom.comp (HahnSeries.mapRingHom φ) :=
    RingHom.ext (LaurentSeries.mapRingHom_expand φ n)
  rw [adamsExpand_apply, adamsExpand_apply, map_expand, ← RingHom.comp_apply,
    ← PowerSeries.map_comp, ← RingHom.comp_apply, ← PowerSeries.map_comp, hcomp]

end AdamsExpand

end PowerSeries
