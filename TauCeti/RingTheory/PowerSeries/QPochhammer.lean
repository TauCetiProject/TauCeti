/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.PowerSeries.Basic

/-!
# Formal shifted `q`-Pochhammer power series

`TauCeti.qPochhammerSeries N c x` is defined unconditionally as the power series in `R⟦X⟧` whose
`m`-th coefficient is the `m`-th coefficient of the partial product
`∏ n ∈ Finset.range (m + 1), (1 - C x * X ^ (N * n + c))`. When `0 < N` (for every `c : ℕ`,
including `c = 0`), all factors with `n ≥ m + 1` have degree at least `m + 1`, so the partial
products stabilize in each degree (`coeff_qPochhammerSeries_eq_coeff_prod_range`) and
`qPochhammerSeries N c x` represents the formal infinite product `∏_{n ≥ 0} (1 - x X^{N n + c})`
satisfying `qPochhammerSeries_eq_one_sub_mul` and `qPochhammerSeries_eq_prod_range_mul`. When
`N = 0`, it is only a finite truncation (`∏_{n ≤ m} (1 - x X^c)`) rather than an infinite product.
-/

public noncomputable section

namespace TauCeti

variable {R S : Type*} [CommRing R] [CommRing S]

/-- The formal shifted `q`-Pochhammer power series over a commutative ring `R`, defined
unconditionally so that its `m`-th coefficient is that of the partial product
`∏ n ∈ Finset.range (m + 1), (1 - C x * X ^ (N * n + c))`. For `0 < N`, the partial products
stabilize in each degree and model the infinite product `∏_{n ≥ 0} (1 - x X^{N n + c})`; for
`N = 0`, this is a formal degree-indexed truncation. -/
def qPochhammerSeries (N c : ℕ) (x : R) : PowerSeries R :=
  PowerSeries.mk fun m ↦ PowerSeries.coeff m
    (∏ n ∈ Finset.range (m + 1), (1 - PowerSeries.C x * PowerSeries.X ^ (N * n + c)))

/-- The `m`-th coefficient of `qPochhammerSeries N c x` is that of the partial product over
`n < m + 1`. -/
theorem coeff_qPochhammerSeries (N c : ℕ) (x : R) (m : ℕ) :
    (qPochhammerSeries N c x).coeff m = PowerSeries.coeff m
      (∏ n ∈ Finset.range (m + 1), (1 - PowerSeries.C x * PowerSeries.X ^ (N * n + c))) :=
  PowerSeries.coeff_mk m _

/-- For `0 < c`, the constant coefficient of `qPochhammerSeries N c x` is `1`. -/
@[simp]
theorem constantCoeff_qPochhammerSeries {N c : ℕ} (hc : 0 < c) (x : R) :
    PowerSeries.constantCoeff (qPochhammerSeries N c x) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_qPochhammerSeries]
  simp [hc.ne']

/-- At `c = 0`, the constant coefficient of `qPochhammerSeries N 0 x` is `1 - x`. -/
@[simp]
theorem constantCoeff_qPochhammerSeries_zero (N : ℕ) (x : R) :
    PowerSeries.constantCoeff (qPochhammerSeries N 0 x) = 1 - x := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff, coeff_qPochhammerSeries]
  simp

/-- Mapping coefficients along a ring homomorphism commutes with `qPochhammerSeries`. -/
@[simp]
theorem map_qPochhammerSeries (f : R →+* S) (N c : ℕ) (x : R) :
    (qPochhammerSeries N c x).map f = qPochhammerSeries N c (f x) := by
  ext m
  rw [PowerSeries.coeff_map, coeff_qPochhammerSeries, coeff_qPochhammerSeries,
    ← PowerSeries.coeff_map]
  simp

/-- At `x = 0`, `qPochhammerSeries N c 0 = 1`. -/
@[simp]
theorem qPochhammerSeries_zero (N c : ℕ) : qPochhammerSeries N c (0 : R) = 1 := by
  ext m
  simp [coeff_qPochhammerSeries]

/-- For `0 < N`, the `m`-th coefficient of `qPochhammerSeries N c x` agrees with that of the
partial product of any length `K ≥ m + 1`. -/
theorem coeff_qPochhammerSeries_eq_coeff_prod_range {N : ℕ} (hN : 0 < N) (c : ℕ) (x : R)
    {m K : ℕ} (hmK : m + 1 ≤ K) :
    (qPochhammerSeries N c x).coeff m = PowerSeries.coeff m
      (∏ n ∈ Finset.range K, (1 - PowerSeries.C x * PowerSeries.X ^ (N * n + c))) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmK
  induction d with
  | zero => rw [add_zero, coeff_qPochhammerSeries]
  | succ d ih =>
    rw [← add_assoc, Finset.prod_range_succ, mul_sub, mul_one, map_sub,
      ← ih (Nat.le_add_right (m + 1) d), mul_comm _ (PowerSeries.C x * _), mul_assoc,
      PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul']
    simp [(by have := Nat.mul_le_mul hN (Nat.le_add_right (m + 1) d); omega :
      m < N * (m + 1 + d) + c).not_ge]

/-- **Shift recurrence for `qPochhammerSeries`.** For `0 < N`, splitting off the `n = 0` factor
gives `qPochhammerSeries N c x = (1 - C x * X ^ c) * qPochhammerSeries N (N + c) x`. -/
theorem qPochhammerSeries_eq_one_sub_mul {N : ℕ} (hN : 0 < N) (c : ℕ) (x : R) :
    qPochhammerSeries N c x =
      (1 - PowerSeries.C x * PowerSeries.X ^ c) * qPochhammerSeries N (N + c) x := by
  ext m
  rw [coeff_qPochhammerSeries_eq_coeff_prod_range hN c x (by omega : m + 1 ≤ m + 2),
    Finset.prod_range_succ', mul_zero, zero_add, mul_comm, PowerSeries.coeff_mul,
    PowerSeries.coeff_mul]
  refine Finset.sum_congr rfl fun p hp ↦ ?_
  have hshift (n : ℕ) : N * (n + 1) + c = N * n + (N + c) := by rw [Nat.mul_succ]; ring
  simp_rw [hshift]
  rw [coeff_qPochhammerSeries_eq_coeff_prod_range hN (N + c) x
    (by have := Finset.mem_antidiagonal.mp hp; omega : p.2 + 1 ≤ m + 1)]

/-- Splitting off the first `k` factors of `qPochhammerSeries N c x` for `0 < N`. -/
theorem qPochhammerSeries_eq_prod_range_mul {N : ℕ} (hN : 0 < N) (c k : ℕ) (x : R) :
    qPochhammerSeries N c x =
      (∏ n ∈ Finset.range k, (1 - PowerSeries.C x * PowerSeries.X ^ (N * n + c))) *
        qPochhammerSeries N (N * k + c) x := by
  induction k generalizing c with
  | zero => simp
  | succ k ih =>
    have hshift (n : ℕ) : N * n + (N + c) = N * (n + 1) + c := by rw [Nat.mul_succ]; ring
    rw [qPochhammerSeries_eq_one_sub_mul hN c x, ih (N + c), Finset.prod_range_succ', mul_zero,
      zero_add]
    simp_rw [hshift]
    rw [Nat.mul_succ]
    ring_nf

end TauCeti
